#include <Debug.h>
#include <kenshi/GameWorld.h>
#include <kenshi/PlayerInterface.h>
#include <kenshi/InputHandler.h>
#include <kenshi/Character.h>
#include <kenshi/CharMovement.h>
#include <kenshi/CombatClass.h>
#include <kenshi/CameraClass.h>
#include <kenshi/Globals.h>
#include <kenshi/Enums.h>
#include <kenshi/gui/ForgottenGUI.h>
#include <kenshi/gui/MainBarGUI.h>
#include <kenshi/gui/OrdersPanel.h>
#include <core/Functions.h>

#define WIN32_LEAN_AND_MEAN
#include <Windows.h>
#include <stdio.h>
#include <mygui/MyGUI.h>

// Set to 1 and rebuild to restore verbose per-frame diagnostic logs.
#define DIAG_VERBOSE 0

// Set to 1 to re-enable per-event retreat suppression logs + timing diagnostics.
// 0 = only log retreat start / end / summary (eliminates log spam with many enemies).
#define RETREAT_VERBOSE_DIAG 0

// Set to 1 to re-enable inventory/loot UI diagnostic logs (field states, widget names,
// per-second inventory window breakdown).  0 = silent in release builds.
#define LOOT_DIAG 0

// -----------------------------------------------------------------------
// Control modes
// -----------------------------------------------------------------------
enum ControlMode { MODE_VANILLA = 0, MODE_FREE_MOVE = 1 };

static volatile ControlMode s_mode   = MODE_VANILLA;
static volatile bool        s_wHeld  = false;
static volatile bool        s_aHeld  = false;
static volatile bool        s_sHeld  = false;
static volatile bool        s_dHeld  = false;
static volatile bool        s_xPressed = false;

// NPC loot UI suspension — blocks all V-Mode input and WASD injection while looting.
// s_mode is NOT changed; the suspend is a transparent pause that restores automatically.
static volatile bool   s_lootUiSuspendActive    = false;
static bool            s_lootUiWasPrevOpen      = false;
static ULONGLONG       s_lootSuspendStartTick   = 0;
static const ULONGLONG LOOT_SUSPEND_DEBOUNCE_MS = 250;

// Per-frame snapshot of volatile input state — set once at the top of mainLoop_hook,
// consumed by all per-character hooks that fire during s_mainLoopOrig.
// Eliminates per-character volatile reads (memory fence overhead) for hooks that
// fire 100+ times per frame in large enemy encounters.
static ControlMode s_frameMode        = MODE_VANILLA;
static bool        s_frameWasdHeld    = false;
static bool        s_frameLootSuspend = false;

// Melee/combat awareness range.  No separate middle zone.
static const float     ATTACK_RANGE    = 500.0f;
static const ULONGLONG SCAN_INTERVAL_MS = 5000; // squad-threat scan interval

static const char* modeName(ControlMode m)
{
    return m == MODE_FREE_MOVE ? "FREE_MOVE" : "VANILLA";
}

static void setMode(ControlMode next)
{
    ControlMode prev = s_mode;
    if (next == prev) return;
    s_mode = next;
    char buf[128];
    sprintf_s(buf, sizeof(buf), "[WASDCombat] MODE: %s -> %s", modeName(prev), modeName(next));
    DebugLog(buf);
}

// -----------------------------------------------------------------------
// Key press handler — poll thread only
// -----------------------------------------------------------------------
static void onPress(int vk)
{
    if (s_lootUiSuspendActive)
        return;
    if (vk == 'V')
    {
        if (s_mode == MODE_FREE_MOVE) setMode(MODE_VANILLA);
        else                          setMode(MODE_FREE_MOVE);
    }
    else if (vk == 'X')
    {
        if (s_mode == MODE_FREE_MOVE)
            s_xPressed = true;
    }
}

// -----------------------------------------------------------------------
// Polling thread
// -----------------------------------------------------------------------
struct PollKey { int vk; const char* name; bool prev; };
static PollKey s_keys[] =
{
    { 'W', "W", false }, { 'A', "A", false },
    { 'S', "S", false }, { 'D', "D", false },
    { 'V', "V", false }, { 'X', "X", false },
};
static const int NUM_KEYS = 6;

static bool isKenshiForeground()
{
    HWND fg = GetForegroundWindow();
    if (!fg) return false;
    DWORD pid = 0;
    GetWindowThreadProcessId(fg, &pid);
    return pid == GetCurrentProcessId();
}

static DWORD WINAPI PollThread(LPVOID)
{
    while (true)
    {
        Sleep(50);
        if (!isKenshiForeground()) continue;
        for (int i = 0; i < NUM_KEYS; ++i)
        {
            bool down = (GetAsyncKeyState(s_keys[i].vk) & 0x8000) != 0;
            if (down == s_keys[i].prev) continue;
            s_keys[i].prev = down;
            switch (s_keys[i].vk) {
                case 'W': s_wHeld = down; break;
                case 'A': s_aHeld = down; break;
                case 'S': s_sHeld = down; break;
                case 'D': s_dHeld = down; break;
            }
            if (down) onPress(s_keys[i].vk);
        }
    }
}

// -----------------------------------------------------------------------
// HUD — disabled for reload stability
// -----------------------------------------------------------------------
struct HudWidget { MyGUI::TextBox* label; bool shown; const char* tag;
    HudWidget() : label(nullptr), shown(false), tag("") {} };
static HudWidget s_vHud;
static bool      s_hudReady = false;
static void hudUpdate() {}

// -----------------------------------------------------------------------
// World state — main thread only
// -----------------------------------------------------------------------
static Character*    s_selectedCharacter = nullptr;
static CharMovement* s_selectedMovement  = nullptr;
static Character*    s_freeMoveAnchor    = nullptr;
static bool          s_wasdWasActive     = false;
static bool          s_combatWASDLogged  = false;
static bool          s_retreatLogged     = false;

static bool          s_squadThreat         = false;
static bool          s_consciousAllyThreat = false;

// Cached movement pointer — used by charMovUpdate_hook without dereferencing
// s_freeMoveAnchor (which may be freed during a LOADGAME transition).
static CharMovement* s_anchorMovement = nullptr;

static volatile bool s_loadGuardActive      = false;
static int           s_stabilizationCountdown = 0;
static bool          s_postLoadReacquire   = false;
static bool          s_enemyTargetingLogged = false;
static ULONGLONG     s_lastScanTick        = 0;

static ControlMode   s_fmTrackedMode = MODE_VANILLA;

// CombatClass state tracking
static swordStateEnum s_lastCombatState  = COMBAT_FINISHED;
static bool           s_wasPrevInCombat  = false;
static ULONGLONG      s_wasdReleasedTick = 0;

// Combat engagement tracking
static Character*     s_prevAttackTarget  = nullptr;
static bool           s_prevTargetInRange = false;

// Protected animation state tracking (knockdown / get-up / stagger)
static bool           s_wasProtectedState = false;

// Instant-stop: set when WASD movement is applied, cleared on release.
static bool           s_wasdMovementApplied = false;

// Attack commitment — protects CHOP_WEAPON from early interruption
static bool           s_attackCommitmentActive = false;
static ULONGLONG      s_attackCommitmentStart  = 0;

// WASD retreat state — tracks active retreat for suppression diagnostics
static bool          s_wasdRetreatActive      = false;
static bool          s_retreatCleanLogged     = false;
static ULONGLONG     s_retreatActiveStartTick  = 0;
static ULONGLONG     s_lastCombatEnterExitTick = 0;
static bool          s_combatFlickerLogged    = false;

// Post-WASD grace period — suppress combat re-entry after WASD release
static const ULONGLONG POST_WASD_GRACE_MS          = 2000;
static const float     POST_WASD_REENGAGEMENT_RANGE = 200.0f;
static bool            s_postWasdGraceActive        = false;
static ULONGLONG       s_postWasdGraceStart          = 0;
static bool            s_combatReentryAllowed        = false;

// CombatClass::_NV_go suppression — set when go() was skipped this frame
static bool            s_retreatLockGoSuppressed     = false;
// Sticky: once go() is suppressed during a WASD hold, stays true until release
static bool            s_retreatLockEverActive       = false;

// Downed/crippled movement tracking — set each frame applyDownedMovement fires
static bool            s_wasdDownedMovementActive    = false;

// Medical job suppression — set once when any medical job is blocked during a WASD hold,
// cleared on WASD release.  Prevents repeated per-frame log spam.
static bool            s_medicalJobSuppressedThisHold = false;

// Multi-enemy tracking
static int             s_retreatBlockedAttackerCount  = 0;
static int             s_retreatTargetsProcessed      = 0;
static int             s_retreatTargetsCachedSkipped  = 0;
static int             s_lastKnownEnemyCount          = 0;

// Performance: throttle step-7 job removal to once per 250 ms.
static const ULONGLONG JOB_REMOVAL_INTERVAL_MS = 250;
static ULONGLONG       s_jobRemovalLastTick     = 0;

// Performance: session cache — each attacker blocked exactly once per WASD hold.
// No TTL: valid for the entire retreat lock; cleared on WASD release.
// 256 entries covers large guard squads without repeated miss-scans.
static const int  RETREAT_CACHE_SIZE       = 256;
static Character* s_retreatSessionCache[RETREAT_CACHE_SIZE];
static int        s_retreatSessionCacheCount = 0;

// -----------------------------------------------------------------------
// clearAllState
// -----------------------------------------------------------------------
static void clearAllState()
{
    s_mode              = MODE_VANILLA;
    s_wHeld             = false;
    s_aHeld             = false;
    s_sHeld             = false;
    s_dHeld             = false;
    s_selectedCharacter = nullptr;
    s_selectedMovement  = nullptr;
    s_freeMoveAnchor    = nullptr;
    s_anchorMovement    = nullptr;
    s_wasdWasActive     = false;
    s_combatWASDLogged  = false;
    s_retreatLogged     = false;
    s_squadThreat       = false;
    s_consciousAllyThreat = false;
    s_enemyTargetingLogged = false;
    s_lastScanTick      = 0;
    s_fmTrackedMode     = MODE_VANILLA;
    s_xPressed          = false;
    s_stabilizationCountdown = 0;
    s_lastCombatState   = COMBAT_FINISHED;
    s_wasPrevInCombat   = false;
    s_wasdReleasedTick  = 0;
    s_prevAttackTarget  = nullptr;
    s_prevTargetInRange = false;
    s_wasProtectedState = false;
    s_wasdMovementApplied    = false;
    s_attackCommitmentActive = false;
    s_attackCommitmentStart  = 0;
    s_wasdRetreatActive      = false;
    s_retreatCleanLogged     = false;
    s_retreatActiveStartTick  = 0;
    s_lastCombatEnterExitTick = 0;
    s_combatFlickerLogged    = false;
    s_postWasdGraceActive      = false;
    s_postWasdGraceStart       = 0;
    s_combatReentryAllowed     = false;
    s_retreatLockGoSuppressed     = false;
    s_retreatLockEverActive       = false;
    s_wasdDownedMovementActive    = false;
    s_medicalJobSuppressedThisHold = false;
    s_retreatBlockedAttackerCount  = 0;
    s_retreatTargetsProcessed      = 0;
    s_retreatTargetsCachedSkipped  = 0;
    s_lastKnownEnemyCount          = 0;
    s_jobRemovalLastTick           = 0;
    s_retreatSessionCacheCount     = 0;
    s_lootUiSuspendActive          = false;
    s_lootUiWasPrevOpen            = false;
    s_lootSuspendStartTick         = 0;
}

// -----------------------------------------------------------------------
// computeWASDDirection — camera-relative direction helper.
// -----------------------------------------------------------------------
static bool computeWASDDirection(bool bW, bool bA, bool bS, bool bD, Ogre::Vector3& outDir)
{
    if (!ou || !ou->player || !ou->player->camera) return false;
    Ogre::Vector3 camFwd = ou->player->camera->getFacingDirection();
    camFwd.y = 0.0f;
    float cflen = camFwd.length();
    if (cflen < 0.001f) return false;
    camFwd /= cflen;
    Ogre::Vector3 camRight(-camFwd.z, 0.0f, camFwd.x);
    Ogre::Vector3 move = Ogre::Vector3::ZERO;
    if (bW) move += camFwd;
    if (bS) move -= camFwd;
    if (bD) move += camRight;
    if (bA) move -= camRight;
    float mlen = move.length();
    if (mlen < 0.001f) return false;
    outDir = move / mlen;
    return true;
}

// -----------------------------------------------------------------------
// applyPlayerMovement — halt() + setDirectMovement in camera-relative WASD.
// -----------------------------------------------------------------------
static bool applyPlayerMovement(bool bW, bool bA, bool bS, bool bD)
{
    CharMovement* mv = s_freeMoveAnchor ? s_freeMoveAnchor->movement : nullptr;
    if (!s_freeMoveAnchor || !mv) return false;
    if (!ou || !ou->player || !ou->player->camera) return false;

    Ogre::Vector3 move;
    if (!computeWASDDirection(bW, bA, bS, bD, move)) return false;

    mv->halt();
    mv->setDesiredSpeed(mv->speedOrders);
    mv->setDirectMovement(move, 99.0f);
    return true;
}

// -----------------------------------------------------------------------
// isProtectedAnimationState — returns true when V-Mode must not interfere.
// -----------------------------------------------------------------------
static bool isProtectedAnimationState(Character* ch)
{
    if (!ch) return false;
    ProneState prone = ch->getProneState();
    if (prone == PS_KO || prone == PS_PLAYING_DEAD) return true;
    if (ch->isDown())              return true;
    if (ch->isCurrentlyGettingUp) return true;
    CombatClass* cc = ch->getCombatClass();
    if (cc && cc->getCombatState() == STUMBLE) return true;
    return false;
}

// -----------------------------------------------------------------------
// isUsingStationaryTurret — true when character is manning a turret/crossbow.
// When WASD is not held, V-Mode must not suppress aiming input.
// When WASD is held, turret use is cancelled (player takes movement authority).
// -----------------------------------------------------------------------
static bool isUsingStationaryTurret(Character* ch)
{
    if (!ch) return false;
    // isUsingTurret is a hand (reference to the turret building); truthy when valid.
    return (bool)(ch->isUsingTurret);
}

// -----------------------------------------------------------------------
// Retreat session cache — each enemy processed once per WASD hold, then
// immediately skipped on every subsequent call with zero overhead.
// Cleared on WASD release via s_retreatSessionCacheCount = 0.
// -----------------------------------------------------------------------
static bool retreatSessionCacheContains(Character* ch)
{
    for (int i = 0; i < s_retreatSessionCacheCount; ++i)
        if (s_retreatSessionCache[i] == ch) return true;
    return false;
}

static void retreatSessionCacheAdd(Character* ch)
{
    if (!ch) return;
    for (int i = 0; i < s_retreatSessionCacheCount; ++i)
        if (s_retreatSessionCache[i] == ch) return;
    if (s_retreatSessionCacheCount < RETREAT_CACHE_SIZE)
        s_retreatSessionCache[s_retreatSessionCacheCount++] = ch;
    // If full: silently drop — best-effort optimization
}

// -----------------------------------------------------------------------
// isDownedButMovable — true when character is downed/crippled/playing-dead but
// vanilla point-click movement still works (crawl/limp).  Hard blocks (truly
// unconscious, getting-up animation, stumble) return false.
// -----------------------------------------------------------------------
static bool isDownedButMovable(Character* ch)
{
    if (!ch) return false;
    ProneState prone = ch->getProneState();
    // PS_KO is the authoritative hard block — truly knocked out, cannot crawl.
    // Do NOT use isUnconcious() here: it returns true for PS_PLAYING_DEAD and
    // crippled characters in Kenshi even though point-click crawl still works.
    if (prone == PS_KO) return false;
    if (ch->isCurrentlyGettingUp) return false;
    // Playing-dead and crippled can crawl/limp via the point-click path.
    if (prone == PS_PLAYING_DEAD || prone == PS_CRIPPLED) return true;
    // Down but not KO and not getting up — conscious downed state.
    if (ch->isDown() && !ch->isUnconcious()) return true;
    return false;
}

// applyDownedMovement — issue point-click-equivalent order for downed/crippled
// characters.  Uses playerMoveOrderDefault (pathfind/crawl path) rather than
// setDirectMovement, which is only valid for standing locomotion.
static void applyDownedMovement(bool bW, bool bA, bool bS, bool bD)
{
    if (!s_freeMoveAnchor || !s_freeMoveAnchor->movement) return;
    Ogre::Vector3 dir;
    if (!computeWASDDirection(bW, bA, bS, bD, dir)) return;
    Ogre::Vector3 dest = s_freeMoveAnchor->movement->pos + dir * 500.0f;
    s_freeMoveAnchor->playerMoveOrderDefault(nullptr, nullptr, dest);
}

// -----------------------------------------------------------------------
// CharMovement::_NV_update hook — WASD priority with animation protection
//
// WASD held:   apply halt+MOVE_DIRECTION before original; instant-stop on release.
// WASD not held: original runs freely; protected animations are untouched.
// -----------------------------------------------------------------------
static void (*s_charMovUpdateOrig)(CharMovement* thisptr, float time);

static void charMovUpdate_hook(CharMovement* thisptr, float time)
{
    // Fast path: non-anchor characters exit immediately with no further work.
    // s_anchorMovement is non-volatile; this single pointer comparison is the
    // only cost for every NPC/guard CharMovement::update call.
    if (thisptr != s_anchorMovement || s_loadGuardActive)
    {
        s_charMovUpdateOrig(thisptr, time);
        return;
    }

    // Anchor character only from this point.  Use frame-cached values so no
    // volatile reads are needed inside the per-frame anchor logic.
    bool wasdHeld    = s_frameWasdHeld;
    bool inVMode     = (s_frameMode == MODE_FREE_MOVE);
    bool lootSuspend = s_frameLootSuspend;

    if (!inVMode || !wasdHeld || lootSuspend)
    {
        // Not in WASD-drive mode for the anchor.
        if (inVMode && !wasdHeld && !lootSuspend)
        {
            Character*   chR = thisptr->getCharacter();
            CombatClass* ccR = chR ? chR->getCombatClass() : nullptr;

            // Instant stop: clear residual WASD motion before original runs.
            if (s_wasdMovementApplied)
            {
                bool inProtected = chR && isProtectedAnimationState(chR);
                swordStateEnum stStop = ccR ? ccR->getCombatState() : COMBAT_FINISHED;
                bool inCombatAct = (stStop == CHOP_WEAPON || stStop == STARTUP_STATE);

                if (!inProtected && !inCombatAct)
                {
                    Ogre::Vector3 velPre = thisptr->currentMotion;
                    thisptr->halt();
                    thisptr->desiredMotion = Ogre::Vector3::ZERO;
                    thisptr->moveLimit     = 0.0f;
                    s_wasdMovementApplied  = false;
#if DIAG_VERBOSE
                    char buf[256];
                    sprintf_s(buf, sizeof(buf),
                        "[WASDCombat] instant_stop vel_pre=(%.3f,%.3f,%.3f)",
                        velPre.x, velPre.y, velPre.z);
                    DebugLog(buf);
#else
                    (void)velPre;
#endif
                }
            }
        }
        s_charMovUpdateOrig(thisptr, time);
        return;
    }

    // WASD held — check protected states first (knockdown/get-up/stagger).
    {
        Character* chP = thisptr->getCharacter();
        if (isProtectedAnimationState(chP))
        {
            s_charMovUpdateOrig(thisptr, time);
            return;
        }
    }

    // WASD held, no protected state — apply movement override.
    swordStateEnum capturedCombatState = COMBAT_FINISHED;
    {
        Character*   ch = thisptr->getCharacter();
        CombatClass* cc = ch ? ch->getCombatClass() : nullptr;
        if (cc) capturedCombatState = cc->getCombatState();
    }

    Ogre::Vector3 wasdDir;
    bool dirOk = computeWASDDirection(s_wHeld, s_aHeld, s_sHeld, s_dHeld, wasdDir);

    if (dirOk)
    {
        s_wasdMovementApplied      = true;
        thisptr->halt();
        thisptr->animationOverride = false;
        thisptr->movementMode      = MOVE_DIRECTION;
        thisptr->setDesiredSpeed(thisptr->speedOrders);
        thisptr->setDirectMovement(wasdDir, 99.0f);

        s_charMovUpdateOrig(thisptr, time);

#if DIAG_VERBOSE
        bool animReenabled = thisptr->animationOverride;
        bool modeChanged   = (thisptr->movementMode != MOVE_DIRECTION);
        if (animReenabled || modeChanged)
            DebugLog("[WASDCombat] combat_locomotion_attempt_detected");
#endif

        // Post-original suppression: undo combat-driven animation/locomotion overrides during WASD retreat.
        // The original CharMovement::update may re-enable animationOverride and change movementMode
        // when the combat AI has pushed BLOCK, STARTUP_STATE, CIRCLE_MENACINGLY, TARGET_PATHFINDING etc.
        // We re-assert MOVE_DIRECTION after the original so those states cannot cause visual twitching.
        // CHOP_WEAPON is intentionally excluded — attack commitment completes normally.
        {
            Character*   chPost = thisptr->getCharacter();
            CombatClass* ccPost = chPost ? chPost->getCombatClass() : nullptr;
            if (ccPost)
            {
                swordStateEnum stPost = ccPost->getCombatState();
                bool shouldSuppress =
                    stPost == CHOP_WEAPON                || stPost == BLOCK                  ||
                    stPost == CIRCLE_MENACINGLY          || stPost == WAIT_MENACINGLY        ||
                    stPost == HESITATE                   || stPost == DECISION               ||
                    stPost == TARGET_PATHFINDING         || stPost == TARGET_PATHFINDING_STARTUP ||
                    stPost == STARTUP_STATE;

                if (shouldSuppress)
                {
                    thisptr->animationOverride = false;
                    thisptr->movementMode      = MOVE_DIRECTION;
                    thisptr->setDirectMovement(wasdDir, 99.0f);
                    if (ccPost->combatModeActive)
                        ccPost->combatModeActive = false;
                }
            }
        }
    }
    else
    {
        s_charMovUpdateOrig(thisptr, time);
    }
}

// -----------------------------------------------------------------------
// CombatClass::_NV_initCombatMode hook — block combat entry at the source.
//
// go() clears combatState each frame, but initCombatMode is called from enemy
// AI targeting code — a separate callsite that runs after go() and re-enters
// DECISION.  Blocking initCombatMode prevents the COMBAT_FINISHED->DECISION
// flicker from ever being generated, not just suppressed after the fact.
// -----------------------------------------------------------------------
static bool (*s_initCombatModeOrig)(CombatClass* thisptr, const hand& subject,
                                    int end, bool focusedTarget);

static bool initCombatMode_hook(CombatClass* thisptr, const hand& subject,
                                int end, bool focusedTarget)
{
    if (thisptr->me == s_freeMoveAnchor && !s_loadGuardActive &&
        s_frameMode == MODE_FREE_MOVE && s_frameWasdHeld)
    {
        Character* atk = subject.getCharacter();

            // Session cache fast-path: if this attacker was already blocked during
            // this WASD hold, return false immediately with no further work.
            if (atk && retreatSessionCacheContains(atk))
            {
                s_retreatTargetsCachedSkipped++;
#if RETREAT_VERBOSE_DIAG
                static ULONGLONG s_cacheHitTick = 0;
                ULONGLONG tc = GetTickCount64();
                if (tc - s_cacheHitTick >= 2000) { s_cacheHitTick = tc;
                    DebugLog("[WASDCombat] retreat_suppression_skipped_cached_attacker");
                    DebugLog("[WASDCombat] retreat_attacker_cache_used"); }
#endif
                return false;
            }
            retreatSessionCacheAdd(atk);
            s_retreatTargetsProcessed++;
            s_retreatBlockedAttackerCount++;

#if RETREAT_VERBOSE_DIAG
            {
            static ULONGLONG s_initBlockTick    = 0;
            static int       s_initBlockedInWin = 0;
            ULONGLONG t = GetTickCount64();
            s_initBlockedInWin++;
            if (t - s_initBlockTick >= 2000) { s_initBlockTick = t;
                DebugLog("[WASDCombat] combat_enter_request_blocked_by_retreat_lock");
                DebugLog("[WASDCombat] combat_reacquire_request_blocked_by_retreat_lock");
                DebugLog("[WASDCombat] combat_state_generation_blocked");
                DebugLog("[WASDCombat] combat_state_machine_bypassed_during_retreat");
                if (s_initBlockedInWin > 1)
                {
                    char buf[128];
                    sprintf_s(buf, sizeof(buf),
                        "[WASDCombat] multi_enemy_targeting_detected count=%d", s_initBlockedInWin);
                    DebugLog(buf);
                    DebugLog("[WASDCombat] multi_enemy_targeting_ignored_by_retreat_lock");
                }
                s_initBlockedInWin = 0; }
            }
#endif
        return false;
    }
    return s_initCombatModeOrig(thisptr, subject, end, focusedTarget);
}

// -----------------------------------------------------------------------
// CombatClass::youDoKnowImAttackingYouRight hook — block per-enemy attack
// notification during retreat lock to suppress multi-attacker locomotion pulses.
// -----------------------------------------------------------------------
static void (*s_youKnowImAttackingOrig)(CombatClass* thisptr, const hand& h);

static void youKnowImAttacking_hook(CombatClass* thisptr, const hand& h)
{
    if (thisptr->me == s_freeMoveAnchor && !s_loadGuardActive &&
        s_frameMode == MODE_FREE_MOVE && s_frameWasdHeld)
    {
        Character* atk = h.getCharacter();
        if (atk && retreatSessionCacheContains(atk))
        {
            s_retreatTargetsCachedSkipped++;
            return;
        }
        retreatSessionCacheAdd(atk);
        s_retreatTargetsProcessed++;
        s_retreatBlockedAttackerCount++;
#if RETREAT_VERBOSE_DIAG
        static ULONGLONG s_notifyBlockTick = 0;
        ULONGLONG t = GetTickCount64();
        if (t - s_notifyBlockTick >= 2000) { s_notifyBlockTick = t;
            DebugLog("[WASDCombat] all_reacquire_requests_blocked_by_retreat_lock"); }
#endif
        return;
    }
    s_youKnowImAttackingOrig(thisptr, h);
}

// -----------------------------------------------------------------------
// CombatClass::_NV_go hook — suppress all combat AI for anchor while WASD held.
//
// CombatClass::go() is the per-frame combat state machine.  Even with attack
// jobs removed it runs independently and drives CIRCLE_MENACINGLY /
// STARTUP_STATE / TARGET_PATHFINDING every frame, causing the visual stutter.
// Skipping it entirely — and resetting combatState to COMBAT_FINISHED — is
// the equivalent of what point-click movement does internally.
// -----------------------------------------------------------------------
static void (*s_combatClassGoOrig)(CombatClass* thisptr, float frameTime);

static void combatClassGo_hook(CombatClass* thisptr, float frameTime)
{
    // Fast path: all non-anchor CombatClass::go() calls exit here.
    // Avoids volatile reads of s_mode/s_loadGuardActive for every NPC per frame.
    if (thisptr->me != s_freeMoveAnchor || s_loadGuardActive)
    {
        s_combatClassGoOrig(thisptr, frameTime);
        return;
    }
    if (s_frameMode == MODE_FREE_MOVE)
    {
        bool wasdHeld = s_frameWasdHeld;
        if (wasdHeld)
        {
            thisptr->combatModeActive  = false;
            thisptr->combatState       = COMBAT_FINISHED;
            s_retreatLockGoSuppressed  = true;
            s_retreatLockEverActive    = true;
#if RETREAT_VERBOSE_DIAG
            {
            swordStateEnum prevState = thisptr->combatState; // read before overwrite above
            static ULONGLONG s_lockLogTick = 0;
            ULONGLONG t = GetTickCount64();
            if (t - s_lockLogTick >= 2000) { s_lockLogTick = t;
                DebugLog("[WASDCombat] wasd_manual_retreat_lock_active");
                if      (prevState == TARGET_PATHFINDING || prevState == TARGET_PATHFINDING_STARTUP)
                    DebugLog("[WASDCombat] target_pathfinding_blocked_by_retreat_lock");
                else if (prevState == CIRCLE_MENACINGLY  || prevState == WAIT_MENACINGLY)
                    DebugLog("[WASDCombat] circle_state_blocked_by_retreat_lock");
                else if (prevState == STARTUP_STATE)
                {
                    DebugLog("[WASDCombat] startup_state_blocked_by_retreat_lock");
                    DebugLog("[WASDCombat] combat_startup_request_blocked_by_retreat_lock");
                }
                else if (prevState != COMBAT_FINISHED)
                    DebugLog("[WASDCombat] combat_locomotion_state_blocked_by_retreat_lock"); }
            }
#endif
            return;
        }
    }
    s_combatClassGoOrig(thisptr, frameTime);
}

// -----------------------------------------------------------------------
// Main-thread hook — GameWorld::mainLoop_GPUSensitiveStuff
//
// Execution order:
//   1.  Safety gate (load-guard)
//   2.  Selection tracking
//   3.  V-Mode transition
//   4.  HUD + X speed key
//   5.  Pre-AI WASD
//   6.  s_mainLoopOrig (AI + CharMovement::update + CombatClass::go)
//   7.  Post-AI combat job suppression
//   8.  Periodic squad-threat scan
//   9.  Post-AI WASD re-application + instant stop
// -----------------------------------------------------------------------
static void (*s_mainLoopOrig)(GameWorld* thisptr, float time);

static void mainLoop_hook(GameWorld* thisptr, float time)
{
    // 1. Safety gate.
    {
        bool isLoading = (!ou || !ou->player || ou->isLoadingFromASaveGame());

        if (isLoading)
        {
            if (!s_loadGuardActive)
            {
                s_loadGuardActive = true;
                clearAllState();
                s_vHud.label = nullptr;
                s_vHud.shown = false;
                s_hudReady   = false;
                DebugLog("[WASDCombat] load_guard_enabled");
            }
            hudUpdate();
            s_mainLoopOrig(thisptr, time);
            return;
        }

        if (s_loadGuardActive)
        {
            if (s_stabilizationCountdown == 0)
            {
                s_stabilizationCountdown = 60;
                DebugLog("[WASDCombat] reload_stabilization_started");
            }

            s_stabilizationCountdown--;

            if (s_stabilizationCountdown > 0)
            {
                hudUpdate();
                s_mainLoopOrig(thisptr, time);
                return;
            }

            s_loadGuardActive        = false;
            s_postLoadReacquire      = true;
            s_stabilizationCountdown = 0;
            DebugLog("[WASDCombat] reload_complete_reacquire_started");
        }
    }

    // Loot UI suspension — detect any open inventory window.
    // s_mode is untouched; all V-Mode processing suspends while any inventory is open.
    // Diagnostic logs identify which specific inventory type was detected.
    {
        bool anyInvOpen      = gui && gui->isAnyInventoryWindowOpen();
        int  numInvOpen      = gui ? gui->getNumOpenInventoryWindows() : 0;
        bool npcFieldOpen    = gui && gui->inventoryWindowNPC.getCharacter()       != nullptr;
        bool charFieldOpen   = gui && gui->inventoryWindowCharacter.getCharacter() != nullptr;
        bool traderFieldOpen = gui && gui->inventoryWindowTrader.getCharacter()    != nullptr;
        bool tradeAOpen      = gui && gui->tradeA.getCharacter()                   != nullptr;
        bool tradeBOpen      = gui && gui->tradeB.getCharacter()                   != nullptr;

#if LOOT_DIAG
        // Periodic diagnostics while in V-Mode and any inventory is open.
        if (anyInvOpen && s_mode == MODE_FREE_MOVE)
        {
            static ULONGLONG s_invDiagTick = 0;
            ULONGLONG t = GetTickCount64();
            if (t - s_invDiagTick >= 1000) { s_invDiagTick = t;
                DebugLog("[WASDCombat] any_inventory_ui_detected");
                if (charFieldOpen)
                    DebugLog("[WASDCombat] player_inventory_ui_detected");
                if (npcFieldOpen)
                    DebugLog("[WASDCombat] npc_inventory_ui_detected");
                if (tradeAOpen || tradeBOpen)
                    DebugLog("[WASDCombat] unconscious_body_inventory_ui_detected");
                if (!charFieldOpen && !npcFieldOpen && !traderFieldOpen && !tradeAOpen && !tradeBOpen)
                    DebugLog("[WASDCombat] loot_ui_detection_failed");

                bool modal = MyGUI::InputManager::getInstance().isModalAny();
                if (modal) DebugLog("[WASDCombat] current_ui_modal_state");

                char wbuf[256];
                sprintf_s(wbuf, sizeof(wbuf),
                    "[WASDCombat] current_ui_window_name open=%d npc=%d char=%d trader=%d tradeA=%d tradeB=%d modal=%d",
                    numInvOpen, (int)npcFieldOpen, (int)charFieldOpen, (int)traderFieldOpen,
                    (int)tradeAOpen, (int)tradeBOpen, (int)modal);
                DebugLog(wbuf);

                MyGUI::Widget* mfocus = MyGUI::InputManager::getInstance().getMouseFocusWidget();
                if (mfocus)
                {
                    char abuf[256];
                    sprintf_s(abuf, sizeof(abuf),
                        "[WASDCombat] current_ui_active_widget_name name=%s",
                        mfocus->getName().c_str());
                    DebugLog(abuf);

                    MyGUI::Widget* root = mfocus;
                    while (root->getParent() != nullptr) root = root->getParent();
                    char rbuf[256];
                    sprintf_s(rbuf, sizeof(rbuf),
                        "[WASDCombat] current_ui_root_name name=%s",
                        root->getName().c_str());
                    DebugLog(rbuf);
                }
            }
        }
#endif

        // Suspension trigger: any open inventory window.
        // showTradeWindow_hook may have already set s_lootUiSuspendActive before
        // the window was visible; this block confirms open/close state and manages
        // s_lootUiWasPrevOpen for edge detection.
        if (anyInvOpen && !s_lootUiWasPrevOpen)
        {
            // Window is now confirmed open.  Hook may have already set suspension;
            // if not (non-trade path such as showInventoryNPC), set it now.
            if (!s_lootUiSuspendActive)
            {
                s_lootUiSuspendActive  = true;
                s_lootSuspendStartTick = GetTickCount64();
            }
            s_lootUiWasPrevOpen = true;
            DebugLog("[WASDCombat] loot_ui_open_suspend_vmode");
        }
        else if (!anyInvOpen && s_lootUiWasPrevOpen)
        {
            // Window closed — enforce debounce before releasing suspension.
            ULONGLONG elapsed = GetTickCount64() - s_lootSuspendStartTick;
            if (elapsed >= LOOT_SUSPEND_DEBOUNCE_MS)
            {
                s_lootUiSuspendActive = false;
                s_lootUiWasPrevOpen   = false;
                DebugLog("[WASDCombat] loot_ui_closed_restore_vmode");
            }
            else
            {
#if LOOT_DIAG
                static ULONGLONG s_debBlockTick = 0;
                ULONGLONG t = GetTickCount64();
                if (t - s_debBlockTick >= 100) { s_debBlockTick = t;
                    DebugLog("[WASDCombat] duplicate_initial_loot_open_blocked"); }
#endif
            }
        }
        else if (s_lootUiSuspendActive && !s_lootUiWasPrevOpen && s_lootSuspendStartTick > 0)
        {
            // Hook fired but window never appeared (cancelled interaction).
            // Release after 1 s to avoid a stuck suspension.
            ULONGLONG elapsed = GetTickCount64() - s_lootSuspendStartTick;
            if (elapsed >= 1000)
            {
                s_lootUiSuspendActive  = false;
                s_lootSuspendStartTick = 0;
            }
        }
    }

    // Frame snapshot — read all volatile input state once before any per-character
    // hooks run inside s_mainLoopOrig.  Hooks use s_frame* instead of re-reading
    // volatiles, eliminating memory fence overhead for 100+ hook calls per frame.
    s_frameMode        = s_mode;
    s_frameWasdHeld    = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
    s_frameLootSuspend = s_lootUiSuspendActive;

    // 2. Selection tracking.
    {
        Character*    ch = ou->player->selectedCharacter.getCharacter();
        CharMovement* mv = ch ? ch->movement : nullptr;
        if (ch != s_selectedCharacter || mv != s_selectedMovement)
        {
            s_selectedCharacter = ch;
            s_selectedMovement  = mv;
        }

        if (s_postLoadReacquire && ch)
        {
            s_postLoadReacquire = false;
            DebugLog("[WASDCombat] reload_reacquire_complete");
        }
    }

    // 3. V-Mode transition.
    {
        ControlMode curMode = s_mode;
        bool curInVM  = (curMode         == MODE_FREE_MOVE);
        bool prevInVM = (s_fmTrackedMode == MODE_FREE_MOVE);

        if (curInVM && !prevInVM && !s_lootUiSuspendActive)
        {
            s_freeMoveAnchor      = s_selectedCharacter;
            s_anchorMovement      = s_freeMoveAnchor ? s_freeMoveAnchor->movement : nullptr;
            s_wasdWasActive       = false;
            s_combatWASDLogged    = false;
            s_retreatLogged       = false;
            s_squadThreat         = false;
            s_consciousAllyThreat = false;
            s_enemyTargetingLogged = false;
            s_lastScanTick        = 0;

            if (s_freeMoveAnchor)
                ou->player->startTrackCharacter(s_freeMoveAnchor);
            ou->showPlayerAMessage("Direct Control Enabled", false);
        }
        else if (!curInVM && prevInVM && !s_lootUiSuspendActive)
        {
            ou->player->stopTrackCharacter();
            s_freeMoveAnchor      = nullptr;
            s_anchorMovement      = nullptr;
            s_wasdWasActive       = false;
            s_combatWASDLogged    = false;
            s_retreatLogged       = false;
            s_squadThreat         = false;
            s_consciousAllyThreat = false;
            s_enemyTargetingLogged = false;
            s_lastScanTick        = 0;
            ou->showPlayerAMessage("Direct Control Disabled", false);
        }
        else if (curInVM && s_freeMoveAnchor && !s_lootUiSuspendActive)
        {
            Character* sel = s_selectedCharacter;
            if (sel && sel != s_freeMoveAnchor && sel->isPlayerCharacter())
            {
                s_freeMoveAnchor      = sel;
                s_anchorMovement      = sel->movement;
                s_combatWASDLogged    = false;
                s_retreatLogged       = false;
                s_squadThreat         = false;
                s_consciousAllyThreat = false;
                s_enemyTargetingLogged = false;
                s_lastScanTick        = 0;
                ou->player->startTrackCharacter(s_freeMoveAnchor);
            }
        }
        s_fmTrackedMode = curMode;
    }

    // 4. HUD + X speed key.
    hudUpdate();

    if (s_xPressed && !s_lootUiSuspendActive)
    {
        s_xPressed = false;
        if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor && s_freeMoveAnchor->movement)
        {
            OrdersPanel* op = (gui && gui->mainbar) ? gui->mainbar->ordersDataPanel : nullptr;
            if (op)
            {
                op->speedNext(nullptr);
                MoveSpeed ns = MoveSpeed(int((unsigned char)op->speedImageNamesIdx));
                if (ns < GROUPED)
                {
                    s_freeMoveAnchor->movement->setDesiredSpeedOrders(ns);
                    s_freeMoveAnchor->movement->setDesiredSpeed(ns);
                }
                DebugLog(ns == WALK ? "[WASDCombat] speed_walk"
                       : ns == JOG  ? "[WASDCombat] speed_jog"
                                    : "[WASDCombat] speed_run");
            }
        }
    }

    // 5. Pre-AI WASD application.
    if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor && s_freeMoveAnchor->movement && !s_lootUiSuspendActive)
    {
        bool bW = s_wHeld, bA = s_aHeld, bS = s_sHeld, bD = s_dHeld;
        if (bW || bA || bS || bD)
        {
            if (!isProtectedAnimationState(s_freeMoveAnchor))
                applyPlayerMovement(bW, bA, bS, bD);
            else if (isDownedButMovable(s_freeMoveAnchor))
            {
                applyDownedMovement(bW, bA, bS, bD);
                s_wasdDownedMovementActive = true;
                static ULONGLONG s_downMoveTick = 0;
                ULONGLONG t = GetTickCount64();
                if (t - s_downMoveTick >= 2000) { s_downMoveTick = t;
                    ProneState prone = s_freeMoveAnchor->getProneState();
                    if (prone == PS_PLAYING_DEAD)   DebugLog("[WASDCombat] playing_dead_state_detected");
                    else if (prone == PS_CRIPPLED)  DebugLog("[WASDCombat] crippled_state_detected");
                    else                            DebugLog("[WASDCombat] downed_state_detected");
                    DebugLog("[WASDCombat] wasd_downed_movement_attempt");
                    DebugLog("[WASDCombat] pointclick_movement_allowed_while_downed");
                    DebugLog("[WASDCombat] wasd_downed_movement_uses_pointclick_path");
                    DebugLog("[WASDCombat] wasd_downed_destination_created");
                    DebugLog("[WASDCombat] wasd_downed_destination_source_wasd");
                    if (s_freeMoveAnchor->isCrippled())
                    {
                        DebugLog("[WASDCombat] wasd_crippled_movement_allowed");
                        DebugLog("[WASDCombat] wasd_crippled_movement_success");
                    } }
            }
            else if (s_freeMoveAnchor->isUnconcious())
            {
                static ULONGLONG s_koTick = 0;
                ULONGLONG t = GetTickCount64();
                if (t - s_koTick >= 2000) { s_koTick = t;
                    DebugLog("[WASDCombat] wasd_true_unconscious_movement_blocked"); }
            }
        }
    }

    // 6. Run original game loop — AI + CharMovement::update + CombatClass::go run here.
    s_retreatLockGoSuppressed = false;
    s_mainLoopOrig(thisptr, time);

    // Post-loop load guard.
    if (!ou || !ou->player || ou->isLoadingFromASaveGame())
    {
        DebugLog("[WASDCombat] loadgame_signal_hard_shutdown");
        s_loadGuardActive = true;
        clearAllState();
        s_vHud.label = nullptr;
        s_vHud.shown = false;
        s_hudReady   = false;
        return;
    }

    // 7. Combat job suppression (post-AI).
    // WASD held: full point-click-equivalent disengage — remove all combat engagement jobs each frame.
    // WASD not held: squad-assist removal only, respecting attack commitment.
    if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor && !s_lootUiSuspendActive)
    {
        bool wasdNowHeld = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
        bool inProtected = isProtectedAnimationState(s_freeMoveAnchor);
        bool atTurret    = !wasdNowHeld && isUsingStationaryTurret(s_freeMoveAnchor);

        if (!inProtected && !atTurret)
        {
            if (wasdNowHeld)
            {
                // Throttled to JOB_REMOVAL_INTERVAL_MS — addJob_hook blocks re-addition
                // between windows, so every-frame removal is unnecessary.
                ULONGLONG nowJob = GetTickCount64();
                if (nowJob - s_jobRemovalLastTick >= JOB_REMOVAL_INTERVAL_MS)
                {
                    s_jobRemovalLastTick = nowJob;
                    s_freeMoveAnchor->removeJob(MELEE_ATTACK);
                    s_freeMoveAnchor->removeJob(FOCUSED_MELEE_ATTACK);
                    s_freeMoveAnchor->removeJob(CHOOSE_ENEMY_AND_ATTACK);
                    s_freeMoveAnchor->removeJob(ATTACK_CHARACTERS_ATTACKER);
                    s_freeMoveAnchor->removeJob(ATTACK_ENEMIES);
                    s_freeMoveAnchor->removeJob(PROTECT_ALLIES);
                    s_freeMoveAnchor->removeJob(CHOOSE_ATTACKER_OF_ALLY);
                    s_freeMoveAnchor->removeJob(ATTACK_ATTACKERS_OF);
                    s_freeMoveAnchor->removeJob(JOB_MEDIC);
                    s_freeMoveAnchor->removeJob(FIRST_AID_ORDER);
                    s_freeMoveAnchor->removeJob(FIRST_AID_ROBOT);
                    s_freeMoveAnchor->removeJob(JOB_REPAIR_ROBOT);
                    s_freeMoveAnchor->removeJob(SPLINT_ORDER);
                    s_freeMoveAnchor->removeJob(SPLINT_JOB);
                    s_freeMoveAnchor->removeJob(HEAL_MY_LEGS);
                }
                else
                {
#if RETREAT_VERBOSE_DIAG
                    static ULONGLONG s_scanThrottleTick = 0;
                    if (nowJob - s_scanThrottleTick >= 2000) { s_scanThrottleTick = nowJob;
                        DebugLog("[WASDCombat] retreat_scan_throttled"); }
#endif
                }
            }
            else if (!s_attackCommitmentActive)
            {
                s_freeMoveAnchor->removeJob(PROTECT_ALLIES);
                s_freeMoveAnchor->removeJob(CHOOSE_ATTACKER_OF_ALLY);
                s_freeMoveAnchor->removeJob(ATTACK_ATTACKERS_OF);
            }
        }
    }

    // 8. Periodic squad-threat scan.
    if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor)
    {
        ULONGLONG nowMs   = GetTickCount64();
        bool inCombat     = s_freeMoveAnchor->isInCombatMode(true, true);

        if (nowMs - s_lastScanTick >= SCAN_INTERVAL_MS)
        {
            s_lastScanTick = nowMs;

            bool foundEnemyTargetingAnchor     = false;
            bool foundEnemyTargetingSquad      = false;
            bool foundConsciousAllyUnderAttack = false;
            int  enemiesTargetingAnchor        = 0;

            auto& allChars = thisptr->getCharacterUpdateList();
            for (auto it = allChars.begin(); it != allChars.end(); ++it)
            {
                Character* c = *it;
                if (!c || c == s_freeMoveAnchor || !c->movement) continue;
                if (!c->isEnemy(s_freeMoveAnchor, true)) continue;

                Character* attacked = c->getAttackTarget().getCharacter();
                if (!attacked) continue;

                if (attacked == s_freeMoveAnchor)
                {
                    foundEnemyTargetingAnchor = true;
                    enemiesTargetingAnchor++;
                }
                else if (attacked->isPlayerCharacter())
                {
                    foundEnemyTargetingSquad = true;
                    if (!attacked->isUnconcious() && !attacked->isDead())
                        foundConsciousAllyUnderAttack = true;
                }
            }
            s_lastKnownEnemyCount = enemiesTargetingAnchor;

            {
                bool wasdNow = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
                if (foundEnemyTargetingAnchor && !s_enemyTargetingLogged)
                {
                    if (wasdNow && s_retreatLockGoSuppressed)
                    {
#if RETREAT_VERBOSE_DIAG
                        static ULONGLONG s_ignTick = 0;
                        ULONGLONG tign = GetTickCount64();
                        if (tign - s_ignTick >= 2000) { s_ignTick = tign;
                            DebugLog("[WASDCombat] enemy_targeting_ignored_by_retreat_lock"); }
#endif
                    }
                    else
                    {
                        DebugLog("[WASDCombat] enemy_targeting_player");
                        s_enemyTargetingLogged = true;
                    }
                }
                if (!inCombat) s_enemyTargetingLogged = false;

#if RETREAT_VERBOSE_DIAG
                // Verbose hostile count / blocked attacker summary.
                if (wasdNow && s_retreatLockGoSuppressed && enemiesTargetingAnchor > 0)
                {
                    static ULONGLONG s_hostileCountTick = 0;
                    ULONGLONG tenc = GetTickCount64();
                    if (tenc - s_hostileCountTick >= 2000) { s_hostileCountTick = tenc;
                        char hbuf[128];
                        sprintf_s(hbuf, sizeof(hbuf),
                            "[WASDCombat] hostile_count_during_retreat count=%d",
                            enemiesTargetingAnchor);
                        DebugLog(hbuf);
                        if (s_retreatBlockedAttackerCount > 0)
                        {
                            char abuf[128];
                            sprintf_s(abuf, sizeof(abuf),
                                "[WASDCombat] retreat_lock_blocked_attacker_count count=%d",
                                s_retreatBlockedAttackerCount);
                            DebugLog(abuf);
                            s_retreatBlockedAttackerCount = 0;
                        }
                    }
                }
#endif
            }

            s_squadThreat         = foundEnemyTargetingSquad;
            s_consciousAllyThreat = foundConsciousAllyUnderAttack;

            // Combat engagement tracking — target acquired/lost, range entry/exit.
            Character* curTgt = s_freeMoveAnchor->getAttackTarget().getCharacter();
            if (curTgt != s_prevAttackTarget)
            {
                if (curTgt && !s_prevAttackTarget)
                    DebugLog("[WASDCombat] combat_target_acquired");
                else if (!curTgt && s_prevAttackTarget)
                    DebugLog("[WASDCombat] combat_target_lost");
                s_prevAttackTarget = curTgt;
            }

            bool curInRange = false;
            if (curTgt && curTgt->movement)
            {
                Ogre::Vector3 toTgt = curTgt->movement->pos - s_freeMoveAnchor->movement->pos;
                toTgt.y = 0.0f;
                float tgtDist = toTgt.length();
                curInRange = (tgtDist <= ATTACK_RANGE);

                if (curInRange && !s_prevTargetInRange)
                {
                    char buf[128];
                    sprintf_s(buf, sizeof(buf),
                        "[WASDCombat] enemy_entered_attack_range dist=%.0f", tgtDist);
                    DebugLog(buf);
                }
                else if (!curInRange && s_prevTargetInRange)
                {
                    char buf[128];
                    sprintf_s(buf, sizeof(buf),
                        "[WASDCombat] enemy_left_attack_range dist=%.0f", tgtDist);
                    DebugLog(buf);
                }
            }
            s_prevTargetInRange = curInRange;
        }
    }

    // ----------------------------------------------------------------
    // 9. Post-AI WASD re-application + instant stop.
    // ----------------------------------------------------------------
    if (!(s_mode == MODE_FREE_MOVE && s_freeMoveAnchor && s_freeMoveAnchor->movement) || s_lootUiSuspendActive)
    {
        s_wasdWasActive    = false;
        s_combatWASDLogged = false;
        s_retreatLogged    = false;
        return;
    }

    bool bW = s_wHeld, bA = s_aHeld, bS = s_sHeld, bD = s_dHeld;
    bool wasdActive = bW || bA || bS || bD;
    bool inCombat   = s_freeMoveAnchor->isInCombatMode(true, true);

    // Combat mode transition — suppress log and detect flicker during WASD retreat.
    if (inCombat && !s_wasPrevInCombat)
    {
        if (!wasdActive)
            DebugLog("[WASDCombat] combat_entered");
#if RETREAT_VERBOSE_DIAG
        else
        {
            ULONGLONG t = GetTickCount64();
            if (s_lastCombatEnterExitTick > 0 && t - s_lastCombatEnterExitTick < 500)
            {
                if (!s_combatFlickerLogged) { s_combatFlickerLogged = true;
                    DebugLog("[WASDCombat] combat_state_flicker_detected"); }
            }
            s_lastCombatEnterExitTick = t;
            static ULONGLONG s_enterSuppTick = 0;
            if (t - s_enterSuppTick >= 2000) { s_enterSuppTick = t;
                DebugLog("[WASDCombat] combat_enter_exit_suppressed_during_wasd"); }
        }
#endif
    }
    else if (!inCombat && s_wasPrevInCombat)
    {
        if (!wasdActive)
            DebugLog("[WASDCombat] combat_exited");
#if RETREAT_VERBOSE_DIAG
        else
        {
            ULONGLONG t = GetTickCount64();
            if (s_lastCombatEnterExitTick > 0 && t - s_lastCombatEnterExitTick < 500)
            {
                if (!s_combatFlickerLogged) { s_combatFlickerLogged = true;
                    DebugLog("[WASDCombat] combat_state_flicker_detected"); }
            }
            s_lastCombatEnterExitTick = t;
        }
#endif
    }
    s_wasPrevInCombat = inCombat;

    if (wasdActive)
    {
        if (!s_wasdWasActive)
        {
            s_combatWASDLogged     = false;
            s_retreatLogged        = false;
            s_postWasdGraceActive  = false;
            s_combatReentryAllowed = false;

            if (isUsingStationaryTurret(s_freeMoveAnchor))
                DebugLog("[WASDCombat] stationary_crossbow_cancelled_by_wasd");

            // First WASD press: always send disengage order (matches point-click behavior).
            // Only protected animations prevent it — character physically cannot disengage.
            if (!isProtectedAnimationState(s_freeMoveAnchor) && s_freeMoveAnchor->movement)
            {
                Ogre::Vector3 cancelDir;
                if (computeWASDDirection(bW, bA, bS, bD, cancelDir))
                {
                    Ogre::Vector3 dest = s_freeMoveAnchor->movement->pos + cancelDir * 3.0f;
                    s_freeMoveAnchor->playerMoveOrderDefault(nullptr, nullptr, dest);
#if RETREAT_VERBOSE_DIAG
                    DebugLog("[WASDCombat] wasd_pointclick_disengage_path_used");
                    DebugLog("[WASDCombat] pointclick_cancel_function_called_by_wasd");
                    if (inCombat || s_retreatLockGoSuppressed)
                    {
                        DebugLog("[WASDCombat] wasd_attack_target_cleared");
                        DebugLog("[WASDCombat] wasd_combat_focus_cleared");
                        DebugLog("[WASDCombat] wasd_retreat_matches_pointclick_behavior");
                    }
#endif
                }
            }
        }

        if (!isProtectedAnimationState(s_freeMoveAnchor))
            applyPlayerMovement(bW, bA, bS, bD);
        // Note: downed/crippled movement is handled in step 5 (pre-AI) only —
        // playerMoveOrderDefault persists through the AI loop, no re-issue needed.

        // Retreat detection.
        if (inCombat && !s_retreatLogged && ou->player->camera)
        {
            Character* aiTarget = s_freeMoveAnchor->getAttackTarget().getCharacter();
            if (aiTarget && aiTarget->movement)
            {
                Ogre::Vector3 camFwd = ou->player->camera->getFacingDirection();
                camFwd.y = 0.0f;
                float cflen = camFwd.length();
                if (cflen > 0.001f)
                {
                    camFwd /= cflen;
                    Ogre::Vector3 camRight(-camFwd.z, 0.0f, camFwd.x);
                    Ogre::Vector3 mv = Ogre::Vector3::ZERO;
                    if (bW) mv += camFwd; if (bS) mv -= camFwd;
                    if (bD) mv += camRight; if (bA) mv -= camRight;
                    float mlen = mv.length();
                    if (mlen > 0.001f)
                    {
                        mv /= mlen;
                        Ogre::Vector3 toEnemy = aiTarget->movement->getPosition()
                                              - s_freeMoveAnchor->movement->getPosition();
                        toEnemy.y = 0.0f;
                        float elen = toEnemy.length();
                        if (elen > 0.001f && mv.dotProduct(toEnemy / elen) < -0.3f)
                            s_retreatLogged = true;
                    }
                }
            }
        }
    }
    else
    {
        if (s_wasdWasActive)
        {
            s_combatWASDLogged     = false;
            s_retreatLogged        = false;
            s_wasdReleasedTick     = GetTickCount64();
            s_postWasdGraceActive  = true;
            s_postWasdGraceStart   = GetTickCount64();
            s_combatReentryAllowed = false;

            // Downed/crippled instant stop.
            // Gate on s_wasdDownedMovementActive alone — NOT isDownedButMovable.
            // isDownedButMovable may flip false mid-release (e.g. isCurrentlyGettingUp
            // becomes true inside the AI loop), yet the WASD-issued destination is
            // still pending and must be cancelled.
            if (s_wasdDownedMovementActive)
            {
                CharMovement* mvDown = s_freeMoveAnchor ? s_freeMoveAnchor->movement : nullptr;
                if (mvDown)
                {
                    // playerMoveOrderDefault at current pos cancels the MOVE job entirely,
                    // not just the CharMovement destination field.
                    s_freeMoveAnchor->playerMoveOrderDefault(nullptr, nullptr, mvDown->pos);
                    mvDown->halt();
                }
                ProneState proneStop = s_freeMoveAnchor ? s_freeMoveAnchor->getProneState()
                                                        : PS_NORMAL;
                DebugLog("[WASDCombat] wasd_downed_key_released");
                DebugLog("[WASDCombat] wasd_downed_destination_cleared");
                DebugLog("[WASDCombat] wasd_downed_cached_direction_cleared");
                DebugLog("[WASDCombat] wasd_downed_movement_stopped");
                if (proneStop == PS_CRIPPLED ||
                    (s_freeMoveAnchor && s_freeMoveAnchor->isCrippled()))
                    DebugLog("[WASDCombat] wasd_crippled_instant_stop_applied");
                DebugLog("[WASDCombat] wasd_downed_pointclick_destination_not_persisted");
            }
            else if (s_freeMoveAnchor && isDownedButMovable(s_freeMoveAnchor))
            {
                // Destination was not WASD-created — likely a real player point-click.
                DebugLog("[WASDCombat] vanilla_pointclick_downed_destination_preserved");
            }
            s_wasdDownedMovementActive    = false;
            s_retreatLockEverActive       = false;
            s_retreatSessionCacheCount    = 0;  // clear session cache on WASD release
            s_retreatTargetsProcessed     = 0;
            s_retreatTargetsCachedSkipped = 0;
            s_retreatBlockedAttackerCount = 0;
            s_jobRemovalLastTick          = 0;  // next hold fires immediately

            if (s_medicalJobSuppressedThisHold)
            {
                DebugLog("[WASDCombat] medical_job_restored_after_wasd_release");
                s_medicalJobSuppressedThisHold = false;
            }

            // Standing instant stop after AI loop.
            CharMovement* mvStop = s_freeMoveAnchor->movement;
            if (mvStop && !isProtectedAnimationState(s_freeMoveAnchor) &&
                !isDownedButMovable(s_freeMoveAnchor))
            {
                Ogre::Vector3 velPre = mvStop->currentMotion;
                mvStop->halt();
                mvStop->desiredMotion = Ogre::Vector3::ZERO;
                mvStop->moveLimit     = 0.0f;
                s_wasdMovementApplied = false;

                char buf[192];
                sprintf_s(buf, sizeof(buf),
                    "[WASDCombat] wasd_released instant_stop vel_pre=(%.1f,%.1f,%.1f)",
                    velPre.x, velPre.y, velPre.z);
                DebugLog(buf);
            }
        }
    }

    s_wasdWasActive = wasdActive;

    // Post-WASD grace period: suppress combat re-entry unless enemy is close and actively targeting.
    if (!wasdActive)
    {
        if (s_postWasdGraceActive)
        {
            ULONGLONG elapsed = GetTickCount64() - s_postWasdGraceStart;
            if (elapsed >= POST_WASD_GRACE_MS)
            {
                s_postWasdGraceActive  = false;
                s_combatReentryAllowed = true;
                DebugLog("[WASDCombat] combat_state_restored_after_wasd_release");
            }
            else
            {
                // Allow re-engagement only if the old target is within close range and attacking us.
                bool enemyCloseAndActive = false;
                Character* tgt = s_freeMoveAnchor->getAttackTarget().getCharacter();
                if (tgt && tgt->movement)
                {
                    float dist = (tgt->movement->pos - s_freeMoveAnchor->movement->pos).length();
                    bool tgtAttackingUs = (tgt->getAttackTarget().getCharacter() == s_freeMoveAnchor);
                    if (dist <= POST_WASD_REENGAGEMENT_RANGE && tgtAttackingUs)
                        enemyCloseAndActive = true;
                }
                s_combatReentryAllowed = enemyCloseAndActive;
            }
        }
    }
    else
    {
        s_combatReentryAllowed = false;
    }

    // Retreat state tracking — WASD held while combat AI has been suppressed.
    // s_retreatLockEverActive is sticky: set on the first frame go() is suppressed
    // during this WASD hold, cleared on release.  This prevents log bursts on frames
    // where Kenshi skips calling go() (no enemy nearby) while WASD is still held.
    {
        bool curRetreat = wasdActive && s_retreatLockEverActive;
        if (curRetreat && !s_wasdRetreatActive)
        {
            s_wasdRetreatActive      = true;
            s_retreatActiveStartTick = GetTickCount64();
            s_retreatCleanLogged     = false;
            s_combatFlickerLogged    = false;
#if RETREAT_VERBOSE_DIAG
            DebugLog("[WASDCombat] wasd_retreat_state_active");
#endif
        }
        else if (!curRetreat && s_wasdRetreatActive)
        {
            s_wasdRetreatActive = false;
#if RETREAT_VERBOSE_DIAG
            if (!wasdActive)
                DebugLog("[WASDCombat] wasd_manual_retreat_lock_released");
#endif
        }
        if (s_wasdRetreatActive && !s_retreatCleanLogged &&
            GetTickCount64() - s_retreatActiveStartTick >= 1000)
        {
            s_retreatCleanLogged = true;
            DebugLog("[WASDCombat] retreat_clean_locomotion_confirmed");
            if (s_lastKnownEnemyCount > 1)
                DebugLog("[WASDCombat] retreat_locomotion_stable_under_multi_chase");
            DebugLog("[WASDCombat] retreat_perf_optimized");
            char scanBuf[128];
            sprintf_s(scanBuf, sizeof(scanBuf),
                "[WASDCombat] retreat_scan_interval_ms %llu cache_size=%d processed=%d skipped=%d",
                JOB_REMOVAL_INTERVAL_MS, s_retreatSessionCacheCount,
                s_retreatTargetsProcessed, s_retreatTargetsCachedSkipped);
            DebugLog(scanBuf);
#if RETREAT_VERBOSE_DIAG
            {
            char fb[64];
            sprintf_s(fb, sizeof(fb), "[WASDCombat] retreat_attacker_cache_size count=%d",
                s_retreatSessionCacheCount);
            DebugLog(fb);
            if (s_retreatTargetsCachedSkipped > 0)
                DebugLog("[WASDCombat] retreat_fast_path_used");
            }
#endif
        }
    }

    // CombatClass state transition tracking.
    if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor)
    {
        CombatClass* cc2 = s_freeMoveAnchor->getCombatClass();
        if (cc2)
        {
            swordStateEnum curState = cc2->getCombatState();
            if (curState != s_lastCombatState)
            {
#if RETREAT_VERBOSE_DIAG
                {
                const char* stateNames[] = {
                    "CHOP_WEAPON", "BLOCK", "REACTION_BLOCK", "STARTUP_STATE",
                    "DECISION", "CIRCLE_MENACINGLY", "WAIT_MENACINGLY", "HESITATE",
                    "STUMBLE", "COMBAT_FINISHED", "TARGET_PATHFINDING_STARTUP", "TARGET_PATHFINDING"
                };
                const char* curName  = (curState           < 12) ? stateNames[curState]           : "UNKNOWN";
                const char* prevName = (s_lastCombatState  < 12) ? stateNames[s_lastCombatState]  : "UNKNOWN";
                char buf[192];
                sprintf_s(buf, sizeof(buf),
                    "[WASDCombat] combat_state %s -> %s", prevName, curName);
                DebugLog(buf);
                }

                if (wasdActive)
                {
                    if      (curState == CHOP_WEAPON)
                        DebugLog("[WASDCombat] wasd_prevented_run_back_to_target");
                    else if (curState == BLOCK)
                        DebugLog("[WASDCombat] block_pulse_suppressed_during_wasd");
                    else if (curState == STARTUP_STATE)
                        DebugLog("[WASDCombat] startup_state_suppressed_during_wasd");
                    else if (curState == TARGET_PATHFINDING || curState == TARGET_PATHFINDING_STARTUP)
                        DebugLog("[WASDCombat] target_pathfinding_suppressed_during_wasd");
                    else if (curState == CIRCLE_MENACINGLY)
                        DebugLog("[WASDCombat] circle_menacingly_suppressed_during_wasd");
                }
#endif

                if (curState == CHOP_WEAPON)
                {
                    s_attackCommitmentActive = true;
                    s_attackCommitmentStart  = GetTickCount64();
#if RETREAT_VERBOSE_DIAG
                    DebugLog("[WASDCombat] attack_commitment_started");
#endif
                    if (s_wasdReleasedTick > 0 && (GetTickCount64() - s_wasdReleasedTick) < 5000)
                        DebugLog("[WASDCombat] attack_after_wasd_release");
                }
                else if (s_lastCombatState == CHOP_WEAPON)
                {
                    bool wasdAtEnd = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
                    if (wasdAtEnd)
                    {
#if RETREAT_VERBOSE_DIAG
                        DebugLog("[WASDCombat] attack_commitment_cancelled_by_wasd");
#endif
                        s_attackCommitmentActive = false;
                        s_attackCommitmentStart  = 0;
                    }
                    else if (curState == DECISION)
                    {
#if RETREAT_VERBOSE_DIAG
                        DebugLog("[WASDCombat] attack_recovery_phase");
#endif
                        // Keep commitment active through recovery.
                    }
                    else if (curState == CIRCLE_MENACINGLY)
                    {
#if RETREAT_VERBOSE_DIAG
                        DebugLog("[WASDCombat] attack_interrupted_by_circle_menacingly");
#endif
                        s_attackCommitmentActive = false;
                        s_attackCommitmentStart  = 0;
                    }
                    else
                    {
#if RETREAT_VERBOSE_DIAG
                        DebugLog("[WASDCombat] attack_commitment_completed");
#endif
                        s_attackCommitmentActive = false;
                        s_attackCommitmentStart  = 0;
                    }
                }
                else if (s_attackCommitmentActive && s_lastCombatState == DECISION)
                {
                    // Recovery phase ended.
                    bool wasdAtEnd = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
#if RETREAT_VERBOSE_DIAG
                    if (wasdAtEnd)
                        DebugLog("[WASDCombat] attack_commitment_cancelled_by_wasd");
                    else if (curState == CIRCLE_MENACINGLY)
                        DebugLog("[WASDCombat] attack_interrupted_by_circle_menacingly");
                    else if (curState != CHOP_WEAPON)
                        DebugLog("[WASDCombat] attack_commitment_completed");
#else
                    (void)wasdAtEnd;
#endif
                    if (curState != CHOP_WEAPON)
                    {
                        s_attackCommitmentActive = false;
                        s_attackCommitmentStart  = 0;
                    }
                }

                s_lastCombatState = curState;
            }
        }
    }

    // Protected animation state transition tracking.
    if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor)
    {
        bool nowProtected = isProtectedAnimationState(s_freeMoveAnchor);

        if (nowProtected && !s_wasProtectedState)
        {
            if (s_freeMoveAnchor->isCurrentlyGettingUp)
                DebugLog("[WASDCombat] getup_animation_started");
            else
                DebugLog("[WASDCombat] knockdown_or_stagger_started");
        }
        else if (!nowProtected && s_wasProtectedState)
        {
            DebugLog("[WASDCombat] protected_animation_completed");
            DebugLog("[WASDCombat] vmode_runtime_resumed");
        }

        s_wasProtectedState = nowProtected;
    }
}

// -----------------------------------------------------------------------
// ForgottenGUI::showTradeWindow hook — earliest possible loot/trade detection.
//
// showTradeWindow is called the instant the player opens a loot/trade window,
// before isAnyInventoryWindowOpen() returns true and before playerControl_hook
// fires for that frame.  Setting s_lootUiSuspendActive here blocks the very
// first startTrackCharacter call that would otherwise produce the opening sound.
//
// s_lootUiWasPrevOpen is intentionally NOT set here — the mainLoop step-2
// detection manages that flag once the window is confirmed open.  Setting it
// here would cause the close-side to immediately fire (window not yet open).
// -----------------------------------------------------------------------
static void (*s_showTradeWindowOrig)(ForgottenGUI*, const hand&, const hand&, TradeWindowType);

static void showTradeWindow_hook(ForgottenGUI* thisptr, const hand& a, const hand& b, TradeWindowType type)
{
    if (!s_loadGuardActive && s_mode == MODE_FREE_MOVE)
    {
        if (!s_lootUiSuspendActive)
        {
            s_lootUiSuspendActive  = true;
            s_lootSuspendStartTick = GetTickCount64();
#if LOOT_DIAG
            DebugLog("[WASDCombat] loot_interaction_edge_detected_before_ui_open");
            DebugLog("[WASDCombat] early_loot_suspend_applied");
            DebugLog("[WASDCombat] second_loot_sound_prevented");
            char dbuf[64];
            sprintf_s(dbuf, sizeof(dbuf),
                "[WASDCombat] loot_open_debounce_ms %llu", LOOT_SUSPEND_DEBOUNCE_MS);
            DebugLog(dbuf);
#endif
        }
#if LOOT_DIAG
        else
        {
            DebugLog("[WASDCombat] duplicate_initial_loot_open_blocked");
        }
#endif
    }
    s_showTradeWindowOrig(thisptr, a, b, type);
}

// -----------------------------------------------------------------------
// PlayerInterface::playerControl hook
// -----------------------------------------------------------------------
static void (*s_playerControlOrig)(PlayerInterface*, InputHandler&);

static void playerControl_hook(PlayerInterface* thisptr, InputHandler& k)
{
    if (!ou || !ou->player || ou->isLoadingFromASaveGame())
    {
        s_playerControlOrig(thisptr, k);
        return;
    }
    if (s_mode == MODE_FREE_MOVE && !s_lootUiSuspendActive)
    {
        bool wasdHeld = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
        bool atTurret = isUsingStationaryTurret(s_freeMoveAnchor);

        // Preserve directional input when at a stationary turret and WASD not held.
        // Zeroing k.up/down/left/right while the character is aiming a turret causes
        // it to snap back to default every frame, producing the twitch.
        if (wasdHeld || !atTurret)
        {
            k.up    = false;
            k.down  = false;
            k.left  = false;
            k.right = false;
        }
        else
        {
            static ULONGLONG s_turretProtTick = 0;
            ULONGLONG t = GetTickCount64();
            if (t - s_turretProtTick >= 2000) { s_turretProtTick = t;
                DebugLog("[WASDCombat] stationary_crossbow_action_detected");
                DebugLog("[WASDCombat] stationary_action_protected");
                DebugLog("[WASDCombat] vmode_suppression_skipped_stationary_crossbow"); }
        }
    }
    s_playerControlOrig(thisptr, k);
    if (s_mode == MODE_FREE_MOVE && s_freeMoveAnchor && !s_lootUiSuspendActive)
        thisptr->startTrackCharacter(s_freeMoveAnchor);
}

// -----------------------------------------------------------------------
// taskTypeName — used by removeJob_hook
// -----------------------------------------------------------------------
static const char* taskTypeName(TaskType t)
{
    switch (t)
    {
        case MELEE_ATTACK:               return "MELEE_ATTACK";
        case FOCUSED_MELEE_ATTACK:       return "FOCUSED_MELEE_ATTACK";
        case CHOOSE_ENEMY_AND_ATTACK:    return "CHOOSE_ENEMY_AND_ATTACK";
        case CHOOSE_ATTACKER_OF_ALLY:    return "CHOOSE_ATTACKER_OF_ALLY";
        case ATTACK_CHARACTERS_ATTACKER: return "ATTACK_CHARACTERS_ATTACKER";
        case ATTACK_ATTACKERS_OF:        return "ATTACK_ATTACKERS_OF";
        case PROTECT_ALLIES:             return "PROTECT_ALLIES";
        case ATTACK_ENEMIES:             return "ATTACK_ENEMIES";
        case JOB_MEDIC:                  return "JOB_MEDIC";
        case FIRST_AID_ORDER:            return "FIRST_AID_ORDER";
        case FIRST_AID_ROBOT:            return "FIRST_AID_ROBOT";
        case JOB_REPAIR_ROBOT:           return "JOB_REPAIR_ROBOT";
        case SPLINT_ORDER:               return "SPLINT_ORDER";
        case SPLINT_JOB:                 return "SPLINT_JOB";
        case HEAL_MY_LEGS:               return "HEAL_MY_LEGS";
        default: { static char buf[32]; sprintf_s(buf, sizeof(buf), "TASK_%d", (int)t); return buf; }
    }
}

// -----------------------------------------------------------------------
// Character::removeJob hook — misclassification guard
// -----------------------------------------------------------------------
static void (*s_removeJobOrig)(Character* thisptr, TaskType t);

static void removeJob_hook(Character* thisptr, TaskType t)
{
    if (!s_loadGuardActive && s_mode == MODE_FREE_MOVE && thisptr == s_freeMoveAnchor)
    {
        bool wasdHeld    = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
        bool isAttackJob = (t == MELEE_ATTACK            || t == FOCUSED_MELEE_ATTACK  ||
                            t == CHOOSE_ENEMY_AND_ATTACK || t == ATTACK_CHARACTERS_ATTACKER ||
                            t == ATTACK_ENEMIES);
        if (isAttackJob)
        {
            if (wasdHeld)
            {
#if RETREAT_VERBOSE_DIAG
                static ULONGLONG s_chaseTick = 0;
                ULONGLONG tn = GetTickCount64();
                if (tn - s_chaseTick >= 2000) { s_chaseTick = tn;
                    DebugLog("[WASDCombat] wasd_chase_cancelled");
                    DebugLog("[WASDCombat] wasd_old_attack_target_ignored"); }
#endif
            }
            else
            {
                char buf[192];
                sprintf_s(buf, sizeof(buf),
                    "[WASDCombat] WARN removejob_attack_job_misclassification type=%s",
                    taskTypeName(t));
                DebugLog(buf);
            }
        }
    }
    s_removeJobOrig(thisptr, t);
}

// -----------------------------------------------------------------------
// Character::addJob hook — log attack job creation
// -----------------------------------------------------------------------
static void (*s_addJobOrig)(Character* thisptr, TaskType t, RootObject* subject,
                             bool shift, bool addDontClear, const Ogre::Vector3& location);

static void addJob_hook(Character* thisptr, TaskType t, RootObject* subject,
                         bool shift, bool addDontClear, const Ogre::Vector3& location)
{
    if (!s_loadGuardActive && s_mode == MODE_FREE_MOVE && thisptr == s_freeMoveAnchor)
    {
        bool wasdHeld         = s_wHeld || s_aHeld || s_sHeld || s_dHeld;
        bool isAttackJob      = (t == MELEE_ATTACK            || t == FOCUSED_MELEE_ATTACK      ||
                                  t == CHOOSE_ENEMY_AND_ATTACK || t == ATTACK_CHARACTERS_ATTACKER ||
                                  t == ATTACK_ENEMIES);
        bool isSquadAssistJob = (t == PROTECT_ALLIES || t == CHOOSE_ATTACKER_OF_ALLY || t == ATTACK_ATTACKERS_OF);

        bool isMedicalJob     = (t == JOB_MEDIC        || t == FIRST_AID_ORDER  ||
                                  t == FIRST_AID_ROBOT  || t == JOB_REPAIR_ROBOT ||
                                  t == SPLINT_ORDER     || t == SPLINT_JOB       ||
                                  t == HEAL_MY_LEGS);

        // During WASD: block medical jobs — prevents healing-slide locomotion conflict.
        // Logs fire once per hold (s_medicalJobSuppressedThisHold gate); silent on re-entry.
        if (wasdHeld && isMedicalJob)
        {
            if (!s_medicalJobSuppressedThisHold)
            {
                s_medicalJobSuppressedThisHold = true;
                DebugLog("[WASDCombat] medical_job_detected");
                if      (t == JOB_MEDIC)                                  DebugLog("[WASDCombat] self_heal_job_detected");
                else if (t == FIRST_AID_ORDER || t == FIRST_AID_ROBOT)   DebugLog("[WASDCombat] first_aid_job_detected");
                else if (t == SPLINT_ORDER    || t == SPLINT_JOB)        DebugLog("[WASDCombat] splint_job_detected");
                else if (t == JOB_REPAIR_ROBOT)                          DebugLog("[WASDCombat] robotics_repair_job_detected");
                DebugLog("[WASDCombat] medical_job_suppressed_by_wasd");
                DebugLog("[WASDCombat] medical_animation_suppressed_by_wasd");
                DebugLog("[WASDCombat] wasd_prevented_healing_slide");
            }
            return;
        }

        // During WASD: block all combat job re-addition (matches point-click disengage).
        if (wasdHeld && (isAttackJob || isSquadAssistJob))
        {
            if (isAttackJob)
            {
                static ULONGLONG s_reacqTick = 0;
                ULONGLONG tn = GetTickCount64();
                if (tn - s_reacqTick >= 2000) { s_reacqTick = tn;
                    DebugLog("[WASDCombat] wasd_target_reacquire_suppressed");
                    DebugLog("[WASDCombat] old_target_reacquire_blocked_by_retreat_lock");
                    DebugLog("[WASDCombat] combat_reentry_blocked_during_wasd"); }
            }
            return;
        }

        // Post-WASD grace period: block attack jobs unless enemy is close and actively targeting.
        if (s_postWasdGraceActive && !wasdHeld && isAttackJob)
        {
            if (!s_combatReentryAllowed)
            {
                static ULONGLONG s_graceBlockTick = 0;
                ULONGLONG tn = GetTickCount64();
                if (tn - s_graceBlockTick >= 1000) { s_graceBlockTick = tn;
                    DebugLog("[WASDCombat] combat_reentry_blocked_after_wasd_release_enemy_far");
                    DebugLog("[WASDCombat] old_target_attack_resume_blocked_enemy_not_pursuing"); }
                return;
            }
            else
            {
                static ULONGLONG s_graceAllowTick = 0;
                ULONGLONG tn = GetTickCount64();
                if (tn - s_graceAllowTick >= 1000) { s_graceAllowTick = tn;
                    DebugLog("[WASDCombat] combat_reentry_allowed_after_wasd_release_enemy_close"); }
            }
        }

        if (isAttackJob)
        {
            char buf[128];
            sprintf_s(buf, sizeof(buf), "[WASDCombat] attack_job_created type=%s", taskTypeName(t));
            DebugLog(buf);
        }
    }
    s_addJobOrig(thisptr, t, subject, shift, addDontClear, location);
}

// -----------------------------------------------------------------------
// DllMain / startPlugin
// -----------------------------------------------------------------------
BOOL APIENTRY DllMain(HMODULE, DWORD reason, LPVOID)
{
    if (reason == DLL_PROCESS_DETACH)
        DebugLog("WASDCombatPlugin: unloaded");
    return TRUE;
}

__declspec(dllexport) void startPlugin()
{
    DebugLog("WASDCombatPlugin v1.0 — V=toggle X=speed WASD=move");

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&GameWorld::_NV_mainLoop_GPUSensitiveStuff),
            &mainLoop_hook, &s_mainLoopOrig))
        ErrorLog("WASDCombatPlugin: mainLoop hook FAILED");
    else
        DebugLog("WASDCombatPlugin: mainLoop hook OK");

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&CharMovement::_NV_update),
            &charMovUpdate_hook, &s_charMovUpdateOrig))
        ErrorLog("WASDCombatPlugin: charMovUpdate hook FAILED");
    else
        DebugLog("WASDCombatPlugin: charMovUpdate hook OK");

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&PlayerInterface::playerControl),
            &playerControl_hook, &s_playerControlOrig))
        ErrorLog("WASDCombatPlugin: playerControl hook FAILED");
    else
        DebugLog("WASDCombatPlugin: playerControl hook OK");

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&Character::removeJob),
            &removeJob_hook, &s_removeJobOrig))
        ErrorLog("WASDCombatPlugin: removeJob hook FAILED");
    else
        DebugLog("WASDCombatPlugin: removeJob hook OK");

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&Character::addJob),
            &addJob_hook, &s_addJobOrig))
        ErrorLog("WASDCombatPlugin: addJob hook FAILED");
    else
        DebugLog("WASDCombatPlugin: addJob hook OK");

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&CombatClass::_NV_initCombatMode),
            &initCombatMode_hook, &s_initCombatModeOrig))
        ErrorLog("WASDCombatPlugin: initCombatMode hook FAILED");
    else
        DebugLog("WASDCombatPlugin: initCombatMode hook OK");

    // youDoKnowImAttackingYouRight has no _NV_ alias — GetRealAddress can't resolve it.
    // Compute the absolute address directly from the module base + RVA (0x60B570).
    {
        intptr_t base    = (intptr_t)GetModuleHandle(nullptr);
        intptr_t youAddr = base + 0x60B570;
        if (KenshiLib::SUCCESS != KenshiLib::AddHook(
                youAddr, &youKnowImAttacking_hook, &s_youKnowImAttackingOrig))
            ErrorLog("WASDCombatPlugin: youKnowImAttacking hook FAILED");
        else
            DebugLog("WASDCombatPlugin: youKnowImAttacking hook OK");
    }

    if (KenshiLib::SUCCESS != KenshiLib::AddHook(
            KenshiLib::GetRealAddress(&CombatClass::_NV_go),
            &combatClassGo_hook, &s_combatClassGoOrig))
        ErrorLog("WASDCombatPlugin: combatClassGo hook FAILED");
    else
        DebugLog("WASDCombatPlugin: combatClassGo hook OK");

    // showTradeWindow — earliest loot/trade UI detection (RVA 0x7905D0).
    // Fires when the player initiates a loot/trade interaction, before the window
    // is visible and before playerControl_hook can fire startTrackCharacter.
    {
        intptr_t base  = (intptr_t)GetModuleHandle(nullptr);
        intptr_t twAddr = base + 0x7905D0;
        if (KenshiLib::SUCCESS != KenshiLib::AddHook(
                twAddr, &showTradeWindow_hook, &s_showTradeWindowOrig))
            ErrorLog("WASDCombatPlugin: showTradeWindow hook FAILED");
        else
            DebugLog("WASDCombatPlugin: showTradeWindow hook OK");
    }

    HANDLE h = CreateThread(nullptr, 0, PollThread, nullptr, 0, nullptr);
    if (!h)
    {
        char buf[64];
        sprintf_s(buf, sizeof(buf), "WASDCombatPlugin: poll thread FAILED err=%lu", GetLastError());
        ErrorLog(buf);
    }
    else
    {
        CloseHandle(h);
        DebugLog("WASDCombatPlugin: poll thread OK");
    }
}
