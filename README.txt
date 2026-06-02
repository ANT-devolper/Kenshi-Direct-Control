================================================================
  DIRECT CONTROL FOR KENSHI
  Version 1.1
================================================================

WHAT IT DOES
------------
Direct Control gives you full WASD movement for your selected
character in Kenshi. Press V to toggle it on, use WASD to move,
and your character will immediately respond — overriding
point-click pathing, combat AI locomotion, and squad commands.

Built for players who want precise, manual control during
combat, retreats, ambushes, and city navigation without losing
any of Kenshi's survival systems.

CONTROLS
--------
  V         Toggle Direct Control on / off
  W A S D   Move character (camera-relative)
  X         Cycle movement speed (Walk / Jog / Run)

FEATURES
--------
  Immediate override
    WASD instantly cancels point-click destinations and overrides
    combat AI locomotion. No startup delay. No grace period on
    key press.

  Combat retreat
    Holding WASD while enemies are targeting you suppresses
    combat job re-addition, blocks combat state machine cycling,
    and keeps your character running instead of snapping back
    into attack animations.

  Speed toggle (X key)
    Cycles through Walk, Jog, and Run using the game's own speed
    system. Works with squads and orders panel.

  Stationary crossbow protection
    While manning a turret or crossbow and not holding WASD,
    Direct Control does not interfere with aiming input.
    Pressing WASD cancels turret use and returns to free movement.

  Downed / crippled movement
    Characters that are crippled or playing dead can still be
    moved with WASD using the game's crawl/limp system.

  Loot UI suspend
    Direct Control automatically pauses while any loot or trade
    window is open. Input and camera tracking restore cleanly
    when the window closes.

  Save / load safety
    A stabilization countdown prevents any input from firing
    during game load transitions. State resets cleanly on reload.

  Medical job protection
    Medical and healing jobs are suppressed during WASD holds to
    prevent locomotion conflicts. They resume automatically on
    key release.

REQUIREMENTS
------------
  - Kenshi (Steam)
  - RE_Kenshi mod loader

  RE_Kenshi must be installed and active in your mod list.
  Direct Control will not load without it.

COMPATIBILITY
-------------
  Works alongside most combat, AI, and faction mods.
  Does not modify game data files — DLL only.
  Safe for use with large mod lists.

KNOWN LIMITATIONS
-----------------
  - Direct Control is per-character. Switch characters in-game
    normally; V-Mode follows your selected character.
  - During knockdown or stagger animations the character cannot
    be moved (protected state). Movement resumes automatically
    when the animation completes.
  - Squad members are not controlled by Direct Control. Only
    your currently selected character responds to WASD.

CREDITS
-------
  Developed as "WASDCombatPlugin" using the RE_Kenshi SDK.
  Built for Kenshi v1.0.x (Steam).

================================================================
