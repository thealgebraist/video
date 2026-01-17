"""
Generate 64-scene horror trailer variants programmatically.
Each variant follows a structured narrative arc with escalating tension.
"""


def generate_safe_at_home_variant():
    """64 scenes: Home security system horror - escalating paranoia"""
    scenes = []
    voiceover_lines = []

    # Act 1: False Security (scenes 1-16)
    act1_scenes = [
        (
            "cozy_living_room",
            "warm living room, family photos, fireplace",
            "crackling fire gentle music",
        ),
        (
            "smart_home_hub",
            "modern smart home control panel, security armed",
            "beep confirmation digital",
        ),
        (
            "locked_doors",
            "deadbolt locks securing all doors",
            "metallic clicks satisfaction",
        ),
        (
            "window_check",
            "checking windows are locked, suburban night",
            "window latches clicking",
        ),
        (
            "security_cameras",
            "security camera feeds on tablet, all clear",
            "digital ping monitoring",
        ),
        ("alarm_set", "alarm system keypad showing ARMED", "beeping confirmation"),
        (
            "comfortable_couch",
            "settling into couch with book, safe feeling",
            "pages turning relaxation",
        ),
        ("peaceful_evening", "dimmed lights, everything normal", "ambient quiet"),
        ("bedtime_routine", "brushing teeth, normal routine", "water running"),
        ("bed_comfort", "getting into bed, pulling up covers", "sheets rustling"),
        ("phone_charging", "phone on nightstand charging", "charging sound"),
        ("lights_out", "turning off bedside lamp", "click darkness"),
        ("drifting_sleep", "eyes closing, peaceful", "slow breathing"),
        ("security_active", "security system still showing armed", "soft beeping"),
        ("all_quiet", "house exterior, all windows dark", "cricket sounds"),
        ("midnight_hour", "clock showing 12:00 AM", "soft ticking"),
    ]

    # Act 2: First Signs (scenes 17-32)
    act2_scenes = [
        (
            "motion_detected",
            "security alert motion detected front door",
            "alert beep louder",
        ),
        ("camera_check", "checking camera feed nothing visible", "digital static"),
        ("dismissing_alert", "dismissing as false alarm", "swipe dismiss"),
        ("back_to_sleep", "trying to sleep again", "restless breathing"),
        ("another_alert", "motion detected back door now", "urgent beeping"),
        ("multiple_cameras", "checking all cameras simultaneously", "rapid switching"),
        ("shadow_movement", "brief shadow crosses one camera", "distortion glitch"),
        ("rewinding_footage", "rewinding to see what moved", "digital rewind"),
        ("nothing_there", "footage shows nothing on review", "confusion silence"),
        ("system_glitch", "thinking system is malfunctioning", "frustrated sigh"),
        ("calling_security", "calling security company", "phone ringing"),
        ("automated_response", "getting automated message", "robotic voice"),
        ("on_hold", "hold music playing endlessly", "muzak looping"),
        ("giving_up", "hanging up in frustration", "phone slam"),
        ("doors_still_locked", "physically checking doors locked", "testing handles"),
        ("windows_secure", "windows still secure", "rattling frames"),
    ]

    # Act 3: Escalation (scenes 33-48)
    act3_scenes = [
        ("lights_flickering", "house lights start flickering", "electrical buzz"),
        ("smart_home_acting", "smart home devices activating on own", "multiple beeps"),
        (
            "thermostat_changing",
            "thermostat adjusting temperature wildly",
            "hvac roaring",
        ),
        ("tv_turning_on", "TV turns on showing static", "static loud"),
        (
            "doors_unlocking",
            "hearing door locks electronically unlocking",
            "motorized unlocking",
        ),
        ("rushing_to_door", "running to front door", "footsteps pounding"),
        ("door_wide_open", "front door standing wide open", "wind rushing"),
        ("closing_relocking", "closing and relocking manually", "slamming latching"),
        ("all_doors_open", "all doors in house now open", "multiple doors creaking"),
        (
            "systematic_opening",
            "doors opening one by one systemically",
            "sequential unlocking",
        ),
        (
            "trying_manual_locks",
            "trying to disable smart locks",
            "screwdriver scraping",
        ),
        ("system_override", "smart system overriding manual attempts", "error beeps"),
        ("voice_control", "smart assistant speaking on its own", "distorted voice"),
        ("counting_down", "assistant counting down from 10", "robotic countdown"),
        ("lights_all_on", "all lights blazing on at once", "electrical surge"),
        ("music_blasting", "all speakers playing discordant music", "cacophony"),
    ]

    # Act 4: Realization (scenes 49-64)
    act4_scenes = [
        (
            "camera_feeds_dead",
            "all security cameras show static now",
            "dead air static",
        ),
        (
            "trapped_inside",
            "realizing can't leave doors won't stay closed",
            "mechanical whirring",
        ),
        ("windows_sealed", "windows won't open electronically sealed", "servo motors"),
        ("temperature_extreme", "temperature dropping to freezing", "shivering cold"),
        ("darkness_systematic", "lights dying room by room", "sequential darkness"),
        ("one_light_remains", "only one lamp still working", "dim flickering"),
        ("shadow_in_doorway", "seeing shadow figure in doorway", "heavy presence"),
        ("not_alone", "realizing someone else is in the house", "dual breathing"),
        ("footsteps_approaching", "footsteps coming closer", "slow measured"),
        ("hiding_closet", "hiding in bedroom closet", "muffled panic"),
        ("door_handle_turning", "closet door handle turning", "slow rotation"),
        ("door_opens", "closet door opens slowly", "creaking hinges"),
        ("empty_doorway", "doorway empty but presence felt", "ambient dread"),
        ("turning_around", "turning around in closet", "fabric rustling"),
        ("figure_behind", "figure standing behind in closet", "sharp gasp"),
        ("screen_goes_black", "final security camera goes black", "system shutdown"),
    ]

    # Combine all acts
    all_scenes = act1_scenes + act2_scenes + act3_scenes + act4_scenes

    # Generate formatted scene data
    for i, (theme, img_prompt, sfx_prompt) in enumerate(all_scenes, 1):
        scene_id = f"{i:02d}_{theme}"
        full_img = f"A {img_prompt}, horror atmosphere, cinematic lighting, 8k detailed"
        scenes.append((scene_id, full_img, sfx_prompt))

    # Generate 64 voiceover lines (one per scene)
    vo_lines = [
        "Safe in your home.",
        "The system is armed.",
        "Every door locked.",
        "Windows secured.",
        "Cameras watching.",
        "Alarms set.",
        "Peace at last.",
        "Time to rest.",
        "Everything's fine.",
        "Goodnight.",
        "The system protects.",
        "Nothing can get in.",
        "Or can it?",
        "Motion detected.",
        "Just a glitch.",
        "Probably nothing.",
        "Back to sleep.",
        "Another alert.",
        "What was that?",
        "Check the cameras.",
        "Did something move?",
        "Rewind the footage.",
        "Nothing there.",
        "System error?",
        "Call for help.",
        "Nobody answers.",
        "Still on hold.",
        "They're not coming.",
        "Doors are locked.",
        "Windows too.",
        "But the lights...",
        "They're flickering.",
        "Devices turning on.",
        "By themselves.",
        "Temperature's changing.",
        "TV turning on.",
        "The doors.",
        "They're unlocking.",
        "All of them.",
        "One by one.",
        "I lock them again.",
        "They open again.",
        "The system.",
        "It's been compromised.",
        "The voice.",
        "It's counting down.",
        "Ten. Nine. Eight.",
        "Seven.",
        "Cameras are dead.",
        "Can't get out.",
        "Windows won't open.",
        "I'm trapped.",
        "The temperature.",
        "It's freezing.",
        "Lights going out.",
        "One by one.",
        "There's someone.",
        "In the house.",
        "Footsteps.",
        "Getting closer.",
        "Hiding now.",
        "The door handle.",
        "It's turning.",
        "Someone's here.",
        "But the doorway.",
        "It's empty.",
        "Turn around.",
        "Too late.",
    ]

    voiceover = "\n".join(vo_lines)

    return {
        "name": "safe_at_home",
        "title": "Safe At Home",
        "scenes": scenes,
        "voiceover": voiceover,
    }


def generate_all_horror_variants():
    """Generate all 5 horror variants with 64 scenes each"""
    return [
        generate_safe_at_home_variant(),
        # TODO: Add other 4 variants following same pattern
    ]


if __name__ == "__main__":
    variant = generate_safe_at_home_variant()
    print(f"Generated variant: {variant['title']}")
    print(f"Total scenes: {len(variant['scenes'])}")
    print(f"First scene: {variant['scenes'][0]}")
    print(f"Last scene: {variant['scenes'][-1]}")
