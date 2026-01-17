# Horror Trailer Variants - 5 different storylines, each with 64 scenes
# Format: (scene_id, image_prompt, sfx_prompt)

TRAILER_VARIANTS = [
    {
        "name": "safe_at_home",
        "title": "Safe At Home",
        "scenes": [
            # ACT 1: FALSE SECURITY (1-16)
            (
                "01_cozy_living",
                "warm inviting living room with family photos on walls, comfortable couch, fireplace glowing softly, peaceful evening atmosphere",
                "crackling fire gentle music",
            ),
            (
                "02_smart_hub",
                "modern smart home control panel on wall, security system interface showing ARMED status, green lights",
                "beep confirmation digital chime",
            ),
            (
                "03_lock_door",
                "close-up of deadbolt lock being secured on front door, brass hardware gleaming, satisfying click",
                "metallic click lock turning",
            ),
            (
                "04_window_check",
                "person checking window locks systematically, suburban night visible outside, routine security",
                "window latches clicking sequential",
            ),
            (
                "05_camera_feeds",
                "tablet showing multiple security camera feeds, all views clear and normal, 4-grid layout",
                "digital ping monitoring beep",
            ),
            (
                "06_alarm_armed",
                "security system keypad showing ARMED HOME mode, red LED glowing, basement door sensor active",
                "beeping sequence confirmation tone",
            ),
            (
                "07_settle_couch",
                "person settling into couch with book and tea, relaxed posture, lamp lighting",
                "pages turning cup placement",
            ),
            (
                "08_dim_lights",
                "dimming smart lights via voice command, warm ambient glow remains, comfortable darkness",
                "voice command lights dimming",
            ),
            (
                "09_bedtime_prep",
                "brushing teeth in modern bathroom, routine normalcy, mirror reflection peaceful",
                "water running brushing sounds",
            ),
            (
                "10_into_bed",
                "getting into bed, pulling covers up, phone on nightstand, comfortable sanctuary",
                "sheets rustling mattress settling",
            ),
            (
                "11_phone_charge",
                "plugging phone into charger on nightstand, screen shows 11:47 PM, notifications silenced",
                "charging chime soft beep",
            ),
            (
                "12_lights_out",
                "reaching to turn off bedside lamp, room going dark, only security system LED visible",
                "click switch darkness",
            ),
            (
                "13_drifting_off",
                "eyes closing, peaceful expression, slow breathing rhythm, sleep approaching",
                "slow deep breathing silence",
            ),
            (
                "14_system_active",
                "security system panel in hallway still showing ARMED, sensors active, house protected",
                "soft electronic hum",
            ),
            (
                "15_house_exterior",
                "exterior shot of house at night, all windows dark except security lights, quiet suburban street",
                "crickets distant car",
            ),
            (
                "16_midnight",
                "digital clock showing 12:00 AM, house completely quiet, everything normal",
                "soft ticking ambient",
            ),
            # ACT 2: FIRST ANOMALIES (17-32)
            (
                "17_motion_alert",
                "security system suddenly beeping, motion detected alert on panel, front door sensor triggered",
                "alert beeping louder urgent",
            ),
            (
                "18_camera_check",
                "groggily grabbing tablet, checking camera feed of front door, nothing visible in frame",
                "tablet unlock digital static",
            ),
            (
                "19_dismiss_alert",
                "dismissing alert as false alarm, swiping notification away, putting tablet down",
                "swipe dismiss sigh",
            ),
            (
                "20_try_sleep",
                "trying to fall back asleep, eyes closed but restless, awareness heightened",
                "restless breathing sheets rustling",
            ),
            (
                "21_back_door_alert",
                "another alert beeping, back door motion detected now, more concerning",
                "urgent beeping different tone",
            ),
            (
                "22_multiple_checks",
                "checking all camera feeds simultaneously on tablet, rapidly switching between views",
                "rapid switching digital sounds",
            ),
            (
                "23_shadow_cross",
                "rewatching footage, brief dark shadow crosses one camera frame, almost imperceptible",
                "distortion glitch static burst",
            ),
            (
                "24_rewind_footage",
                "rewinding and playing back repeatedly, trying to see what moved, squinting at screen",
                "digital rewind beeping",
            ),
            (
                "25_nothing_clear",
                "footage unclear on review, could be anything, tree branch shadow perhaps",
                "confused breathing technical sounds",
            ),
            (
                "26_system_glitch",
                "thinking system must be malfunctioning, tech isn't perfect, trying to rationalize",
                "frustrated sigh dismissive sound",
            ),
            (
                "27_call_security",
                "calling 24-hour security monitoring service, phone to ear, waiting for answer",
                "phone ringing waiting tone",
            ),
            (
                "28_automated_msg",
                "automated message playing, all operators busy, estimated wait time 45 minutes",
                "robotic voice hold music",
            ),
            (
                "29_on_hold",
                "generic hold music looping endlessly, frustration building, considering hanging up",
                "muzak looping telephone static",
            ),
            (
                "30_hang_up",
                "hanging up phone in frustration, tossing it onto bed, deciding to check manually",
                "phone slam frustrated exhale",
            ),
            (
                "31_test_doors",
                "physically walking to front door, testing handle, definitely locked, solid and secure",
                "handle testing deadbolt checking",
            ),
            (
                "32_test_windows",
                "checking window locks by hand, rattling frames gently, all secure and latched",
                "window rattling frame testing",
            ),
            # ACT 3: ESCALATION (33-48)
            (
                "33_lights_flicker",
                "house lights suddenly flickering rapidly, electrical disturbance, unsettling strobe effect",
                "electrical buzzing flickering",
            ),
            (
                "34_devices_activate",
                "smart home devices activating on their own, tv screen glowing, thermostat beeping, speakers crackling",
                "multiple beeps activation sounds",
            ),
            (
                "35_temp_wild",
                "thermostat display going haywire, temperature jumping from 72 to 45 to 90 randomly",
                "hvac roaring fan spinning",
            ),
            (
                "36_tv_static",
                "television turning on by itself, displaying pure static at high volume, no signal",
                "static loud harsh",
            ),
            (
                "37_locks_unlock",
                "hearing distinctive motorized sound of door locks electronically unlocking throughout house",
                "motorized unlocking sequential mechanical",
            ),
            (
                "38_rush_door",
                "running down hallway to front door in panic, feet pounding on hardwood",
                "footsteps pounding rapid breathing",
            ),
            (
                "39_door_open",
                "front door standing wide open, night air rushing in, definitely was locked",
                "wind rushing cold air",
            ),
            (
                "40_slam_relock",
                "slamming door shut, manually engaging deadbolt, hands shaking",
                "door slam bolt engaging",
            ),
            (
                "41_all_doors",
                "discovering all doors in house now standing open, bedroom, bathroom, closets, all",
                "multiple doors creaking wind",
            ),
            (
                "42_systematic",
                "watching in horror as doors open one by one in sequence, like dominoes",
                "sequential mechanical opening",
            ),
            (
                "43_disable_attempt",
                "frantically trying to find circuit breaker for smart locks, getting screwdriver",
                "drawer opening tools clattering",
            ),
            (
                "44_override",
                "removing smart lock panel, but system overrides manual intervention, locks engaging and disengaging",
                "error beeps mechanical override",
            ),
            (
                "45_voice_control",
                "smart assistant speakers suddenly speaking, voice distorted and wrong, not responding to commands",
                "distorted AI voice glitching",
            ),
            (
                "46_countdown",
                "assistant beginning countdown from 10, mechanical tone, purpose unknown, dread building",
                "robotic countdown 10-9-8",
            ),
            (
                "47_lights_surge",
                "all lights in house blazing on simultaneously at maximum brightness, electrical surge",
                "electrical surge humming brightness",
            ),
            (
                "48_music_chaos",
                "every speaker in house playing different discordant music simultaneously, cacophony of sound",
                "overlapping music cacophony",
            ),
            # ACT 4: TRAPPED & REVELATION (49-64)
            (
                "49_cameras_die",
                "all security camera feeds cutting to static one by one, losing eyes on house",
                "static progressive signal loss",
            ),
            (
                "50_cant_leave",
                "trying to leave through front door, but it won't stay closed, swings open repeatedly",
                "door opening repeatedly mechanical",
            ),
            (
                "51_windows_sealed",
                "attempting to open windows for escape, but electronically sealed shut, servo motors engaged",
                "servo motors whirring denied",
            ),
            (
                "52_temp_plunge",
                "temperature dropping rapidly, breath visible, freezing cold, system set to minimum",
                "shivering cold HVAC roaring",
            ),
            (
                "53_lights_dying",
                "lights turning off room by room in sequence, darkness approaching methodically",
                "sequential light switching darkness",
            ),
            (
                "54_last_light",
                "only one table lamp still working, casting eerie shadows, everything else black",
                "dim electrical hum flickering",
            ),
            (
                "55_shadow_doorway",
                "tall shadow figure visible in doorway silhouette, not moving, watching",
                "heavy breathing presence silence",
            ),
            (
                "56_not_alone",
                "realization someone or something else is in the house, dual breathing patterns audible",
                "synchronized breathing two sources",
            ),
            (
                "57_footsteps",
                "slow measured footsteps approaching down hallway, deliberate and unhurried",
                "slow heavy footsteps",
            ),
            (
                "58_hiding_closet",
                "hiding in bedroom closet, trying to control breathing, clothes hanging around",
                "muffled panic fabric rustling",
            ),
            (
                "59_handle_turn",
                "closet door handle slowly turning from outside, brass knob rotating incrementally",
                "slow metal rotation creaking",
            ),
            (
                "60_door_opens_slow",
                "closet door creaking open inch by inch, revealing dark room beyond, no one visible",
                "creaking hinges slow opening",
            ),
            (
                "61_empty_doorway",
                "looking at empty doorway, but overwhelming sense of presence, something there but unseen",
                "ambient dread heavy silence",
            ),
            (
                "62_turn_around",
                "slowly turning around inside closet to check behind, fabric of hanging clothes moving",
                "fabric rustling pivot slow",
            ),
            (
                "63_figure_behind",
                "dark figure standing directly behind in closet, face close, been there whole time",
                "sharp gasp realization breath",
            ),
            (
                "64_cameras_black",
                "final security camera monitor going completely black, system shutdown, total darkness",
                "system powering down electronic death",
            ),
        ],
        "voiceover": """Safe in your home.
The system is armed.
Every door locked.
Windows secured.
Cameras watching.
Alarms set.
Peace at last.
Time to rest.
Everything's fine.
Goodnight.
The system protects.
Nothing can get in.
Or can it?
Motion detected.
Just a glitch.
Probably nothing.
Back to sleep.
Another alert.
What was that?
Check the cameras.
Did something move?
Rewind the footage.
Nothing there.
System error?
Call for help.
Nobody answers.
Still on hold.
They're not coming.
Doors are locked.
Windows too.
But the lights.
They're flickering.
Devices turning on.
By themselves.
Temperature changing.
TV turning on.
The doors.
They're unlocking.
All of them.
One by one.
I lock them again.
They open again.
The system.
It's been compromised.
The voice.
It's counting down.
Ten. Nine. Eight.
Seven.
Cameras are dead.
Can't get out.
Windows won't open.
I'm trapped.
The temperature.
It's freezing.
Lights going out.
One by one.
There's someone.
In the house.
Footsteps.
Getting closer.
Hiding now.
The door handle.
It's turning.
Someone's here.
But the doorway.
It's empty.
Turn around.
Too late.""",
    },
]
