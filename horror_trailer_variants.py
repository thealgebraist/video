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
    # VARIANT 2: THE LAST BROADCAST
    {
        "name": "last_broadcast",
        "title": "The Last Broadcast",
        "scenes": [
            # ACT 1: NORMAL BROADCAST (1-16)
            (
                "01_studio_entrance",
                "vintage 1950s radio broadcast studio entrance, art deco signage 'ON AIR', warm nostalgic lighting",
                "door opening footsteps echo",
            ),
            (
                "02_equipment_room",
                "tube radio equipment glowing amber, analog dials, patch cables, professional broadcast gear",
                "electronic hum gentle buzzing",
            ),
            (
                "03_host_prep",
                "cheerful radio host preparing notes, adjusting headphones, checking microphone levels, professional routine",
                "paper rustling microphone tap",
            ),
            (
                "04_countdown",
                "studio clock showing 30 seconds to broadcast, red ON AIR light warming up, anticipation",
                "clock ticking countdown beep",
            ),
            (
                "05_on_air",
                "ON AIR light illuminates bright red, host smiling into microphone, beginning evening show",
                "light click theme music",
            ),
            (
                "06_intro_speech",
                "host speaking enthusiastically into microphone, animated gestures, connecting with audience",
                "voice speaking clearly warm tone",
            ),
            (
                "07_reading_ads",
                "reading sponsor advertisements from script, vintage product names, nostalgic commercial copy",
                "paper turning voice continuing",
            ),
            (
                "08_playing_music",
                "cueing up vinyl record on turntable, gentle needle drop, music filling studio",
                "vinyl static music playing",
            ),
            (
                "09_listener_calls",
                "switchboard lighting up with incoming calls, host taking requests, engaged conversation",
                "phone ringing switchboard clicking",
            ),
            (
                "10_weather_report",
                "reading local weather forecast from teletype printout, routine segment, normal evening",
                "teletype printing voice reading",
            ),
            (
                "11_time_check",
                "announcing current time 8:47 PM, everything on schedule, smooth broadcast flow",
                "voice speaking clock ticking",
            ),
            (
                "12_commercial_break",
                "pushing slider to play pre-recorded commercials, leaning back in chair, brief rest",
                "audio playing breath exhaling",
            ),
            (
                "13_equipment_check",
                "during break checking signal strength meters, all needles in green zone, everything nominal",
                "meters clicking dials turning",
            ),
            (
                "14_sip_coffee",
                "taking sip of coffee from vintage mug, stretching, preparing for next segment",
                "liquid sipping mug clinking",
            ),
            (
                "15_back_live",
                "commercial ending, host back on air, continuing evening program, professional demeanor",
                "music fading voice returning",
            ),
            (
                "16_normal_broadcast",
                "studio shot showing everything normal, host comfortable, equipment functioning, routine night",
                "ambient studio sounds calm",
            ),
            # ACT 2: FIRST GLITCHES (17-32)
            (
                "17_static_burst",
                "sudden burst of static through speakers, brief interruption, host pausing mid-sentence",
                "static burst sharp interruption",
            ),
            (
                "18_signal_check",
                "host checking equipment, tapping microphone, looking at meters, slight concern",
                "tapping checking confused",
            ),
            (
                "19_continue_on",
                "shrugging off glitch, continuing broadcast, maintaining professional composure",
                "clearing throat voice resuming",
            ),
            (
                "20_lights_dim",
                "studio lights dimming slightly then returning to normal, brief power fluctuation",
                "lights dimming electrical surge",
            ),
            (
                "21_phone_dead",
                "switchboard going dark, all incoming calls cutting off simultaneously, no dial tone",
                "phone lines dying silence",
            ),
            (
                "22_try_calling",
                "attempting to call station engineer, phone completely dead, no signal",
                "phone clicking dead tone",
            ),
            (
                "23_music_distorts",
                "vinyl record playing but audio becoming warped and slowed, pitch dropping unnaturally",
                "music warping slowing distortion",
            ),
            (
                "24_stop_record",
                "lifting needle off record, but warped music continues playing from speakers somehow",
                "needle lift music continues",
            ),
            (
                "25_speakers_off",
                "turning off powered speakers, but audio still emanating from somewhere in studio",
                "switch off audio persisting",
            ),
            (
                "26_looking_around",
                "host standing, looking around studio confused, trying to locate audio source",
                "footsteps searching confusion",
            ),
            (
                "27_clock_wrong",
                "studio clock now showing impossible time, hands moving backwards, time distortion",
                "clock clicking reversed motion",
            ),
            (
                "28_teletype_gibberish",
                "teletype machine activating on its own, printing incomprehensible symbols, not text",
                "teletype chattering nonsense printing",
            ),
            (
                "29_no_door",
                "walking to exit door, but door handle won't turn, appears locked from outside",
                "handle rattling locked resistance",
            ),
            (
                "30_window_check",
                "checking observation window to control room, but room beyond is completely dark, empty",
                "tapping glass darkness beyond",
            ),
            (
                "31_microphone_feedback",
                "microphone screeching with feedback despite not being too close to speakers, harsh sound",
                "feedback screeching piercing",
            ),
            (
                "32_signal_meters",
                "all signal meters pinned at maximum red, indicating impossible signal strength, equipment malfunction",
                "meters slamming alarms beeping",
            ),
            # ACT 3: BROADCAST NEVER ENDED (33-48)
            (
                "33_tape_loop",
                "discovering reel-to-reel tape playing, but it's recording of own voice from earlier tonight",
                "tape playing voice echo",
            ),
            (
                "34_loop_perfect",
                "voice on tape sync perfectly with current speech, predicting every word spoken",
                "synchronized voices perfect timing",
            ),
            (
                "35_cant_stop",
                "trying to stop speaking but voice continues independently, mouth moving on its own",
                "voice continuing involuntary",
            ),
            (
                "36_script_changes",
                "looking down at script, words rearranging themselves on page, text flowing like liquid",
                "paper rustling words shifting",
            ),
            (
                "37_calendar_old",
                "studio calendar showing date from 1952, decades old, but looks freshly printed",
                "page flip impossible date",
            ),
            (
                "38_dust_appearing",
                "thick dust accumulating on equipment in real-time, decades of deterioration accelerating",
                "dust falling settling decay",
            ),
            (
                "39_paint_peeling",
                "studio walls paint peeling and cracking rapidly, revealing older paint beneath, decay spreading",
                "paint crackling walls crumbling",
            ),
            (
                "40_equipment_aging",
                "tube equipment flickering and failing, vacuum tubes burning out, wiring fraying visibly",
                "tubes popping wiring sparking",
            ),
            (
                "41_photos_changing",
                "framed photos on wall showing host growing older in pictures, aging before eyes",
                "subtle creaking reality shifting",
            ),
            (
                "42_mirror_reflection",
                "catching reflection in glass window, but reflection shows host as elderly, decades older",
                "breath catching realization",
            ),
            (
                "43_hands_aging",
                "looking down at own hands, veins prominent, age spots appearing, skin weathering rapidly",
                "gasp horror breathing",
            ),
            (
                "44_voice_older",
                "voice coming from mouth sounds elderly and raspy, no longer youthful radio voice",
                "old voice crackling rasp",
            ),
            (
                "45_memory_gaps",
                "struggling to remember, how long broadcasting, days, years, decades, time meaningless",
                "confused muttering memory strain",
            ),
            (
                "46_studio_decay",
                "studio now clearly abandoned, equipment broken, walls crumbling, but broadcast continues",
                "decay settling destruction",
            ),
            (
                "47_skeleton_crew",
                "seeing reflection of technical crew in glass, but they're skeletal remains at their posts",
                "bones rattling presence",
            ),
            (
                "48_never_left",
                "horror realization never left studio, been broadcasting continuously for 70 years",
                "panicked breathing revelation",
            ),
            # ACT 4: THE TRANSMISSION (49-64)
            (
                "49_audience_none",
                "understanding there's been no audience for decades, broadcasting to empty air, meaningless transmission",
                "silence empty airwaves",
            ),
            (
                "50_cant_stop_broadcast",
                "physically unable to stop talking, voice perpetually streaming, eternal broadcast curse",
                "voice endless compulsive",
            ),
            (
                "51_time_loop",
                "clock showing same time as when broadcast started, trapped in temporal loop, repeating forever",
                "clock ticking stuck time",
            ),
            (
                "52_script_endless",
                "script pages infinite, more pages appearing as reading, never-ending copy, eternal content",
                "pages multiplying paper rustling",
            ),
            (
                "53_other_hosts",
                "seeing shadowy figures of other hosts from other eras, all trapped broadcasting, all cursed",
                "multiple voices overlapping whispers",
            ),
            (
                "54_their_studios",
                "glimpsing other studio timelines overlapping, different decades all broadcasting simultaneously",
                "temporal overlap echo",
            ),
            (
                "55_same_curse",
                "all hosts repeating same shows eternally, same scripts, same music, same loop forever",
                "voices synchronizing unity",
            ),
            (
                "56_trying_scream",
                "attempting to scream for help but voice only produces smooth radio patter, words controlled",
                "smooth voice despite panic",
            ),
            (
                "57_commercial_eternal",
                "commercial break starting but it's sponsor from 1952, same ad repeating infinitely",
                "old commercial looping",
            ),
            (
                "58_products_gone",
                "products advertised don't exist anymore, companies bankrupt 50 years ago, anachronistic",
                "dated copy obsolete references",
            ),
            (
                "59_listeners_dead",
                "callers on switchboard all deceased decades ago, speaking from beyond, dead listeners",
                "ghostly voices static",
            ),
            (
                "60_answering_dead",
                "host answering calls from the dead, taking requests from listeners long buried, macabre interaction",
                "dead voices hollow echoing",
            ),
            (
                "61_music_funeral",
                "playing music requests, but all songs are funeral dirges, mourning music, death march",
                "funeral music slow mournful",
            ),
            (
                "62_final_sign_off",
                "attempting to sign off for the night, but words impossible, broadcast must continue forever",
                "voice struggling failing",
            ),
            (
                "63_eternal_broadcast",
                "accepting fate, will broadcast forever in abandoned studio, timeless loop, eternal prison",
                "resignation acceptance breathing",
            ),
            (
                "64_on_air_forever",
                "ON AIR light still glowing bright red, will never turn off, transmission continuing forever into darkness",
                "light humming eternal signal",
            ),
        ],
        "voiceover": """Good evening listeners.
This is your host.
Broadcasting live.
From the studio.
On this beautiful night.
Time for music.
Time for news.
Your company.
Your comfort.
Everything is fine.
The broadcast continues.
As it always has.
Did you hear that?
Just static.
Technical difficulty.
We'll continue.
The phones are ringing.
But no one answers.
The music plays.
But I didn't cue it.
The clock is wrong.
Time moves strangely.
I try to leave.
The door won't open.
The control room.
It's empty.
How long have I been here?
Minutes? Hours?
The script changes.
I read words.
I never wrote.
My calendar.
It's from 1952.
But that's impossible.
The dust.
Gathering so fast.
The walls.
They're crumbling.
My hands.
They look so old.
My voice.
It sounds ancient.
How long.
Have I been broadcasting?
Days?
Years?
Decades?
I remember now.
I never left.
The show never ended.
The audience.
They're all gone.
But I keep talking.
I can't stop.
The clock shows.
The same time.
Other hosts.
All trapped here.
Broadcasting forever.
We can't stop.
Commercial break.
It never ends.
The listeners.
They're all dead.
But they still call.
I must continue.
The broadcast.
Will never end.
ON AIR.
Forever.""",
    },
]
