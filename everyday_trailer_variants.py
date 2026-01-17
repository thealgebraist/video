# Everyday Horror Trailer Variants - 5 different mundane scenarios turned sinister
# Each trailer has: name, scenes (id, image_prompt, sfx_prompt), voiceover_script

EVERYDAY_TRAILER_VARIANTS = [
    {
        "name": "morning_routine",
        "title": "Morning Routine",
        "scenes": [
            (
                "01_alarm_clock",
                "Digital alarm clock showing 6:00 AM, red LED numbers, bedside table, morning light filtering through curtains",
                "alarm beeping gentle buzzing",
            ),
            (
                "02_shower_running",
                "Steam-filled bathroom, shower running, silhouette visible through frosted glass, peaceful morning ritual",
                "water running shower head spray",
            ),
            (
                "03_coffee_brewing",
                "Coffee machine brewing, dark liquid filling a white mug, kitchen counter, routine comfort",
                "coffee machine gurgling dripping liquid pouring",
            ),
            (
                "04_mirror_staring",
                "Person staring into bathroom mirror, but their expression is blank, eyes unfocused, too long, unnatural stillness",
                "silence shallow breathing",
            ),
            (
                "05_repeating_loop",
                "The alarm clock again showing 6:00 AM, same exact scene as before, trapped in a loop",
                "alarm beeping identical pattern distorted time",
            ),
        ],
        "voiceover": """
Wake up.
Shower.
Coffee.
Work.
You've doone this a thousand times.
""",
    },
    {
        "name": "the_commute",
        "title": "The Commute",
        "scenes": [
            (
                "01_subway_platform",
                "Busy subway platform, commuters waiting, fluorescent lighting, tiles and advertisements, mundane urban life",
                "train approaching crowd murmuring",
            ),
            (
                "02_crowded_train",
                "Inside a packed subway car, people reading phones, avoiding eye contact, compressed personal space",
                "train rattling doors closing compressed air",
            ),
            (
                "03_doors_closing",
                "The subway doors closing, but no one else is on the car anymore, completely empty except for one person",
                "door slam silence sudden echo",
            ),
            (
                "04_lights_flickering",
                "The subway lights flicker as the train enters a tunnel, reflections in the windows show more people than are actually there",
                "electrical flicker buzzing multiple whispers",
            ),
            (
                "05_wrong_stop",
                "The train has stopped at a station that doesn't exist, tiled walls are blank, no exit signs, endless platform",
                "screeching halt silence wind whistling",
            ),
        ],
        "voiceover": """
Same train.
Same route.
Same faces.
But today the doors won't open.
And you don't recognize the stop.
""",
    },
    {
        "name": "the_meeting",
        "title": "The Meeting",
        "scenes": [
            (
                "01_office_building",
                "Modern glass office building exterior, corporate logo, people in suits entering, morning business atmosphere",
                "revolving door glass footsteps chatter",
            ),
            (
                "02_conference_room",
                "A sterile conference room with a long table, office chairs, projector screen showing quarterly reports, fluorescent lighting",
                "projector hum papers shuffling typing",
            ),
            (
                "03_colleagues_smiling",
                "Close-up of coworkers sitting around the table, all smiling the exact same smile, too perfect, synchronized",
                "synchronized breathing light humming",
            ),
            (
                "04_screen_glitching",
                "The presentation screen glitches, showing disturbing images of the same conference room but aged and decaying",
                "digital distortion static electrical surge",
            ),
            (
                "05_empty_office",
                "The same conference room is now abandoned, chairs knocked over, papers scattered, decades of dust, but the lights are still on",
                "fluorescent buzzing dripping water silence",
            ),
        ],
        "voiceover": """
The meeting starts at nine.
Everyone's on time.
Everyone's smiling.
But no one remembers what the meeting is about.
And it never ends.
""",
    },
    {
        "name": "grocery_run",
        "title": "The Grocery Run",
        "scenes": [
            (
                "01_parking_lot",
                "Suburban grocery store parking lot, shopping carts scattered, cars parked neatly, familiar retail landscape",
                "car doors shutting carts rattling distant traffic",
            ),
            (
                "02_fluorescent_aisles",
                "Brightly lit grocery store aisles, perfectly stocked shelves, clean floor, elevator music playing, consumer paradise",
                "muzak playing scanner beeping wheels rolling",
            ),
            (
                "03_other_shoppers",
                "Other shoppers moving through the aisles, but they're all moving in the same pattern, synchronized, robotic movements",
                "footsteps in unison rhythmic pattern cart wheels synchronized",
            ),
            (
                "04_checkout_frozen",
                "The checkout counter with the cashier frozen mid-scan, other customers in line are completely still, time has stopped",
                "silence frozen moment heartbeat",
            ),
            (
                "05_exit_blocked",
                "The exit doors are now just a painted wall, no windows, no way out, endless aisles stretching forever",
                "echo footsteps heavy breathing impossibility",
            ),
        ],
        "voiceover": """
Just a quick grocery run.
In and out.
But the aisles keep going.
And the other shoppers aren't shopping

.
They're waiting.
""",
    },
    {
        "name": "the_workout",
        "title": "The Workout",
        "scenes": [
            (
                "01_gym_entrance",
                "Modern gym entrance with glass doors, motivational posters, reception desk, bright and energetic atmosphere",
                "upbeat music door chime greeting",
            ),
            (
                "02_treadmill_running",
                "Person running on a treadmill, digital display showing time and distance, other gym-goers in background, normal fitness scene",
                "treadmill running footfalls beeping display",
            ),
            (
                "03_mirror_reflection",
                "Wall of gym mirrors reflecting rows of treadmills, but the reflections are running at different speeds than reality",
                "asynchronous footsteps speed variation distortion",
            ),
            (
                "04_endurance_test",
                "The digital display on the treadmill shows an impossible distance covered, time shows hours passing, but it's only been minutes",
                "labored breathing machine speeding up time distortion",
            ),
            (
                "05_cant_stop",
                "The emergency stop button doesn't work, the treadmill keeps accelerating, the person can't get off, other gym-goers don't notice",
                "panicked breathing machine roaring desperate shouts",
            ),
        ],
        "voiceover": """
Push yourself.
One more mile.
But the machine knows.
You can't stop.
You've been running for days.
""",
    },
]
