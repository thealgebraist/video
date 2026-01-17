# Everyday Horror Trailer Variants - 2 different mundane scenarios turned sinister
# Each with 64 scenes: (scene_id, image_prompt, sfx_prompt)

EVERYDAY_TRAILER_VARIANTS = [
    {
        "name": "morning_routine",
        "title": "Morning Routine",
        "scenes": [
            # ACT 1: NORMAL MORNING (1-16)
            (
                "01_alarm_clock",
                "digital alarm clock showing 6:00 AM in bright red LED, bedside table, curtains closed, morning stillness",
                "alarm beeping gentle rhythm",
            ),
            (
                "02_hit_snooze",
                "hand reaching out to hit snooze button, 9 more minutes, familiar motion, comfort",
                "button press beep silence",
            ),
            (
                "03_alarm_again",
                "alarm beeping again at 6:09, slightly more insistent, routine continuation",
                "alarm beeping louder",
            ),
            (
                "04_getting_up",
                "person sitting up in bed, yawning, stretching, normal morning grogginess, predictable start",
                "yawning stretching sheets",
            ),
            (
                "05_bathroom_walk",
                "walking down hallway to bathroom, half-asleep shuffle, muscle memory guiding steps",
                "footsteps soft padding",
            ),
            (
                "06_light_switch",
                "flipping bathroom light switch, fluorescent lights flickering on, harsh morning brightness",
                "switch click lights buzzing",
            ),
            (
                "07_mirror_face",
                "looking at reflection in bathroom mirror, tired face, bedhead, normal morning appearance",
                "water running ambient",
            ),
            (
                "08_toothbrush_grab",
                "grabbing toothbrush from holder, adding toothpaste, automatic morning task",
                "toothbrush tap paste squirt",
            ),
            (
                "09_brushing_teeth",
                "brushing teeth while staring blankly at mirror, 2 minutes of autopilot routine",
                "brushing scrubbing water",
            ),
            (
                "10_rinse_spit",
                "rinsing mouth, spitting into sink, routine completion, refreshed feeling",
                "water rinsing spitting",
            ),
            (
                "11_shower_on",
                "turning on shower, waiting for water to warm, steam beginning to rise",
                "water running shower spray",
            ),
            (
                "12_in_shower",
                "standing in shower, hot water cascading, eyes closed, peaceful morning meditation",
                "water streaming breathing",
            ),
            (
                "13_shampooing",
                "applying shampoo, lathering hair, familiar scent, routine cleansing",
                "lathering water splashing",
            ),
            (
                "14_shower_off",
                "turning off shower, grabbing towel, stepping onto bath mat, dripping wet",
                "water stopping towel rustling",
            ),
            (
                "15_towel_dry",
                "drying off with towel, wiping mirror clear of steam, seeing reflection again",
                "towel rubbing mirror squeak",
            ),
            (
                "16_dressing",
                "pulling on clothes from closet, same routine outfit, getting ready for work",
                "fabric rustling zipper",
            ),
            # ACT 2: FIRST REPETITIONS (17-32)
            (
                "17_kitchen_walk",
                "walking to kitchen, flipping light switch, same path as always, automatic",
                "footsteps switch click",
            ),
            (
                "18_coffee_start",
                "starting coffee machine, same button press, same gurgling sound, daily ritual",
                "button press machine gurgling",
            ),
            (
                "19_fridge_open",
                "opening refrigerator, same items in same places, milk, eggs, routine grocery",
                "fridge opening cold air",
            ),
            (
                "20_eggs_crack",
                "cracking eggs into pan, same motion as yesterday, and day before, repetition",
                "eggs cracking pan sizzle",
            ),
            (
                "21_toast_pop",
                "toast popping up from toaster, slight char, spreading butter, mechanical action",
                "toast pop knife scraping",
            ),
            (
                "22_coffee_pour",
                "pouring coffee into same mug, same amount creamer, same stirring pattern",
                "liquid pouring spoon stirring",
            ),
            (
                "23_eat_breakfast",
                "eating breakfast while scrolling phone, mindless consumption, double routine",
                "chewing scrolling swallowing",
            ),
            (
                "24_dishes_wash",
                "washing dishes in sink, rinsing plate, drying glass, putting away, loop closing",
                "water running dishes clinking",
            ),
            (
                "25_check_time",
                "checking watch showing 7:15, same time as always, perfectly on schedule",
                "watch check tick",
            ),
            (
                "26_grab_keys",
                "grabbing car keys from hook by door, wallet, phone, same pockets, same order",
                "keys jingling rustling",
            ),
            (
                "27_door_lock",
                "locking front door behind, testing handle, walking to car, leaving for work",
                "lock turning handle check",
            ),
            (
                "28_car_start",
                "starting car, backing out driveway, same route ahead, predictable commute",
                "engine starting gear shifting",
            ),
            (
                "29_same_route",
                "driving same streets, same順序 traffic lights, same radio station, loop continuation",
                "traffic ambient radio",
            ),
            (
                "30_arrive_work",
                "pulling into work parking lot, same spot, same building entrance, arriving",
                "car parking door slam",
            ),
            (
                "31_day_passes",
                "montage of workday passing, meetings, lunch, emails, hours blurring together",
                "keyboard typing phone ringing",
            ),
            (
                "32_drive_home",
                "driving home same route reversed, same landmarks, same timing, returning home",
                "traffic engine road noise",
            ),
            # ACT 3: LOOP REALIZATION (33-48)
            (
                "33_home_again",
                "pulling into driveway at home, unlocking front door, stepping inside, déjà vu strong",
                "car door lock door open",
            ),
            (
                "34_evening_routine",
                "making dinner, eating, watching TV, scrolling phone, mechanical evening habits",
                "cooking tv ambient scrolling",
            ),
            (
                "35_ready_bed",
                "brushing teeth again, putting on pajamas, setting alarm for 6:00 AM tomorrow",
                "brushing fabric alarm beep",
            ),
            (
                "36_alarm_set",
                "alarm clock set for 6:00, same as every night, same routine awaiting tomorrow",
                "beep confirmation digital",
            ),
            (
                "37_lights_out",
                "turning off lights, getting into bed, closing eyes, sleep approaching",
                "switch light sheets",
            ),
            (
                "38_sleep",
                "darkness, breathing slowing, unconsciousness approaching, day ending",
                "breathing deepening silence",
            ),
            (
                "39_alarm_again",
                "alarm beeping at 6:00 AM, same red LEDs, same sound, same routine starting",
                "alarm beeping identical",
            ),
            (
                "40_confusion",
                "hitting snooze but feeling strange, wasn't this just happening, sense of repetition",
                "button press confusion",
            ),
            (
                "41_same_again",
                "getting up, same grogginess, same hallway, same bathroom, everything identical",
                "footsteps familiar exact",
            ),
            (
                "42_mirror_stare",
                "staring longer at mirror reflection, something wrong, but can't identify what",
                "breathing mirror staring",
            ),
            (
                "43_teeth_again",
                "brushing teeth, same motions, same duration, muscle memory too perfect",
                "brushing mechanical exact",
            ),
            (
                "44_shower_again",
                "shower again, same temperature, same duration, same thoughts, loop tightening",
                "water identical pattern",
            ),
            (
                "45_clothes_same",
                "putting on same outfit as yesterday, or was it yesterday, time confusion",
                "fabric same rustling",
            ),
            (
                "46_kitchen_déjà",
                "kitchen feels wrong, coffee machine already on, déjà vu overwhelming",
                "machine already running",
            ),
            (
                "47_eggs_repeat",
                "cracking eggs but knowing exact crack location, done this before, many times",
                "eggs perfect crack",
            ),
            (
                "48_check_date",
                "checking phone calendar but date doesn't change, stuck on same day, horror dawning",
                "phone check same date",
            ),
            # ACT 4: TRAPPED IN LOOP (49-64)
            (
                "49_car_same",
                "driving to work, every car in exact same position, same red light, perfect repetition",
                "traffic identical perfect",
            ),
            (
                "50_work_repeat",
                "arriving at work, coworkers saying exact same words, perfect script repetition",
                "voices echoing same",
            ),
            (
                "51_try_change",
                "attempting to break routine, take different route, but car drives same path",
                "struggling steering resistance",
            ),
            (
                "52_cant_deviate",
                "trying to order different lunch, but same sandwich appears, cannot change anything",
                "confusion same food",
            ),
            (
                "53_time_frozen",
                "clock at work perpetually showing same time, hours not progressing, stuck",
                "clock frozen ticking",
            ),
            (
                "54_people_loop",
                "coworkers moving in loops, repeating same motions endlessly, unaware automatons",
                "voices looping movement",
            ),
            (
                "55_scream_ignored",
                "screaming but no one reacts, continuing their loops, invisible to them",
                "screaming silence continuing",
            ),
            (
                "56_home_instant",
                "instantly home without driving, time skipped, loop compressing, losing coherence",
                "sudden transition displacement",
            ),
            (
                "57_dinner_auto",
                "eating dinner without choosing to, hands moving automatically, no control",
                "eating automatic mechanical",
            ),
            (
                "58_bed_pulled",
                "pulled toward bed against will, routine forcing compliance, irresistible",
                "movement resistance forced",
            ),
            (
                "59_alarm_louder",
                "alarm at 6:00 deafeningly loud, inescapable, starting loop again, consciousness screaming",
                "alarm piercing overwhelming",
            ),
            (
                "60_loop_speeds",
                "routine accelerating, hours becoming minutes, day compressing, spiraling faster",
                "time compression accelerating",
            ),
            (
                "61_simultaneous",
                "experiencing all moments of routine simultaneously, temporal collapse, madness approaching",
                "overlapping chaos simultaneity",
            ),
            (
                "62_acceptance",
                "stopping struggle, accepting loop, becoming automation, consciousness fading",
                "resignation mechanical breathing",
            ),
            (
                "63_perfect_loop",
                "routine now perfect, no thought required, complete automation, no awareness",
                "mechanical perfect silence",
            ),
            (
                "64_alarm_eternal",
                "alarm beeping eternally, 6:00 AM forever, consciousness trapped in single moment repeating infinitely",
                "alarm eternal looping",
            ),
        ],
        "voiceover": """Six AM.
Same alarm.
Every morning.
Wake up.
Bathroom.
Brush teeth.
Same face.
Same routine.
Shower.
Get dressed.
Make coffee.
Crack eggs.
Toast pops.
Check time.
On schedule.
Drive to work.
Same route.
Same traffic.
Work all day.
Drive home.
Make dinner.
Watch TV.
Go to bed.
Set alarm.
Six AM tomorrow.
The routine.
It's comforting.
Or is it?
Six AM. Again.
Same alarm.
Wasn't this?
Just now?
Same bathroom.
Same reflection.
Same toothbrush.
Same shower.
Same clothes.
Same kitchen.
Same coffee.
Same eggs.
Same toast.
Check the date.
It hasn't changed.
Yesterday.
Is today.
Drive to work.
Everyone.
Says same things.
Exact words.
Try to change.
Can't.
The routine.
It won't let me.
Time isn't moving.
Stuck.
In this day.
Same coworkers.
Same lunch.
Same everything.
How many times?
Have I done this?
Hundreds?
Thousands?
I can't break free.
The routine owns me.
Six AM.""",
    },
    # VARIANT 2: THE COMMUTE
    {
        "name": "the_commute",
        "title": "The Commute",
        "scenes": [
            # ACT 1: NORMAL COMMUTE (1-16)
            (
                "01_apartment_door",
                "urban apartment building hallway, closing door, keys locking deadbolt, morning commute beginning",
                "door closing lock turning",
            ),
            (
                "02_elevator_wait",
                "pressing elevator button, waiting in corridor, other residents leaving for work, routine crowd",
                "button press doors opening",
            ),
            (
                "03_elevator_ride",
                "riding elevator down with neighbors, avoiding eye contact, phone scrolling, silent descent",
                "elevator humming ding",
            ),
            (
                "04_lobby_exit",
                "crossing apartment lobby, doorman nodding, revolving door spinning, stepping onto city street",
                "footsteps door revolving",
            ),
            (
                "05_subway_entrance",
                "descending subway station stairs, metro card ready, morning rush hour beginning",
                "footsteps echo card ready",
            ),
            (
                "06_turnstile",
                "swiping metro card through turnstile, pushing through, joining platform crowd",
                "card beep turnstile push",
            ),
            (
                "07_platform_crowd",
                "standing on subway platform with hundreds of commuters, everyone waiting, impersonal mass",
                "crowd murmuring train distant",
            ),
            (
                "08_train_arriving",
                "subway train approaching, headlights in tunnel, brakes screeching, doors will open",
                "train approaching screeching",
            ),
            (
                "09_doors_open",
                "train doors sliding open, crowd pushing forward, squeezing into packed car",
                "doors opening crowd rushing",
            ),
            (
                "10_inside_car",
                "standing in crowded subway car, holding pole, compressed against other bodies, normal discomfort",
                "train moving crowd breathing",
            ),
            (
                "11_reading_phone",
                "scrolling phone to avoid eye contact, checking news, passing time, standard commute",
                "phone scrolling train rattling",
            ),
            (
                "12_first_stop",
                "train stopping at first station, some exit, more enter, continuous flow of humanity",
                "brakes doors chime",
            ),
            (
                "13_second_stop",
                "second station, same pattern, people shuffling, no one speaking, urban isolation together",
                "train stopping shuffling",
            ),
            (
                "14_third_stop",
                "third stop arriving, checking route mentally, four more stops to go, calculating time",
                "announcement doors opening",
            ),
            (
                "15_settling_in",
                "adjusting grip on pole, finding stable position, accepting compression, routine martyrdom",
                "train accelerating swaying",
            ),
            (
                "16_passing_stations",
                "train moving through tunnel, lights flickering outside windows, darkness between stations",
                "rumbling tunnel rushing",
            ),
            # ACT 2: ANOMALIES BEGIN (17-32)
            (
                "17_lights_flicker",
                "subway car lights flickering briefly, power surge, passengers barely notice, continuing routine",
                "lights flickering buzz",
            ),
            (
                "18_look_around",
                "looking around car at other passengers, all staring at phones, faces downward, uniform",
                "silence phone glow",
            ),
            (
                "19_same_faces",
                "noticing same person from yesterday, and day before, same car, same position, coincidence",
                "train rattling recognition",
            ),
            (
                "20_station_repeat",
                "stopping at fourth station, but announcement sounds wrong, same as previous station",
                "announcement distorted",
            ),
            (
                "21_doors_close",
                "doors closing but no one got off, no one got on, car still full, strange",
                "doors closing no movement",
            ),
            (
                "22_tunnel_long",
                "tunnel between stations taking longer than usual, darkness outside prolonged, lights flickering more",
                "tunnel rushing extended darkness",
            ),
            (
                "23_checking_phone",
                "checking phone for time, but signal lost, no service, can't check route, concern rising",
                "phone checking no signal",
            ),
            (
                "24_fifth_stop",
                "arriving at what should be fifth stop, but station sign is blank, white tiles only",
                "train stopping blank platform",
            ),
            (
                "25_no_one_leaves",
                "doors open but no one gets off, no one boards, empty platform, everyone frozen",
                "doors open silence stillness",
            ),
            (
                "26_doors_stay",
                "doors staying open longer than normal, waiting, but for what, uncomfortable pause",
                "ambient hum waiting tension",
            ),
            (
                "27_doors_close",
                "doors finally closing, train lurching forward, continuing into tunnel, wrong direction feeling",
                "doors slam train jerking",
            ),
            (
                "28_all_phones",
                "looking around, everyone's phones showing same blank screen, all lost signal simultaneously",
                "silence glowing screens",
            ),
            (
                "29_same_stop",
                "stopping again at same blank station, same empty platform, impossible, going in circles",
                "train stopping same platform",
            ),
            (
                "30_people_statue",
                "other passengers completely still, not moving, not breathing, frozen mid-scroll, statues",
                "silence no movement stillness",
            ),
            (
                "31_try_door",
                "walking to door, trying to force open, budge, escape, locked, sealed, trapped",
                "handle rattling resistance",
            ),
            (
                "32_conductor_check",
                "walking to front of car, looking for conductor, but connecting door won't open, isolated",
                "door handle locked sealed",
            ),
            # ACT 3: TRAPPED LOOP (33-48)
            (
                "33_return_spot",
                "returning to original pole position, other passengers still frozen, alone but compressed",
                "footsteps return stillness",
            ),
            (
                "34_blank_station",
                "stopping at blank station again, third time, fourth time, counting lost, endless loop",
                "train stopping same blank",
            ),
            (
                "35_lights_die",
                "car lights dying one by one, darkness spreading, only emergency lights remaining, dimming",
                "lights dying one by one",
            ),
            (
                "36_faces_wrong",
                "in dim light, seeing other passengers faces clearly, but faces are wrong, too similar, clones",
                "breathing dread realization",
            ),
            (
                "37_all_same",
                "all passengers are same person, repeated hundreds of times, same clothes, same posture, horror",
                "silence synchronized breathing",
            ),
            (
                "38_check_reflection",
                "seeing own reflection in dark window, but reflection is one of the clones, becoming them",
                "glass reflection gasp",
            ),
            (
                "39_starting_freeze",
                "feeling limbs stiffening, body assuming same posture as others, losing control, conforming",
                "resistance stiffening",
            ),
            (
                "40_phone_glow",
                "phone in hand lighting up on its own, same blank screen as others, joining collective",
                "phone glow soft hum",
            ),
            (
                "41_cant_move",
                "unable to move arms, legs locked in position, frozen like the others, trapped in pose",
                "silence paralysis breathing",
            ),
            (
                "42_station_loop",
                "train stopping at blank station perpetually, doors open, close, open, close, endless rhythm",
                "doors cycling repetition",
            ),
            (
                "43_time_blur",
                "time losing meaning, how many stops, hours, days, stuck in loop, consciousness fragmenting",
                "rhythmic cycling blur",
            ),
            (
                "44_other_cars",
                "seeing through connecting window, other subway cars, all filled with frozen passengers, hundreds of cars",
                "glass reflection infinite",
            ),
            (
                "45_all_frozen",
                "entire subway system filled with frozen commuters, thousands, millions, eternal transport",
                "silence vast stillness",
            ),
            (
                "46_destination_none",
                "understanding there is no destination, never was, commute itself is the trap, the purpose",
                "realization dread",
            ),
            (
                "47_always_commute",
                "been commuting forever, never arrived, never will, eternal transit between nowhere",
                "train rumbling endless",
            ),
            (
                "48_accepting",
                "accepting fate, stopping resistance, becoming another frozen commuter, joining collective",
                "breathing slowing stillness",
            ),
            # ACT 4: ETERNAL COMMUTE (49-64)
            (
                "49_frozen_complete",
                "completely frozen, phone glowing, staring down, indistinguishable from others, assimilated",
                "silence collective",
            ),
            (
                "50_consciousness_remains",
                "consciousness remains trapped inside frozen body, aware but immobile, eternal prison",
                "internal screaming silence",
            ),
            (
                "51_watching_doors",
                "watching doors open close infinitely, same blank station, same nothing, time meaningless",
                "doors cycling eternal",
            ),
            (
                "52_counting_stops",
                "trying to count stops but numbers become meaningless, thousand, million, infinite",
                "cycling counting madness",
            ),
            (
                "53_other_aware",
                "sensing others also conscious inside frozen bodies, all trapped, all aware, all silent",
                "collective awareness presence",
            ),
            (
                "54_telepathic_scream",
                "silent screaming together, all frozen commuters screaming internally, soundless chorus",
                "silence mental screaming",
            ),
            (
                "55_new_passengers",
                "new passengers boarding, living people, taking positions, beginning their freezing, cycle continues",
                "footsteps entering doom",
            ),
            (
                "56_watching_freeze",
                "watching new commuters slowly stiffen, faces changing, joining collective, helpless to warn",
                "transformation silence",
            ),
            (
                "57_they_realize",
                "seeing recognition in their eyes as they understand, too late, becoming us, eternal",
                "realization fear acceptance",
            ),
            (
                "58_train_full",
                "train completely full now, every position filled, frozen commuters packed perfectly, sardines",
                "silence compression fullness",
            ),
            (
                "59_doors_sealed",
                "doors sealing permanently, no more entering, no more attempting to exit, final configuration",
                "doors sealing permanent",
            ),
            (
                "60_lights_out",
                "all lights dying completely, total darkness, but consciousness remains, feeling not seeing",
                "lights dying complete darkness",
            ),
            (
                "61_train_stops",
                "train finally stopping permanently, no more movement, frozen in tunnel, eternal darkness",
                "silence stillness forever",
            ),
            (
                "62_breathing_stops",
                "collective breathing stopping, no longer needed, frozen forever, preserved in moment",
                "silence no breath death",
            ),
            (
                "63_waiting_forever",
                "waiting for next station that won't come, commute that won't end, destination that doesn't exist",
                "silence waiting eternal",
            ),
            (
                "64_eternal_transit",
                "eternal commute, forever between stations, forever compressed, forever frozen, forever waiting",
                "silence forever nothing",
            ),
        ],
        "voiceover": """Another morning.
Another commute.
Lock the door.
Elevator down.
Subway stairs.
Swipe the card.
Platform crowd.
Train arriving.
Doors open.
Push inside.
Compressed bodies.
Hold the pole.
Check phone.
First stop.
Second stop.
Third stop.
Four more to go.
Same route.
Every day.
Same people.
Same faces.
Wait.
Same faces?
The lights.
They're flickering.
Fourth stop.
But the sign.
It's blank.
Doors open.
No one moves.
No one boards.
This isn't right.
Still no signal.
Fifth stop.
The same blank station.
How is this?
The same station.
Again.
Everyone's frozen.
Not moving.
Not breathing.
Their faces.
All the same.
Looking at me.
But they're me.
We're all.
The same.
My reflection.
I'm one of them.
Can't move.
Arms locked.
Frozen.
Like the others.
The doors.
Opening closing.
Opening closing.
Forever.
How long?
Have I been here?
Days?
Years?
There's no destination.
Just this.
The commute.
Forever.
Between stations.
Never arriving.""",
    },
]
