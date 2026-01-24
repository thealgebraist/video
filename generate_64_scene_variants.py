def get_airport_scenes():
    base = [
        ("01_security_line", "Cinematic wide shot of an infinite, snaking security line in a sterile, grey airport terminal, exhausted travelers, harsh overhead lighting, 8k", "High fidelity crisp foley, security line chatter, no static"),
        ("02_boot_struggle", "Close up of a frustrated man hopping on one foot, trying to remove a complex leather boot while holding a grey plastic security bin with his teeth, airport security background", "High fidelity crisp foley, boot leather squeak and plastic bin rattle"),
        ("03_sad_sandwich", "Macro shot of a sad, wilted ham sandwich wrapped in crinkly plastic under a flickering yellow heat lamp in an airport cafe, $18 price tag visible", "High fidelity crisp foley, crinkly plastic wrap sounds"),
        ("04_delayed_sign", "Close up of a digital airport gate sign flipping from 'ON TIME' to 'DELAYED: 6 HOURS', frustrated reflections in the screen", "High fidelity crisp foley, digital flip and announcement chime"),
        ("05_gate_lice", "A crowd of travelers standing too close to the boarding gate, huddled together like a pack of wolves, looking intensely at the gate agent", "High fidelity crisp foley, shuffling feet and murmuring"),
        ("06_tiny_seat", "Interior of an airplane, wide shot of a passenger squeezed into a tiny middle seat between two massive people, knees pushed against the seat in front", "High fidelity crisp foley, plastic creak and heavy breathing"),
        ("07_crying_baby", "Extreme close up of a baby with its mouth wide open, crying, red-faced, sitting in an airplane seat, blurred passenger in foreground looking distressed", "High fidelity crisp foley, clear baby crying sound"),
        ("08_seat_recline", "Close up of a laptop screen being crushed by the seat in front reclining abruptly, sparks and cracked plastic, airplane interior", "High fidelity crisp foley, sharp plastic crack"),
        ("09_turbulence", "Close up of a small plastic cup of tomato juice on a tray table vibrating violently, red liquid splashing out during turbulence", "High fidelity crisp foley, rattling tray and liquid slosh"),
        ("10_lost_suitcase", "Wide shot of a single, battered, lonely suitcase circling an empty baggage carousel in a dimly lit, deserted airport hall at night", "High fidelity crisp foley, mechanical carousel motor"),
        ("11_title_card", "Cinematic title card: 'AIRPORT HELL' in bold, distressed metallic font, airport runway lights in the background, bokeh effect", "High fidelity crisp foley, cinematic orchestral hit"),
        ("12_forgotten_passport", "Close up of a hand slapping a forehead in realization, through a plane window as it pulls away from the gate, a blue passport visible left behind on a seat", "High fidelity crisp foley, muffled voice gasp and jet whine"),
    ]
    
    extra_ideas = [
        ("TSA random search", "gloved hands patting down a confused elderly woman in a wheelchair"),
        ("The liquid baggie leak", "sticky shampoo covering everything in a clear plastic bag"),
        ("One working outlet fight", "three people huddled around a single wall outlet, looking suspicious of each other"),
        ("Loud speakerphone talker", "man shouting into a phone held like a piece of toast in a quiet gate area"),
        ("Slow walkers in groups", "a family of six walking abreast slowly down a narrow concourse"),
        ("Middle seat armrest war", "two elbows fighting for an inch of space on a shared armrest"),
        ("4 AM terminal sleep", "person curled in a fetal position across three metal chairs with armrests"),
        ("Wrong side of gate walk", "exhausted person realizing they walked to Gate A1 instead of Gate F99"),
        ("Car rental shuttle wait", "crowd of people staring hopelessly into the distance for a bus that never comes"),
        ("Duty-free perfume cloud", "person walking through a visible mist of perfume sprayed by an overzealous clerk"),
        ("Gate yoga", "person doing a full downward dog in a crowded boarding area"),
        ("Moving walkway blocker", "two people standing still on the left side of a moving walkway, ignoring the 'walk left' sign"),
        ("Tiny bathroom sink", "hands barely fitting under a faucet that only stays on for 0.5 seconds"),
        ("Impossible toilet paper", "hand clawing at a toilet paper dispenser that only gives 1-inch squares"),
        ("De-icing delay", "thick grey fluid being sprayed onto a plane wing through a window blurred with ice"),
        ("Standing after landing", "a row of people hunched over under the overhead bins while the plane is still taxiing"),
        ("Overhead bin hog", "person putting a tiny jacket and a large shopping bag in the bin sideways"),
        ("Bag sizer struggle", "man sweating while jumping on a suitcase to try and fit it into a metal frame"),
        ("Uber pickup chaos", "hundreds of people staring at phones while cars honk and double-park in the rain"),
        ("Smelly tuna sandwich", "passenger opening a pungent foil-wrapped sandwich in a pressurized cabin"),
        ("Neighbor life story", "trapped passenger nodding politely while neighbor shows 500 photos of their cat"),
        ("Broken screen error", "an airplane seatback screen showing only static and a red 'ERROR' message"),
        ("Scratchy blanket lint", "close up of a paper-thin blue blanket that looks like it's made of dryer lint"),
        ("Call button ping ignore", "close up of a lit-up attendant call button while a flight attendant walks right past"),
        ("Lost keys in dark garage", "man emptying his entire backpack onto the floor of a dark parking garage"),
        ("Liquid restrictions trash", "TSA officer throwing a 10.1oz bottle of expensive hot sauce into a trash can"),
        ("Bare feet on armrest", "a pair of bare feet resting on the armrest of the person in front"),
        ("Tray table hair crumbs", "close up of a tray table covered in hair and unidentified crumbs from a previous flight"),
        ("No snacks water only", "flight attendant handing a passenger a single cup of water and an apologetic look"),
        ("Window shade war hand", "one hand reaching to open a window shade while another hand immediately closes it"),
        ("Customs line maze", "endless maze of tens of thousands of people in a windowless room with no AC"),
        ("Charging cord short", "person sitting on the floor leaning against a trash can to reach a plug"),
        ("Lost connection sprint", "man running through a terminal with a look of pure desperation"),
        ("Vending machine theft", "a bag of chips hanging precariously by a hook in an airport vending machine"),
        ("Emotional support bird", "a large bird sitting on a suitcase in a crowded terminal"),
        ("Wet floor slip", "person slipping on a freshly mopped floor next to a tiny yellow sign"),
        ("Automatic door trap bag", "automatic sliding doors closing on a person with five bags"),
        ("Baggage carousel jam pile", "suitcases piling up in a mountain at the mouth of the carousel"),
        ("The fifteen dollar beer", "a small plastic cup of lukewarm beer next to a receipt"),
        ("Pilot at the bar stare", "a man in a pilot uniform staring intensely into a martini (actually water)"),
        ("Flight path loop screen", "screen showing the plane circling the airport for the 10th time"),
        ("Cup full of ice", "a cup that is 99% ice and 1% soda"),
        ("Priority tag last bag", "a 'Priority' tag on a suitcase that is the last one to come off the belt"),
        ("Hotel voucher sadness", "a sad piece of paper for a 'Discounted Rate' at a 1-star hotel"),
        ("Middle of night page", "empty terminal with a loud voice shouting names over the speakers"),
        ("Upgrade tease denial", "gate agent looking at a screen, then telling a hopeful passenger 'no' "),
        ("Armrest elbow theft", "neighbor's elbow slowly creeping into the passenger's side"),
        ("Snoring neighbor mouth", "man with his head back, mouth open, snoring loudly next to a passenger"),
        ("Child kicking seat back", "the back of a seat vibrating from rhythmic kicks"),
        ("Plastic wrap luggage redundant", "a suitcase completely encased in 50 layers of green plastic wrap"),
        ("Last minute gate change", "crowd of people suddenly turning around and sprinting the other way"),
        ("All natural snack birdseed", "a bag of birdseed-like trail mix that costs $12"),
    ]

    scenes = base[:]
    for i, (desc, prompt_core) in enumerate(extra_ideas):
        s_id = f"{i+13:02d}_{desc.lower().replace(' ', '_').replace("'", '')[:20]}"
        full_prompt = f"Cinematic shot of {prompt_core}, airport setting, 8k, detailed, dramatic lighting"
        sfx_prompt = f"High fidelity crisp foley, {desc.lower()}, no noise, studio quality"
        scenes.append((s_id, full_prompt, sfx_prompt))
    
    return scenes[:64]

def get_dinner_scenes():
    base = [
        ("01_food_photo", "Cinematic medium shot of a guest standing on a chair in a posh dining room, holding an iPhone high to take a photo of a gourmet salad, frustrated guests in background, warm candlelight, 8k", "High fidelity crisp foley, camera shutter click and plate clink"),
        ("02_wine_snob", "Close up of a pretentious man in a turtleneck swirling red wine in a crystal glass, nose deep in the glass, look of utter disdain, expensive dinner party background", "High fidelity crisp foley, wine swirl and sniffing"),
        ("03_double_dip", "Macro shot of a half-eaten pita chip being dipped back into a bowl of creamy hummus, blurred guest in background, messy table, high detail", "High fidelity crisp foley, squelch of dip"),
        ("04_diet_bomb", "Medium shot of a host looking horrified while a guest points at a roast turkey and talks loudly, dinner table setting, awkward expressions of other guests", "High fidelity crisp foley, awkward silence and voice murmur"),
        ("05_phone_under_table", "Close up of hands under a wooden table illuminated by the bright blue glow of a smartphone, dark room background, elegant dinner party atmosphere", "High fidelity crisp foley, phone vibrate and tap"),
        ("06_uninvited_dog", "Action shot of a large Golden Retriever jumping onto a formal dinner table, licking a block of butter, knocked over wine glasses, chaos, high speed photography", "High fidelity crisp foley, dog lick and plate smash"),
        ("07_boring_story", "Medium shot of a bored guest with glazed eyes trapped in a corner by a man talking animatedly and gesturing with a greasy fork, dinner party background", "High fidelity crisp foley, monotonous voice and fork tap"),
        ("08_wine_spill", "Slow motion close up of a glass of red wine tipping over, a wave of dark red liquid hitting a white linen tablecloth, dramatic lighting", "High fidelity crisp foley, liquid splash and gasp"),
        ("09_kitchen_clutter", "A guest standing awkwardly in a tiny kitchen directly in front of an oven, holding a drink, while a stressed host tries to squeeze past with a tray", "High fidelity crisp foley, pan clatter and sorry whisper"),
        ("10_political_fight", "Wide shot of a candlelit dinner party where guests are pointing fingers and shouting at each other across the table, dramatic shadows, chaotic energy", "High fidelity crisp foley, shouting and table bang"),
        ("11_title_card", "Cinematic title card: 'DINNER PARTY HELL' in elegant serif font, stained with red wine splatters, dark background, cinematic lighting", "High fidelity crisp foley, dramatic orchestral hit"),
        ("12_long_goodbye", "A host standing by an open door looking exhausted and checking their watch, while a guest in a coat has one hand on the door handle and is still talking", "High fidelity crisp foley, clock tick and endless talking"),
    ]

    extra_ideas = [
        ("Guest breaks plate", "guest dropping an expensive ceramic plate while 'helping' to clear the table"),
        ("Shoes off smell under", "guest taking their shoes off under the table, others sniffing the air with concern"),
        ("Kid adult table mess", "a 5-year-old playing with mashed potatoes like Play-Doh at a formal dinner"),
        ("Salt shaker theft", "guest shaking half a bottle of salt onto the host's signature dish without tasting it"),
        ("I brought my own guest", "guest pulling a bottle of hot sauce and a bag of kale chips from their purse"),
        ("Over-shared health info", "guest describing their recent colonoscopy in vivid detail while others are eating"),
        ("The loud chewer mouth", "extreme close up of a mouth chewing loudly, visible food, disgusting"),
        ("Stealing spotlight song", "host trying to make an announcement while a guest starts a loud birthday song for themselves"),
        ("The un-ironic actually", "man with a smug face saying 'Actually...' to a expert on the topic"),
        ("Truffle hogging scoop", "guest scooping all the truffles out of a pasta dish into their own plate"),
        ("Overcooked meat brick", "host serving a piece of meat that looks like a charcoal brick"),
        ("Awkward drunk toast", "drunk guest making a 10-minute toast that reveals a dark family secret"),
        ("Cold oily coffee film", "guest looking disappointed at a cup of coffee with a film of oil on top"),
        ("Diet cheat pantry", "person who said they were vegan secretly eating a large piece of cheese in the pantry"),
        ("Unsolicited parenting", "guest lecturing a tired mother while her child draws on the walls with wine"),
        ("One more drink whiskey", "guest pouring the last of the host's expensive whiskey into their glass"),
        ("Tech fix light off", "guest trying to fix the host's smart home system and turning off all the lights"),
        ("Off-key opera singing", "guest belting out opera along with the background music, off-key"),
        ("Better made whisper", "two guests whispering behind their hands while looking at the food"),
        ("Silk napkin in soup", "an expensive silk napkin floating in a bowl of hot soup"),
        ("Forgotten nut allergy", "guest swelling up like a balloon after eating 'nut-free' brownies"),
        ("Mismatched plastic spork", "a formal table setting where one guest has a plastic spork"),
        ("Cheese wheel fingers", "guest eating half of a communal cheese wheel with their fingers"),
        ("Crumbs in the beard man", "man with a large beard full of breadcrumbs and sauce"),
        ("Offensive satire joke", "guest telling a offensive joke and saying 'it's satire' when no one laughs"),
        ("Staring at host partner", "guest looking a bit too intensely at the host's spouse"),
        ("Influencer ring light", "guest bringing a ring light to the dinner table"),
        ("Wrong shrimp fork steak", "guest using a tiny shrimp fork to eat a giant steak"),
        ("I dont believe guest", "guest announcing they don't believe in gravity or germs"),
        ("Emptying whiskey bottle", "guest tipping a bottle upside down into their glass, eyes wide"),
        ("Accidental touch knee", "guest's hand lingering on another guest's knee under the table"),
        ("Water on laptop electronics", "a pitcher of water falling onto the host's laptop on a side table"),
        ("Is this organic query", "guest looking suspiciously at a carrot with a magnifying glass"),
        ("Talking mouth full crumbs", "guest spraying crumbs while shouting about their crypto portfolio"),
        ("Guest tissues on antique", "a guest leaving a pile of used tissues on an antique side table"),
        ("Dishes lie exit", "guest looking at a mountain of dishes and then quietly leaving"),
        ("I know the chef lie", "guest claiming they taught the host how to make this dish"),
        ("It is a bit salty face", "guest making a face after the first bite"),
        ("Staying over hint blankets", "guest asking where the extra blankets are at 1 AM"),
        ("Forgot wallet fifth time", "guest who forgot their wallet for the 5th time"),
        ("Minimalist single pea", "serving a single pea on a massive white plate"),
        ("Maximalist table clutter", "a table so covered in decorations there's no room for plates"),
        ("Mixologist vinegar drink", "guest making a 'custom cocktail' using the host's finest vinegar"),
        ("Photographer candid setup", "guest rearranging the host's entire living room for a 'candid' shot"),
        ("Therapist childhood anal", "guest analyzing the host's childhood based on the choice of appetizer"),
        ("Lawyer lease invalid", "guest explaining why the host's lease is technically invalid"),
        ("Doctor rare disease", "guest diagnosing everyone at the table with a rare tropical disease"),
        ("Musician guitar wonder", "guest picking up the host's decorative guitar and playing Wonderwall"),
        ("Comedian Borat impression", "guest who won't stop doing a bad 'Borat' impression"),
        ("Foodie foraged by hand", "guest who refuses to eat anything that wasn't foraged by hand"),
        ("Local lost soul since 94", "guest complaining that the city has 'lost its soul' since 1994"),
        ("Traveler in Bali start", "guest who starts every sentence with 'When I was in Bali...' ")
    ]

    scenes = base[:]
    for i, (desc, prompt_core) in enumerate(extra_ideas):
        s_id = f"{i+13:02d}_{desc.lower().replace(' ', '_').replace("'", '')[:20]}"
        full_prompt = f"Cinematic shot of {prompt_core}, dinner party setting, 8k, detailed, dramatic lighting"
        sfx_prompt = f"High fidelity crisp foley, {desc.lower()}, no noise, studio quality"
        scenes.append((s_id, full_prompt, sfx_prompt))
    
    return scenes[:64]

def update_asset_file(file_path, scenes, is_airport):
    with open(file_path, 'r') as f:
        content = f.read()
    
    import re
    # 1. Replace SCENES block
    scenes_lines = []
    for s_id, prompt, sfx in scenes:
        scenes_lines.append(f'    (\n        "{s_id}",\n        "{prompt}",\n        "{sfx}",\n    ),')
    scenes_str = "SCENES = [\n" + "\n".join(scenes_lines) + "\n]"
    content = re.sub(r"SCENES = \[.*?\]", scenes_str, content, flags=re.DOTALL)
    
    # 2. Update VO_SCRIPT
    if is_airport:
        vo_lines = [
            "In a world where time stands still.", "And dignity comes to die.", "Welcome to the terminal.",
            "Where a sandwich costs more than your soul.", "And your gate is always further than you think.",
            "The battle for Group 9 begins now.", "Brace for impact.", "Because the person in 14B is already reclining.",
            "And the infant in 15C has a lot to say.", "Buckle up.", "Because you're never leaving.", "Airport Hell.",
            "Coming to a terminal near you.", "Random searches.", "Leaking baggies.", "One outlet to rule them all.",
            "Speakerphone shouters.", "The slow-walking wall.", "Armrest wars.", "Cold metal chair sleep.",
            "Gate F99 is a marathon.", "Shuttle bus to nowhere.", "Perfume clouds.", "Downward dog at Gate 4.",
            "Stay right, walk left.", "Faucet drip.", "Single ply paper.", "Ice wing spray.", "Standing in the aisle.",
            "Overhead bin hogs.", "Bag sizer struggle.", "Uber lane chaos.", "Tuna sandwich air.", "Cat photo show.",
            "Static screen.", "Lint blanket.", "Ignored call button.", "Garage key hunt.", "Hot sauce in the bin.",
            "Feet on the seat.", "Crumby table.", "Water only.", "Shade wars.", "Customs maze.", "Charging on the floor.",
            "The missed connection.", "Vending machine theft.", "Support bird.", "Wet floor slide.", "Door trap.",
            "Bag mountain.", "Fifteen dollar beer.", "Pilot at the bar.", "Orbiting the city.", "Cup of ice.",
            "Priority last.", "Hotel voucher.", "Empty terminal.", "Upgrade denied.", "Elbow creep.", "Snore fest.",
            "Seat kick.", "Plastic wrap.", "Gate change sprint.", "Birdseed snack.",
        ]
    else:
        vo_lines = [
            "In the pursuit of the perfect evening.", "Dignity is off the menu.", "Welcome to the table.",
            "Where the wine is pretentious.", "And the dip is double.", "Did they mention they're fruitarian now?",
            "Connection has never been further away.", "The story that never ends.", "The spill that never cleans.",
            "Bon Appétit.", "Dinner Party Hell.", "No one is leaving early.", "Broken plates.", "Mystery smells.",
            "Potato play.", "Salt assault.", "The kale chip bandit.", "Medical history.", "Loud chewers.",
            "Self-birthday song.", "Actually...", "Truffle theft.", "Meat bricks.", "Dark secrets.", "Oil film coffee.",
            "Pantry cheese.", "Wall drawings.", "Whiskey hog.", "Total darkness.", "Off-key opera.", "The whisperers.",
            "Soup napkin.", "Nut allergy.", "The plastic spork.", "Finger food.", "Beard crumbs.", "Satire jokes.",
            "Lustful stares.", "Ring lights.", "Shrimp forks.", "Gravity deniers.", "Upside down bottles.",
            "Under-table touch.", "Laptop flood.", "Magnifying glass organic.", "Crypto crumbs.", "Tissue mountain.",
            "Dish desertion.", "The fake teacher.", "A bit salty.", "Extra blankets.", "Empty wallet.", "The single pea.",
            "Clutter maximalism.", "Vinegar cocktail.", "Candid setup.", "Childhood analysis.", "Lease invalidation.",
            "Rare diseases.", "Wonderwall.", "Borat.", "Foraged by hand.", "Lost soul 94.", "Bali stories.",
        ]
    
    vo_script_str = 'VO_SCRIPT = """\n' + "\n".join(vo_lines[:64]) + '\n"""'
    content = re.sub(r'VO_SCRIPT = """.*?"""', vo_script_str, content, flags=re.DOTALL)

    with open(file_path, 'w') as f:
        f.write(content)

def update_assembly_file(file_path, scenes):
    with open(file_path, 'r') as f:
        content = f.read()
    
    import re
    content = re.sub(r"TOTAL_DURATION = \d+", "TOTAL_DURATION = 120", content)
    scenes_list_str = "SCENES = [\n        " + ", ".join([f'\"{s}\"' for s in scenes]) + "\n    ]"
    content = re.sub(r"SCENES = \[.*?\}", scenes_list_str, content, flags=re.DOTALL)
    with open(file_path, 'w') as f:
        f.write(content)

if __name__ == "__main__":
    airport_scenes = get_airport_scenes()
    dinner_scenes = get_dinner_scenes()
    update_asset_file("generate_airport_assets.py", airport_scenes, True)
    update_asset_file("generate_dinner_party_assets.py", dinner_scenes, False)
    update_assembly_file("assemble_airport_trailer.py", [s[0] for s in airport_scenes])
    update_assembly_file("assemble_dinner_party_trailer.py", [s[0] for s in dinner_scenes])
    with open("airport_trailer_script.md", "w") as f:
        f.write("# Airport Hell (64 Scenes)\n\n")
        for s_id, prompt, sfx in airport_scenes: f.write(f"## {s_id}\nVisual: {prompt}\nAudio: {sfx}\n\n")
    with open("dinner_party_script.md", "w") as f:
        f.write("# Dinner Party Hell (64 Scenes)\n\n")
        for s_id, prompt, sfx in dinner_scenes: f.write(f"## {s_id}\nVisual: {prompt}\nAudio: {sfx}\n\n")
    print("Updated all files with 64 scenes and noise-free SFX prompts.")