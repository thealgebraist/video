import torch
import os
import numpy as np
import scipy.io.wavfile as wavfile
import argparse
import utils
import gc
import subprocess
from diffusers import DiffusionPipeline, StableAudioPipeline
from PIL import Image

# --- Configuration & Defaults ---
PROJECT_NAME = "dinner"
ASSETS_DIR = f"assets_{PROJECT_NAME}"
DEVICE = (
    "cuda"
    if torch.cuda.is_available()
    else ("mps" if torch.backends.mps.is_available() else "cpu")
)

# Default values
DEFAULT_MODEL = "black-forest-labs/FLUX.1-schnell"
DEFAULT_STEPS = 4
DEFAULT_GUIDANCE = 0.0

# Scene Definitions (Prompts & SFX Prompts)
SCENES = [
    (
        "01_food_photo",
        "Cinematic medium shot of a guest standing on a chair in a posh dining room, holding an iPhone high to take a photo of a gourmet salad, frustrated guests in background, warm candlelight, 8k",
        "distant chatter, camera shutter click, fork clinking on plate",
    ),
    (
        "02_wine_snob",
        "Close up of a pretentious man in a turtleneck swirling red wine in a crystal glass, nose deep in the glass, look of utter disdain, expensive dinner party background",
        "liquid swirling in glass, pretentious sniffing sound, soft classical music",
    ),
    (
        "03_double_dip",
        "Macro shot of a half-eaten pita chip being dipped back into a bowl of creamy hummus, blurred guest in background, messy table, high detail",
        "squelch of dip, background conversation hum",
    ),
    (
        "04_diet_bomb",
        "Medium shot of a host looking horrified while a guest points at a roast turkey and talks loudly, dinner table setting, awkward expressions of other guests",
        "awkward silence, muffled 'actually I'm a fruitarian' voice",
    ),
    (
        "05_phone_under_table",
        "Close up of hands under a wooden table illuminated by the bright blue glow of a smartphone, dark room background, elegant dinner party atmosphere",
        "low digital notification bloop, muffled laughter",
    ),
    (
        "06_uninvited_dog",
        "Action shot of a large Golden Retriever jumping onto a formal dinner table, licking a block of butter, knocked over wine glasses, chaos, high speed photography",
        "dog barking, plates smashing, collective scream",
    ),
    (
        "07_boring_story",
        "Medium shot of a bored guest with glazed eyes trapped in a corner by a man talking animatedly and gesturing with a greasy fork, dinner party background",
        "monotonous drone of male voice, distant party noise",
    ),
    (
        "08_wine_spill",
        "Slow motion close up of a glass of red wine tipping over, a wave of dark red liquid hitting a white linen tablecloth, dramatic lighting",
        "slow motion liquid splash, sharp intake of breath",
    ),
    (
        "09_kitchen_clutter",
        "A guest standing awkwardly in a tiny kitchen directly in front of an oven, holding a drink, while a stressed host tries to squeeze past with a tray",
        "clattering pans, 'sorry, just trying to get in here' muffled voice",
    ),
    (
        "10_political_fight",
        "Wide shot of a candlelit dinner party where guests are pointing fingers and shouting at each other across the table, dramatic shadows, chaotic energy",
        "loud overlapping arguments, table banging, dish rattling",
    ),
    (
        "11_title_card",
        "Cinematic title card: 'DINNER PARTY HELL' in elegant serif font, stained with red wine splatters, dark background, cinematic lighting",
        "dramatic orchestral hit, glass shattering sound",
    ),
    (
        "12_long_goodbye",
        "A host standing by an open door looking exhausted and checking their watch, while a guest in a coat has one hand on the door handle and is still talking",
        "clock ticking, muffled endless talking, night crickets",
    ),
    (
        "13_guest_breaks_plate",
        "Cinematic shot of guest dropping an expensive ceramic plate while 'helping' to clear the table, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, guest breaks plate",
    ),
    (
        "14_shoes_off_smell_unde",
        "Cinematic shot of guest taking their shoes off under the table, others sniffing the air with concern, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, shoes off smell under",
    ),
    (
        "15_kid_adult_table_mess",
        "Cinematic shot of a 5-year-old playing with mashed potatoes like Play-Doh at a formal dinner, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, kid adult table mess",
    ),
    (
        "16_salt_shaker_theft",
        "Cinematic shot of guest shaking half a bottle of salt onto the host's signature dish without tasting it, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, salt shaker theft",
    ),
    (
        "17_i_brought_my_own_gue",
        "Cinematic shot of guest pulling a bottle of hot sauce and a bag of kale chips from their purse, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, i brought my own guest",
    ),
    (
        "18_over-shared_health_i",
        "Cinematic shot of guest describing their recent colonoscopy in vivid detail while others are eating, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, over-shared health info",
    ),
    (
        "19_the_loud_chewer_mout",
        "Cinematic shot of extreme close up of a mouth chewing loudly, visible food, disgusting, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, the loud chewer mouth",
    ),
    (
        "20_stealing_spotlight_s",
        "Cinematic shot of host trying to make an announcement while a guest starts a loud birthday song for themselves, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, stealing spotlight song",
    ),
    (
        "21_the_un-ironic_actual",
        "Cinematic shot of man with a smug face saying 'Actually...' to a expert on the topic, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, the un-ironic actually",
    ),
    (
        "22_truffle_hogging_scoo",
        "Cinematic shot of guest scooping all the truffles out of a pasta dish into their own plate, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, truffle hogging scoop",
    ),
    (
        "23_overcooked_meat_bric",
        "Cinematic shot of host serving a piece of meat that looks like a charcoal brick, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, overcooked meat brick",
    ),
    (
        "24_awkward_drunk_toast",
        "Cinematic shot of drunk guest making a 10-minute toast that reveals a dark family secret, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, awkward drunk toast",
    ),
    (
        "25_cold_oily_coffee_fil",
        "Cinematic shot of guest looking disappointed at a cup of coffee with a film of oil on top, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, cold oily coffee film",
    ),
    (
        "26_diet_cheat_pantry",
        "Cinematic shot of person who said they were vegan secretly eating a large piece of cheese in the pantry, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, diet cheat pantry",
    ),
    (
        "27_unsolicited_parentin",
        "Cinematic shot of guest lecturing a tired mother while her child draws on the walls with wine, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, unsolicited parenting",
    ),
    (
        "28_one_more_drink_whisk",
        "Cinematic shot of guest pouring the last of the host's expensive whiskey into their glass, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, one more drink whiskey",
    ),
    (
        "29_tech_fix_light_off",
        "Cinematic shot of guest trying to fix the host's smart home system and turning off all the lights, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, tech fix light off",
    ),
    (
        "30_off-key_opera_singin",
        "Cinematic shot of guest belting out opera along with the background music, off-key, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, off-key opera singing",
    ),
    (
        "31_better_made_whisper",
        "Cinematic shot of two guests whispering behind their hands while looking at the food, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, better made whisper",
    ),
    (
        "32_silk_napkin_in_soup",
        "Cinematic shot of an expensive silk napkin floating in a bowl of hot soup, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, silk napkin in soup",
    ),
    (
        "33_forgotten_nut_allerg",
        "Cinematic shot of guest swelling up like a balloon after eating 'nut-free' brownies, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, forgotten nut allergy",
    ),
    (
        "34_mismatched_plastic_s",
        "Cinematic shot of a formal table setting where one guest has a plastic spork, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, mismatched plastic spork",
    ),
    (
        "35_cheese_wheel_fingers",
        "Cinematic shot of guest eating half of a communal cheese wheel with their fingers, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, cheese wheel fingers",
    ),
    (
        "36_crumbs_in_the_beard_",
        "Cinematic shot of man with a large beard full of breadcrumbs and sauce, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, crumbs in the beard man",
    ),
    (
        "37_offensive_satire_jok",
        "Cinematic shot of guest telling a offensive joke and saying 'it's satire' when no one laughs, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, offensive satire joke",
    ),
    (
        "38_staring_at_host_part",
        "Cinematic shot of guest looking a bit too intensely at the host's spouse, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, staring at host partner",
    ),
    (
        "39_influencer_ring_ligh",
        "Cinematic shot of guest bringing a ring light to the dinner table, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, influencer ring light",
    ),
    (
        "40_wrong_shrimp_fork_st",
        "Cinematic shot of guest using a tiny shrimp fork to eat a giant steak, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, wrong shrimp fork steak",
    ),
    (
        "41_i_dont_believe_guest",
        "Cinematic shot of guest announcing they don't believe in gravity or germs, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, i dont believe guest",
    ),
    (
        "42_emptying_whiskey_bot",
        "Cinematic shot of guest tipping a bottle upside down into their glass, eyes wide, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, emptying whiskey bottle",
    ),
    (
        "43_accidental_touch_kne",
        "Cinematic shot of guest's hand lingering on another guest's knee under the table, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, accidental touch knee",
    ),
    (
        "44_water_on_laptop_elec",
        "Cinematic shot of a pitcher of water falling onto the host's laptop on a side table, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, water on laptop electronics",
    ),
    (
        "45_is_this_organic_quer",
        "Cinematic shot of guest looking suspiciously at a carrot with a magnifying glass, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, is this organic query",
    ),
    (
        "46_talking_mouth_full_c",
        "Cinematic shot of guest spraying crumbs while shouting about their crypto portfolio, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, talking mouth full crumbs",
    ),
    (
        "47_guest_tissues_on_ant",
        "Cinematic shot of a guest leaving a pile of used tissues on an antique side table, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, guest tissues on antique",
    ),
    (
        "48_dishes_lie_exit",
        "Cinematic shot of guest looking at a mountain of dishes and then quietly leaving, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, dishes lie exit",
    ),
    (
        "49_i_know_the_chef_lie",
        "Cinematic shot of guest claiming they taught the host how to make this dish, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, i know the chef lie",
    ),
    (
        "50_it_is_a_bit_salty_fa",
        "Cinematic shot of guest making a face after the first bite, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, it is a bit salty face",
    ),
    (
        "51_staying_over_hint_bl",
        "Cinematic shot of guest asking where the extra blankets are at 1 AM, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, staying over hint blankets",
    ),
    (
        "52_forgot_wallet_fifth_",
        "Cinematic shot of guest who forgot their wallet for the 5th time, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, forgot wallet fifth time",
    ),
    (
        "53_minimalist_single_pe",
        "Cinematic shot of serving a single pea on a massive white plate, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, minimalist single pea",
    ),
    (
        "54_maximalist_table_clu",
        "Cinematic shot of a table so covered in decorations there's no room for plates, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, maximalist table clutter",
    ),
    (
        "55_mixologist_vinegar_d",
        "Cinematic shot of guest making a 'custom cocktail' using the host's finest vinegar, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, mixologist vinegar drink",
    ),
    (
        "56_photographer_candid_",
        "Cinematic shot of guest rearranging the host's entire living room for a 'candid' shot, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, photographer candid setup",
    ),
    (
        "57_therapist_childhood_",
        "Cinematic shot of guest analyzing the host's childhood based on the choice of appetizer, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, therapist childhood anal",
    ),
    (
        "58_lawyer_lease_invalid",
        "Cinematic shot of guest explaining why the host's lease is technically invalid, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, lawyer lease invalid",
    ),
    (
        "59_doctor_rare_disease",
        "Cinematic shot of guest diagnosing everyone at the table with a rare tropical disease, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, doctor rare disease",
    ),
    (
        "60_musician_guitar_wond",
        "Cinematic shot of guest picking up the host's decorative guitar and playing Wonderwall, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, musician guitar wonder",
    ),
    (
        "61_comedian_borat_impre",
        "Cinematic shot of guest who won't stop doing a bad 'Borat' impression, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, comedian borat impression",
    ),
    (
        "62_foodie_foraged_by_ha",
        "Cinematic shot of guest who refuses to eat anything that wasn't foraged by hand, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, foodie foraged by hand",
    ),
    (
        "63_local_lost_soul_sinc",
        "Cinematic shot of guest complaining that the city has 'lost its soul' since 1994, dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, local lost soul since 94",
    ),
    (
        "64_traveler_in_bali_sta",
        "Cinematic shot of guest who starts every sentence with 'When I was in Bali...' , dinner party setting, 8k, detailed, dramatic lighting",
        "dinner party sounds, traveler in bali start",
    ),
]

VO_SCRIPT = """
In the pursuit of the perfect evening.
Dignity is off the menu.
Welcome to the table.
Where the wine is pretentious.
And the dip is double.
Did they mention they're fruitarian now?
Connection has never been further away.
The story that never ends.
The spill that never cleans.
Bon Appétit.
Dinner Party Hell.
No one is leaving early.
Broken plates.
Mystery smells.
Potato play.
Salt assault.
The kale chip bandit.
Medical history.
Loud chewers.
Self-birthday song.
Actually...
Truffle theft.
Meat bricks.
Dark secrets.
Oil film coffee.
Pantry cheese.
Wall drawings.
Whiskey hog.
Total darkness.
Off-key opera.
The whisperers.
Soup napkin.
Nut allergy.
The plastic spork.
Finger food.
Beard crumbs.
Satire jokes.
Lustful stares.
Ring lights.
Shrimp forks.
Gravity deniers.
Upside down bottles.
Under-table touch.
Laptop flood.
Magnifying glass organic.
Crypto crumbs.
Tissue mountain.
Dish desertion.
The fake teacher.
A bit salty.
Extra blankets.
Empty wallet.
The single pea.
Clutter maximalism.
Vinegar cocktail.
Candid setup.
Childhood analysis.
Lease invalidation.
Rare diseases.
Wonderwall.
Borat.
Foraged by hand.
Lost soul 94.
Bali stories.
"""

def generate_images(args):
    model_id = args.model or DEFAULT_MODEL
    steps = args.steps or DEFAULT_STEPS
    guidance = args.guidance if args.guidance is not None else DEFAULT_GUIDANCE
    print(f"--- Generating {len(SCENES)} Images with {model_id} ---")
    pipe = DiffusionPipeline.from_pretrained(model_id, torch_dtype=torch.bfloat16 if DEVICE in ["cuda", "mps"] else torch.float32)
    if DEVICE in ["cuda", "mps"]: pipe.enable_model_cpu_offload()
    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)
    for s_id, prompt, _ in SCENES:
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        if not os.path.exists(out_path):
            print(f"Generating: {s_id}")
            image = pipe(prompt=prompt, num_inference_steps=steps, guidance_scale=guidance, width=1280, height=720).images[0]
            image.save(out_path)
    del pipe
    gc.collect()

def generate_sfx(args):
    print(f"--- Generating High Quality SFX with Stable Audio Open ---")
    try:
        pipe = StableAudioPipeline.from_pretrained("stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32).to(DEVICE)
        os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)
        for s_id, _, sfx_prompt in SCENES:
            out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
            if not os.path.exists(out_path):
                print(f"Generating SFX for: {s_id}")
                audio = pipe(sfx_prompt, num_inference_steps=100, audio_end_in_s=10.0).audios[0]
                wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
        del pipe
    except Exception as e: print(f"SFX generation failed: {e}")
    gc.collect()

def generate_voiceover(args):
    print("--- Generating High Quality Voiceover with F5-TTS ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    if os.path.exists(out_path_full): return
    lines = [l.strip() for l in VO_SCRIPT.split("\n") if l.strip()]
    temp_dir = f"{ASSETS_DIR}/voice/f5_temp"
    os.makedirs(temp_dir, exist_ok=True)
    full_audio_data, sampling_rate = [], 44100
    for i, line in enumerate(lines):
        line_out_path = f"{ASSETS_DIR}/voice/vo_{i:03d}.wav"
        if os.path.exists(line_out_path):
            sr, data = wavfile.read(line_out_path)
            full_audio_data.append(data); sampling_rate = sr; continue
        print(f"  Generating line {i}: {line[:30]}...")
        cmd = ["f5-tts_infer-cli", "--gen_text", line, "--output_dir", temp_dir]
        try:
            for f in os.listdir(temp_dir): os.remove(os.path.join(temp_dir, f))
            subprocess.run(cmd, check=True)
            generated_wav = next((os.path.join(temp_dir, f) for f in os.listdir(temp_dir) if f.endswith(".wav")), None)
            if generated_wav:
                os.replace(generated_wav, line_out_path)
                sr, data = wavfile.read(line_out_path)
                full_audio_data.append(data); sampling_rate = sr
                full_audio_data.append(np.zeros(int(sr * 0.6), dtype=data.dtype))
        except Exception as e: print(f"  Line {i} failed: {e}")
    if full_audio_data:
        wavfile.write(out_path_full, sampling_rate, np.concatenate(full_audio_data))

def generate_music(args):
    print(f"--- Generating High Quality Music with Stable Audio Open ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    out_path = f"{ASSETS_DIR}/music/dinner_theme.wav"
    if os.path.exists(out_path): return
    try:
        pipe = StableAudioPipeline.from_pretrained("stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32).to(DEVICE)
        prompt = "Elegant classical string quartet, Mozart style, becomes increasingly discordant and chaotic, cinematic movie trailer transitions, high fidelity"
        print("  Generating 45s music track...")
        audio = pipe(prompt, num_inference_steps=200, audio_end_in_s=45.0).audios[0]
        wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
    except Exception as e: print(f"Music generation failed: {e}")
    gc.collect()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    args = parser.parse_args()
    generate_images(args)
    generate_sfx(args)
    generate_voiceover(args)
    generate_music(args)
