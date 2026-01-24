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
        "High fidelity crisp foley, camera shutter click and plate clink",
    ),
    (
        "02_wine_snob",
        "Close up of a pretentious man in a turtleneck swirling red wine in a crystal glass, nose deep in the glass, look of utter disdain, expensive dinner party background",
        "High fidelity crisp foley, wine swirl and sniffing",
    ),
    (
        "03_double_dip",
        "Macro shot of a half-eaten pita chip being dipped back into a bowl of creamy hummus, blurred guest in background, messy table, high detail",
        "High fidelity crisp foley, squelch of dip",
    ),
    (
        "04_diet_bomb",
        "Medium shot of a host looking horrified while a guest points at a roast turkey and talks loudly, dinner table setting, awkward expressions of other guests",
        "High fidelity crisp foley, awkward silence and voice murmur",
    ),
    (
        "05_phone_under_table",
        "Close up of hands under a wooden table illuminated by the bright blue glow of a smartphone, dark room background, elegant dinner party atmosphere",
        "High fidelity crisp foley, phone vibrate and tap",
    ),
    (
        "06_uninvited_dog",
        "Action shot of a large Golden Retriever jumping onto a formal dinner table, licking a block of butter, knocked over wine glasses, chaos, high speed photography",
        "High fidelity crisp foley, dog lick and plate smash",
    ),
    (
        "07_boring_story",
        "Medium shot of a bored guest with glazed eyes trapped in a corner by a man talking animatedly and gesturing with a greasy fork, dinner party background",
        "High fidelity crisp foley, monotonous voice and fork tap",
    ),
    (
        "08_wine_spill",
        "Slow motion close up of a glass of red wine tipping over, a wave of dark red liquid hitting a white linen tablecloth, dramatic lighting",
        "High fidelity crisp foley, liquid splash and gasp",
    ),
    (
        "09_kitchen_clutter",
        "A guest standing awkwardly in a tiny kitchen directly in front of an oven, holding a drink, while a stressed host tries to squeeze past with a tray",
        "High fidelity crisp foley, pan clatter and sorry whisper",
    ),
    (
        "10_political_fight",
        "Wide shot of a candlelit dinner party where guests are pointing fingers and shouting at each other across the table, dramatic shadows, chaotic energy",
        "High fidelity crisp foley, shouting and table bang",
    ),
    (
        "11_title_card",
        "Cinematic title card: 'DINNER PARTY HELL' in elegant serif font, stained with red wine splatters, dark background, cinematic lighting",
        "High fidelity crisp foley, dramatic orchestral hit",
    ),
    (
        "12_long_goodbye",
        "A host standing by an open door looking exhausted and checking their watch, while a guest in a coat has one hand on the door handle and is still talking",
        "High fidelity crisp foley, clock tick and endless talking",
    ),
    (
        "13_guest_breaks_plate",
        "Cinematic shot of guest dropping an expensive ceramic plate while 'helping' to clear the table, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, guest breaks plate, no noise, studio quality",
    ),
    (
        "14_shoes_off_smell_unde",
        "Cinematic shot of guest taking their shoes off under the table, others sniffing the air with concern, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, shoes off smell under, no noise, studio quality",
    ),
    (
        "15_kid_adult_table_mess",
        "Cinematic shot of a 5-year-old playing with mashed potatoes like Play-Doh at a formal dinner, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, kid adult table mess, no noise, studio quality",
    ),
    (
        "16_salt_shaker_theft",
        "Cinematic shot of guest shaking half a bottle of salt onto the host's signature dish without tasting it, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, salt shaker theft, no noise, studio quality",
    ),
    (
        "17_i_brought_my_own_gue",
        "Cinematic shot of guest pulling a bottle of hot sauce and a bag of kale chips from their purse, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, i brought my own guest, no noise, studio quality",
    ),
    (
        "18_over-shared_health_i",
        "Cinematic shot of guest describing their recent colonoscopy in vivid detail while others are eating, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, over-shared health info, no noise, studio quality",
    ),
    (
        "19_the_loud_chewer_mout",
        "Cinematic shot of extreme close up of a mouth chewing loudly, visible food, disgusting, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, the loud chewer mouth, no noise, studio quality",
    ),
    (
        "20_stealing_spotlight_s",
        "Cinematic shot of host trying to make an announcement while a guest starts a loud birthday song for themselves, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, stealing spotlight song, no noise, studio quality",
    ),
    (
        "21_the_un-ironic_actual",
        "Cinematic shot of man with a smug face saying 'Actually...' to a expert on the topic, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, the un-ironic actually, no noise, studio quality",
    ),
    (
        "22_truffle_hogging_scoo",
        "Cinematic shot of guest scooping all the truffles out of a pasta dish into their own plate, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, truffle hogging scoop, no noise, studio quality",
    ),
    (
        "23_overcooked_meat_bric",
        "Cinematic shot of host serving a piece of meat that looks like a charcoal brick, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, overcooked meat brick, no noise, studio quality",
    ),
    (
        "24_awkward_drunk_toast",
        "Cinematic shot of drunk guest making a 10-minute toast that reveals a dark family secret, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, awkward drunk toast, no noise, studio quality",
    ),
    (
        "25_cold_oily_coffee_fil",
        "Cinematic shot of guest looking disappointed at a cup of coffee with a film of oil on top, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, cold oily coffee film, no noise, studio quality",
    ),
    (
        "26_diet_cheat_pantry",
        "Cinematic shot of person who said they were vegan secretly eating a large piece of cheese in the pantry, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, diet cheat pantry, no noise, studio quality",
    ),
    (
        "27_unsolicited_parentin",
        "Cinematic shot of guest lecturing a tired mother while her child draws on the walls with wine, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, unsolicited parenting, no noise, studio quality",
    ),
    (
        "28_one_more_drink_whisk",
        "Cinematic shot of guest pouring the last of the host's expensive whiskey into their glass, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, one more drink whiskey, no noise, studio quality",
    ),
    (
        "29_tech_fix_light_off",
        "Cinematic shot of guest trying to fix the host's smart home system and turning off all the lights, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, tech fix light off, no noise, studio quality",
    ),
    (
        "30_off-key_opera_singin",
        "Cinematic shot of guest belting out opera along with the background music, off-key, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, off-key opera singing, no noise, studio quality",
    ),
    (
        "31_better_made_whisper",
        "Cinematic shot of two guests whispering behind their hands while looking at the food, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, better made whisper, no noise, studio quality",
    ),
    (
        "32_silk_napkin_in_soup",
        "Cinematic shot of an expensive silk napkin floating in a bowl of hot soup, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, silk napkin in soup, no noise, studio quality",
    ),
    (
        "33_forgotten_nut_allerg",
        "Cinematic shot of guest swelling up like a balloon after eating 'nut-free' brownies, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, forgotten nut allergy, no noise, studio quality",
    ),
    (
        "34_mismatched_plastic_s",
        "Cinematic shot of a formal table setting where one guest has a plastic spork, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, mismatched plastic spork, no noise, studio quality",
    ),
    (
        "35_cheese_wheel_fingers",
        "Cinematic shot of guest eating half of a communal cheese wheel with their fingers, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, cheese wheel fingers, no noise, studio quality",
    ),
    (
        "36_crumbs_in_the_beard_",
        "Cinematic shot of man with a large beard full of breadcrumbs and sauce, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, crumbs in the beard man, no noise, studio quality",
    ),
    (
        "37_offensive_satire_jok",
        "Cinematic shot of guest telling a offensive joke and saying 'it's satire' when no one laughs, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, offensive satire joke, no noise, studio quality",
    ),
    (
        "38_staring_at_host_part",
        "Cinematic shot of guest looking a bit too intensely at the host's spouse, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, staring at host partner, no noise, studio quality",
    ),
    (
        "39_influencer_ring_ligh",
        "Cinematic shot of guest bringing a ring light to the dinner table, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, influencer ring light, no noise, studio quality",
    ),
    (
        "40_wrong_shrimp_fork_st",
        "Cinematic shot of guest using a tiny shrimp fork to eat a giant steak, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, wrong shrimp fork steak, no noise, studio quality",
    ),
    (
        "41_i_dont_believe_guest",
        "Cinematic shot of guest announcing they don't believe in gravity or germs, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, i dont believe guest, no noise, studio quality",
    ),
    (
        "42_emptying_whiskey_bot",
        "Cinematic shot of guest tipping a bottle upside down into their glass, eyes wide, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, emptying whiskey bottle, no noise, studio quality",
    ),
    (
        "43_accidental_touch_kne",
        "Cinematic shot of guest's hand lingering on another guest's knee under the table, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, accidental touch knee, no noise, studio quality",
    ),
    (
        "44_water_on_laptop_elec",
        "Cinematic shot of a pitcher of water falling onto the host's laptop on a side table, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, water on laptop electronics, no noise, studio quality",
    ),
    (
        "45_is_this_organic_quer",
        "Cinematic shot of guest looking suspiciously at a carrot with a magnifying glass, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, is this organic query, no noise, studio quality",
    ),
    (
        "46_talking_mouth_full_c",
        "Cinematic shot of guest spraying crumbs while shouting about their crypto portfolio, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, talking mouth full crumbs, no noise, studio quality",
    ),
    (
        "47_guest_tissues_on_ant",
        "Cinematic shot of a guest leaving a pile of used tissues on an antique side table, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, guest tissues on antique, no noise, studio quality",
    ),
    (
        "48_dishes_lie_exit",
        "Cinematic shot of guest looking at a mountain of dishes and then quietly leaving, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, dishes lie exit, no noise, studio quality",
    ),
    (
        "49_i_know_the_chef_lie",
        "Cinematic shot of guest claiming they taught the host how to make this dish, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, i know the chef lie, no noise, studio quality",
    ),
    (
        "50_it_is_a_bit_salty_fa",
        "Cinematic shot of guest making a face after the first bite, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, it is a bit salty face, no noise, studio quality",
    ),
    (
        "51_staying_over_hint_bl",
        "Cinematic shot of guest asking where the extra blankets are at 1 AM, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, staying over hint blankets, no noise, studio quality",
    ),
    (
        "52_forgot_wallet_fifth_",
        "Cinematic shot of guest who forgot their wallet for the 5th time, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, forgot wallet fifth time, no noise, studio quality",
    ),
    (
        "53_minimalist_single_pe",
        "Cinematic shot of serving a single pea on a massive white plate, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, minimalist single pea, no noise, studio quality",
    ),
    (
        "54_maximalist_table_clu",
        "Cinematic shot of a table so covered in decorations there's no room for plates, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, maximalist table clutter, no noise, studio quality",
    ),
    (
        "55_mixologist_vinegar_d",
        "Cinematic shot of guest making a 'custom cocktail' using the host's finest vinegar, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, mixologist vinegar drink, no noise, studio quality",
    ),
    (
        "56_photographer_candid_",
        "Cinematic shot of guest rearranging the host's entire living room for a 'candid' shot, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, photographer candid setup, no noise, studio quality",
    ),
    (
        "57_therapist_childhood_",
        "Cinematic shot of guest analyzing the host's childhood based on the choice of appetizer, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, therapist childhood anal, no noise, studio quality",
    ),
    (
        "58_lawyer_lease_invalid",
        "Cinematic shot of guest explaining why the host's lease is technically invalid, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, lawyer lease invalid, no noise, studio quality",
    ),
    (
        "59_doctor_rare_disease",
        "Cinematic shot of guest diagnosing everyone at the table with a rare tropical disease, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, doctor rare disease, no noise, studio quality",
    ),
    (
        "60_musician_guitar_wond",
        "Cinematic shot of guest picking up the host's decorative guitar and playing Wonderwall, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, musician guitar wonder, no noise, studio quality",
    ),
    (
        "61_comedian_borat_impre",
        "Cinematic shot of guest who won't stop doing a bad 'Borat' impression, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, comedian borat impression, no noise, studio quality",
    ),
    (
        "62_foodie_foraged_by_ha",
        "Cinematic shot of guest who refuses to eat anything that wasn't foraged by hand, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, foodie foraged by hand, no noise, studio quality",
    ),
    (
        "63_local_lost_soul_sinc",
        "Cinematic shot of guest complaining that the city has 'lost its soul' since 1994, dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, local lost soul since 94, no noise, studio quality",
    ),
    (
        "64_traveler_in_bali_sta",
        "Cinematic shot of guest who starts every sentence with 'When I was in Bali...' , dinner party setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, traveler in bali start, no noise, studio quality",
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
