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
PROJECT_NAME = "airport"
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
        "01_security_line",
        "Cinematic wide shot of an infinite, snaking security line in a sterile, grey airport terminal, exhausted travelers, harsh overhead lighting, 8k",
        "High fidelity crisp foley, security line chatter, no static",
    ),
    (
        "02_boot_struggle",
        "Close up of a frustrated man hopping on one foot, trying to remove a complex leather boot while holding a grey plastic security bin with his teeth, airport security background",
        "High fidelity crisp foley, boot leather squeak and plastic bin rattle",
    ),
    (
        "03_sad_sandwich",
        "Macro shot of a sad, wilted ham sandwich wrapped in crinkly plastic under a flickering yellow heat lamp in an airport cafe, $18 price tag visible",
        "High fidelity crisp foley, crinkly plastic wrap sounds",
    ),
    (
        "04_delayed_sign",
        "Close up of a digital airport gate sign flipping from 'ON TIME' to 'DELAYED: 6 HOURS', frustrated reflections in the screen",
        "High fidelity crisp foley, digital flip and announcement chime",
    ),
    (
        "05_gate_lice",
        "A crowd of travelers standing too close to the boarding gate, huddled together like a pack of wolves, looking intensely at the gate agent",
        "High fidelity crisp foley, shuffling feet and murmuring",
    ),
    (
        "06_tiny_seat",
        "Interior of an airplane, wide shot of a passenger squeezed into a tiny middle seat between two massive people, knees pushed against the seat in front",
        "High fidelity crisp foley, plastic creak and heavy breathing",
    ),
    (
        "07_crying_baby",
        "Extreme close up of a baby with its mouth wide open, crying, red-faced, sitting in an airplane seat, blurred passenger in foreground looking distressed",
        "High fidelity crisp foley, clear baby crying sound",
    ),
    (
        "08_seat_recline",
        "Close up of a laptop screen being crushed by the seat in front reclining abruptly, sparks and cracked plastic, airplane interior",
        "High fidelity crisp foley, sharp plastic crack",
    ),
    (
        "09_turbulence",
        "Close up of a small plastic cup of tomato juice on a tray table vibrating violently, red liquid splashing out during turbulence",
        "High fidelity crisp foley, rattling tray and liquid slosh",
    ),
    (
        "10_lost_suitcase",
        "Wide shot of a single, battered, lonely suitcase circling an empty baggage carousel in a dimly lit, deserted airport hall at night",
        "High fidelity crisp foley, mechanical carousel motor",
    ),
    (
        "11_title_card",
        "Cinematic title card: 'AIRPORT HELL' in bold, distressed metallic font, airport runway lights in the background, bokeh effect",
        "High fidelity crisp foley, cinematic orchestral hit",
    ),
    (
        "12_forgotten_passport",
        "Close up of a hand slapping a forehead in realization, through a plane window as it pulls away from the gate, a blue passport visible left behind on a seat",
        "High fidelity crisp foley, muffled voice gasp and jet whine",
    ),
    (
        "13_tsa_random_search",
        "Cinematic shot of gloved hands patting down a confused elderly woman in a wheelchair, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, tsa random search, no noise, studio quality",
    ),
    (
        "14_the_liquid_baggie_le",
        "Cinematic shot of sticky shampoo covering everything in a clear plastic bag, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, the liquid baggie leak, no noise, studio quality",
    ),
    (
        "15_one_working_outlet_f",
        "Cinematic shot of three people huddled around a single wall outlet, looking suspicious of each other, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, one working outlet fight, no noise, studio quality",
    ),
    (
        "16_loud_speakerphone_ta",
        "Cinematic shot of man shouting into a phone held like a piece of toast in a quiet gate area, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, loud speakerphone talker, no noise, studio quality",
    ),
    (
        "17_slow_walkers_in_grou",
        "Cinematic shot of a family of six walking abreast slowly down a narrow concourse, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, slow walkers in groups, no noise, studio quality",
    ),
    (
        "18_middle_seat_armrest_",
        "Cinematic shot of two elbows fighting for an inch of space on a shared armrest, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, middle seat armrest war, no noise, studio quality",
    ),
    (
        "19_4_am_terminal_sleep",
        "Cinematic shot of person curled in a fetal position across three metal chairs with armrests, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, 4 am terminal sleep, no noise, studio quality",
    ),
    (
        "20_wrong_side_of_gate_w",
        "Cinematic shot of exhausted person realizing they walked to Gate A1 instead of Gate F99, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, wrong side of gate walk, no noise, studio quality",
    ),
    (
        "21_car_rental_shuttle_w",
        "Cinematic shot of crowd of people staring hopelessly into the distance for a bus that never comes, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, car rental shuttle wait, no noise, studio quality",
    ),
    (
        "22_duty-free_perfume_cl",
        "Cinematic shot of person walking through a visible mist of perfume sprayed by an overzealous clerk, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, duty-free perfume cloud, no noise, studio quality",
    ),
    (
        "23_gate_yoga",
        "Cinematic shot of person doing a full downward dog in a crowded boarding area, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, gate yoga, no noise, studio quality",
    ),
    (
        "24_moving_walkway_block",
        "Cinematic shot of two people standing still on the left side of a moving walkway, ignoring the 'walk left' sign, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, moving walkway blocker, no noise, studio quality",
    ),
    (
        "25_tiny_bathroom_sink",
        "Cinematic shot of hands barely fitting under a faucet that only stays on for 0.5 seconds, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, tiny bathroom sink, no noise, studio quality",
    ),
    (
        "26_impossible_toilet_pa",
        "Cinematic shot of hand clawing at a toilet paper dispenser that only gives 1-inch squares, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, impossible toilet paper, no noise, studio quality",
    ),
    (
        "27_de-icing_delay",
        "Cinematic shot of thick grey fluid being sprayed onto a plane wing through a window blurred with ice, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, de-icing delay, no noise, studio quality",
    ),
    (
        "28_standing_after_landi",
        "Cinematic shot of a row of people hunched over under the overhead bins while the plane is still taxiing, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, standing after landing, no noise, studio quality",
    ),
    (
        "29_overhead_bin_hog",
        "Cinematic shot of person putting a tiny jacket and a large shopping bag in the bin sideways, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, overhead bin hog, no noise, studio quality",
    ),
    (
        "30_bag_sizer_struggle",
        "Cinematic shot of man sweating while jumping on a suitcase to try and fit it into a metal frame, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, bag sizer struggle, no noise, studio quality",
    ),
    (
        "31_uber_pickup_chaos",
        "Cinematic shot of hundreds of people staring at phones while cars honk and double-park in the rain, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, uber pickup chaos, no noise, studio quality",
    ),
    (
        "32_smelly_tuna_sandwich",
        "Cinematic shot of passenger opening a pungent foil-wrapped sandwich in a pressurized cabin, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, smelly tuna sandwich, no noise, studio quality",
    ),
    (
        "33_neighbor_life_story",
        "Cinematic shot of trapped passenger nodding politely while neighbor shows 500 photos of their cat, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, neighbor life story, no noise, studio quality",
    ),
    (
        "34_broken_screen_error",
        "Cinematic shot of an airplane seatback screen showing only static and a red 'ERROR' message, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, broken screen error, no noise, studio quality",
    ),
    (
        "35_scratchy_blanket_lin",
        "Cinematic shot of close up of a paper-thin blue blanket that looks like it's made of dryer lint, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, scratchy blanket lint, no noise, studio quality",
    ),
    (
        "36_call_button_ping_ign",
        "Cinematic shot of close up of a lit-up attendant call button while a flight attendant walks right past, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, call button ping ignore, no noise, studio quality",
    ),
    (
        "37_lost_keys_in_dark_ga",
        "Cinematic shot of man emptying his entire backpack onto the floor of a dark parking garage, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, lost keys in dark garage, no noise, studio quality",
    ),
    (
        "38_liquid_restrictions_",
        "Cinematic shot of TSA officer throwing a 10.1oz bottle of expensive hot sauce into a trash can, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, liquid restrictions trash, no noise, studio quality",
    ),
    (
        "39_bare_feet_on_armrest",
        "Cinematic shot of a pair of bare feet resting on the armrest of the person in front, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, bare feet on armrest, no noise, studio quality",
    ),
    (
        "40_tray_table_hair_crum",
        "Cinematic shot of close up of a tray table covered in hair and unidentified crumbs from a previous flight, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, tray table hair crumbs, no noise, studio quality",
    ),
    (
        "41_no_snacks_water_only",
        "Cinematic shot of flight attendant handing a passenger a single cup of water and an apologetic look, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, no snacks water only, no noise, studio quality",
    ),
    (
        "42_window_shade_war_han",
        "Cinematic shot of one hand reaching to open a window shade while another hand immediately closes it, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, window shade war hand, no noise, studio quality",
    ),
    (
        "43_customs_line_maze",
        "Cinematic shot of endless maze of tens of thousands of people in a windowless room with no AC, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, customs line maze, no noise, studio quality",
    ),
    (
        "44_charging_cord_short",
        "Cinematic shot of person sitting on the floor leaning against a trash can to reach a plug, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, charging cord short, no noise, studio quality",
    ),
    (
        "45_lost_connection_spri",
        "Cinematic shot of man running through a terminal with a look of pure desperation, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, lost connection sprint, no noise, studio quality",
    ),
    (
        "46_vending_machine_thef",
        "Cinematic shot of a bag of chips hanging precariously by a hook in an airport vending machine, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, vending machine theft, no noise, studio quality",
    ),
    (
        "47_emotional_support_bi",
        "Cinematic shot of a large bird sitting on a suitcase in a crowded terminal, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, emotional support bird, no noise, studio quality",
    ),
    (
        "48_wet_floor_slip",
        "Cinematic shot of person slipping on a freshly mopped floor next to a tiny yellow sign, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, wet floor slip, no noise, studio quality",
    ),
    (
        "49_automatic_door_trap_",
        "Cinematic shot of automatic sliding doors closing on a person with five bags, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, automatic door trap bag, no noise, studio quality",
    ),
    (
        "50_baggage_carousel_jam",
        "Cinematic shot of suitcases piling up in a mountain at the mouth of the carousel, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, baggage carousel jam pile, no noise, studio quality",
    ),
    (
        "51_the_fifteen_dollar_b",
        "Cinematic shot of a small plastic cup of lukewarm beer next to a receipt, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, the fifteen dollar beer, no noise, studio quality",
    ),
    (
        "52_pilot_at_the_bar_sta",
        "Cinematic shot of a man in a pilot uniform staring intensely into a martini (actually water), airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, pilot at the bar stare, no noise, studio quality",
    ),
    (
        "53_flight_path_loop_scr",
        "Cinematic shot of screen showing the plane circling the airport for the 10th time, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, flight path loop screen, no noise, studio quality",
    ),
    (
        "54_cup_full_of_ice",
        "Cinematic shot of a cup that is 99% ice and 1% soda, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, cup full of ice, no noise, studio quality",
    ),
    (
        "55_priority_tag_last_ba",
        "Cinematic shot of a 'Priority' tag on a suitcase that is the last one to come off the belt, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, priority tag last bag, no noise, studio quality",
    ),
    (
        "56_hotel_voucher_sadnes",
        "Cinematic shot of a sad piece of paper for a 'Discounted Rate' at a 1-star hotel, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, hotel voucher sadness, no noise, studio quality",
    ),
    (
        "57_middle_of_night_page",
        "Cinematic shot of empty terminal with a loud voice shouting names over the speakers, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, middle of night page, no noise, studio quality",
    ),
    (
        "58_upgrade_tease_denial",
        "Cinematic shot of gate agent looking at a screen, then telling a hopeful passenger 'no' , airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, upgrade tease denial, no noise, studio quality",
    ),
    (
        "59_armrest_elbow_theft",
        "Cinematic shot of neighbor's elbow slowly creeping into the passenger's side, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, armrest elbow theft, no noise, studio quality",
    ),
    (
        "60_snoring_neighbor_mou",
        "Cinematic shot of man with his head back, mouth open, snoring loudly next to a passenger, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, snoring neighbor mouth, no noise, studio quality",
    ),
    (
        "61_child_kicking_seat_b",
        "Cinematic shot of the back of a seat vibrating from rhythmic kicks, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, child kicking seat back, no noise, studio quality",
    ),
    (
        "62_plastic_wrap_luggage",
        "Cinematic shot of a suitcase completely encased in 50 layers of green plastic wrap, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, plastic wrap luggage redundant, no noise, studio quality",
    ),
    (
        "63_last_minute_gate_cha",
        "Cinematic shot of crowd of people suddenly turning around and sprinting the other way, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, last minute gate change, no noise, studio quality",
    ),
    (
        "64_all_natural_snack_bi",
        "Cinematic shot of a bag of birdseed-like trail mix that costs $12, airport setting, 8k, detailed, dramatic lighting",
        "High fidelity crisp foley, all natural snack birdseed, no noise, studio quality",
    ),
]

VO_SCRIPT = """
In a world where time stands still.
And dignity comes to die.
Welcome to the terminal.
Where a sandwich costs more than your soul.
And your gate is always further than you think.
The battle for Group 9 begins now.
Brace for impact.
Because the person in 14B is already reclining.
And the infant in 15C has a lot to say.
Buckle up.
Because you're never leaving.
Airport Hell.
Coming to a terminal near you.
Random searches.
Leaking baggies.
One outlet to rule them all.
Speakerphone shouters.
The slow-walking wall.
Armrest wars.
Cold metal chair sleep.
Gate F99 is a marathon.
Shuttle bus to nowhere.
Perfume clouds.
Downward dog at Gate 4.
Stay right, walk left.
Faucet drip.
Single ply paper.
Ice wing spray.
Standing in the aisle.
Overhead bin hogs.
Bag sizer struggle.
Uber lane chaos.
Tuna sandwich air.
Cat photo show.
Static screen.
Lint blanket.
Ignored call button.
Garage key hunt.
Hot sauce in the bin.
Feet on the seat.
Crumby table.
Water only.
Shade wars.
Customs maze.
Charging on the floor.
The missed connection.
Vending machine theft.
Support bird.
Wet floor slide.
Door trap.
Bag mountain.
Fifteen dollar beer.
Pilot at the bar.
Orbiting the city.
Cup of ice.
Priority last.
Hotel voucher.
Empty terminal.
Upgrade denied.
Elbow creep.
Snore fest.
Seat kick.
Plastic wrap.
Gate change sprint.
"""

def generate_images(args):
    model_id = args.model or DEFAULT_MODEL
    steps = args.steps or DEFAULT_STEPS
    guidance = args.guidance if args.guidance is not None else DEFAULT_GUIDANCE

    print(f"--- Generating {len(SCENES)} Images with {model_id} ---")
    
    pipe = DiffusionPipeline.from_pretrained(
        model_id, 
        torch_dtype=torch.bfloat16 if DEVICE in ["cuda", "mps"] else torch.float32
    )
    
    if DEVICE == "cuda" or DEVICE == "mps":
        pipe.enable_model_cpu_offload()

    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)
    for s_id, prompt, _ in SCENES:
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        if not os.path.exists(out_path):
            print(f"Generating: {s_id}")
            image = pipe(
                prompt=prompt,
                num_inference_steps=steps,
                guidance_scale=guidance,
                width=1280,
                height=720,
            ).images[0]
            image.save(out_path)
    del pipe
    gc.collect()

def generate_sfx(args):
    print(f"--- Generating SFX with Stable Audio Open ---")
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", 
            torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
        ).to(DEVICE)
    except Exception as e:
        print(f"Could not load Stable Audio: {e}. Skipping SFX.")
        return

    os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)
    for s_id, _, sfx_prompt in SCENES:
        out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
        if not os.path.exists(out_path):
            print(f"Generating SFX for: {s_id}")
            audio = pipe(
                sfx_prompt, num_inference_steps=100, audio_end_in_s=10.0
            ).audios[0]
            audio_np = audio.T.cpu().numpy()
            wavfile.write(out_path, 44100, (audio_np * 32767).astype(np.int16))
    del pipe
    gc.collect()

def generate_voiceover(args):
    print("--- Generating Voiceover with F5-TTS ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    if os.path.exists(out_path_full):
        return

    lines = [l.strip() for l in VO_SCRIPT.split("\n") if l.strip()]
    temp_dir = f"{ASSETS_DIR}/voice/f5_temp"
    os.makedirs(temp_dir, exist_ok=True)

    full_audio_data = []
    sampling_rate = 44100

    for i, line in enumerate(lines):
        line_filename = f"vo_{i:03d}.wav"
        line_out_path = f"{ASSETS_DIR}/voice/{line_filename}"

        if os.path.exists(line_out_path):
            print(f"  Skipping existing line {i}")
            sr, data = wavfile.read(line_out_path)
            full_audio_data.append(data)
            sampling_rate = sr
            continue

        print(f"  Generating line {i}: {line[:30]}...")
        # Using the CLI tool if available, otherwise this will fall back or error gracefully
        cmd = [
            "f5-tts_infer-cli",
            "--gen_text", line,
            "--output_dir", temp_dir,
        ]
        
        try:
            # Clear temp
            for f in os.listdir(temp_dir): os.remove(os.path.join(temp_dir, f))
            subprocess.run(cmd, check=True)
            
            generated_wav = None
            for file in os.listdir(temp_dir):
                if file.endswith(".wav"):
                    generated_wav = os.path.join(temp_dir, file)
                    break

            if generated_wav:
                os.replace(generated_wav, line_out_path)
                sr, data = wavfile.read(line_out_path)
                full_audio_data.append(data)
                sampling_rate = sr
                # Add silence between lines
                silence = np.zeros(int(sr * 0.6), dtype=data.dtype)
                full_audio_data.append(silence)
        except Exception as e:
            print(f"  Line {i} failed: {e}. Ensure f5-tts is installed.")

    if full_audio_data:
        combined = np.concatenate(full_audio_data)
        wavfile.write(out_path_full, sampling_rate, combined)

def generate_music(args):
    print(f"--- Generating High Quality Music with Stable Audio Open ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    out_path = f"{ASSETS_DIR}/music/airport_theme.wav"
    if os.path.exists(out_path):
        return

    try:
        # Stable Audio Open 1.0 is the largest/highest quality open music model here
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", 
            torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
        ).to(DEVICE)
        
        # High quality prompt for the requested genre
        prompt = "Cinematic movie trailer music, intense building orchestral tension, deep brass hits, comedic bassoon accents, 44.1kHz, high fidelity, professional master"
        
        print("  Generating 45s music track...")
        # Generate in chunks if needed, but Stable Audio Open does ~47s
        audio = pipe(prompt, num_inference_steps=200, audio_end_in_s=45.0).audios[0]
        wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
    except Exception as e:
        print(f"Music generation failed: {e}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate Airport Assets")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    args = parser.parse_args()

    generate_images(args)
    generate_sfx(args)
    generate_voiceover(args)
    generate_music(args)
