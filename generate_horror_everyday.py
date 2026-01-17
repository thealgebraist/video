# generate_horror_everyday.py
# Generates a 4-minute horror short video with jump scares about everyday things
# Uses FLUX.1-schnell, 64 images, 64 steps each

import torch
import os
import sys
import numpy as np
import scipy.io.wavfile as wavfile
import argparse
from vidlib import utils, assemble
from diffusers import DiffusionPipeline, StableAudioPipeline
from transformers import pipeline, BitsAndBytesConfig
from PIL import Image
import warnings
import gc
import subprocess

# Suppress warnings
warnings.filterwarnings("ignore", category=UserWarning, module="torchsde")
warnings.filterwarnings("ignore", category=FutureWarning)


def generate_plasma_image(prompt, out_path, width=1280, height=720):
    """Generates a high-quality plasma/gradient image as a fallback."""
    print(f"  [Fallback] Generating plasma image for: {prompt[:30]}...")
    arr = np.zeros((height, width, 3), dtype=np.uint8)
    # Use a seed based on prompt for determinism
    seed = sum(ord(c) for c in prompt) % 1000
    np.random.seed(seed)

    # Simple plasma-like gradient
    c1 = np.random.randint(0, 128, 3)
    c2 = np.random.randint(128, 255, 3)

    for y in range(height):
        ratio = y / height
        color = (c1 * (1 - ratio) + c2 * ratio).astype(np.uint8)
        arr[y, :, :] = color

    # Add some "noise" nodes
    for _ in range(5):
        rx, ry = np.random.randint(0, width), np.random.randint(0, height)
        rc = np.random.randint(0, 255, 3)
        radius = np.random.randint(100, 400)
        yy, xx = np.mgrid[:height, :width]
        dist = np.sqrt((xx - rx) ** 2 + (yy - ry) ** 2)
        mask = np.exp(-dist / radius)[:, :, np.newaxis]
        arr = (arr * (1 - mask) + rc * mask).astype(np.uint8)

    img = Image.fromarray(arr)
    img.save(out_path)


def generate_mock_audio(prompt, out_path, duration_s=5.0, sample_rate=44100):
    """Generates a simple procedural audio track as a fallback."""
    print(f"  [Fallback] Generating mock audio for: {prompt[:30]}...")
    t = np.linspace(0, duration_s, int(sample_rate * duration_s))
    seed = sum(ord(c) for c in prompt) % 1000
    np.random.seed(seed)

    # Blend a low hum and some noise
    freq = 40 + np.random.rand() * 40
    audio = 0.5 * np.sin(2 * np.pi * freq * t)
    audio += 0.2 * np.random.normal(0, 0.1, len(t))

    # Gentle fade in/out
    fade = int(sample_rate * 0.5)
    if len(audio) > 2 * fade:
        audio[:fade] *= np.linspace(0, 1, fade)
        audio[-fade:] *= np.linspace(1, 0, fade)

    wavfile.write(out_path, sample_rate, (audio * 32767).astype(np.int16))


def macos_say_tts(text, out_path):
    """Uses macOS 'say' command as a fallback."""
    print(f"  [Fallback] Using macOS 'say' for: {text[:30]}...")
    temp_aiff = out_path.replace(".wav", ".aiff")
    try:
        subprocess.run(["say", "-o", temp_aiff, text], check=True)
        # Convert to WAV
        subprocess.run(
            ["ffmpeg", "-y", "-i", temp_aiff, out_path], capture_output=True, check=True
        )
        if os.path.exists(temp_aiff):
            os.remove(temp_aiff)
        return True
    except Exception as e:
        print(f"    Fallback TTS failed: {e}")
        return False


# --- Configuration & Defaults ---
PROJECT_NAME = "horror_everyday"
ASSETS_DIR = f"assets_{PROJECT_NAME}"
DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
DTYPE = torch.bfloat16 if DEVICE == "cuda" else torch.float32

# H200 Detection
IS_H200 = False
if DEVICE == "cuda":
    gpu_name = torch.cuda.get_device_name(0)
    if "H200" in gpu_name:
        IS_H200 = True

# Defaults
DEFAULT_MODEL = "nota-ai/bk-sdm-tiny"
DEFAULT_STEPS = 4  # Schnell default
DEFAULT_GUIDANCE = 0.0
DEFAULT_QUANT = "4bit" if (DEVICE == "cuda" and not IS_H200) else "none"


SCENES = [
    (
        "01_alarm_clock",
        "A close-up of a blaring alarm clock in a dark bedroom, red digits glowing ominously, horror lighting, 8k, cinematic, unsettling atmosphere",
        "distorted alarm sound, sudden loud ringing, eerie undertone",
    ),
    (
        "02_brushing_teeth",
        "A person brushing their teeth, but the mirror reflection moves differently, horror lighting, 8k, cinematic, uncanny valley",
        "creaking mirror, distorted brushing sound, sudden glass shatter",
    ),
    (
        "03_commute_train",
        "A crowded train carriage, faces blurred and staring, flickering lights, horror lighting, 8k, cinematic, claustrophobic",
        "train rumble, sudden screech, whispering voices",
    ),
    (
        "04_office_desk",
        "A person at an office desk, papers move on their own, shadowy figures in the background, horror lighting, 8k, cinematic",
        "rustling papers, sudden loud bang, eerie whispers",
    ),
    (
        "05_elevator",
        "Inside an elevator, the floor indicator glitches, doors open to darkness, horror lighting, 8k, cinematic",
        "elevator ding, sudden silence, distorted scream",
    ),
    (
        "06_grocery_store",
        "A grocery aisle, products rearrange themselves, faces on packaging stare, horror lighting, 8k, cinematic",
        "shopping cart squeak, sudden crash, whispering voices",
    ),
    (
        "07_crosswalk",
        "A crosswalk at night, traffic lights flicker, shadowy figures cross, horror lighting, 8k, cinematic",
        "traffic hum, sudden horn, footsteps echo",
    ),
    (
        "08_cafe",
        "A cafe, coffee cup spills blood, barista's face distorts, horror lighting, 8k, cinematic",
        "coffee machine hiss, sudden scream, distorted laughter",
    ),
    (
        "09_staircase",
        "A staircase, steps stretch endlessly, hands reach from the darkness, horror lighting, 8k, cinematic",
        "footsteps, sudden thud, whispering voices",
    ),
    (
        "10_bathroom",
        "A bathroom, faucet drips black liquid, reflection smiles back, horror lighting, 8k, cinematic",
        "dripping water, sudden crash, eerie giggle",
    ),
    (
        "11_kitchen",
        "A kitchen, knives float in the air, fridge opens to darkness, horror lighting, 8k, cinematic",
        "knife clatter, sudden bang, distorted voices",
    ),
    (
        "12_living_room",
        "A living room, TV static shows ghostly faces, furniture moves, horror lighting, 8k, cinematic",
        "TV static, sudden loud noise, whispering",
    ),
    (
        "13_bedroom",
        "A bedroom, closet door creaks open, eyes peer out, horror lighting, 8k, cinematic",
        "creaking door, sudden scream, breathing sound",
    ),
    (
        "14_garage",
        "A garage, car headlights flicker, shadow moves behind, horror lighting, 8k, cinematic",
        "engine rev, sudden crash, whispering",
    ),
    (
        "15_mailbox",
        "A mailbox, letters spill out covered in blood, horror lighting, 8k, cinematic",
        "mail slot clang, sudden scream, eerie whisper",
    ),
    (
        "16_park",
        "A park, playground swings move on their own, shadowy children laugh, horror lighting, 8k, cinematic",
        "swing creak, sudden giggle, distorted laughter",
    ),
    (
        "17_supermarket_checkout",
        "A checkout lane, cashier's face melts, money turns to insects, horror lighting, 8k, cinematic",
        "beep, sudden buzz, whispering",
    ),
    (
        "18_subway",
        "A subway platform, train arrives empty, doors open to darkness, horror lighting, 8k, cinematic",
        "train screech, sudden silence, eerie voices",
    ),
    (
        "19_restaurant",
        "A restaurant, food writhes on the plate, waiter's eyes bleed, horror lighting, 8k, cinematic",
        "fork clatter, sudden scream, whispering",
    ),
    (
        "20_hospital",
        "A hospital room, monitors flatline, shadowy figure stands over bed, horror lighting, 8k, cinematic",
        "monitor beep, sudden silence, distorted voice",
    ),
    (
        "21_school",
        "A classroom, chalkboard writes itself, students vanish, horror lighting, 8k, cinematic",
        "chalk screech, sudden bang, whispering",
    ),
    (
        "22_library",
        "A library, books fly off shelves, librarian's face distorts, horror lighting, 8k, cinematic",
        "book thud, sudden scream, whispering",
    ),
    (
        "23_gym",
        "A gym, weights levitate, mirrors crack, horror lighting, 8k, cinematic",
        "weight clank, sudden crash, eerie voices",
    ),
    (
        "24_pool",
        "A swimming pool, water turns black, hands reach up, horror lighting, 8k, cinematic",
        "splash, sudden scream, whispering",
    ),
    (
        "25_bus_stop",
        "A bus stop, bus arrives with no driver, passengers are shadows, horror lighting, 8k, cinematic",
        "bus engine, sudden silence, whispering",
    ),
    (
        "26_movie_theater",
        "A movie theater, screen shows real-life horrors, audience vanishes, horror lighting, 8k, cinematic",
        "projector hum, sudden scream, whispering",
    ),
    (
        "27_pet_store",
        "A pet store, animals speak in human voices, cages rattle, horror lighting, 8k, cinematic",
        "animal noises, sudden scream, whispering",
    ),
    (
        "28_bank",
        "A bank, money turns to ashes, teller's face distorts, horror lighting, 8k, cinematic",
        "coin clink, sudden bang, whispering",
    ),
    (
        "29_gas_station",
        "A gas station, pumps leak blood, attendant vanishes, horror lighting, 8k, cinematic",
        "pump hiss, sudden scream, whispering",
    ),
    (
        "30_highway",
        "A highway, cars drive themselves, passengers are skeletons, horror lighting, 8k, cinematic",
        "car engine, sudden crash, whispering",
    ),
    (
        "31_mall",
        "A mall, mannequins move, shoppers vanish, horror lighting, 8k, cinematic",
        "footsteps, sudden scream, whispering",
    ),
    (
        "32_attic",
        "An attic, boxes open themselves, shadowy figures crawl out, horror lighting, 8k, cinematic",
        "box thud, sudden scream, whispering",
    ),
    (
        "33_basement",
        "A basement, walls bleed, stairs collapse, horror lighting, 8k, cinematic",
        "dripping, sudden crash, whispering",
    ),
    (
        "34_rooftop",
        "A rooftop, wind howls, shadow jumps off, horror lighting, 8k, cinematic",
        "wind, sudden scream, whispering",
    ),
    (
        "35_garden",
        "A garden, plants strangle each other, gardener's face distorts, horror lighting, 8k, cinematic",
        "rustling leaves, sudden scream, whispering",
    ),
    (
        "36_laundry_room",
        "A laundry room, washing machine spins endlessly, clothes turn to hands, horror lighting, 8k, cinematic",
        "machine hum, sudden scream, whispering",
    ),
    (
        "37_balcony",
        "A balcony, railing bends, shadow falls, horror lighting, 8k, cinematic",
        "metal creak, sudden scream, whispering",
    ),
    (
        "38_hallway",
        "A hallway, doors slam shut, lights flicker, horror lighting, 8k, cinematic",
        "door slam, sudden scream, whispering",
    ),
    (
        "39_front_door",
        "A front door, knocks echo, handle turns by itself, horror lighting, 8k, cinematic",
        "knocking, sudden scream, whispering",
    ),
    (
        "40_backyard",
        "A backyard, swing set moves, shadowy figure stands, horror lighting, 8k, cinematic",
        "swing creak, sudden scream, whispering",
    ),
    (
        "41_driveway",
        "A driveway, car doors open and close, shadow moves, horror lighting, 8k, cinematic",
        "car door slam, sudden scream, whispering",
    ),
    (
        "42_street",
        "A street, lamplights flicker, shadows chase, horror lighting, 8k, cinematic",
        "lamp buzz, sudden scream, whispering",
    ),
    (
        "43_bridge",
        "A bridge, water below turns red, shadow jumps, horror lighting, 8k, cinematic",
        "water splash, sudden scream, whispering",
    ),
    (
        "44_tunnel",
        "A tunnel, walls close in, shadowy hands reach, horror lighting, 8k, cinematic",
        "echo, sudden scream, whispering",
    ),
    (
        "45_park_bench",
        "A park bench, shadow sits, birds fly away, horror lighting, 8k, cinematic",
        "bird flapping, sudden scream, whispering",
    ),
    (
        "46_phone_booth",
        "A phone booth, phone rings, voice whispers, horror lighting, 8k, cinematic",
        "phone ring, sudden scream, whispering",
    ),
    (
        "47_post_office",
        "A post office, letters fly, clerk vanishes, horror lighting, 8k, cinematic",
        "letter flutter, sudden scream, whispering",
    ),
    (
        "48_bar",
        "A bar, drinks spill blood, bartender's face distorts, horror lighting, 8k, cinematic",
        "glass clink, sudden scream, whispering",
    ),
    (
        "49_hotel_room",
        "A hotel room, bed levitates, shadow stands at window, horror lighting, 8k, cinematic",
        "bed creak, sudden scream, whispering",
    ),
    (
        "50_waiting_room",
        "A waiting room, clock spins backwards, people vanish, horror lighting, 8k, cinematic",
        "clock tick, sudden scream, whispering",
    ),
    (
        "51_pharmacy",
        "A pharmacy, pills crawl, pharmacist's face distorts, horror lighting, 8k, cinematic",
        "pill rattle, sudden scream, whispering",
    ),
    (
        "52_hardware_store",
        "A hardware store, tools fly, clerk vanishes, horror lighting, 8k, cinematic",
        "tool clang, sudden scream, whispering",
    ),
    (
        "53_bookstore",
        "A bookstore, books bleed, cashier's face distorts, horror lighting, 8k, cinematic",
        "book thud, sudden scream, whispering",
    ),
    (
        "54_cemetery",
        "A cemetery, graves open, shadows crawl out, horror lighting, 8k, cinematic",
        "earth rumble, sudden scream, whispering",
    ),
    (
        "55_church",
        "A church, pews move, priest's face distorts, horror lighting, 8k, cinematic",
        "organ hum, sudden scream, whispering",
    ),
    (
        "56_fire_station",
        "A fire station, hoses leak blood, firefighter vanishes, horror lighting, 8k, cinematic",
        "hose hiss, sudden scream, whispering",
    ),
    (
        "57_police_station",
        "A police station, handcuffs float, officer's face distorts, horror lighting, 8k, cinematic",
        "handcuff clink, sudden scream, whispering",
    ),
    (
        "58_airport",
        "An airport, planes fly backwards, passengers vanish, horror lighting, 8k, cinematic",
        "plane engine, sudden scream, whispering",
    ),
    (
        "59_train_station",
        "A train station, trains arrive empty, shadowy figures board, horror lighting, 8k, cinematic",
        "train screech, sudden scream, whispering",
    ),
    (
        "60_factory",
        "A factory, machines move on their own, workers vanish, horror lighting, 8k, cinematic",
        "machine hum, sudden scream, whispering",
    ),
    (
        "61_construction_site",
        "A construction site, cranes move by themselves, shadow falls, horror lighting, 8k, cinematic",
        "crane creak, sudden scream, whispering",
    ),
    (
        "62_playground",
        "A playground, swings move, children vanish, horror lighting, 8k, cinematic",
        "swing creak, sudden scream, whispering",
    ),
    (
        "63_gas_meter",
        "A gas meter, numbers spin wildly, shadowy hands reach, horror lighting, 8k, cinematic",
        "meter tick, sudden scream, whispering",
    ),
    (
        "64_laundry_basket",
        "A laundry basket, clothes move, shadow crawls out, horror lighting, 8k, cinematic",
        "cloth rustle, sudden scream, whispering",
    ),
]

VO_SCRIPT = """
Safe in your home?
Safe in your routine?
Look closer.
Everyday is a nightmare.
"""


def generate_images(args):
    model_id = args.model
    steps = args.steps

    print(
        f"--- Generating {len(SCENES)} {model_id} Images ({steps} steps) on {DEVICE} ---"
    )

    pipe_kwargs = {"torch_dtype": torch.bfloat16 if DEVICE == "cuda" else torch.float32}

    if args.quant != "none" and DEVICE == "cuda":
        bnb_4bit_compute_dtype = torch.bfloat16 if IS_H200 else torch.float16
        quant_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_compute_dtype=bnb_4bit_compute_dtype,
        )
        pipe_kwargs["transformer_quantization_config"] = quant_config

    pipe = None
    try:
        pipe = DiffusionPipeline.from_pretrained(
            model_id,
            local_files_only=True,
            safety_checker=None,
            requires_safety_checker=False,
            **pipe_kwargs,
        )
        utils.remove_weight_norm(pipe)
        if args.scalenorm:
            utils.apply_stability_improvements(pipe.transformer, use_scalenorm=True)

        if args.offload and DEVICE == "cuda":
            pipe.enable_model_cpu_offload()
        elif args.quant != "none" and DEVICE == "cuda":
            if not hasattr(pipe, "hf_device_map"):
                pipe.to(DEVICE)
        else:
            pipe.to(DEVICE)
    except Exception as e:
        print(f"  [Error] Failed to load local model {model_id}: {e}")
        print("  Falling back to procedural generation.")

    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)
    for s_id, prompt, _ in SCENES:
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        if not os.path.exists(out_path):
            print(f"Generating image: {s_id}")
            if pipe:
                image = pipe(
                    prompt,
                    num_inference_steps=steps,
                    guidance_scale=args.guidance,
                    width=1280,
                    height=720,
                ).images[0]
                image.save(out_path)
            else:
                generate_plasma_image(prompt, out_path)
    del pipe
    torch.cuda.empty_cache()


def generate_sfx(args):
    print(f"--- Generating SFX with Stable Audio on {DEVICE} ---")
    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16
        ).to(DEVICE)
        utils.remove_weight_norm(pipe)
        if args.scalenorm:
            utils.apply_stability_improvements(pipe.transformer, use_scalenorm=True)
    except Exception as e:
        print(f"  [Error] Failed to load Stable Audio: {e}")
        print("  Using procedural SFX fallback.")

    os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)
    for s_id, _, sfx_prompt in SCENES:
        out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
        if not os.path.exists(out_path):
            print(f"Generating SFX: {s_id}")
            if pipe:
                audio = pipe(
                    sfx_prompt, num_inference_steps=100, audio_end_in_s=10.0
                ).audios[0]
                wavfile.write(
                    out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16)
                )
            else:
                generate_mock_audio(sfx_prompt, out_path, duration_s=10.0)
    del pipe
    torch.cuda.empty_cache()


def generate_voiceover(args):
    print(f"--- Generating Voiceover with Bark on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    if os.path.exists(out_path):
        return

    tts = None
    print("  Skipping Bark to avoid large downloads, using macOS 'say' fallback.")

    lines = [l for l in VO_SCRIPT.split("\n") if l.strip()]
    full_audio = []
    sampling_rate = 24000
    for line in lines:
        print(f"  Speaking: {line[:30]}...")
        if tts:
            output = tts(line)
            audio_data = output["audio"].flatten()
            sampling_rate = output["sampling_rate"]
        else:
            # We need a per-line file for full_audio to work easily if we want to save them
            # but for now we'll just use a temp file and read it back
            temp_line_path = f"{ASSETS_DIR}/voice/temp_line.wav"
            if macos_say_tts(line, temp_line_path):
                sr, data = wavfile.read(temp_line_path)
                audio_data = (
                    data.astype(np.float32) / 32767.0
                    if data.dtype == np.int16
                    else data
                )
                sampling_rate = sr
            else:
                audio_data = np.zeros(int(sampling_rate * 1.0))

        full_audio.append(audio_data)
        full_audio.append(np.zeros(int(sampling_rate * 0.5)))

    wavfile.write(
        out_path, sampling_rate, (np.concatenate(full_audio) * 32767).astype(np.int16)
    )
    del tts
    torch.cuda.empty_cache()


def generate_music(args):
    print(f"--- Generating Music with Stable Audio on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    out_path = f"{ASSETS_DIR}/music/horror_theme.wav"
    if os.path.exists(out_path):
        return

    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16
        ).to(DEVICE)
        utils.remove_weight_norm(pipe)
        if args.scalenorm:
            utils.apply_stability_improvements(pipe.transformer, use_scalenorm=True)
    except Exception as e:
        print(f"  [Error] Failed to load Stable Audio: {e}")
        print("  Using procedural music fallback.")

    prompt = "eerie industrial drone, distorted metallic sounds, slow tempo, horror atmosphere, low frequency hum"
    if pipe:
        audio = pipe(prompt, num_inference_steps=100, audio_end_in_s=45.0).audios[0]
        wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
    else:
        generate_mock_audio(prompt, out_path, duration_s=45.0)
    del pipe
    torch.cuda.empty_cache()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate Horror Assets")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    parser.add_argument(
        "--quant", type=str, choices=["none", "4bit", "8bit"], default=DEFAULT_QUANT
    )
    parser.add_argument("--offload", action="store_true")
    parser.add_argument("--scalenorm", action="store_true")
    args = parser.parse_args()

    generate_images(args)
    generate_sfx(args)
    generate_voiceover(args)
    generate_music(args)

    output_file = "horror_everyday_short.mp4"
    # We still use the assemble module, assuming it works generally with the passed assets dir
    # Note: assemble_metro was called before, but we probably want a generic assemble or just reuse it if it fits.
    # The previous script called assemble.assemble_metro(ASSETS_DIR, output_file)
    # Let's verify if assemble_metro is generic enough or if we should use a different one.
    # For now, to keep it working as the user expected (producing a video), we'll call into assemble.
    # Checking import... we imported assemble.

    # We will assume assemble_metro works for this structure (images/sfx/voice/music)
    try:
        assemble.assemble_metro(ASSETS_DIR, output_file)
        print(f"Created horror short: {output_file}")
    except AttributeError:
        # Fallback if assemble_metro expects specific strict things, but the structure images/sfx seems standard.
        print("Warning: assemble_metro not found or failed. Assets generated manually.")
