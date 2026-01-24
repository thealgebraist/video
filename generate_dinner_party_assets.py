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
