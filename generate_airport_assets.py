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
        "Cinematic wide shot of an infinite, snaking security line in a sterile, grey airport terminal, exhausted travelers, harsh overhead lighting, 8k, highly detailed",
        "airport terminal ambience, crowded chatter, distant PA announcements",
    ),
    (
        "02_boot_struggle",
        "Close up of a frustrated man hopping on one foot, trying to remove a complex leather boot while holding a grey plastic security bin with his teeth, airport security background",
        "grunting, plastic bin rattling, heavy breathing",
    ),
    (
        "03_sad_sandwich",
        "Macro shot of a sad, wilted ham sandwich wrapped in crinkly plastic under a flickering yellow heat lamp in an airport cafe, $18 price tag visible",
        "crinkly plastic sound, electrical hum of heat lamp",
    ),
    (
        "04_delayed_sign",
        "Close up of a digital airport gate sign flipping from 'ON TIME' to 'DELAYED: 6 HOURS', frustrated reflections in the screen",
        "airport announcement chime, collective groan",
    ),
    (
        "05_gate_lice",
        "A crowd of travelers standing too close to the boarding gate, huddled together like a pack of wolves, looking intensely at the gate agent",
        "shuffling feet, murmuring crowd, backpack zippers",
    ),
    (
        "06_tiny_seat",
        "Interior of an airplane, wide shot of a passenger squeezed into a tiny middle seat between two massive people, knees pushed against the seat in front",
        "airplane cabin white noise, plastic creaking",
    ),
    (
        "07_crying_baby",
        "Extreme close up of a baby with its mouth wide open, crying, red-faced, sitting in an airplane seat, blurred passenger in foreground looking distressed",
        "loud baby crying, engine drone",
    ),
    (
        "08_seat_recline",
        "Close up of a laptop screen being crushed by the seat in front reclining abruptly, sparks and cracked plastic, airplane interior",
        "loud plastic crack, metal hinge squeak",
    ),
    (
        "09_turbulence",
        "Close up of a small plastic cup of tomato juice on a tray table vibrating violently, red liquid splashing out during turbulence",
        "violent shaking sound, rattling tray table, wind roar",
    ),
    (
        "10_lost_suitcase",
        "Wide shot of a single, battered, lonely suitcase circling an empty baggage carousel in a dimly lit, deserted airport hall at night",
        "mechanical carousel hum, distant thud of baggage",
    ),
    (
        "11_title_card",
        "Cinematic title card: 'AIRPORT HELL' in bold, distressed metallic font, airport runway lights in the background, bokeh effect",
        "deep cinematic bass hit, terminal bell",
    ),
    (
        "12_forgotten_passport",
        "Close up of a hand slapping a forehead in realization, through a plane window as it pulls away from the gate, a blue passport left behind on a seat",
        "muffled 'oh no' voice, jet engine whine",
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
