import torch
import torch.multiprocessing as mp
import os
import numpy as np
import scipy.io.wavfile as wavfile
import argparse
import utils
import gc
import subprocess
from diffusers import StableDiffusion3Pipeline, StableAudioPipeline
from transformers import BitsAndBytesConfig
from PIL import Image

# --- Configuration & Defaults ---
PROJECT_NAME = "toilet"
ASSETS_DIR = f"assets_{PROJECT_NAME}"
DEVICE = (
    "cuda"
    if torch.cuda.is_available()
    else ("mps" if torch.backends.mps.is_available() else "cpu")
)

# Use SD3.5 Large as requested. 
# TensorRT optimization is usually handled via specific model exports or engine loading.
# Here we use the standard pipeline which is highly compatible.
DEFAULT_MODEL = "stabilityai/stable-diffusion-3.5-large"
DEFAULT_STEPS = 40
DEFAULT_GUIDANCE = 4.5

# 32 Scenes for the Zen Throne
SCENES = [
    ("01_led_strip", "Extreme close up of a sleek matte-black ceramic toilet surface with a glowing neon blue LED strip, steam rising elegantly, high tech, 8k", "High fidelity crisp foley, digital hum and steam hiss"),
    ("02_tokyo_view", "Wide shot of a minimalist white marble bathroom in a Tokyo skyscraper at night, futuristic toilet in center, city lights bokeh background", "High fidelity crisp foley, city ambience and soft wind"),
    ("03_lid_open", "Action shot of a toilet lid opening automatically, hydraulic gold mechanical interior, high tech luxury, precise movement", "High fidelity crisp foley, hydraulic hiss and mechanical whir"),
    ("04_hologram", "Close up of a holographic control panel rising from a toilet armrest, neon icons showing Quantum Wash, futuristic interface", "High fidelity crisp foley, digital UI sounds and holographic hum"),
    ("05_laser_jet", "Action shot of a laser-guided water jet firing a perfectly precise stream into a crystal prism, refracted light, high tech precision", "High fidelity crisp foley, sharp water jet zip sound"),
    ("06_heated_seat", "Close up of a warm orange glowing heated toilet seat with a digital temperature display showing 98.6F, luxury bathroom", "High fidelity crisp foley, soft electrical hum and warmth"),
    ("07_espresso", "Medium shot of an integrated espresso machine on the side of a futuristic toilet pouring a perfect crema into a porcelain cup", "High fidelity crisp foley, espresso machine gurgle and steam"),
    ("08_speakers", "Action shot of a toilet with hidden speakers, 7.1 surround sound icons, vibrating with musical energy, sleek design", "High fidelity crisp foley, orchestral swell and bass vibration"),
    ("09_deodorizer", "Close up of a deodorizer vent releasing a visible mist of sandalwood, glowing particles, high tech filtration", "High fidelity crisp foley, gentle mist spray and fan whir"),
    ("10_biometric", "Extreme close up of a biometric fingerprint sensor on a sleek flush button, red laser scan, cyberpunk technology", "High fidelity crisp foley, biometric scan beep and laser sweep"),
    ("11_neon_flush", "Action shot of a toilet bowl lighting up in a rainbow of neon colors during a high-pressure flush, futuristic vortex", "High fidelity crisp foley, high pressure vacuum flush thump"),
    ("12_massage", "Medium shot of a built-in kinetic massager in a toilet backrest, vibrating chrome parts, high tech ergonomics", "High fidelity crisp foley, kinetic vibration and mechanical pulse"),
    ("13_medical_scan", "Close up of a screen on a bathroom wall showing a 3D medical health analysis, glowing DNA strands, futuristic diagnostics", "High fidelity crisp foley, data processing noise and medical beep"),
    ("14_robotic_arm", "Action shot of a tiny sleek robotic arm extending from a toilet to offer a warm scented silk towel", "High fidelity crisp foley, tiny robotic servo whir and silk rustle"),
    ("15_maglev", "Wide shot of a futuristic toilet floating slightly off the marble floor using mag-lev technology, glowing blue ring underneath", "High fidelity crisp foley, magnetic hum and zero-gravity float"),
    ("16_silence_button", "Close up of a button labeled Absolute Silence being pressed by a finger, ripples in the air, soundproofing effect", "High fidelity crisp foley, air pressure drop and absolute silence"),
    ("17_uv_clean", "Action shot of a toilet bowl being sterilized by a powerful beam of deep purple UV light, glowing bacteria disappearing", "High fidelity crisp foley, electrical hum and ozone sizzle"),
    ("18_guest_awe", "Medium shot of a guest looking at a glowing toilet in awe, their face lit by neon lights, futuristic bathroom background", "High fidelity crisp foley, soft gasp and ambient party noise"),
    ("19_turbo_flush", "Close up of a control panel showing Emergency Turbo Flush in blinking red neon letters, high stakes technology", "High fidelity crisp foley, alarm beep and powering up sound"),
    ("20_briefcase", "Action shot of a high tech toilet folding into a compact metallic titanium briefcase, transformer-like mechanism", "High fidelity crisp foley, metallic folding and locking clicks"),
    ("21_gold_nozzle", "Extreme close up of a gold-plated and diamond-encrusted water nozzle extending from a luxury toilet, sparkling", "High fidelity crisp foley, metallic slide and diamond twinkle"),
    ("22_movie_screen", "Action shot of a toilet interface projecting a 120-inch holographic movie screen onto a bathroom door, cinematic", "High fidelity crisp foley, projector hum and cinematic audio"),
    ("23_wind_tunnel", "Close up of a wind tunnel dryer blowing air with extreme force, a guest's hair blowing back, high tech power", "High fidelity crisp foley, jet engine roar and rushing air"),
    ("24_social_sync", "Medium shot of a toilet syncing with a smartphone, screen showing Achievement Unlocked: Royal Flush, high tech social integration", "High fidelity crisp foley, digital notification ding and sync sound"),
    ("25_umbrella", "Action shot of a toilet deploying a tiny spring-loaded umbrella during a comical malfunction, high tech mishap", "High fidelity crisp foley, spring pop and umbrella opening"),
    ("26_digital_drop", "Extreme close up of a water drop landing on ceramic, turning into digital binary code zeros and ones, matrix effect", "High fidelity crisp foley, digital plink and data flow"),
    ("27_factory", "Wide shot of a futuristic factory with giant robotic arms assembling thousands of Zen Throne toilets, sparks flying", "High fidelity crisp foley, heavy industrial robots and welding sparks"),
    ("28_power_button", "Close up of a flush button glowing like a nuclear reactor core, intense energy, high tech power source", "High fidelity crisp foley, electrical surge and deep hum"),
    ("29_drone", "Action shot of a toilet launching a tiny sleek quadcopter drone to fetch a roll of toilet paper, high tech assistance", "High fidelity crisp foley, quadcopter drone buzz and wind"),
    ("30_support_voice", "Medium shot of a toilet with a glowing voice interface saying 'You did a great job today', friendly AI", "High fidelity crisp foley, soothing AI voice and soft chime"),
    ("31_title_card", "Cinematic title card: 'THE ZEN THRONE' in elegant silver font, matte black background, high tech luxury typography", "High fidelity crisp foley, dramatic orchestral hit"),
    ("32_subscription", "Post-title shot of a credit card reader on a toilet showing 'Insert Card for Premium Flush', corporate satire", "High fidelity crisp foley, credit card swipe and error beep"),
]

VO_SCRIPT = """
The future has arrived.
Where technology meets biology.
Introducing... the Zen Throne X-1.
Temperature controlled... by your soul.
Acoustic... perfection.
Security... for your most private moments.
Comfort... beyond comprehension.
Integrated... health diagnostics.
Gravity... is now optional.
You've never felt... this clean.
Only the finest... for your behind.
Entertainment... redefined.
Data-driven... relief.
A new era... of hygiene.
The Zen Throne.
The last seat you'll ever need.
Subscription required.
"""

def image_worker(proc_id, task_queue, args):
    """Worker process for SD3.5 generation"""
    os.environ["PYTORCH_ALLOC_CONF"] = "expandable_segments:True"
    model_id = args.model or DEFAULT_MODEL
    
    print(f"  [Process {proc_id}] Loading {model_id}...")
    
    # SD3.5 Large is very heavy. Use T5 offloading or quantization if possible.
    # For 24GB cards, we use the standard pipeline with CPU offload.
    try:
        pipe = StableDiffusion3Pipeline.from_pretrained(
            model_id, 
            torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
        )
        if DEVICE == "cuda":
            pipe.enable_model_cpu_offload()
            # SD3.5 specific optimizations
            pipe.vae.enable_tiling()
            pipe.vae.enable_slicing()
    except Exception as e:
        print(f"  [Process {proc_id}] Failed to load SD3.5: {e}")
        return

    while True:
        try:
            task = task_queue.get_nowait()
        except:
            break
            
        s_id, prompt = task
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        
        print(f"  [Process {proc_id}] Generating: {s_id}")
        try:
            image = pipe(
                prompt=prompt,
                num_inference_steps=args.steps,
                guidance_scale=args.guidance,
                width=1024, # SD3.5 defaults
                height=1024,
            ).images[0]
            # Resize to 1280x720 for trailer
            image = image.resize((1280, 720), Image.LANCZOS)
            image.save(out_path)
        except Exception as e:
            print(f"  [Process {proc_id}] Error generating {s_id}: {e}")
        
    del pipe
    gc.collect()

def generate_images(args):
    print(f"--- Launching {args.num_procs} SD3.5 Processes for {len(SCENES)} Scenes ---")
    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)
    to_generate = [(s_id, prompt) for s_id, prompt, _ in SCENES if not os.path.exists(f"{ASSETS_DIR}/images/{s_id}.png")]
    if not to_generate:
        print("All images exist.")
        return

    try:
        mp.set_start_method('spawn', force=True)
    except RuntimeError:
        pass

    task_queue = mp.Queue()
    for task in to_generate:
        task_queue.put(task)
        
    processes = []
    for i in range(args.num_procs):
        p = mp.Process(target=image_worker, args=(i, task_queue, args))
        p.start()
        processes.append(p)
    for p in processes:
        p.join()

def generate_sfx(args):
    print(f"--- Generating High Quality SFX with Stable Audio Open ---")
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", 
            torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
        ).to(DEVICE)
        os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)
        for s_id, _, sfx_prompt in SCENES:
            out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
            if os.path.exists(out_path) and not utils.is_audio_bad(out_path):
                continue
            print(f"Generating SFX for: {s_id}")
            for attempt in range(2):
                audio = pipe(sfx_prompt, num_inference_steps=200, audio_end_in_s=10.0).audios[0]
                wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
                if not utils.is_audio_bad(out_path):
                    break
        del pipe
    except Exception as e:
        print(f"SFX generation failed: {e}")
    gc.collect()

def generate_voiceover(args):
    print("--- Generating High Quality Voiceover with F5-TTS ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    if os.path.exists(out_path_full) and not utils.is_audio_bad(out_path_full):
        return

    lines = [l.strip() for l in VO_SCRIPT.split("\n") if l.strip()]
    temp_dir = f"{ASSETS_DIR}/voice/f5_temp"
    os.makedirs(temp_dir, exist_ok=True)

    full_audio_data, sampling_rate = [], 44100
    for i, line in enumerate(lines):
        line_out_path = f"{ASSETS_DIR}/voice/vo_{i:03d}.wav"
        if os.path.exists(line_out_path) and not utils.is_audio_bad(line_out_path):
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
                full_audio_data.append(np.zeros(int(sr * 0.8), dtype=data.dtype))
        except Exception as e:
            print(f"  Line {i} failed: {e}")

    if full_audio_data:
        wavfile.write(out_path_full, sampling_rate, np.concatenate(full_audio_data))

def generate_music(args):
    print(f"--- Generating High Quality Music with Stable Audio Open ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    out_path = f"{ASSETS_DIR}/music/toilet_theme.wav"
    if os.path.exists(out_path) and not utils.is_audio_bad(out_path):
        return
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", 
            torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
        ).to(DEVICE)
        prompt = "Futuristic ethereal synth pads transition to massive heavy industrial techno bass beat, tech guru vibe, cinematic master"
        audio = pipe(prompt, num_inference_steps=200, audio_end_in_s=60.0).audios[0]
        wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
    except Exception as e:
        print(f"Music generation failed: {e}")
    gc.collect()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    parser.add_argument("--num_procs", type=int, default=2) # SD3.5 is VERY heavy, 2 procs safer for 24GB
    args = parser.parse_args()

    generate_images(args)
    generate_sfx(args)
    generate_voiceover(args)
    generate_music(args)
