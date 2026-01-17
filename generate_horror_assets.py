import torch
import os
import sys
import numpy as np
import scipy.io.wavfile as wavfile
import argparse
import utils
import subprocess
import sys
import gc
import warnings
from diffusers import DiffusionPipeline, StableAudioPipeline
from vidlib.flux1_balanced import generate_flux1_balanced_image
from transformers import BitsAndBytesConfig
from PIL import Image

# Suppress torchsde warnings which can be spammy with Stable Audio
warnings.filterwarnings("ignore", category=UserWarning, module="torchsde")

# --- Configuration & Defaults ---
PROJECT_NAME = "horror"
ASSETS_DIR = f"assets_{PROJECT_NAME}"
DEVICE = (
    "cuda"
    if torch.cuda.is_available()
    else ("mps" if torch.backends.mps.is_available() else "cpu")
)
DTYPE = torch.bfloat16 if DEVICE in ["cuda", "mps"] else torch.float32

IS_H200 = False
if DEVICE == "cuda":
    gpu_name = torch.cuda.get_device_name(0)
    if "H200" in gpu_name:
        IS_H200 = True

DEFAULT_MODEL = (
    "black-forest-labs/FLUX.1-dev" if IS_H200 else "black-forest-labs/FLUX.1-schnell"
)
DEFAULT_STEPS = 64 if IS_H200 else 4
DEFAULT_GUIDANCE = 3.5 if IS_H200 else 0.0
DEFAULT_QUANT = "4bit" if (DEVICE == "cuda" and not IS_H200) else "none"

# --- SCENES and VO_SCRIPT ---
SCENES = [
    (
        "01_foggy_forest",
        "A dense, foggy forest at night, twisted trees, moonlight barely visible, horror atmosphere, 8k, highly detailed",
        "eerie wind howling distant owl screech",
    ),
    (
        "02_abandoned_house",
        "An old, abandoned house with broken windows, overgrown weeds, and a creaking door, horror, cinematic lighting",
        "creaking wood door slamming ghostly whispers",
    ),
    (
        "03_shadowy_figure",
        "A shadowy figure standing at the end of a long hallway, backlit, indistinct face, horror, suspenseful mood",
        "footsteps echoing heartbeat rising suspense",
    ),
    (
        "04_bloody_mirror",
        "A cracked mirror with bloody handprints, dim candlelight, horror, unsettling reflection",
        "glass cracking blood dripping faint breathing",
    ),
    (
        "05_final_scream",
        "A terrified person screaming in the rain, lightning flash, horror, dramatic close-up",
        "thunder crash rain pouring terrified scream",
    ),
]

VO_SCRIPT = """
It started with a whisper in the dark.
The forest was alive, but not with life.
Every shadow hid a secret, every sound a warning.
We should have turned back.
But the house called to us.
Inside, the air was thick with memories and fear.
A figure watched from the end of the hall.
We ran, but the mirror showed us what we could not escape.
In the storm, we screamed. But no one heard.
"""


def generate_images(args):
    model_id = args.model if args.model else DEFAULT_MODEL
    steps = 32  # Always use 32 iterations per image

    guidance = args.guidance
    quant = args.quant
    offload = args.offload
    use_scalenorm = args.scalenorm

    print(
        f"--- Generating {len(SCENES)} {model_id} Images ({steps} steps) on {DEVICE} ---"
    )
    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)
    for s_id, prompt, _ in SCENES:
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        if not os.path.exists(out_path):
            print(f"Generating: {s_id}")
            if getattr(args, "flux1_balanced", False):
                generate_flux1_balanced_image(
                    prompt,
                    out_path,
                    model_id=model_id,
                    steps=steps,
                    guidance=guidance if guidance is not None else 0.0,
                    max_sequence_length=256,
                    seed=0,
                    dtype=torch.bfloat16,
                    device_map="balanced",
                )
            else:
                pipe_kwargs = {
                    "torch_dtype": torch.bfloat16
                    if DEVICE == "cuda"
                    else torch.float32,
                }
                if quant != "none" and DEVICE == "cuda":
                    bnb_4bit_compute_dtype = (
                        torch.bfloat16 if IS_H200 else torch.float16
                    )
                    quant_config = BitsAndBytesConfig(
                        load_in_4bit=True,
                        bnb_4bit_quant_type="nf4",
                        bnb_4bit_compute_dtype=bnb_4bit_compute_dtype,
                    )
                    pipe_kwargs["transformer_quantization_config"] = quant_config
                    if not offload:
                        pass
                is_local = os.path.isdir(model_id)
                pipe = DiffusionPipeline.from_pretrained(
                    model_id, local_files_only=is_local, **pipe_kwargs
                )
                utils.remove_weight_norm(pipe)
                if use_scalenorm:
                    utils.apply_stability_improvements(
                        pipe.transformer, use_scalenorm=True
                    )
                if (offload or not IS_H200) and (DEVICE == "cuda" or DEVICE == "mps"):
                    print(
                        f"Enabling Model CPU Offload for VRAM efficiency on {DEVICE}..."
                    )
                    pipe.enable_model_cpu_offload()
                elif DEVICE == "cuda" or DEVICE == "mps":
                    pipe.to(DEVICE)
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
                torch.cuda.empty_cache()


def generate_sfx(args):
    print(f"--- Generating SFX with Stable Audio Open on {DEVICE} ---")
    pipe = StableAudioPipeline.from_pretrained(
        "stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16
    ).to(DEVICE)
    utils.remove_weight_norm(pipe)
    if args.scalenorm:
        utils.apply_stability_improvements(pipe.transformer, use_scalenorm=True)

    os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)
    for s_id, _, sfx_prompt in SCENES:
        out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
        if not os.path.exists(out_path):
            print(f"Generating SFX for: {s_id} -> {sfx_prompt}")
            audio = pipe(
                sfx_prompt, num_inference_steps=100, audio_end_in_s=12.0
            ).audios[0]
            audio_np = audio.T.cpu().numpy()
            wavfile.write(out_path, 44100, (audio_np * 32767).astype(np.int16))
    del pipe
    gc.collect()
    torch.cuda.empty_cache()


def apply_trailer_voice_effect(input_path):
    print(f"  [Stub] Applying trailer voice effects to {input_path}...")


def generate_voiceover(args):
    print(f"--- Generating Voiceover with F5-TTS (Local CLI) on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    lines = [l.strip() for l in VO_SCRIPT.split("\n") if l.strip()]
    temp_dir = f"{ASSETS_DIR}/voice/f5_temp"
    os.makedirs(temp_dir, exist_ok=True)
    full_audio_data = []
    sampling_rate = 44100
    for i, line in enumerate(lines):
        line_filename = f"vo_{i:03d}.wav"
        line_out_path = f"{ASSETS_DIR}/voice/{line_filename}"
        if os.path.exists(line_out_path):
            print(f"  Skipping existing line {i}: {line[:30]}...")
            try:
                sr, data = wavfile.read(line_out_path)
                full_audio_data.append(data)
                sampling_rate = sr
            except Exception as e:
                print(f"    Error reading {line_out_path}: {e}")
            continue
        print(f"  Generating line {i}: {line[:30]}...")
        cmd = [
            "python3",
            "-m",
            "f5_tts_infer_cli",
            "--gen_text",
            line,
            "--output_dir",
            temp_dir,
        ]
        try:
            for f in os.listdir(temp_dir):
                if f.endswith(".wav"):
                    os.remove(os.path.join(temp_dir, f))
            subprocess.run(cmd, check=True)
            generated_wav = None
            for file in os.listdir(temp_dir):
                if file.endswith(".wav"):
                    generated_wav = os.path.join(temp_dir, file)
                    break
            if generated_wav and os.path.exists(generated_wav):
                os.replace(generated_wav, line_out_path)
                apply_trailer_voice_effect(line_out_path)
                sr, data = wavfile.read(line_out_path)
                full_audio_data.append(data)
                sampling_rate = sr
                silence = np.zeros(int(sr * 0.5), dtype=data.dtype)
                full_audio_data.append(silence)
            else:
                print(f"  Error: No output found for line {i}")
        except Exception as e:
            print(f"  Failed to generate line {i}: {e}")
    if full_audio_data:
        try:
            combined = np.concatenate(full_audio_data)
            wavfile.write(out_path_full, sampling_rate, combined)
            print(f"  Full voiceover saved to {out_path_full}")
        except ValueError as e:
            print(f"  Error concatenating audio (shape mismatch?): {e}")
    try:
        if os.path.exists(temp_dir):
            for f in os.listdir(temp_dir):
                os.remove(os.path.join(temp_dir, f))
            os.rmdir(temp_dir)
    except Exception:
        pass


def generate_music(args):
    print(f"--- Generating Background Music with Stable Audio on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    tracks = [
        ("horror_theme.wav", 45.0),
        ("horror_theme_long_01.wav", 160.0),
        ("horror_theme_long_02.wav", 160.0),
    ]
    pipe = None
    for filename, duration_s in tracks:
        out_path = f"{ASSETS_DIR}/music/{filename}"
        if os.path.exists(out_path):
            print(f"  Skipping {filename} (exists)")
            continue
        if pipe is None:
            pipe = StableAudioPipeline.from_pretrained(
                "stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16
            ).to(DEVICE)
            utils.remove_weight_norm(pipe)
            if args.scalenorm:
                utils.apply_stability_improvements(pipe.transformer, use_scalenorm=True)
        prompt = "eerie minimal synth drone, dark ambient, horror soundtrack, slow pulsing deep bass, cinematic atmosphere, high quality"
        print(f"  Generating {filename} ({duration_s}s)...")
        chunk_len = 40.0
        num_chunks = int(np.ceil(duration_s / chunk_len))
        full_audio = []
        for k in range(num_chunks):
            print(f"    Generating chunk {k + 1}/{num_chunks}...")
            audio = pipe(
                prompt, num_inference_steps=100, audio_end_in_s=chunk_len
            ).audios[0]
            audio_np = audio.T.cpu().numpy()
            full_audio.append(audio_np)
        if full_audio:
            combined = np.concatenate(full_audio, axis=0)
            wavfile.write(out_path, 44100, (combined * 32767).astype(np.int16))
            print(f"    Saved {out_path}")
    if pipe:
        del pipe
        gc.collect()
        torch.cuda.empty_cache()


if __name__ == "__main__":
    from vidlib import assets

    parser = argparse.ArgumentParser(description="Generate Horror Assets")
    parser.add_argument("--model", type=str)
    parser.add_argument("--steps", type=int)
    parser.add_argument("--guidance", type=float)
    parser.add_argument("--quant", type=str, choices=["none", "4bit", "8bit"])
    parser.add_argument("--offload", action="store_true")
    parser.add_argument("--scalenorm", action="store_true")
    parser.add_argument(
        "--flux1_balanced",
        action="store_true",
        help="Use FluxPipeline with device_map=balanced",
    )
    args = parser.parse_args()

    assets.horror_generate_images(args)
    assets.horror_generate_sfx(args)
    assets.horror_generate_voiceover(args)
    assets.horror_generate_music(args)
