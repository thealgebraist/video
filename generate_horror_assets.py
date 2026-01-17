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

# Suppress warnings
warnings.filterwarnings("ignore", category=UserWarning, module="torchsde")
warnings.filterwarnings("ignore", category=FutureWarning)


def generate_plasma_image(prompt, out_path, width=1280, height=720):
    """Generates a high-quality plasma/gradient image as a fallback."""
    print(f"  [Fallback] Generating plasma image for: {prompt[:30]}...")
    arr = np.zeros((height, width, 3), dtype=np.uint8)
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
    """Uses macOS 'say' command as a high-quality local TTS fallback."""
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

DEFAULT_MODEL = "black-forest-labs/FLUX.1-dev" if IS_H200 else "nota-ai/bk-sdm-tiny"
DEFAULT_STEPS = 64 if IS_H200 else 4
DEFAULT_GUIDANCE = 3.5 if IS_H200 else 0.0
DEFAULT_QUANT = "4bit" if (DEVICE == "cuda" and not IS_H200) else "none"

# Import trailer variants
from horror_trailer_variants import TRAILER_VARIANTS


def generate_images(args, variant):
    """Generate images for a specific trailer variant."""
    model_id = args.model if args.model else DEFAULT_MODEL
    steps = 32
    guidance = args.guidance
    quant = args.quant
    offload = args.offload
    use_scalenorm = args.scalenorm

    assets_dir = f"assets_horror_{variant['name']}"
    scenes = variant["scenes"]

    print(
        f"--- Generating {len(scenes)} {model_id} Images for '{variant['title']}' ({steps} steps) on {DEVICE} ---"
    )
    os.makedirs(f"{assets_dir}/images", exist_ok=True)
    for s_id, prompt, _ in scenes:
        out_path = f"{assets_dir}/images/{s_id}.png"
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
                    if use_scalenorm:
                        utils.apply_stability_improvements(
                            pipe.transformer, use_scalenorm=True
                        )
                    if (offload or not IS_H200) and (
                        DEVICE == "cuda" or DEVICE == "mps"
                    ):
                        print(
                            f"Enabling Model CPU Offload for VRAM efficiency on {DEVICE}..."
                        )
                        pipe.enable_model_cpu_offload()
                    elif DEVICE == "cuda" or DEVICE == "mps":
                        pipe.to(DEVICE)
                except Exception as e:
                    print(f"  [Error] Failed to load local model {model_id}: {e}")
                    print("  Falling back to procedural generation.")

                if pipe:
                    image = pipe(
                        prompt=prompt,
                        num_inference_steps=steps,
                        guidance_scale=guidance,
                        width=1280,
                        height=720,
                    ).images[0]
                    image.save(out_path)
                    del pipe
                else:
                    generate_plasma_image(prompt, out_path)

                gc.collect()
                if DEVICE == "cuda":
                    torch.cuda.empty_cache()


def generate_sfx(args):
    print(f"--- Generating SFX with Stable Audio Open on {DEVICE} ---")
    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0",
            torch_dtype=torch.float16,
            local_files_only=True,
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
            if pipe:
                print(f"Generating SFX for: {s_id} -> {sfx_prompt}")
                audio = pipe(
                    sfx_prompt, num_inference_steps=100, audio_end_in_s=12.0
                ).audios[0]
                audio_np = audio.T.cpu().numpy()
                wavfile.write(out_path, 44100, (audio_np * 32767).astype(np.int16))
            else:
                generate_mock_audio(sfx_prompt, out_path, duration_s=10.0)
    if pipe:
        del pipe
    gc.collect()
    torch.cuda.empty_cache()


def apply_trailer_voice_effect(input_path):
    print(f"  [Stub] Applying trailer voice effects to {input_path}...")


def generate_voiceover(args):
    print(f"--- Generating Voiceover fallback on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    lines = [l.strip() for l in VO_SCRIPT.split("\n") if l.strip()]
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
        if macos_say_tts(line, line_out_path):
            sr, data = wavfile.read(line_out_path)
            full_audio_data.append(data)
            sampling_rate = sr
            full_audio_data.append(np.zeros(int(sr * 0.5), dtype=data.dtype))
        else:
            print(f"  Failed even with fallback for line {i}")

    if full_audio_data:
        try:
            combined = np.concatenate(full_audio_data)
            wavfile.write(out_path_full, sampling_rate, combined)
            print(f"  Full voiceover saved to {out_path_full}")
        except ValueError as e:
            print(f"  Error concatenating audio (shape mismatch?): {e}")


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
            try:
                pipe = StableAudioPipeline.from_pretrained(
                    "stabilityai/stable-audio-open-1.0",
                    torch_dtype=torch.float16,
                    local_files_only=True,
                ).to(DEVICE)
                utils.remove_weight_norm(pipe)
                if args.scalenorm:
                    utils.apply_stability_improvements(
                        pipe.transformer, use_scalenorm=True
                    )
            except Exception as e:
                print(f"  [Error] Failed to load Stable Audio: {e}")
                print("  Using procedural music fallback.")
        prompt = "eerie minimal synth drone, dark ambient, horror soundtrack, slow pulsing deep bass, cinematic atmosphere, high quality"
        print(f"  Generating {filename} ({duration_s}s)...")
        chunk_len = 40.0
        num_chunks = int(np.ceil(duration_s / chunk_len))
        full_audio = []
        for k in range(num_chunks):
            print(f"    Generating chunk {k + 1}/{num_chunks}...")
        if pipe:
            audio = pipe(
                prompt, num_inference_steps=100, audio_end_in_s=chunk_len
            ).audios[0]
            audio_np = audio.T.cpu().numpy()
            full_audio.append(audio_np)
        else:
            # Procedural music fallback
            print(f"    [Fallback] Generating chunk {k + 1} procedurally...")
            t = np.linspace(0, chunk_len, int(44100 * chunk_len))
            chunk_audio = (
                0.3
                * np.sin(2 * np.pi * (50 + k * 10) * t)
                * (0.5 + 0.5 * np.cos(2 * np.pi * 0.1 * t))
            )
            full_audio.append(chunk_audio[:, np.newaxis] * np.ones((1, 2)))  # Stereo
        if full_audio:
            combined = np.concatenate(full_audio, axis=0)
            wavfile.write(out_path, 44100, (combined * 32767).astype(np.int16))
            print(f"    Saved {out_path}")
    if pipe:
        del pipe
        gc.collect()
        torch.cuda.empty_cache()


if __name__ == "__main__":
    import multiprocessing as mp
    from vidlib import assets

    # Set multiprocessing start method for CUDA compatibility
    mp.set_start_method("spawn", force=True)

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
    parser.add_argument(
        "--multigpu",
        type=int,
        default=None,
        help="Number of GPUs for parallel generation",
    )
    args = parser.parse_args()

    # Generate assets for all horror variants
    for variant in TRAILER_VARIANTS:
        print(f"\n{'=' * 60}\nGenerating assets for: {variant['title']}\n{'=' * 60}\n")
        generate_images(args, variant)
        generate_sfx(args, variant)
        generate_voiceover(args, variant)
        generate_music(args, variant)
        print(f"\nCompleted: {variant['title']}\n")
