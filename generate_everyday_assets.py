# generate_everyday_assets.py
# Generates assets for "Everyday Horror" trailer variants
# Uses multi-GPU acceleration for Images, SFX, and Voiceover

import warnings

warnings.filterwarnings("ignore", message=".*add_prefix_space.*")
warnings.filterwarnings("ignore", message=".*slow tokenizers.*")

import torch
import os
import sys

sys.path.append(os.getcwd())
import numpy as np
import scipy.io.wavfile as wavfile
import argparse
import multiprocessing as mp

from diffusers import DiffusionPipeline, StableAudioPipeline, FluxPipeline
from transformers import pipeline, BitsAndBytesConfig
from everyday_trailer_variants import EVERYDAY_TRAILER_VARIANTS

if __name__ == "__main__":
    mp.set_start_method("spawn", force=True)

# --- Configuration ---
DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
DTYPE = torch.bfloat16 if DEVICE == "cuda" else torch.float32

DEFAULT_MODEL = "black-forest-labs/FLUX.1-schnell"
DEFAULT_STEPS = 64
DEFAULT_GUIDANCE = 0.0
DEFAULT_QUANT = "4bit" if DEVICE == "cuda" else "none"


def remove_weight_norm(model):
    """Removes weight normalization for stability."""
    if not hasattr(model, "parameters"):
        return
    for module in model.modules():
        try:
            torch.nn.utils.remove_weight_norm(module)
        except (ValueError, AttributeError):
            pass


def apply_stability_improvements(model, use_scalenorm=False):
    """Applies stability improvements to the model."""
    if use_scalenorm:
        # Placeholder for ScaleNorm implementation
        pass


def _generate_images_worker(gpu_id, scenes_chunk, assets_dir, args):
    """Worker function for multi-GPU image generation."""
    device = f"cuda:{gpu_id}"
    print(f"[GPU {gpu_id}] Starting image generation for {len(scenes_chunk)} scenes")

    pipe = None
    try:
        if args.model == "black-forest-labs/FLUX.1-schnell":
            from transformers import BitsAndBytesConfig
            from diffusers import FluxTransformer2DModel

            if args.quant == "8bit":
                print(f"[GPU {gpu_id}] Loading with 8-bit quantization...")
                quantization_config = BitsAndBytesConfig(
                    load_in_8bit=True,
                    llm_int8_threshold=6.0,
                )
                transformer = FluxTransformer2DModel.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    subfolder="transformer",
                    quantization_config=quantization_config,
                    torch_dtype=torch.bfloat16,
                    device_map={"": device},
                )
                pipe = FluxPipeline.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    transformer=transformer,
                    torch_dtype=torch.bfloat16,
                ).to(device)

            elif args.quant == "4bit":
                print(f"[GPU {gpu_id}] Loading with 4-bit quantization...")
                quantization_config = BitsAndBytesConfig(
                    load_in_4bit=True,
                    bnb_4bit_quant_type="nf4",
                    bnb_4bit_compute_dtype=torch.bfloat16,
                )
                transformer = FluxTransformer2DModel.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    subfolder="transformer",
                    quantization_config=quantization_config,
                    torch_dtype=torch.bfloat16,
                    device_map={"": device},
                )
                pipe = FluxPipeline.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    transformer=transformer,
                    torch_dtype=torch.bfloat16,
                ).to(device)

            else:
                print(f"[GPU {gpu_id}] Loading without quantization...")
                pipe = FluxPipeline.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    torch_dtype=torch.bfloat16,
                )
                pipe.enable_model_cpu_offload(gpu_id=gpu_id)

            print(f"[GPU {gpu_id}] Model loaded successfully on {device}")
        else:
            # Other models (e.g. SDXL)
            pipe = DiffusionPipeline.from_pretrained(
                args.model,
                torch_dtype=torch.float16,
            ).to(device)

    except Exception as e:
        print(f"[GPU {gpu_id}] Failed to load model: {e}")
        return

    for s_id, prompt, _ in scenes_chunk:
        out_path = f"{assets_dir}/images/{s_id}.png"
        if not os.path.exists(out_path):
            if pipe:
                print(f"[GPU {gpu_id}] Generating: {s_id}")
                try:
                    image = pipe(
                        prompt,
                        num_inference_steps=args.steps,
                        guidance_scale=args.guidance,
                        width=1280,
                        height=720,
                    ).images[0]
                    image.save(out_path)
                except Exception as e:
                    print(f"[GPU {gpu_id}] Error generating {s_id}: {e}")

    if pipe:
        del pipe
        torch.cuda.empty_cache()
    print(f"[GPU {gpu_id}] Completed image generation")


def _generate_sfx_worker(gpu_id, scenes_chunk, assets_dir, args):
    """Worker function for multi-GPU SFX generation."""
    device = f"cuda:{gpu_id}"
    print(f"[GPU {gpu_id}] Starting SFX generation for {len(scenes_chunk)} scenes")

    # Check work
    active_scenes = []
    for s_id, _, _ in scenes_chunk:
        if not os.path.exists(f"{assets_dir}/sfx/{s_id}.wav"):
            active_scenes.append(s_id)

    if not active_scenes:
        print(f"[GPU {gpu_id}] All SFX scenes already exist. Exiting.")
        return

    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0",
            torch_dtype=torch.float16,
        ).to(device)
    except Exception as e:
        print(f"[GPU {gpu_id}] Failed to load Stable Audio: {e}")
        return

    # Process in batches of 3
    BATCH_SIZE = 3

    for i in range(0, len(scenes_chunk), BATCH_SIZE):
        batch = scenes_chunk[i : i + BATCH_SIZE]

        active_batch = []
        for s in batch:
            s_id, _, sfx_prompt = s
            out_path = f"{assets_dir}/sfx/{s_id}.wav"
            if not os.path.exists(out_path):
                active_batch.append((s_id, sfx_prompt))

        if not active_batch:
            continue

        if pipe:
            prompts = [s[1] for s in active_batch]
            ids = [s[0] for s in active_batch]

            print(
                f"[GPU {gpu_id}] Generating SFX batch ({len(prompts)}): {', '.join(ids)}"
            )

            try:
                outputs = pipe(
                    prompts, num_inference_steps=100, audio_end_in_s=5.0
                ).audios

                for j, audio in enumerate(outputs):
                    out_path = f"{assets_dir}/sfx/{ids[j]}.wav"
                    wavfile.write(
                        out_path,
                        44100,
                        (audio.T.cpu().numpy() * 32767).astype(np.int16),
                    )
            except Exception as e:
                print(f"[GPU {gpu_id}] Error generating batch {ids}: {e}")

    if pipe:
        del pipe
        torch.cuda.empty_cache()
    print(f"[GPU {gpu_id}] Completed SFX generation")


def _generate_voiceover_worker(gpu_id, lines_chunk, start_idx, assets_dir, args):
    """Worker function for multi-GPU voiceover generation."""
    device = f"cuda:{gpu_id}"
    print(f"[GPU {gpu_id}] Starting VO generation for {len(lines_chunk)} lines")

    try:
        from transformers import pipeline

        tts = pipeline("text-to-speech", model="suno/bark", device=device)

        if hasattr(tts.model, "generation_config"):
            tts.model.generation_config.pad_token_id = (
                tts.model.generation_config.eos_token_id
            )

        for i, line in enumerate(lines_chunk):
            global_idx = start_idx + i
            out_path_i = f"{assets_dir}/voice/vo_{global_idx:03d}.wav"

            if not os.path.exists(out_path_i):
                print(f"[GPU {gpu_id}] Speaking {global_idx + 1}: {line[:30]}...")
                output = tts(line)
                audio_data = output["audio"].flatten()
                wavfile.write(
                    out_path_i,
                    output["sampling_rate"],
                    (audio_data * 32767).astype(np.int16),
                )
    except Exception as e:
        print(f"[GPU {gpu_id}] Error in VO worker: {e}")


def _generate_music_worker(gpu_id, prompts_chunk, assets_dir, args):
    """Worker function for multi-GPU music generation."""
    device = f"cuda:{gpu_id}"
    print(f"[GPU {gpu_id}] Starting Music generation for {len(prompts_chunk)} tracks")

    # Check work
    active_prompts = []
    for name, _, _ in prompts_chunk:
        if not os.path.exists(f"{assets_dir}/music/{name}.wav"):
            active_prompts.append(name)

    if not active_prompts:
        print(f"[GPU {gpu_id}] All music tracks exist. Exiting.")
        return

    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0",
            torch_dtype=torch.float16,
        ).to(device)
        remove_weight_norm(pipe)
        if args.scalenorm:
            apply_stability_improvements(pipe.transformer, use_scalenorm=True)
    except Exception as e:
        print(f"[GPU {gpu_id}] Failed to load Stable Audio: {e}")
        return

    for name, prompt, duration in prompts_chunk:
        out_path = f"{assets_dir}/music/{name}.wav"
        if not os.path.exists(out_path):
            print(f"[GPU {gpu_id}] Generating Music: {name}")
            try:
                audio = pipe(
                    prompt, num_inference_steps=100, audio_end_in_s=duration
                ).audios[0]
                wavfile.write(
                    out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16)
                )
            except Exception as e:
                print(f"[GPU {gpu_id}] Error generating {name}: {e}")

    if pipe:
        del pipe
        torch.cuda.empty_cache()
    print(f"[GPU {gpu_id}] Completed Music generation")


def generate_variant(variant, args):
    name = variant["name"]
    scenes = variant["scenes"]

    # Parse voiceover lines from string to list
    vo_text = variant["voiceover"]
    vo_lines = [line.strip() for line in vo_text.strip().split("\n") if line.strip()]

    assets_dir = f"assets_everyday_{name}"
    print(f"\n=== Generating Assets for Variant: {variant['title']} ===")
    print(f"Output Directory: {assets_dir}")

    os.makedirs(f"{assets_dir}/images", exist_ok=True)
    os.makedirs(f"{assets_dir}/sfx", exist_ok=True)
    os.makedirs(f"{assets_dir}/voice", exist_ok=True)
    os.makedirs(f"{assets_dir}/music", exist_ok=True)

    # --- 1. Images ---
    if args.multigpu and args.multigpu > 1:
        chunk_size = len(scenes) // args.multigpu
        chunks = [scenes[i : i + chunk_size] for i in range(0, len(scenes), chunk_size)]
        if len(chunks) > args.multigpu:
            chunks[-2] = chunks[-2] + chunks[-1]
            chunks = chunks[:-1]

        processes = []
        for gpu_id, chunk in enumerate(chunks):
            p = mp.Process(
                target=_generate_images_worker, args=(gpu_id, chunk, assets_dir, args)
            )
            p.start()
            processes.append(p)
        for p in processes:
            p.join()
    else:
        # Single GPU fallback (simplified)
        _generate_images_worker(0, scenes, assets_dir, args)

    # --- 2. SFX ---
    if args.multigpu and args.multigpu > 1:
        chunk_size = len(scenes) // args.multigpu
        chunks = [scenes[i : i + chunk_size] for i in range(0, len(scenes), chunk_size)]
        if len(chunks) > args.multigpu:
            chunks[-2] = chunks[-2] + chunks[-1]
            chunks = chunks[:-1]

        processes = []
        for gpu_id, chunk in enumerate(chunks):
            p = mp.Process(
                target=_generate_sfx_worker, args=(gpu_id, chunk, assets_dir, args)
            )
            p.start()
            processes.append(p)
        for p in processes:
            p.join()
    else:
        _generate_sfx_worker(0, scenes, assets_dir, args)

    # --- 3. Voiceover ---
    if args.multigpu and args.multigpu > 1:
        chunk_size = len(vo_lines) // args.multigpu
        chunks = [
            vo_lines[i : i + chunk_size] for i in range(0, len(vo_lines), chunk_size)
        ]
        if len(chunks) > args.multigpu:
            chunks[-2] = chunks[-2] + chunks[-1]
            chunks = chunks[:-1]

        processes = []
        current_idx = 0
        for gpu_id, chunk in enumerate(chunks):
            p = mp.Process(
                target=_generate_voiceover_worker,
                args=(gpu_id, chunk, current_idx, assets_dir, args),
            )
            p.start()
            processes.append(p)
            current_idx += len(chunk)
        for p in processes:
            p.join()
    else:
        _generate_voiceover_worker(0, vo_lines, 0, assets_dir, args)

    # Assemble full VO mix
    full_audio = []
    sampling_rate = 24000
    for i in range(len(vo_lines)):
        out_path_i = f"{assets_dir}/voice/vo_{i:03d}.wav"
        if os.path.exists(out_path_i):
            try:
                rate, data = wavfile.read(out_path_i)
                sampling_rate = rate
                full_audio.append(data.astype(np.float32) / 32767.0)
                full_audio.append(np.zeros(int(rate * 0.5)))
            except Exception:
                pass

    if full_audio:
        final_mix = np.concatenate(full_audio)
        wavfile.write(
            f"{assets_dir}/voice/full_mix.wav",
            sampling_rate,
            (final_mix * 32767).astype(np.int16),
        )

    # --- 4. Music (Narrative Arc - 240s Total) ---
    print(f"--- Generating Narrative Music (6 Segments) ---")

    # 6 segments * 47s = ~282s (enough for 240s with crossfades)
    music_prompts = [
        (
            "music_01_mundane",
            "lo-fi hip hop beats, morning coffee vibe, sunny, repetitive, safe, mundane, high quality",
            47.0,
        ),
        (
            "music_02_glitch",
            "lo-fi beats but with subtle vinyl crackle and slight tempo skipping, unease, repetitive melody, glitch",
            47.0,
        ),
        (
            "music_03_looping",
            "repetitive electronic synth loop, hypnotic, minimal techno, slight dissonance, feeling trapped, ticking clock rhythm",
            47.0,
        ),
        (
            "music_04_dread",
            "dark ambient drone, rising shepherd tone, anxiety, mechanical industrial sounds, heart beat, psychological horror",
            47.0,
        ),
        (
            "music_05_climax",
            "terrifying industrial noise, metallic screeching, chaotic drums, panic, jagged synth, horror chase",
            47.0,
        ),
        (
            "music_06_void",
            "deep sub-bass drone, empty void, hollow wind, melancholic strings, acceptance of doom, cinematic ending",
            47.0,
        ),
    ]

    if args.multigpu and args.multigpu > 1:
        chunk_size = len(music_prompts) // args.multigpu
        chunks = [
            music_prompts[i : i + chunk_size]
            for i in range(0, len(music_prompts), chunk_size)
        ]
        if len(chunks) > args.multigpu:
            chunks[-2] = chunks[-2] + chunks[-1]
            chunks = chunks[:-1]

        processes = []
        for gpu_id, chunk in enumerate(chunks):
            p = mp.Process(
                target=_generate_music_worker, args=(gpu_id, chunk, assets_dir, args)
            )
            p.start()
            processes.append(p)
        for p in processes:
            p.join()
    else:
        _generate_music_worker(0, music_prompts, assets_dir, args)


def main():
    parser = argparse.ArgumentParser(
        description="Generate assets for Everyday Horror variants"
    )
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    parser.add_argument(
        "--quant", type=str, default=DEFAULT_QUANT, choices=["none", "8bit", "4bit"]
    )
    parser.add_argument(
        "--offload",
        action="store_true",
        help="Enable CPU offload for non-quantized models",
    )
    parser.add_argument("--scalenorm", action="store_true")
    parser.add_argument("--multigpu", type=int, default=0, help="Number of GPUs to use")
    parser.add_argument(
        "--variant", type=str, help="Specific variant name to generate (optional)"
    )

    args = parser.parse_args()

    print(f"--- Starting Everyday Assets Generation ---")
    print(f"Model: {args.model}")
    print(f"Quantization: {args.quant}")
    print(f"Multi-GPU: {args.multigpu}")

    variants_to_process = EVERYDAY_TRAILER_VARIANTS
    if args.variant:
        variants_to_process = [
            v for v in EVERYDAY_TRAILER_VARIANTS if v["name"] == args.variant
        ]
        if not variants_to_process:
            print(f"Variant '{args.variant}' not found.")
            return

    for variant in variants_to_process:
        generate_variant(variant, args)

    print("\nAll tasks complete.")


if __name__ == "__main__":
    main()
