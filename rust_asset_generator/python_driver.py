import torch
from diffusers import StableDiffusionPipeline
import sys
import argparse
import os


import numpy as np
from PIL import Image


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompt", type=str, required=True)
    parser.add_argument("--output", type=str, required=True)
    parser.add_argument("--model", type=str, default="nota-ai/bk-sdm-tiny")
    parser.add_argument("--device", type=str, default=None)
    parser.add_argument("--steps", type=int, default=25)
    args = parser.parse_args()

    # Automatic device detection if not specified
    if args.device is None or args.device == "auto":
        if torch.cuda.is_available():
            device = "cuda"
        elif torch.backends.mps.is_available():
            device = "mps"
        else:
            device = "cpu"
    else:
        device = args.device

    print(f"Loading model {args.model} on {device}...")

    pipe = None
    try:
        pipe = StableDiffusionPipeline.from_pretrained(
            args.model,
            torch_dtype=torch.float32,
            safety_checker=None,
            requires_safety_checker=False,
            local_files_only=True,
        )
        pipe = pipe.to(device)
    except Exception as e:
        print(f"Error loading model {args.model}: {e}")
        print("Falling back to plasma generation.")

    if pipe:
        print(f"Generating image for: {args.prompt} ({args.steps} steps)...")
        result = pipe(args.prompt, num_inference_steps=args.steps)
        image = result.images[0]
        output_dir = os.path.dirname(args.output)
        if output_dir:
            os.makedirs(output_dir, exist_ok=True)
        image.save(args.output)
        print(f"Saved to {args.output}")
    else:
        generate_plasma_image(args.prompt, args.output)


if __name__ == "__main__":
    main()
