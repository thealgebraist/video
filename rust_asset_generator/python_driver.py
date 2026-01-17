import torch
from diffusers import StableDiffusionPipeline
import sys
import argparse
import os


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

    # Disable safety checker to avoid missing weight errors and for speed
    try:
        pipe = StableDiffusionPipeline.from_pretrained(
            args.model,
            torch_dtype=torch.float32,
            safety_checker=None,
            requires_safety_checker=False,
        )
    except Exception as e:
        print(f"Error loading model: {e}")
        print("Retrying with local_files_only=False...")
        pipe = StableDiffusionPipeline.from_pretrained(
            args.model,
            torch_dtype=torch.float32,
            safety_checker=None,
            requires_safety_checker=False,
            local_files_only=False,
        )

    pipe = pipe.to(device)

    print(f"Generating image for: {args.prompt} ({args.steps} steps)...")
    result = pipe(args.prompt, num_inference_steps=args.steps)
    image = result.images[0]

    output_dir = os.path.dirname(args.output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    image.save(args.output)
    print(f"Saved to {args.output}")


if __name__ == "__main__":
    main()
