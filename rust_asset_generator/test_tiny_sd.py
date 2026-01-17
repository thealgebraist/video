import torch
from diffusers import StableDiffusionPipeline
import time


def test():
    model_id = "nota-ai/bk-sdm-tiny"
    print(f"Testing {model_id}...")

    device = "cuda" if torch.cuda.is_available() else "cpu"
    if torch.backends.mps.is_available():
        device = "mps"

    print(f"Using device: {device}")

    start = time.time()
    pipe = StableDiffusionPipeline.from_pretrained(
        model_id,
        torch_dtype=torch.float32,
        safety_checker=None,
        requires_safety_checker=False,
    )
    pipe = pipe.to(device)
    load_time = time.time() - start
    print(f"Model loaded in {load_time:.2f}s")

    prompt = "A simple test image of a sunset"
    print(f"Generating image for prompt: '{prompt}'")

    start = time.time()
    # Using 5 steps for a quick test
    image = pipe(prompt, num_inference_steps=5).images[0]
    gen_time = time.time() - start

    image.save("tiny_sd_test.png")
    print(f"Image saved to tiny_sd_test.png (Generation time: {gen_time:.2f}s)")


if __name__ == "__main__":
    try:
        test()
    except Exception as e:
        print(f"Test failed: {e}")
