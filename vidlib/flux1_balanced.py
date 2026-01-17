import torch
from diffusers import FluxPipeline
import os
from PIL import Image

def generate_flux1_balanced_image(prompt, output_path, model_id="black-forest-labs/FLUX.1-schnell", steps=4, guidance=0.0, max_sequence_length=256, seed=0, dtype=torch.bfloat16, device_map="balanced"):
    pipe = FluxPipeline.from_pretrained(
        model_id,
        torch_dtype=dtype,
        device_map=device_map
    )
    generator = torch.Generator("cpu").manual_seed(seed)
    image = pipe(
        prompt,
        guidance_scale=guidance,
        num_inference_steps=steps,
        max_sequence_length=max_sequence_length,
        generator=generator
    ).images[0]
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    image.save(output_path)
    return output_path
