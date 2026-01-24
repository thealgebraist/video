import torch
import os
import numpy as np
import scipy.io.wavfile as wavfile
import utils
import gc
import warnings

# Suppress torchsde warnings which can be spammy with Stable Audio
warnings.filterwarnings("ignore", category=UserWarning, module="torchsde")

from diffusers import StableAudioPipeline

DEVICE = (
    "cuda"
    if torch.cuda.is_available()
    else ("mps" if torch.backends.mps.is_available() else "cpu")
)

def generate_film_music():
    output_dir = "generations/music"
    os.makedirs(output_dir, exist_ok=True)
    
    print(f"--- Loading Stable Audio Open 1.0 on {DEVICE} ---")
    pipe = StableAudioPipeline.from_pretrained(
        "stabilityai/stable-audio-open-1.0", 
        torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
    ).to(DEVICE)
    
    # Apply standard project improvements if available
    if hasattr(utils, "remove_weight_norm"):
        utils.remove_weight_norm(pipe)

    tracks = [
        ("cinematic_ambient_01.wav", "Lush cinematic ambient background music, sweeping strings, subtle piano, emotive and film-like, high fidelity, 44.1kHz"),
        ("cinematic_tension_02.wav", "Slow building cinematic tension, deep pulses, atmospheric textures, film noir aesthetic, professional master, high quality"),
        ("cinematic_hopeful_03.wav", "Uplifting cinematic orchestral piece, light woodwinds, warm cello, hopeful and inspiring film soundtrack, 44.1kHz")
    ]

    for filename, prompt in tracks:
        out_path = os.path.join(output_dir, filename)
        if os.path.exists(out_path):
            print(f"Skipping {filename} (exists)")
            continue
            
        print(f"Generating: {filename} (60s)...")
        
        # Stable Audio Open 1.0 handles up to ~47s natively. 
        # To get 60s, we generate two 30s chunks and crossfade or just concatenate.
        # For "nice film like" music, we'll do 45s + 15s to minimize seams.
        
        full_audio = []
        durations = [45.0, 15.0]
        
        for i, dur in enumerate(durations):
            print(f"  Chunk {i+1}/2 ({dur}s)...")
            audio = pipe(
                prompt, 
                num_inference_steps=200, 
                audio_end_in_s=dur
            ).audios[0]
            full_audio.append(audio.T.cpu().numpy())
            
        combined = np.concatenate(full_audio, axis=0)
        # Scale to int16
        wav_data = (combined * 32767).astype(np.int16)
        wavfile.write(out_path, 44100, wav_data)
        print(f"Saved to {out_path}")

    del pipe
    gc.collect()
    if torch.cuda.is_available():
        torch.cuda.empty_cache()

if __name__ == "__main__":
    generate_film_music()
