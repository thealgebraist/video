import os
import shutil
import subprocess
import numpy as np
from PIL import Image
import scipy.io.wavfile as wavfile

def create_fresh_assets(base_dir, num_scenes):
    if os.path.exists(base_dir):
        shutil.rmtree(base_dir)
    os.makedirs(f"{base_dir}/images", exist_ok=True)
    os.makedirs(f"{base_dir}/sfx", exist_ok=True)
    os.makedirs(f"{base_dir}/voice", exist_ok=True)
    os.makedirs(f"{base_dir}/music", exist_ok=True)
    
    sr = 44100
    t = np.linspace(0, 2, sr * 2) # 2s pieces
    music = np.sin(2 * np.pi * 220 * t) * 0.1
    wavfile.write(f"{base_dir}/music/airport_theme.wav", sr, (music * 32767).astype(np.int16))
    
    expected_names = [
        "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign"
    ]
    
    for i in range(num_scenes):
        img = Image.new('RGB', (1280, 720), color=(i*60, 100, 255 - i*60))
        img.save(f"{base_dir}/images/{expected_names[i]}.png")
        
        # SFX length varies
        sfx_t = np.linspace(0, 1 + i*0.5, int(sr * (1 + i*0.5)))
        sfx = np.sin(2 * np.pi * (440 + i*100) * sfx_t) * 0.5
        wavfile.write(f"{base_dir}/sfx/{expected_names[i]}.wav", sr, (sfx * 32767).astype(np.int16))
        
        # VO length varies
        vo_t = np.linspace(0, 2 - i*0.2, int(sr * (2 - i*0.2)))
        vo = np.sin(2 * np.pi * 880 * vo_t) * 0.8
        wavfile.write(f"{base_dir}/voice/vo_{i:03d}.wav", sr, (vo * 32767).astype(np.int16))

def run_test(test_id, num_scenes):
    assets_dir = f"temp_test_assets_{test_id}"
    output = f"test_results/test_{test_id}_{num_scenes}scenes.mp4"
    os.makedirs("test_results", exist_ok=True)
    
    create_fresh_assets(assets_dir, num_scenes)
    
    print(f"Running Test {test_id} with {num_scenes} scenes...")
    # Run the ROBUST assembler
    subprocess.run(["./assemble_video", assets_dir, output], check=True)
    
    shutil.rmtree(assets_dir)
    return output

if __name__ == "__main__":
    if os.path.exists("test_results"):
        shutil.rmtree("test_results")
        
    for i in range(1, 9):
        n = ((i-1) % 4) + 1
        run_test(i, n)
