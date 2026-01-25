import subprocess
import os
import argparse

def assemble_souffle(assets_dir, output_file):
    TOTAL_DURATION = 60 # Seconds
    SCENES = [
        "01_kitchen", "02_sweat", "03_whisk", "04_ramekin", "05_start_button", 
        "06_egg_crack", "07_chocolate", "08_arthur_profile", "09_egg_whites", 
        "10_clock", "11_nebula", "12_folding", "13_eye_reflect", "14_rim_wipe", 
        "15_tray_slide", "16_door_seal", "17_tectonic", "18_vibration", 
        "19_steam_vent", "20_arthur_burn", "21_mountain", "22_apex_rise", 
        "23_countdown", "24_glitch", "25_exhale", "26_reveal", "27_monument", 
        "28_blackout", "29_title", "30_structure", "31_outnow", "32_spoon"
    ]
    scene_duration = TOTAL_DURATION / len(SCENES)
    
    cmd = ["ffmpeg", "-y"]
    
    for s_id in SCENES:
        img_path = f"{assets_dir}/images/{s_id}.png"
        if os.path.exists(img_path):
            cmd += ["-loop", "1", "-t", str(scene_duration), "-i", img_path]
        else:
            cmd += ["-f", "lavfi", "-t", str(scene_duration), "-i", "color=c=black:s=1280x720:r=25"]
            
    for s_id in SCENES:
        sfx_path = f"{assets_dir}/sfx/{s_id}.wav"
        if os.path.exists(sfx_path):
            cmd += ["-stream_loop", "-1", "-t", str(scene_duration), "-i", sfx_path]
        else:
            cmd += ["-f", "lavfi", "-t", str(scene_duration), "-i", "anullsrc=r=44100:cl=stereo"]
            
    vo_path = f"{assets_dir}/voice/voiceover_full.wav"
    if os.path.exists(vo_path):
        cmd += ["-i", vo_path]
    else:
        cmd += ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
        
    music_path = f"{assets_dir}/music/souffle_theme.wav"
    if os.path.exists(music_path):
        cmd += ["-i", music_path]
    else:
        cmd += ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
        
    filter_complex = ""
    for i in range(len(SCENES)):
        filter_complex += f"[{i}:v]scale=8000:-1,zoompan=z='min(zoom+0.001,1.5)':d={int(scene_duration*25)}:x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':s=1280x720[v{i}];"
    
    v_concat = "".join([f"[v{i}]" for i in range(len(SCENES))])
    filter_complex += f"{v_concat}concat=n={len(SCENES)}:v=1:a=0[vout];"
    
    sfx_mixed_outputs = ""
    for i in range(len(SCENES)):
        input_idx = len(SCENES) + i
        delay_ms = int(i * scene_duration * 1000)
        filter_complex += f"[{input_idx}:a]adelay={delay_ms}|{delay_ms}[sfx{i}];"
        sfx_mixed_outputs += f"[sfx{i}]"
    
    filter_complex += f"{sfx_mixed_outputs}amix=inputs={len(SCENES)}:dropout_transition=0[sfx_all];"
    
    vo_idx = len(SCENES) * 2
    music_idx = vo_idx + 1
    
    filter_complex += f"[sfx_all]volume=0.6[sfx_final];"
    filter_complex += f"[{vo_idx}:a]volume=2.0[vo_final];"
    filter_complex += f"[{music_idx}:a]volume=0.5[music_final];"
    filter_complex += f"[sfx_final][vo_final][music_final]amix=inputs=3:duration=first:dropout_transition=0[aout]"
    
    cmd += ["-filter_complex", filter_complex]
    cmd += ["-map", "[vout]", "-map", "[aout]"]
    cmd += [
        "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18",
        "-c:a", "aac", "-b:a", "320k",
        "-t", str(TOTAL_DURATION),
        output_file
    ]
    
    subprocess.run(cmd, check=True)
    print(f"--- Created {output_file} ---")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--assets", type=str, default="assets_souffle", help="Path to assets directory")
    parser.add_argument("--output", type=str, default="souffle_trailer.mp4", help="Output filename")
    args = parser.parse_args()
    assemble_souffle(args.assets, args.output)
