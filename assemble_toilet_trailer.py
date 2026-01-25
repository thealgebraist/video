import subprocess
import os
import argparse

def assemble_toilet(assets_dir, output_file):
    TOTAL_DURATION = 60 # Seconds
    SCENES = [
        "01_led_strip", "02_tokyo_view", "03_lid_open", "04_hologram", "05_laser_jet", 
        "06_heated_seat", "07_espresso", "08_speakers", "09_deodorizer", "10_biometric", 
        "11_neon_flush", "12_massage", "13_medical_scan", "14_robotic_arm", "15_maglev", 
        "16_silence_button", "17_uv_clean", "18_guest_awe", "19_turbo_flush", "20_briefcase", 
        "21_gold_nozzle", "22_movie_screen", "23_wind_tunnel", "24_social_sync", "25_umbrella", 
        "26_digital_drop", "27_factory", "28_power_button", "29_drone", "30_support_voice", 
        "31_title_card", "32_subscription"
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
        
    music_path = f"{assets_dir}/music/toilet_theme.wav"
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
    
    filter_complex += f"[sfx_all]volume=0.5[sfx_final];"
    filter_complex += f"[{vo_idx}:a]volume=2.2[vo_final];"
    filter_complex += f"[{music_idx}:a]volume=0.6[music_final];"
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
    parser.add_argument("--assets", type=str, default="assets_toilet", help="Path to assets directory")
    parser.add_argument("--output", type=str, default="toilet_trailer.mp4", help="Output filename")
    args = parser.parse_args()
    assemble_toilet(args.assets, args.output)
