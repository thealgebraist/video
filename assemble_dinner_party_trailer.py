import subprocess
import os
import argparse

def assemble_dinner(assets_dir, output_file):
    TOTAL_DURATION = 30
    SCENES = [
        "01_food_photo", "02_wine_snob", "03_double_dip", 
        "04_diet_bomb", "05_phone_under_table", "06_uninvited_dog", 
        "07_boring_story", "08_wine_spill", "09_kitchen_clutter", 
        "10_political_fight", "11_title_card", "12_long_goodbye"
    ]
    scene_duration = TOTAL_DURATION / len(SCENES)
    cmd = ["ffmpeg", "-y"]
    for s_id in SCENES:
        img_path = f"{assets_dir}/images/{s_id}.png"
        cmd += ["-loop", "1", "-t", str(scene_duration), "-i", img_path] if os.path.exists(img_path) else ["-f", "lavfi", "-t", str(scene_duration), "-i", "color=c=black:s=1280x720:r=25"]
    for s_id in SCENES:
        sfx_path = f"{assets_dir}/sfx/{s_id}.wav"
        cmd += ["-stream_loop", "-1", "-t", str(scene_duration), "-i", sfx_path] if os.path.exists(sfx_path) else ["-f", "lavfi", "-t", str(scene_duration), "-i", "anullsrc=r=44100:cl=stereo"]
    vo_path = f"{assets_dir}/voice/voiceover_full.wav"
    cmd += ["-i", vo_path] if os.path.exists(vo_path) else ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
    music_path = f"{assets_dir}/music/dinner_theme.wav"
    cmd += ["-i", music_path] if os.path.exists(music_path) else ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
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
    vo_idx, music_idx = len(SCENES) * 2, len(SCENES) * 2 + 1
    filter_complex += f"[sfx_all]volume=0.5[sfx_final];"
    filter_complex += f"[{vo_idx}:a]volume=2.0[vo_final];"
    filter_complex += f"[{music_idx}:a]volume=0.4[music_final];"
    filter_complex += f"[sfx_final][vo_final][music_final]amix=inputs=3:duration=first:dropout_transition=0[aout]"
    cmd += ["-filter_complex", filter_complex, "-map", "[vout]", "-map", "[aout]", "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18", "-c:a", "aac", "-b:a", "320k", "-t", str(TOTAL_DURATION), output_file]
    subprocess.run(cmd, check=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--assets", type=str, default="assets_dinner", help="Path to assets directory")
    parser.add_argument("--output", type=str, default="dinner_trailer.mp4", help="Output filename")
    args = parser.parse_args()
    assemble_dinner(args.assets, args.output)
