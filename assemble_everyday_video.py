import os
import argparse
import subprocess
import glob


def get_scene_files(assets_dir):
    # Get all images sorted
    images = sorted(glob.glob(f"{assets_dir}/images/*.png"))
    # Get all sfx
    sfx = sorted(glob.glob(f"{assets_dir}/sfx/*.wav"))
    # Get all voiceovers (use index based naming if possible, but fallback to glob)
    # The generator uses vo_000.wav, vo_001.wav
    voiceovers = sorted(glob.glob(f"{assets_dir}/voice/vo_*.wav"))
    return images, sfx, voiceovers


def assemble_video(assets_dir, output_file):
    print(f"Assembling video using assets from: {assets_dir}")
    images, sfx_files, vo_files = get_scene_files(assets_dir)

    if not images:
        print("No images found!")
        return

    # Configuration
    SCENE_DURATION = 4.5
    TRANSITION_DURATION = 0.5  # Simple crossfade
    TOTAL_SCENES = len(images)

    # --- Build FFmpeg Filtergraph ---
    inputs = []
    filter_complex = []

    # 1. Visual Track (Images with Zoompan)
    # We will output a single video stream 'v'

    # Optimization: Create a concat file for images to avoid massive command line
    # But zoompan needs to be applied per image.
    # We can do strictly sequential render for the video track to an intermediate file.

    # Let's try to do it in one pass if possible, or 2 passes.
    # Pass 1: Video only (Images -> Ken Burns -> Concat)
    # Pass 2: Audio mixing
    # Pass 3: Combine

    video_temp = "temp_video.mp4"
    audio_temp = "temp_audio.wav"

    # --- STEP 1: VIDEO GENERATION ---
    print("--- Step 1: Rendering Video Track with Zoom Effect ---")

    # Create inputArgs with zoompan filters
    # Because 64 inputs is a lot for one command, we might hit shell limits.
    # We will use the 'concat demuxer' approach but zoompan requires processing.
    # Alternative: Generate 64 short clips with zoompan, then concat (fastest/safest).

    os.makedirs("temp_clips", exist_ok=True)
    clip_list_file = "clips.txt"
    with open(clip_list_file, "w") as f:
        for i, img in enumerate(images):
            clip_out = f"temp_clips/clip_{i:03d}.mp4"
            # Zoom effect: Zoom in slightly over SCENE_DURATION
            # zoompan=z='min(zoom+0.0015,1.5)':d=125:x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)'
            # 4.5s * 24fps = 108 frames. Let's start with 5s clip.

            cmd = [
                "ffmpeg",
                "-y",
                "-i",
                img,
                "-vf",
                f"zoompan=z='min(zoom+0.0015,1.5)':d={int(SCENE_DURATION * 25)}:x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':s=1280x720:fps=24",
                "-t",
                str(SCENE_DURATION),
                "-c:v",
                "libx264",
                "-pix_fmt",
                "yuv420p",
                "-crf",
                "23",
                clip_out,
            ]
            if not os.path.exists(clip_out):
                subprocess.run(cmd, stderr=subprocess.DEVNULL)
                print(f"Rendered clip {i + 1}/{TOTAL_SCENES}", end="\r")

            f.write(f"file '{os.path.abspath(clip_out)}'\n")

    print("\nConcatenating clips...")
    subprocess.run(
        [
            "ffmpeg",
            "-y",
            "-f",
            "concat",
            "-safe",
            "0",
            "-i",
            clip_list_file,
            "-c",
            "copy",
            video_temp,
        ]
    )

    # --- STEP 2: AUDIO GENERATION ---
    print("--- Step 2: Mixing Audio Tracks ---")

    # We need to mix:
    # 1. Voiceovers (sequenced at start of each scene)
    # 2. SFX (sequenced at start of each scene)
    # 3. Music (6 tracks, crossfaded)

    # We will use a complex filtergraph for audio mixing.
    # To avoid argument length limits, we'll do this in stages or use a specialized python script for the mix.
    # Mixing 64 VO + 64 SFX + 6 Music = 134 inputs! Too many.

    # Sub-strategy: Mix VO and SFX into one "speech_sfx.wav"
    # Then mix Music into "music.wav"
    # Then combine.

    # A. Mix VO/SFX
    # Construct a filtergraph that delays each audio by i * SCENE_DURATION
    # adelay=deltas=dur_ms|dur_ms

    # Be careful with max inputs.
    # Let's create 'scene_audio_X.wav' for each scene (vo + sfx mixed).
    # Then concat them.

    audio_clips_list = "audio_clips.txt"
    with open(audio_clips_list, "w") as f:
        for i in range(len(images)):
            scene_audio_out = f"temp_clips/scene_audio_{i:03d}.wav"

            # Inputs
            vo = vo_files[i] if i < len(vo_files) else None
            # Find matching SFX? Filenames are random-ish (by scene id).
            # We assumed sorted order of glob matches scene order.
            # generate_everyday_assets.py names them by scene ID (e.g. 01_...).
            # So sorted glob works.
            sfx = sfx_files[i] if i < len(sfx_files) else None

            cmd = ["ffmpeg", "-y"]
            filter_str = ""
            input_count = 0

            if vo:
                cmd.extend(["-i", vo])
                input_count += 1
            if sfx:
                cmd.extend(["-i", sfx])
                input_count += 1

            # Use filters to mix and pad to SCENE_DURATION
            if input_count == 2:
                filter_str = f"[0:a][1:a]amix=inputs=2:duration=longest[mix];[mix]apad=pad_dur={SCENE_DURATION}[out]"
            elif input_count == 1:
                filter_str = f"[0:a]apad=pad_dur={SCENE_DURATION}[out]"
            else:
                # Silence
                filter_str = f"anullsrc=r=44100:cl=stereo:d={SCENE_DURATION}[out]"
                cmd.extend(
                    ["-f", "lavfi", "-i", "anullsrc=r=44100:cl=stereo:d=0.1"]
                )  # dummy input

            # Force duration crop
            # The pad approach adds silence, but we want exact duration.
            # Best to generate exactly SCENE_DURATION of audio.

            # Simplified: Just take VO and SFX, mix, render to wav.
            # We handle timing in the concat phase.

            cmd.extend(
                [
                    "-filter_complex",
                    filter_str,
                    "-map",
                    "[out]",
                    "-t",
                    str(SCENE_DURATION),
                    scene_audio_out,
                ]
            )

            if not os.path.exists(scene_audio_out):
                subprocess.run(cmd, stderr=subprocess.DEVNULL)

            f.write(f"file '{os.path.abspath(scene_audio_out)}'\n")

    print("Concatenating Scene Audio...")
    subprocess.run(
        [
            "ffmpeg",
            "-y",
            "-f",
            "concat",
            "-safe",
            "0",
            "-i",
            audio_clips_list,
            "-c:a",
            "pcm_s16le",
            "temp_speech_sfx.wav",
        ]
    )

    # B. Music Mix
    # 6 Music tracks.
    # Total duration 240s+
    # We want to crossfade them.
    # Inputs: music/*.wav sorted.
    music_files = sorted(glob.glob(f"{assets_dir}/music/*.wav"))
    if music_files:
        # Simple concat with crossfade is hard in CLI.
        # Just concat for now, or use complex filter.
        # Given 6 files, we can use complex filter.

        music_cmd = ["ffmpeg", "-y"]
        filter_parts = []
        for i, m in enumerate(music_files):
            music_cmd.extend(["-i", m])

        # [0][1]acrossfade=d=5[a01];[a01][2]acrossfade=d=5...
        # Loop to build chain
        current_stream = "[0:a]"
        for i in range(1, len(music_files)):
            next_stream = f"[{i}:a]"
            out_stream = f"[m{i}]"
            filter_parts.append(
                f"{current_stream}{next_stream}acrossfade=d=3{out_stream}"
            )
            current_stream = out_stream

        # Volume adjustment for music (background)
        filter_parts.append(f"{current_stream}volume=0.4[music_out]")

        music_cmd.extend(
            [
                "-filter_complex",
                ";".join(filter_parts),
                "-map",
                "[music_out]",
                "temp_music_bed.wav",
            ]
        )
        subprocess.run(music_cmd)

    # --- STEP 3: FINAL COMBINE ---
    print("--- Step 3: Final Assembly ---")

    # Mix speech/sfx with music
    final_cmd = [
        "ffmpeg",
        "-y",
        "-i",
        video_temp,
        "-i",
        "temp_speech_sfx.wav",
        "-i",
        "temp_music_bed.wav",
        "-filter_complex",
        "[1:a][2:a]amix=inputs=2:duration=first[a_out]",
        "-map",
        "0:v",
        "-map",
        "[a_out]",
        "-c:v",
        "copy",
        "-c:a",
        "aac",
        "-b:a",
        "192k",
        "-shortest",
        output_file,
    ]
    subprocess.run(final_cmd)

    print(f"Done! Video saved to {output_file}")

    # Cleanup
    # os.remove(video_temp)
    # os.remove("temp_speech_sfx.wav")
    # os.remove("temp_music_bed.wav")
    # (Leaving temps for debug)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--assets", required=True, help="Directory containing assets")
    parser.add_argument("--output", default="final_video.mp4", help="Output file path")
    args = parser.parse_args()

    assemble_video(args.assets, args.output)
