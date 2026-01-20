#!/usr/bin/env python3
import os
from pathlib import Path
import sys

PROMPTS = Path("generations/audio_prompts.txt")
OUT_DIR = Path("generations")
STAR_IMG_DIR = Path("star/generations")
TMP_DIR = Path("temp_segments_star_male")
TMP_DIR.mkdir(exist_ok=True)
OUT_DIR.mkdir(exist_ok=True)

if not PROMPTS.exists():
    print("Prompts file missing:", PROMPTS)
    sys.exit(1)

lines = [l.strip() for l in PROMPTS.read_text(encoding='utf-8').splitlines() if l.strip()]
count = len(lines)

api_key = os.environ.get("ELEVENLABS_API_KEY")
if not api_key:
    print("ELEVENLABS_API_KEY not set in environment.")
    sys.exit(1)

print("Using ElevenLabs API key from environment.")

try:
    from elevenlabs import ElevenLabs
except Exception as e:
    print("Failed to import ElevenLabs client:", e)
    sys.exit(1)

client = ElevenLabs(api_key=api_key)

# get voices
voices_list = []
try:
    vs = client.voices.get_all()
    voices_list = getattr(vs, "voices", vs) or []
except Exception:
    try:
        voices_list = client.voices.list() or []
    except Exception:
        voices_list = []

male_choice = None
for v in voices_list:
    name = getattr(v, "name", None) or getattr(v, "voice_name", None) or str(v)
    gender = (getattr(v, "gender", "") or "").lower()
    vid = getattr(v, "id", None) or getattr(v, "voice_id", None) or getattr(v, "voiceId", None) or name
    if (name and "male" in name.lower()) or ("male" in gender) or ("deep" in name.lower()):
        male_choice = vid
        chosen_name = name
        break

if not male_choice:
    # fallback: pick first voice
    if voices_list:
        v = voices_list[0]
        male_choice = getattr(v, "id", None) or getattr(v, "voice_id", None) or getattr(v, "voiceId", None) or getattr(v, "name", None) or str(v)
        chosen_name = getattr(v, "name", None) or str(v)
    else:
        print("No voices available from ElevenLabs; aborting.")
        sys.exit(1)

print(f"Selected ElevenLabs voice: {chosen_name} (id={male_choice})")

# Generate mp3s and wavs
import subprocess
for i, text in enumerate(lines):
    out_mp3 = OUT_DIR / f"zombies_{i:02d}.mp3"
    out_wav = OUT_DIR / f"zombies_{i:02d}.wav"
    print(f"Generating audio {i}/{count}: {out_mp3}")
    try:
        stream = client.text_to_speech.convert(male_choice, text=text)
        with open(out_mp3, "wb") as fh:
            for chunk in stream:
                if chunk is None:
                    continue
                if isinstance(chunk, (bytes, bytearray)):
                    fh.write(chunk)
                elif hasattr(chunk, "content"):
                    fh.write(getattr(chunk, "content"))
                elif isinstance(chunk, str):
                    fh.write(chunk.encode("utf-8"))
        # Convert to wav
        cmd = ["/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning", "-i", str(out_mp3), str(out_wav)]
        subprocess.run(cmd, check=True)
    except Exception as e:
        print(f"ElevenLabs generation failed for index {i}: {e}")
        print("Falling back to legacy/gTTS generation for this prompt.")
        try:
            # try legacy path
            from elevenlabs import set_api_key, generate, save
            set_api_key(api_key)
            audio = generate(text=text, voice=male_choice)
            save(audio, str(out_mp3))
            subprocess.run(["/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning", "-i", str(out_mp3), str(out_wav)], check=True)
        except Exception:
            # final fallback to gTTS
            try:
                from gtts import gTTS
                t = gTTS(text=text, lang="en")
                t.save(str(out_mp3))
                subprocess.run(["/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning", "-i", str(out_mp3), str(out_wav)], check=True)
            except Exception as e2:
                print(f"Failed to generate audio for index {i}: {e2}")

# Build segments mapping audio to star images (repeat images if needed)
star_images = sorted(STAR_IMG_DIR.glob("zombies_*.png"))
if not star_images:
    print("No star images found in", STAR_IMG_DIR)
    sys.exit(1)

n_images = len(star_images)
print(f"Using {n_images} star images to map {count} audio files (will repeat images if needed)")

TMP_DIR.mkdir(exist_ok=True)
for i in range(count):
    img = star_images[i % n_images]
    wav = OUT_DIR / f"zombies_{i:02d}.wav"
    out = TMP_DIR / f"segment_{i:02d}.mp4"
    print(f"Rendering segment {i}: img={img.name} audio={wav.name}")
    cmd = [
        "/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning",
        "-loop", "1", "-i", str(img), "-i", str(wav),
        "-c:v", "libx264", "-tune", "stillimage", "-pix_fmt", "yuv420p",
        "-vf", "scale=1920:1080:force_original_aspect_ratio=decrease,pad=1920:1080:(ow-iw)/2:(oh-ih)/2",
        "-c:a", "aac", "-b:a", "192k", "-shortest", "-crf", "16", "-preset", "slow", str(out)
    ]
    try:
        subprocess.run(cmd, check=True)
    except Exception as e:
        print(f"Failed to render segment {i}: {e}")

# Concatenate
concat_list = TMP_DIR / "concat_list.txt"
with concat_list.open("w", encoding="utf-8") as fh:
    for i in range(count):
        fh.write(f"file '{TMP_DIR / f'segment_{i:02d}.mp4'}'\n")

final_out = OUT_DIR / "zombies_slideshow_star_male.mp4"
try:
    subprocess.run(["/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning", "-f", "concat", "-safe", "0", "-i", str(concat_list), "-c", "copy", str(final_out)], check=True)
    print("Wrote final video:", final_out)
except Exception as e:
    print("Failed to concatenate final video:", e)

print("Done.")
