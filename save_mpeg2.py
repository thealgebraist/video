import os
import subprocess
import numpy as np
import scipy.io.wavfile as wavfile

# --- 1-1 Synchronized bytes from Coq libav_mpeg2_model ---
# Covers: Seq -> SeqExt -> Pic -> PicExt -> Slice -> Block
FORMAL_CORE_BLOCK = bytes([0, 0, 1, 179, 80, 2, 208, 51, 255, 255, 226, 40, 0, 0, 1, 181, 20, 170, 0, 1, 0, 0, 0, 0, 1, 0, 0, 15, 255, 248, 0, 0, 1, 181, 143, 255, 255, 64, 0, 0, 0, 1, 161, 64])

LPCM_HDR = bytes([160, 1, 0, 0, 1]) # 48k/16b/Stereo

def encode_pts(pts):
    return bytes([
        (33 + (pts // 1073741824) * 2) & 0xff,
        (pts // 4194304) % 256,
        ((pts // 32768) % 128 * 2 + 1) & 0xff,
        (pts // 128) % 256,
        (pts % 128 * 2 + 1) & 0xff
    ])

def get_formal_pack_bytes(pts):
    scr = pts
    return bytes([
        0, 0, 1, 186,
        (64 + (scr // 1073741824) * 4 + 4 + (scr // 134217728) % 4) & 0xff,
        (scr // 524288) % 256,
        ((scr // 2048) % 128 * 4 + 4 + (scr // 512) % 4) & 0xff,
        (scr // 2) % 256,
        (scr % 2 * 128 + 1) & 0xff,
        1, 0, 1, 129, 0 
    ])

def write_pes(f, sid, payload, pts, is_lpcm=False):
    f.write(get_formal_pack_bytes(pts))
    extra_len = len(LPCM_HDR) if is_lpcm else 0
    plen = len(payload) + 3 + 5 + extra_len
    f.write(bytes([0, 0, 1, sid, plen >> 8, plen & 0xff, 0x80, 0x80, 0x05]))
    f.write(encode_pts(pts))
    if is_lpcm: f.write(LPCM_HDR)
    f.write(payload)

def get_audio_data_and_duration(vo_path):
    if not os.path.exists(vo_path): return np.zeros((48000, 2), dtype=np.int16), 1.0
    sr, data = wavfile.read(vo_path)
    if data.dtype == np.int16: data = data.astype(np.float32) / 32768.0
    if sr != 48000:
        tmp_in, tmp_out = "temp_in.wav", "temp_out.wav"
        wavfile.write(tmp_in, sr, (data * 32767).astype(np.int16))
        subprocess.run(["ffmpeg", "-y", "-i", tmp_in, "-ar", "48000", tmp_out], capture_output=True)
        sr, data = wavfile.read(tmp_out); data = data.astype(np.float32) / 32768.0
        os.remove(tmp_in); os.remove(tmp_out)
    if len(data.shape) == 1: data = np.stack([data, data], axis=1)
    return (data * 32767).astype(np.int16), len(data) / 48000.0

def generate_formal_mpeg2(assets_dir, output_file):
    scenes = [
        "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign", "05_gate_lice",
        "06_tiny_seat", "07_crying_baby", "08_seat_recline", "09_turbulence", "10_lost_suitcase"
    ]
    with open(output_file, "wb") as f:
        pts = 90000
        for i, s_id in enumerate(scenes):
            audio, duration = get_audio_data_and_duration(f"{assets_dir}/voice/vo_{i:03d}.wav")
            num_frames = int(duration * 25)
            if num_frames == 0: num_frames = 1
            audio_bytes = audio.tobytes()
            bytes_per_frame = len(audio_bytes) // num_frames
            for fr in range(num_frames):
                frame_pts = pts + int(fr * 90000 / 25)
                write_pes(f, 0xE0, FORMAL_CORE_BLOCK, frame_pts)
                a_start = fr * bytes_per_frame
                a_end = a_start + bytes_per_frame if fr < num_frames - 1 else len(audio_bytes)
                a_chunk = audio_bytes[a_start:a_end]
                if a_chunk: write_pes(f, 0xBD, a_chunk, frame_pts, is_lpcm=True)
            pts += int(duration * 90000)
        f.write(bytes([0, 0, 1, 183])) # SEQ_END
    print(f"Saved 1-1 aligned MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")
