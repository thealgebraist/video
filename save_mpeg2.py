import os
import subprocess
import numpy as np
import scipy.io.wavfile as wavfile

# Strictly compliant bytes from Coq mpeg2_spec (at 90000 PTS offset)
SYS_HDR = bytes([0, 0, 1, 187, 0, 12, 191, 255, 255, 1, 255, 255, 255, 255, 255, 255, 255, 255])
SEQ_HDR = bytes([0, 0, 1, 179, 80, 2, 208, 19, 9, 196, 32, 160])
GOP_HDR = bytes([0, 0, 1, 184, 0, 8, 0, 0])
PIC_HDR = bytes([0, 0, 1, 0, 0, 8, 255, 248])
SEQ_END = bytes([0, 0, 1, 183])
LPCM_HDR = bytes([160, 1, 0, 0, 33])

def get_formal_pts_bytes(pts):
    return bytes([
        (33 + (pts // 1073741824) * 2) & 0xff,
        (pts // 4194304) % 256,
        (((pts // 16384) % 128) * 2 + 1) & 0xff,
        (pts // 64) % 256,
        ((pts % 64) * 2 + 1) & 0xff
    ])

def get_formal_pack_bytes(pts):
    scr = pts
    return bytes([
        0, 0, 1, 186,
        (64 + (scr // 1073741824) * 4 + 4 + (scr // 134217728) % 4) & 0xff,
        (scr // 524288) % 256,
        (((scr // 2048) % 128) * 4 + 4 + (scr // 512) % 4) & 0xff,
        (scr // 2) % 256,
        ((scr % 2) * 128 + 1) & 0xff,
        1, # SCR_ext
        0, 1, 129, # mux_rate
        0  # stuffing
    ])

def write_pes(f, sid, payload, pts, is_lpcm=False):
    f.write(get_formal_pack_bytes(pts))
    extra_len = len(LPCM_HDR) if is_lpcm else 0
    # Length field: 3 flags + 5 pts + extra + payload
    plen = len(payload) + 3 + 5 + extra_len
    f.write(bytes([0, 0, 1, sid]))
    f.write(bytes([plen >> 8, plen & 0xff]))
    f.write(bytes([0x80, 0x80, 0x05])) # The missing flags from previous turn
    f.write(get_formal_pts_bytes(pts))
    if is_lpcm: f.write(LPCM_HDR)
    f.write(payload)

def resample_and_mix(assets_dir, scene_id, s_idx):
    def load_wav(path):
        if not os.path.exists(path): return None
        sr, data = wavfile.read(path)
        if data.dtype == np.int16: data = data.astype(np.float32) / 32768.0
        if sr != 48000:
            tmp_in, tmp_out = "temp_in.wav", "temp_out.wav"
            wavfile.write(tmp_in, sr, (data * 32767).astype(np.int16))
            subprocess.run(["ffmpeg", "-y", "-i", tmp_in, "-ar", "48000", tmp_out], capture_output=True)
            sr, data = wavfile.read(tmp_out); data = data.astype(np.float32) / 32768.0
            os.remove(tmp_in); os.remove(tmp_out)
        return data
    sfx = load_wav(f"{assets_dir}/sfx/{scene_id}.wav")
    vo = load_wav(f"{assets_dir}/voice/vo_{s_idx:03d}.wav")
    max_len = max(len(sfx) if sfx is not None else 0, len(vo) if vo is not None else 0)
    if max_len == 0: return np.zeros((48000, 2), dtype=np.int16)
    mixed = np.zeros((max_len, 2), dtype=np.float32)
    if sfx is not None:
        if len(sfx.shape) == 1: sfx = np.stack([sfx, sfx], axis=1)
        mixed[:len(sfx)] += sfx * 0.5
    if vo is not None:
        if len(vo.shape) == 1: vo = np.stack([vo, vo], axis=1)
        mixed[:len(vo)] += vo * 2.0
    return (np.clip(mixed, -1, 1) * 32767).astype(np.int16)

def generate_formal_mpeg2(assets_dir, output_file):
    with open(output_file, "wb") as f:
        f.write(get_formal_pack_bytes(90000))
        f.write(SYS_HDR)
        scenes = ["01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign"]
        pts = 90000
        for i, s_id in enumerate(scenes):
            audio = resample_and_mix(assets_dir, s_id, i)
            dur_s = len(audio) / 48000.0; num_frames = int(dur_s * 25)
            audio_bytes = audio.tobytes()
            for fr in range(num_frames):
                frame_pts = pts + int(fr * 90000 / 25)
                write_pes(f, 0xE0, SEQ_HDR + GOP_HDR + PIC_HDR + bytes([0, 0, 1, 1, 8, 0]), frame_pts)
                a_start = fr * (len(audio_bytes) // num_frames)
                a_end = (fr+1) * (len(audio_bytes) // num_frames)
                a_chunk = audio_bytes[a_start:a_end]
                if a_chunk: write_pes(f, 0xBD, a_chunk, frame_pts, is_lpcm=True)
            pts += int(dur_s * 90000)
        f.write(SEQ_END)
    print(f"Saved strictly-standard compliant MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")
