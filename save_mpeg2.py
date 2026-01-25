import os
import subprocess
import numpy as np
import scipy.io.wavfile as wavfile

# Header bytes generated from verified Coq mpeg2_spec model:
SEQ_HDR = bytes([0, 0, 1, 179, 80, 2, 208, 19, 9, 196, 32, 160])
GOP_HDR = bytes([0, 0, 1, 184, 0, 8, 0, 0])
PIC_HDR = bytes([0, 0, 1, 0, 0, 8, 255, 248])
SEQ_END = bytes([0, 0, 1, 183])

# PES Prefix from Coq: [0; 0; 1; sid; len_h; len_l; 128; 128; 5; ...]
PES_COMMON_HDR = bytes([128, 128, 5]) 

# LPCM Header from Coq (48k/16b/Stereo): [160; 1; 0; 0; 1]
LPCM_HDR = bytes([160, 1, 0, 0, 1])

def encode_pts(pts):
    return bytes([
        0x21 | ((pts >> 30) & 7) << 1,
        (pts >> 22) & 0xff,
        ((pts >> 15) & 0x7f) << 1 | 1,
        (pts >> 7) & 0xff,
        (pts & 0x7f) << 1 | 1
    ])

def write_pack_header(f, pts):
    f.write(bytes([0, 0, 1, 186]))
    scr = pts 
    f.write(bytes([0x44 | ((scr >> 30) & 7) << 1, (scr >> 22) & 0xff, ((scr >> 15) & 0x7f) << 1 | 1, (scr >> 7) & 0xff, (scr & 0x7f) << 1 | 1, 0x01]))
    f.write(bytes([0x01, 0x00])) 

def write_pes(f, sid, payload, pts, is_lpcm=False):
    write_pack_header(f, pts)
    extra_len = len(LPCM_HDR) if is_lpcm else 0
    # Header: prefix(3) + flags(3) + pts(5) + extra
    plen = len(payload) + 3 + 5 + extra_len
    f.write(bytes([0, 0, 1, sid]))
    f.write(bytes([plen >> 8, plen & 0xff]))
    f.write(PES_COMMON_HDR)
    f.write(encode_pts(pts))
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
            sr, data = wavfile.read(tmp_out)
            data = data.astype(np.float32) / 32768.0
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
        scenes = ["01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign"]
        pts = 90000
        for i, s_id in enumerate(scenes):
            audio = resample_and_mix(assets_dir, s_id, i)
            dur_s = len(audio) / 48000.0
            num_frames = int(dur_s * 25)
            # Interleave video frames and audio chunks
            audio_bytes = audio.tobytes()
            chunk_size = 4000 
            for fr in range(num_frames):
                frame_pts = pts + int(fr * 90000 / 25)
                write_pes(f, 0xE0, SEQ_HDR + GOP_HDR + PIC_HDR + bytes([0, 0, 1, 1, 8, 0]), frame_pts)
                a_offset = fr * (len(audio_bytes) // num_frames)
                a_chunk = audio_bytes[a_offset : a_offset + (len(audio_bytes) // num_frames)]
                if a_chunk: write_pes(f, 0xBD, a_chunk, frame_pts, is_lpcm=True)
            pts += int(dur_s * 90000)
        f.write(SEQ_END)
    print(f"Saved robust formal MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")