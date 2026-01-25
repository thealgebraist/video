import os
import subprocess
import numpy as np
import scipy.io.wavfile as wavfile

# Header bytes generated from verified Coq mpeg2_spec model:
SEQ_HDR = bytes([0, 0, 1, 179, 80, 2, 208, 51, 255, 255, 226, 40])
SEQ_EXT = bytes([0, 0, 1, 181, 20, 168, 0, 1, 0, 0])
GOP_HDR = bytes([0, 0, 1, 184, 0, 8, 0, 0])
PIC_HDR = bytes([0, 0, 1, 0, 0, 8, 255, 248])
PIC_EXT = bytes([0, 0, 1, 181, 143, 255, 243, 65, 128])
SEQ_END = bytes([0, 0, 1, 183])

PES_COMMON_HDR = bytes([128, 128, 5]) 
LPCM_HDR = bytes([160, 1, 0, 0, 1])

def encode_pts(pts):
    return bytes([
        (33 + (pts // 1073741824) * 2) & 0xff,
        (pts // 4194304) % 256,
        (((pts // 16384) % 128) * 2 + 1) & 0xff,
        (pts // 64) % 256,
        ((pts % 64) * 2 + 1) & 0xff
    ])

def write_pack_header(f, pts):
    f.write(bytes([0, 0, 1, 186]))
    scr = pts 
    f.write(bytes([0x44 | ((scr >> 30) & 7) << 1, (scr >> 22) & 0xff, ((scr >> 15) & 0x7f) << 1 | 1, (scr >> 7) & 0xff, (scr & 0x7f) << 1 | 1, 0x01]))
    f.write(bytes([0x01, 0x00])) 

def write_pes(f, sid, payload, pts, is_lpcm=False):
    write_pack_header(f, pts)
    extra_len = len(LPCM_HDR) if is_lpcm else 0
    plen = len(payload) + 3 + 5 + extra_len
    f.write(bytes([0, 0, 1, sid]))
    f.write(bytes([plen >> 8, plen & 0xff]))
    f.write(PES_COMMON_HDR)
    f.write(encode_pts(pts))
    if is_lpcm: f.write(LPCM_HDR)
    f.write(payload)

def get_audio_data_and_duration(vo_path):
    if not os.path.exists(vo_path):
        return np.zeros((48000, 2), dtype=np.int16), 1.0
    sr, data = wavfile.read(vo_path)
    if data.dtype == np.int16: data = data.astype(np.float32) / 32768.0
    
    # Resample to 48k if needed
    if sr != 48000:
        tmp_in, tmp_out = "temp_in.wav", "temp_out.wav"
        wavfile.write(tmp_in, sr, (data * 32767).astype(np.int16))
        subprocess.run(["ffmpeg", "-y", "-i", tmp_in, "-ar", "48000", tmp_out], capture_output=True)
        sr, data = wavfile.read(tmp_out); data = data.astype(np.float32) / 32768.0
        os.remove(tmp_in); os.remove(tmp_out)
    
    if len(data.shape) == 1: data = np.stack([data, data], axis=1)
    duration = len(data) / 48000.0
    return (data * 32767).astype(np.int16), duration

def generate_formal_mpeg2(assets_dir, output_file):
    scenes = [
        "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign", "05_gate_lice",
        "06_tiny_seat", "07_crying_baby", "08_seat_recline", "09_turbulence", "10_lost_suitcase"
    ]
    
    with open(output_file, "wb") as f:
        pts = 90000
        for i, s_id in enumerate(scenes):
            vo_path = f"{assets_dir}/voice/vo_{i:03d}.wav"
            audio, duration = get_audio_data_and_duration(vo_path)
            
            num_frames = int(duration * 25)
            if num_frames == 0: num_frames = 1
            
            audio_bytes = audio.tobytes()
            bytes_per_frame = len(audio_bytes) // num_frames
            
            print(f"Processing {s_id}: {duration:.2f}s ({num_frames} frames)")
            
            for fr in range(num_frames):
                frame_pts = pts + int(fr * 90000 / 25)
                # Video Packet
                write_pes(f, 0xE0, SEQ_HDR + SEQ_EXT + GOP_HDR + PIC_HDR + PIC_EXT + bytes([0, 0, 1, 1, 8, 0]), frame_pts)
                
                # Audio Chunk for this frame
                a_start = fr * bytes_per_frame
                a_end = a_start + bytes_per_frame if fr < num_frames - 1 else len(audio_bytes)
                a_chunk = audio_bytes[a_start:a_end]
                if a_chunk:
                    write_pes(f, 0xBD, a_chunk, frame_pts, is_lpcm=True)
            
            pts += int(duration * 90000)
            
        f.write(SEQ_END)
    print(f"Saved duration-accurate MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")