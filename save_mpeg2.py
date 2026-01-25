import os

# From Coq model: SEQ [0xB3], GOP [0xB8], PIC [0x00]
SEQ_HDR = bytes([0, 0, 1, 179, 80, 2, 208, 19, 9, 196, 32, 160])
GOP_HDR = bytes([0, 0, 1, 184, 0, 8, 0, 0])
PIC_HDR = bytes([0, 0, 1, 0, 0, 8, 255, 248])
SEQ_END = bytes([0, 0, 1, 183])

# From Coq encode_lpcm_header: [160; 1; 0; 0; 129] (44.1k, 16bit, Stereo)
LPCM_HDR = bytes([160, 1, 0, 0, 129])

def write_pack_header(f):
    # Standard Pack Header (0xBA)
    f.write(bytes([0, 0, 1, 186, 0x44, 0x00, 0x04, 0x00, 0x04, 0x01, 0x01, 0x00]))

def write_pes(f, sid, payload, pts, is_lpcm=False):
    write_pack_header(f)
    extra_len = len(LPCM_HDR) if is_lpcm else 0
    plen = len(payload) + 5 + extra_len
    f.write(bytes([0, 0, 1, sid]))
    f.write(bytes([plen >> 8, plen & 0xff]))
    # PTS flags and 5-byte PTS data
    f.write(bytes([0x21|((pts>>30)&7)<<1, (pts>>22)&0xff, ((pts>>15)&0x7f)<<1|1, (pts>>7)&0xff, (pts&0x7f)<<1|1]))
    if is_lpcm:
        f.write(LPCM_HDR)
    f.write(payload)

def generate_formal_mpeg2(assets_dir, output_file):
    with open(output_file, "wb") as f:
        scenes = sorted([d for d in os.listdir(f"{assets_dir}/images") if d.endswith(".png")])
        pts = 90000
        
        for scene in scenes:
            # Video Packet (one frame per scene for formal binary structure)
            slice_hdr = bytes([0, 0, 1, 1, 8, 0])
            video_payload = SEQ_HDR + GOP_HDR + PIC_HDR + slice_hdr
            write_pes(f, 0xE0, video_payload, pts)
            
            # Audio Packets (split SFX into PES chunks)
            sfx_name = scene.replace(".png", ".wav")
            sfx_path = f"{assets_dir}/sfx/{sfx_name}"
            if os.path.exists(sfx_path):
                with open(sfx_path, "rb") as sfx_f:
                    audio_data = sfx_f.read()[44:] # Skip WAV header
                # Split audio into standard PES chunks
                for i in range(0, len(audio_data), 32000):
                    chunk = audio_data[i:i+32000]
                    write_pes(f, 0xBD, chunk, pts, is_lpcm=True)
            
            pts += 90000 * 2 # Advance 2s

        f.write(SEQ_END)

    print(f"Saved strictly-packetized formal MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")
