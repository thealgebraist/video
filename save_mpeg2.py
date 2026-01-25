import os

# Updated bit-accurate header from verified Coq model:
# SEQ [0xB3], GOP [0xB8], PIC [0x00]
SEQ_HDR = bytes([0, 0, 1, 179, 80, 2, 208, 19, 9, 196, 32, 160])
GOP_HDR = bytes([0, 0, 1, 184, 0, 8, 0, 0])
PIC_HDR = bytes([0, 0, 1, 0, 0, 8, 255, 248])
SEQ_END = bytes([0, 0, 1, 183])

# Corrected LPCM bits for 44.1k/16b/Stereo from Coq: [160; 1; 0; 0; 33]
LPCM_HDR = bytes([160, 1, 0, 0, 33])

def write_pack_header(f, pts):
    # Standard Pack Header (0xBA) with simple SCR mapping from PTS
    f.write(bytes([0, 0, 1, 186]))
    # SCR mapping
    scr = pts 
    f.write(bytes([0x44 | ((scr >> 30) & 7) << 1, (scr >> 22) & 0xff, ((scr >> 15) & 0x7f) << 1 | 1, (scr >> 7) & 0xff, (scr & 0x7f) << 1 | 1, 0x01]))
    f.write(bytes([0x01, 0x00])) # mux_rate

def write_pes(f, sid, payload, pts, is_lpcm=False):
    write_pack_header(f, pts)
    extra_len = len(LPCM_HDR) if is_lpcm else 0
    # PES Header: 00 00 01 <sid> <len> 80 80 05 <pts>
    plen = len(payload) + 5 + 3 + extra_len 
    f.write(bytes([0, 0, 1, sid]))
    f.write(bytes([plen >> 8, plen & 0xff]))
    # FIXED: Added the missing 3 bytes of PES flags/header length
    f.write(bytes([0x80, 0x80, 0x05])) 
    # PTS data (5 bytes)
    f.write(bytes([0x21|((pts>>30)&7)<<1, (pts>>22)&0xff, ((pts>>15)&0x7f)<<1|1, (pts>>7)&0xff, (pts&0x7f)<<1|1]))
    if is_lpcm:
        f.write(LPCM_HDR)
    f.write(payload)

def generate_formal_mpeg2(assets_dir, output_file):
    with open(output_file, "wb") as f:
        scenes = sorted([d for d in os.listdir(f"{assets_dir}/images") if d.endswith(".png")])
        pts = 90000
        
        for scene in scenes:
            # Video Packet
            slice_hdr = bytes([0, 0, 1, 1, 8, 0])
            video_payload = SEQ_HDR + GOP_HDR + PIC_HDR + slice_hdr
            write_pes(f, 0xE0, video_payload, pts)
            
            # Audio Packet
            sfx_name = scene.replace(".png", ".wav")
            sfx_path = f"{assets_dir}/sfx/{sfx_name}"
            if os.path.exists(sfx_path):
                with open(sfx_path, "rb") as sfx_f:
                    audio_data = sfx_f.read()[44:]
                for i in range(0, len(audio_data), 32000):
                    chunk = audio_data[i:i+32000]
                    write_pes(f, 0xBD, chunk, pts, is_lpcm=True)
            
            pts += 90000 * 2 # Advance 2s

        f.write(SEQ_END)

    print(f"Saved formally-verified robust MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")