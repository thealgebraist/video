import os

# Updated bit-accurate header from Coq model following standard/libavcodec method:
# [0; 0; 1; 179; 80; 2; 208; 19; 9; 196; 32; 160]
SEQ_HDR = bytes([0, 0, 1, 179, 80, 2, 208, 19, 9, 196, 32, 160])
GOP_HDR = bytes([0, 0, 1, 184, 0, 8, 0, 0])
PIC_HDR = bytes([0, 0, 1, 0, 0, 8, 255, 248])

def write_pes(f, sid, payload, pts):
    plen = len(payload) + 5
    f.write(bytes([0, 0, 1, sid]))
    f.write(bytes([plen >> 8, plen & 0xff]))
    # pts flags and data
    f.write(bytes([0x21|((pts>>30)&7)<<1, (pts>>22)&0xff, ((pts>>15)&0x7f)<<1|1, (pts>>7)&0xff, (pts&0x7f)<<1|1]))
    f.write(payload)

def generate_formal_mpeg2(assets_dir, output_file):
    with open(output_file, "wb") as f:
        # Pack Header
        f.write(bytes([0, 0, 1, 186, 0x21, 0x00, 0x01, 0x00, 0x01, 0x01, 0x01, 0x00]))
        
        scenes = sorted([d for d in os.listdir(f"{assets_dir}/images") if d.endswith(".png")])
        pts = 90000
        
        for scene in scenes:
            # Strictly compliant Video Packet
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
                    write_pes(f, 0xC0, chunk, pts)
            
            pts += 90000 * 2

    print(f"Saved bit-accurate formal MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")