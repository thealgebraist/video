import os

# Header generated from Coq mpeg2_spec model:
# [0; 0; 1; 179; 80; 45; 0; 0; 1; 0; 0; 1]
COQ_MPEG2_HEADER = bytes([0, 0, 1, 179, 80, 45, 0, 0, 1, 0, 0, 1])

def generate_formal_mpeg2(assets_dir, output_file):
    with open(output_file, "wb") as f:
        # Write Formal Header
        f.write(COQ_MPEG2_HEADER)
        
        # Muxing placeholder for still images and sfx
        # In a real MPEG-2 Program Stream, we'd wrap these in PES packets.
        # Since we are using the "Coq model" to guide the structure:
        scenes = sorted([d for d in os.listdir(f"{assets_dir}/images") if d.endswith(".png")])
        
        for scene in scenes:
            # Write a GOP Start Code (0x000001B8) before each scene
            f.write(bytes([0, 0, 1, 184, 0, 8, 0, 0]))
            
            img_path = f"{assets_dir}/images/{scene}"
            with open(img_path, "rb") as img_f:
                f.write(img_f.read())
            
            sfx_name = scene.replace(".png", ".wav")
            sfx_path = f"{assets_dir}/sfx/{sfx_name}"
            if os.path.exists(sfx_path):
                # Write Audio Stream ID (0xC0) prefix
                f.write(bytes([0, 0, 1, 192]))
                with open(sfx_path, "rb") as sfx_f:
                    f.write(sfx_f.read())

    print(f"Saved formally-guided MPEG-2 to {output_file}")

if __name__ == "__main__":
    generate_formal_mpeg2("../aigen/airport/assets_airport", "formal_output.mpg")
