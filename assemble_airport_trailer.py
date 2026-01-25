import subprocess
import os
import argparse

def assemble_airport(assets_dir, output_file, crf=18):
    TOTAL_DURATION = 120 # Seconds for a tight trailer
    SCENES = [
        "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign", "05_gate_lice", "06_tiny_seat", "07_crying_baby", "08_seat_recline", "09_turbulence", "10_lost_suitcase", "11_title_card", "12_forgotten_passport", "13_tsa_random_search", "14_the_liquid_baggie_le", "15_one_working_outlet_f", "16_loud_speakerphone_ta", "17_slow_walkers_in_grou", "18_middle_seat_armrest_", "19_4_am_terminal_sleep", "20_wrong_side_of_gate_w", "21_car_rental_shuttle_w", "22_duty-free_perfume_cl", "23_gate_yoga", "24_moving_walkway_block", "25_tiny_bathroom_sink", "26_impossible_toilet_pa", "27_de-icing_delay", "28_standing_after_landi", "29_overhead_bin_hog", "30_bag_sizer_struggle", "31_uber_pickup_chaos", "32_smelly_tuna_sandwich", "33_neighbor_life_story", "34_broken_screen_error", "35_scratchy_blanket_lin", "36_call_button_ping_ign", "37_lost_keys_in_dark_ga", "38_liquid_restrictions_", "39_bare_feet_on_armrest", "40_tray_table_hair_crum", "41_no_snacks_water_only", "42_window_shade_war_han", "43_customs_line_maze", "44_charging_cord_short", "45_lost_connection_spri", "46_vending_machine_thef", "47_emotional_support_bi", "48_wet_floor_slip", "49_automatic_door_trap_", "50_baggage_carousel_jam", "51_the_fifteen_dollar_b", "52_pilot_at_the_bar_sta", "53_flight_path_loop_scr", "54_cup_full_of_ice", "55_priority_tag_last_ba", "56_hotel_voucher_sadnes", "57_middle_of_night_page", "58_upgrade_tease_denial", "59_armrest_elbow_theft", "60_snoring_neighbor_mou", "61_child_kicking_seat_b", "62_plastic_wrap_luggage", "63_last_minute_gate_cha", "64_all_natural_snack_bi"
    ]
    scene_duration = TOTAL_DURATION / len(SCENES)
    
    cmd = ["ffmpeg", "-y"]
    
    # Input Images
    for s_id in SCENES:
        img_path = f"{assets_dir}/images/{s_id}.png"
        if os.path.exists(img_path):
            cmd += ["-loop", "1", "-t", str(scene_duration), "-i", img_path]
        else:
            cmd += ["-f", "lavfi", "-t", str(scene_duration), "-i", "color=c=black:s=1280x720:r=25"]
            
    # Input SFX
    for s_id in SCENES:
        sfx_path = f"{assets_dir}/sfx/{s_id}.wav"
        if os.path.exists(sfx_path):
            cmd += ["-stream_loop", "-1", "-t", str(scene_duration), "-i", sfx_path]
        else:
            cmd += ["-f", "lavfi", "-t", str(scene_duration), "-i", "anullsrc=r=44100:cl=stereo"]
            
    # Input VO
    vo_path = f"{assets_dir}/voice/voiceover_full.wav"
    if os.path.exists(vo_path):
        cmd += ["-i", vo_path]
    else:
        cmd += ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
        
    # Input Music
    music_path = f"{assets_dir}/music/airport_theme.wav"
    if os.path.exists(music_path):
        cmd += ["-i", music_path]
    else:
        cmd += ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
        
    filter_complex = ""
    # Image zoom effects
    for i in range(len(SCENES)):
        filter_complex += f"[{i}:v]scale=8000:-1,zoompan=z='min(zoom+0.001,1.5)':d={int(scene_duration*25)}:x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':s=1280x720[v{i}];"
    
    # Concatenate videos
    v_concat = "".join([f"[v{i}]" for i in range(len(SCENES))])
    filter_complex += f"{v_concat}concat=n={len(SCENES)}:v=1:a=0[vout];"
    
    # SFX delay and mix
    sfx_mixed_outputs = ""
    for i in range(len(SCENES)):
        input_idx = len(SCENES) + i
        delay_ms = int(i * scene_duration * 1000)
        filter_complex += f"[{input_idx}:a]adelay={delay_ms}|{delay_ms}[sfx{i}];"
        sfx_mixed_outputs += f"[sfx{i}]"
    
    filter_complex += f"{sfx_mixed_outputs}amix=inputs={len(SCENES)}:dropout_transition=0[sfx_all];"
    
    vo_idx = len(SCENES) * 2
    music_idx = vo_idx + 1
    
    # Final audio mix
    filter_complex += f"[sfx_all]volume=0.5[sfx_final];"
    filter_complex += f"[{vo_idx}:a]volume=2.0[vo_final];"
    filter_complex += f"[{music_idx}:a]volume=0.4[music_final];"
    filter_complex += f"[sfx_final][vo_final][music_final]amix=inputs=3:duration=first:dropout_transition=0[aout]"
    
    cmd += ["-filter_complex", filter_complex]
    cmd += ["-map", "[vout]", "-map", "[aout]"]
    cmd += [
        "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", str(crf),
        "-c:a", "aac", "-b:a", "320k",
        "-t", str(TOTAL_DURATION),
        output_file
    ]
    
    print(f"--- Executing FFMPEG Assembly (CRF: {crf}) ---")
    subprocess.run(cmd, check=True)
    print(f"--- Created {output_file} ---")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--assets", type=str, default="assets_airport", help="Path to assets directory")
    parser.add_argument("--output", type=str, default="airport_trailer.mp4", help="Output filename")
    parser.add_argument("--quality", type=float, default=None, help="Quality percentage (0-100)")
    parser.add_argument("--crf", type=int, default=18, help="FFMPEG CRF value (0-51)")
    args = parser.parse_args()
    
    crf = args.crf
    if args.quality is not None:
        # Map quality 0-100 to CRF 51-0
        crf = int(51 * (1 - args.quality / 100.0))
        
    assemble_airport(args.assets, args.output, crf=crf)