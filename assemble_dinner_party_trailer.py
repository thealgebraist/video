import subprocess
import os
import argparse

def assemble_dinner(assets_dir, output_file):
    TOTAL_DURATION = 120
    SCENES = [
        "01_food_photo", "02_wine_snob", "03_double_dip", "04_diet_bomb", "05_phone_under_table", "06_uninvited_dog", "07_boring_story", "08_wine_spill", "09_kitchen_clutter", "10_political_fight", "11_title_card", "12_long_goodbye", "13_guest_breaks_plate", "14_shoes_off_smell_unde", "15_kid_adult_table_mess", "16_salt_shaker_theft", "17_i_brought_my_own_gue", "18_over-shared_health_i", "19_the_loud_chewer_mout", "20_stealing_spotlight_s", "21_the_un-ironic_actual", "22_truffle_hogging_scoo", "23_overcooked_meat_bric", "24_awkward_drunk_toast", "25_cold_oily_coffee_fil", "26_diet_cheat_pantry", "27_unsolicited_parentin", "28_one_more_drink_whisk", "29_tech_fix_light_off", "30_off-key_opera_singin", "31_better_made_whisper", "32_silk_napkin_in_soup", "33_forgotten_nut_allerg", "34_mismatched_plastic_s", "35_cheese_wheel_fingers", "36_crumbs_in_the_beard_", "37_offensive_satire_jok", "38_staring_at_host_part", "39_influencer_ring_ligh", "40_wrong_shrimp_fork_st", "41_i_dont_believe_guest", "42_emptying_whiskey_bot", "43_accidental_touch_kne", "44_water_on_laptop_elec", "45_is_this_organic_quer", "46_talking_mouth_full_c", "47_guest_tissues_on_ant", "48_dishes_lie_exit", "49_i_know_the_chef_lie", "50_it_is_a_bit_salty_fa", "51_staying_over_hint_bl", "52_forgot_wallet_fifth_", "53_minimalist_single_pe", "54_maximalist_table_clu", "55_mixologist_vinegar_d", "56_photographer_candid_", "57_therapist_childhood_", "58_lawyer_lease_invalid", "59_doctor_rare_disease", "60_musician_guitar_wond", "61_comedian_borat_impre", "62_foodie_foraged_by_ha", "63_local_lost_soul_sinc", "64_traveler_in_bali_sta"
    ].png"
        cmd += ["-loop", "1", "-t", str(scene_duration), "-i", img_path] if os.path.exists(img_path) else ["-f", "lavfi", "-t", str(scene_duration), "-i", "color=c=black:s=1280x720:r=25"]
    for s_id in SCENES:
        sfx_path = f"{assets_dir}/sfx/{s_id}.wav"
        cmd += ["-stream_loop", "-1", "-t", str(scene_duration), "-i", sfx_path] if os.path.exists(sfx_path) else ["-f", "lavfi", "-t", str(scene_duration), "-i", "anullsrc=r=44100:cl=stereo"]
    vo_path = f"{assets_dir}/voice/voiceover_full.wav"
    cmd += ["-i", vo_path] if os.path.exists(vo_path) else ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
    music_path = f"{assets_dir}/music/dinner_theme.wav"
    cmd += ["-i", music_path] if os.path.exists(music_path) else ["-f", "lavfi", "-t", str(TOTAL_DURATION), "-i", "anullsrc=r=44100:cl=stereo"]
    filter_complex = ""
    for i in range(len(SCENES)):
        filter_complex += f"[{i}:v]scale=8000:-1,zoompan=z='min(zoom+0.001,1.5)':d={int(scene_duration*25)}:x='iw/2-(iw/zoom/2)':y='ih/2-(ih/zoom/2)':s=1280x720[v{i}];"
    v_concat = "".join([f"[v{i}]" for i in range(len(SCENES))])
    filter_complex += f"{v_concat}concat=n={len(SCENES)}:v=1:a=0[vout];"
    sfx_mixed_outputs = ""
    for i in range(len(SCENES)):
        input_idx = len(SCENES) + i
        delay_ms = int(i * scene_duration * 1000)
        filter_complex += f"[{input_idx}:a]adelay={delay_ms}|{delay_ms}[sfx{i}];"
        sfx_mixed_outputs += f"[sfx{i}]"
    filter_complex += f"{sfx_mixed_outputs}amix=inputs={len(SCENES)}:dropout_transition=0[sfx_all];"
    vo_idx, music_idx = len(SCENES) * 2, len(SCENES) * 2 + 1
    filter_complex += f"[sfx_all]volume=0.5[sfx_final];"
    filter_complex += f"[{vo_idx}:a]volume=2.0[vo_final];"
    filter_complex += f"[{music_idx}:a]volume=0.4[music_final];"
    filter_complex += f"[sfx_final][vo_final][music_final]amix=inputs=3:duration=first:dropout_transition=0[aout]"
    cmd += ["-filter_complex", filter_complex, "-map", "[vout]", "-map", "[aout]", "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18", "-c:a", "aac", "-b:a", "320k", "-t", str(TOTAL_DURATION), output_file]
    subprocess.run(cmd, check=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--assets", type=str, default="assets_dinner", help="Path to assets directory")
    parser.add_argument("--output", type=str, default="dinner_trailer.mp4", help="Output filename")
    args = parser.parse_args()
    assemble_dinner(args.assets, args.output)
