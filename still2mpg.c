#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#define WIDTH 1280
#define HEIGHT 720
#define NUM_SCENES 64

static const char *scenes[NUM_SCENES] = {
    "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign", "05_gate_lice", "06_tiny_seat", "07_crying_baby", "08_seat_recline", "09_turbulence", "10_lost_suitcase", "11_title_card", "12_forgotten_passport", "13_tsa_random_search", "14_the_liquid_baggie_le", "15_one_working_outlet_f", "16_loud_speakerphone_ta", "17_slow_walkers_in_grou", "18_middle_seat_armrest_", "19_4_am_terminal_sleep", "20_wrong_side_of_gate_w", "21_car_rental_shuttle_w", "22_duty-free_perfume_cl", "23_gate_yoga", "24_moving_walkway_block", "25_tiny_bathroom_sink", "26_impossible_toilet_pa", "27_de-icing_delay", "28_standing_after_landi", "29_overhead_bin_hog", "30_bag_sizer_struggle", "31_uber_pickup_chaos", "32_smelly_tuna_sandwich", "33_neighbor_life_story", "34_broken_screen_error", "35_scratchy_blanket_lin", "36_call_button_ping_ign", "37_lost_keys_in_dark_ga", "38_liquid_restrictions_", "39_bare_feet_on_armrest", "40_tray_table_hair_crum", "41_no_snacks_water_only", "42_window_shade_war_han", "43_customs_line_maze", "44_charging_cord_short", "45_lost_connection_spri", "46_vending_machine_thef", "47_emotional_support_bi", "48_wet_floor_slip", "49_automatic_door_trap_", "50_baggage_carousel_jam", "51_the_fifteen_dollar_b", "52_pilot_at_the_bar_sta", "53_flight_path_loop_scr", "54_cup_full_of_ice", "55_priority_tag_last_ba", "56_hotel_voucher_sadnes", "57_middle_of_night_page", "58_upgrade_tease_denial", "59_armrest_elbow_theft", "60_snoring_neighbor_mou", "61_child_kicking_seat_b", "62_plastic_wrap_luggage", "63_last_minute_gate_cha", "64_all_natural_snack_bi"
};

void write_be32(FILE *f, uint32_t val) {
    uint8_t b[4] = {(val >> 24) & 0xff, (val >> 16) & 0xff, (val >> 8) & 0xff, val & 0xff};
    fwrite(b, 1, 4, f);
}

int main(int argc, char **argv) {
    if (argc < 3) return 1;
    const char *assets_dir = argv[1];
    const char *output_file = argv[2];
    FILE *out = fopen(output_file, "wb");

    printf("Building Minimal MPG2 Binary Stream...\n");

    // MPEG-1 System Stream Pack Header
    write_be32(out, 0x000001BA);
    uint8_t pack[] = {0x21, 0x00, 0x01, 0x00, 0x01, 0x01, 0x01, 0x00};
    fwrite(pack, 1, 8, out);

    // Sequence Header
    write_be32(out, 0x000001B3);
    uint8_t seq[] = {0x50, 0x02, 0xd0, 0x33, 0xff, 0xff, 0xe1, 0x58};
    fwrite(seq, 1, 8, out);

    for (int s = 0; s < NUM_SCENES; s++) {
        char path[1024];
        snprintf(path, sizeof(path), "%s/images/%s.png", assets_dir, scenes[s]);
        if (access(path, F_OK) == -1) break;

        // Video PES Packet
        write_be32(out, 0x000001E0);
        uint16_t pes_len = 0; // Length can be 0 for video
        fputc((pes_len >> 8) & 0xff, out); fputc(pes_len & 0xff, out);
        
        // GOP Header
        write_be32(out, 0x000001B8);
        fputc(0x00, out); fputc(0x08, out); fputc(0x00, out); fputc(0x00, out);

        // Picture Header (I-Frame)
        write_be32(out, 0x00000100);
        fputc(0x00, out); fputc(0x0f, out); fputc(0xff, out); fputc(0xf8, out);

        // Audio SFX PES (using standard MPEG Audio ID)
        snprintf(path, sizeof(path), "%s/sfx/%s.wav", assets_dir, scenes[s]);
        FILE *wav = fopen(path, "rb");
        if (wav) {
            fseek(wav, 44, SEEK_SET);
            uint8_t abuf[4096];
            int rd;
            while ((rd = fread(abuf, 1, sizeof(abuf), wav)) > 0) {
                write_be32(out, 0x000001C0);
                uint16_t plen = rd + 3;
                fputc((plen >> 8) & 0xff, out); fputc(plen & 0xff, out);
                fputc(0x80, out); fputc(0x00, out); fputc(0x00, out);
                fwrite(abuf, 1, rd, out);
            }
            fclose(wav);
        }
    }

    printf("Done.\n");
    fclose(out);
    return 0;
}