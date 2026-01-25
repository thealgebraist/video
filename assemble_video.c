#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>
#include <libavutil/avutil.h>
#include <libavutil/imgutils.h>
#include <libavutil/opt.h>
#include <libavutil/channel_layout.h>
#include <libswresample/swresample.h>
#include <libswscale/swscale.h>

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#define WIDTH 1280
#define HEIGHT 720
#define FPS 25
#define NUM_SCENES 64
#define SAMPLE_RATE 44100

static const char *scenes[NUM_SCENES] = {
    "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign", "05_gate_lice", "06_tiny_seat", "07_crying_baby", "08_seat_recline", "09_turbulence", "10_lost_suitcase", "11_title_card", "12_forgotten_passport", "13_tsa_random_search", "14_the_liquid_baggie_le", "15_one_working_outlet_f", "16_loud_speakerphone_ta", "17_slow_walkers_in_grou", "18_middle_seat_armrest_", "19_4_am_terminal_sleep", "20_wrong_side_of_gate_w", "21_car_rental_shuttle_w", "22_duty-free_perfume_cl", "23_gate_yoga", "24_moving_walkway_block", "25_tiny_bathroom_sink", "26_impossible_toilet_pa", "27_de-icing_delay", "28_standing_after_landi", "29_overhead_bin_hog", "30_bag_sizer_struggle", "31_uber_pickup_chaos", "32_smelly_tuna_sandwich", "33_neighbor_life_story", "34_broken_screen_error", "35_scratchy_blanket_lin", "36_call_button_ping_ign", "37_lost_keys_in_dark_ga", "38_liquid_restrictions_", "39_bare_feet_on_armrest", "40_tray_table_hair_crum", "41_no_snacks_water_only", "42_window_shade_war_han", "43_customs_line_maze", "44_charging_cord_short", "45_lost_connection_spri", "46_vending_machine_thef", "47_emotional_support_bi", "48_wet_floor_slip", "49_automatic_door_trap_", "50_baggage_carousel_jam", "51_the_fifteen_dollar_b", "52_pilot_at_the_bar_sta", "53_flight_path_loop_scr", "54_cup_full_of_ice", "55_priority_tag_last_ba", "56_hotel_voucher_sadnes", "57_middle_of_night_page", "58_upgrade_tease_denial", "59_armrest_elbow_theft", "60_snoring_neighbor_mou", "61_child_kicking_seat_b", "62_plastic_wrap_luggage", "63_last_minute_gate_cha", "64_all_natural_snack_bi"
};

typedef struct {
    float *data;
    int nb_samples;
} AudioBuffer;

AudioBuffer load_audio(const char *filename) {
    AudioBuffer buf = {NULL, 0};
    AVFormatContext *fmt_ctx = NULL;
    if (avformat_open_input(&fmt_ctx, filename, NULL, NULL) < 0) return buf;
    if (avformat_find_stream_info(fmt_ctx, NULL) < 0) { avformat_close_input(&fmt_ctx); return buf; }
    int stream_idx = av_find_best_stream(fmt_ctx, AVMEDIA_TYPE_AUDIO, -1, -1, NULL, 0);
    if (stream_idx < 0) { avformat_close_input(&fmt_ctx); return buf; }
    AVCodecParameters *codecpar = fmt_ctx->streams[stream_idx]->codecpar;
    const AVCodec *codec = avcodec_find_decoder(codecpar->codec_id);
    AVCodecContext *dec_ctx = avcodec_alloc_context3(codec);
    avcodec_parameters_to_context(dec_ctx, codecpar);
    avcodec_open2(dec_ctx, codec, NULL);
    SwrContext *swr = NULL;
    AVChannelLayout out_ch_layout = AV_CHANNEL_LAYOUT_STEREO;
    swr_alloc_set_opts2(&swr, &out_ch_layout, AV_SAMPLE_FMT_FLT, SAMPLE_RATE, &dec_ctx->ch_layout, dec_ctx->sample_fmt, dec_ctx->sample_rate, 0, NULL);
    swr_init(swr);
    AVPacket *pkt = av_packet_alloc();
    AVFrame *frame = av_frame_alloc();
    int capacity = 1024 * 1024;
    buf.data = malloc(capacity * sizeof(float) * 2);
    while (av_read_frame(fmt_ctx, pkt) >= 0) {
        if (pkt->stream_index == stream_idx) {
            if (avcodec_send_packet(dec_ctx, pkt) == 0) {
                while (avcodec_receive_frame(dec_ctx, frame) == 0) {
                    if (buf.nb_samples + frame->nb_samples > capacity) {
                        capacity *= 2;
                        buf.data = realloc(buf.data, capacity * sizeof(float) * 2);
                    }
                    float *out[] = { buf.data + buf.nb_samples * 2 };
                    swr_convert(swr, (uint8_t**)out, frame->nb_samples, (const uint8_t**)frame->data, frame->nb_samples);
                    buf.nb_samples += frame->nb_samples;
                }
            }
        }
        av_packet_unref(pkt);
    }
    av_frame_free(&frame); av_packet_free(&pkt); swr_free(&swr); avcodec_free_context(&dec_ctx); avformat_close_input(&fmt_ctx);
    return buf;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "Usage: %s <assets_dir> <output_mp4>\n", argv[0]); return 1; }
    const char *assets_dir = argv[1];
    const char *output_file = argv[2]
;

    printf("--- Analyzing Audio Durations ---\n");
    int scene_offsets[NUM_SCENES + 1];
    scene_offsets[0] = 0;
    
    AudioBuffer sfx_bufs[NUM_SCENES];
    AudioBuffer vo_bufs[NUM_SCENES];
    
    char path[1024];
    for (int s = 0; s < NUM_SCENES; s++) {
        snprintf(path, sizeof(path), "%s/sfx/%s.wav", assets_dir, scenes[s]);
        sfx_bufs[s] = load_audio(path);
        snprintf(path, sizeof(path), "%s/voice/vo_%03d.wav", assets_dir, s);
        vo_bufs[s] = load_audio(path);
        
        int sfx_len = sfx_bufs[s].nb_samples;
        int vo_len = vo_bufs[s].nb_samples;
        int max_len = (sfx_len > vo_len) ? sfx_len : vo_len;
        
        if (max_len < SAMPLE_RATE) max_len = SAMPLE_RATE;
        
        scene_offsets[s+1] = scene_offsets[s] + max_len;
        printf("\rAnalyzed Scene %d/%d: %d samples", s+1, NUM_SCENES, max_len); fflush(stdout);
    }
    printf("\n");

    long long total_samples = scene_offsets[NUM_SCENES];
    float *mixed_audio = calloc(total_samples * 2, sizeof(float));

    printf("--- Mixing Audio Tracks ---\n");
    for (int s = 0; s < NUM_SCENES; s++) {
        int offset = scene_offsets[s];
        if (sfx_bufs[s].data) {
            for (int i = 0; i < sfx_bufs[s].nb_samples; i++) {
                mixed_audio[(offset + i)*2] += sfx_bufs[s].data[i*2] * 0.5f;
                mixed_audio[(offset + i)*2+1] += sfx_bufs[s].data[i*2+1] * 0.5f;
            }
            free(sfx_bufs[s].data);
        }
        if (vo_bufs[s].data) {
            for (int i = 0; i < vo_bufs[s].nb_samples; i++) {
                mixed_audio[(offset + i)*2] += vo_bufs[s].data[i*2] * 2.0f;
                mixed_audio[(offset + i)*2+1] += vo_bufs[s].data[i*2+1] * 2.0f;
            }
            free(vo_bufs[s].data);
        }
    }

    snprintf(path, sizeof(path), "%s/music/airport_theme.wav", assets_dir);
    AudioBuffer music = load_audio(path);
    if (music.data) {
        for (int i = 0; i < total_samples; i++) {
            int music_idx = i % music.nb_samples;
            mixed_audio[i*2] += music.data[music_idx*2] * 0.3f;
            mixed_audio[i*2+1] += music.data[music_idx*2+1] * 0.3f;
        }
        free(music.data);
    }

    printf("--- Encoding Video and Audio ---\n");
    AVFormatContext *oc = NULL;
    avformat_alloc_output_context2(&oc, NULL, NULL, output_file);
    const AVCodec *vcodec = avcodec_find_encoder(AV_CODEC_ID_H264);
    AVStream *vst = avformat_new_stream(oc, vcodec);
    AVCodecContext *vctx = avcodec_alloc_context3(vcodec);
    vctx->width = WIDTH; vctx->height = HEIGHT;
    vctx->time_base = (AVRational){1, FPS};
    vctx->framerate = (AVRational){FPS, 1};
    vctx->pix_fmt = AV_PIX_FMT_YUV420P;
    vctx->gop_size = 12;
    av_opt_set(vctx->priv_data, "preset", "slow", 0);
    vctx->bit_rate = 8000000;
    if (oc->oformat->flags & AVFMT_GLOBALHEADER) vctx->flags |= AV_CODEC_FLAG_GLOBAL_HEADER;
    avcodec_open2(vctx, vcodec, NULL);
    avcodec_parameters_from_context(vst->codecpar, vctx);

    const AVCodec *acodec = avcodec_find_encoder(AV_CODEC_ID_AAC);
    AVStream *ast = avformat_new_stream(oc, acodec);
    AVCodecContext *actx = avcodec_alloc_context3(acodec);
    actx->sample_fmt = acodec->sample_fmts[0];
    actx->bit_rate = 192000; actx->sample_rate = SAMPLE_RATE;
    AVChannelLayout out_ch_layout = AV_CHANNEL_LAYOUT_STEREO;
    av_channel_layout_copy(&actx->ch_layout, &out_ch_layout);
    if (oc->oformat->flags & AVFMT_GLOBALHEADER) actx->flags |= AV_CODEC_FLAG_GLOBAL_HEADER;
    avcodec_open2(actx, acodec, NULL);
    avcodec_parameters_from_context(ast->codecpar, actx);

    avio_open(&oc->pb, output_file, AVIO_FLAG_WRITE);
    avformat_write_header(oc, NULL);

    AVFrame *vframe = av_frame_alloc();
    vframe->format = vctx->pix_fmt; vframe->width = WIDTH; vframe->height = HEIGHT;
    av_frame_get_buffer(vframe, 32);
    struct SwsContext *sws = sws_getContext(WIDTH, HEIGHT, AV_PIX_FMT_RGB24, WIDTH, HEIGHT, AV_PIX_FMT_YUV420P, SWS_BICUBIC, NULL, NULL, NULL);

    int total_frames = (int)((double)total_samples / SAMPLE_RATE * FPS);
    unsigned char *img_data = NULL;
    int last_scene = -1;

    for (int f = 0; f < total_frames; f++) {
        long long current_sample = (long long)((double)f / FPS * SAMPLE_RATE);
        int scene_idx = 0;
        while (scene_idx < NUM_SCENES - 1 && current_sample >= scene_offsets[scene_idx+1]) {
            scene_idx++;
        }
        
        if (scene_idx != last_scene) {
            if (img_data) stbi_image_free(img_data);
            int w, h, n;
            snprintf(path, sizeof(path), "%s/images/%s.png", assets_dir, scenes[scene_idx]);
            img_data = stbi_load(path, &w, &h, &n, 3);
            last_scene = scene_idx;
            printf("\rEncoding Scene %d/%d: %s", scene_idx+1, NUM_SCENES, scenes[scene_idx]); fflush(stdout);
        }

        if (img_data) {
            const uint8_t * const src_data[1] = { (const uint8_t *)img_data };
            const int in_linesize[1] = { 3 * WIDTH };
            sws_scale(sws, src_data, in_linesize, 0, HEIGHT, vframe->data, vframe->linesize);
        } else {
            memset(vframe->data[0], 0, vframe->linesize[0] * HEIGHT);
            memset(vframe->data[1], 128, vframe->linesize[1] * HEIGHT/2);
            memset(vframe->data[2], 128, vframe->linesize[2] * HEIGHT/2);
        }
        
        vframe->pts = f;
        avcodec_send_frame(vctx, vframe);
        AVPacket *pkt = av_packet_alloc();
        while (avcodec_receive_packet(vctx, pkt) == 0) {
            av_packet_rescale_ts(pkt, vctx->time_base, vst->time_base);
            pkt->stream_index = vst->index;
            av_interleaved_write_frame(oc, pkt);
            av_packet_unref(pkt);
        }
        av_packet_free(&pkt);
    }
    if (img_data) stbi_image_free(img_data);

    printf("\n--- Finalizing ---\n");
    avcodec_send_frame(vctx, NULL);
    AVPacket *pkt = av_packet_alloc();
    while (avcodec_receive_packet(vctx, pkt) == 0) {
        av_packet_rescale_ts(pkt, vctx->time_base, vst->time_base);
        pkt->stream_index = vst->index;
        av_interleaved_write_frame(oc, pkt);
        av_packet_unref(pkt);
    }

    AVFrame *aframe = av_frame_alloc();
    aframe->nb_samples = actx->frame_size;
    aframe->format = actx->sample_fmt;
    av_channel_layout_copy(&aframe->ch_layout, &actx->ch_layout);
    av_frame_get_buffer(aframe, 0);
    SwrContext *aswr = NULL;
    swr_alloc_set_opts2(&aswr, &actx->ch_layout, actx->sample_fmt, actx->sample_rate, &out_ch_layout, AV_SAMPLE_FMT_FLT, SAMPLE_RATE, 0, NULL);
    swr_init(aswr);

    int audio_pts = 0;
    for (int i = 0; i < total_samples; i += actx->frame_size) {
        int nb = (total_samples - i < actx->frame_size) ? (int)(total_samples - i) : actx->frame_size;
        float *in_ptr = mixed_audio + i * 2;
        const uint8_t *in[] = { (const uint8_t*)in_ptr };
        swr_convert(aswr, aframe->data, actx->frame_size, in, nb);
        aframe->pts = av_rescale_q(audio_pts, (AVRational){1, actx->sample_rate}, actx->time_base);
        audio_pts += nb;
        avcodec_send_frame(actx, aframe);
        while (avcodec_receive_packet(actx, pkt) == 0) {
            av_packet_rescale_ts(pkt, actx->time_base, ast->time_base);
            pkt->stream_index = ast->index;
            av_interleaved_write_frame(oc, pkt);
            av_packet_unref(pkt);
        }
    }
    avcodec_send_frame(actx, NULL);
    while (avcodec_receive_packet(actx, pkt) == 0) {
        av_packet_rescale_ts(pkt, actx->time_base, ast->time_base);
        pkt->stream_index = ast->index;
        av_interleaved_write_frame(oc, pkt);
        av_packet_unref(pkt);
    }
    av_packet_free(&pkt); av_write_trailer(oc); avio_closep(&oc->pb); avformat_free_context(oc); free(mixed_audio);
    return 0;
}
