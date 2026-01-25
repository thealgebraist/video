#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>
#include <libavutil/opt.h>
#include <libavutil/imgutils.h>
#include <libavutil/channel_layout.h>
#include <libswresample/swresample.h>
#include <libswscale/swscale.h>
#include <stdio.h>

#define WIDTH 1280
#define HEIGHT 720
#define FPS 25
#define NUM_SCENES 10

static const char *image_names[NUM_SCENES] = {
    "01_security_line", "02_boot_struggle", "03_sad_sandwich", "04_delayed_sign", "05_gate_lice",
    "06_tiny_seat", "07_crying_baby", "08_seat_recline", "09_turbulence", "10_lost_suitcase"
};

int main() {
    AVFormatContext *oc = NULL;
    avformat_alloc_output_context2(&oc, NULL, "vob", "ref.mpg");

    const AVCodec *vcodec = avcodec_find_encoder_by_name("mpeg2video");
    AVStream *vst = avformat_new_stream(oc, vcodec);
    AVCodecContext *vctx = avcodec_alloc_context3(vcodec);
    vctx->width = WIDTH; vctx->height = HEIGHT;
    vctx->time_base = (AVRational){1, FPS};
    vctx->framerate = (AVRational){FPS, 1};
    vctx->pix_fmt = AV_PIX_FMT_YUV420P;
    vctx->gop_size = 12;
    vctx->bit_rate = 4000000;
    vctx->rc_buffer_size = 1835008;
    vctx->rc_max_rate = 4000000;
    vctx->flags |= AV_CODEC_FLAG_BITEXACT;
    avcodec_open2(vctx, vcodec, NULL);
    avcodec_parameters_from_context(vst->codecpar, vctx);

    const AVCodec *acodec = avcodec_find_encoder_by_name("ac3");
    AVStream *ast = avformat_new_stream(oc, acodec);
    AVCodecContext *actx = avcodec_alloc_context3(acodec);
    actx->sample_fmt = AV_SAMPLE_FMT_FLTP;
    actx->bit_rate = 64000;
    actx->sample_rate = 48000;
    AVChannelLayout ch_layout = AV_CHANNEL_LAYOUT_MONO;
    av_channel_layout_copy(&actx->ch_layout, &ch_layout);
    actx->flags |= AV_CODEC_FLAG_BITEXACT;
    avcodec_open2(actx, acodec, NULL);
    avcodec_parameters_from_context(ast->codecpar, actx);

    avio_open(&oc->pb, "ref.mpg", AVIO_FLAG_WRITE);
    if (avformat_write_header(oc, NULL) < 0) return 1;

    AVFrame *vframe = av_frame_alloc();
    vframe->format = vctx->pix_fmt; vframe->width = WIDTH; vframe->height = HEIGHT;
    av_frame_get_buffer(vframe, 0);

    AVFrame *a_out_frame = av_frame_alloc();
    a_out_frame->format = actx->sample_fmt; a_out_frame->sample_rate = actx->sample_rate;
    av_channel_layout_copy(&a_out_frame->ch_layout, &actx->ch_layout);
    a_out_frame->nb_samples = actx->frame_size;
    av_frame_get_buffer(a_out_frame, 0);

    AVPacket *pkt = av_packet_alloc();
    int64_t v_pts_offset = 0;
    int64_t a_pts = 0;

    for (int s = 0; s < NUM_SCENES; s++) {
        AVFormatContext *ac = NULL;
        char vo_path[1024];
        snprintf(vo_path, sizeof(vo_path), "../aigen/airport/assets_airport/voice/vo_%03d.wav", s);
        if (avformat_open_input(&ac, vo_path, NULL, NULL) < 0) continue;
        avformat_find_stream_info(ac, NULL);
        
        double duration = (double)ac->duration / AV_TIME_BASE;
        int num_frames = (int)(duration * FPS);
        if (num_frames == 0) num_frames = 1;
        printf("Scene %d (%s): Duration %.2fs, %d frames\n", s, image_names[s], duration, num_frames);

        const AVCodec *a_in_codec = avcodec_find_decoder(ac->streams[0]->codecpar->codec_id);
        AVCodecContext *a_in_ctx = avcodec_alloc_context3(a_in_codec);
        avcodec_parameters_to_context(a_in_ctx, ac->streams[0]->codecpar);
        avcodec_open2(a_in_ctx, a_in_codec, NULL);
        
        SwrContext *swr = NULL;
        swr_alloc_set_opts2(&swr, &actx->ch_layout, actx->sample_fmt, actx->sample_rate, &a_in_ctx->ch_layout, a_in_ctx->sample_fmt, a_in_ctx->sample_rate, 0, NULL);
        swr_init(swr);
        
        AVFrame *a_in_frame = av_frame_alloc();
        AVPacket *ipkt = av_packet_alloc();

        AVFormatContext *ic = NULL;
        char img_path[1024];
        snprintf(img_path, sizeof(img_path), "../aigen/airport/assets_airport/images/%s.png", image_names[s]);
        if (avformat_open_input(&ic, img_path, NULL, NULL) < 0) goto cleanup_audio;
        avformat_find_stream_info(ic, NULL);
        const AVCodec *icodec = avcodec_find_decoder(ic->streams[0]->codecpar->codec_id);
        AVCodecContext *ictx = avcodec_alloc_context3(icodec);
        avcodec_parameters_to_context(ictx, ic->streams[0]->codecpar);
        avcodec_open2(ictx, icodec, NULL);
        AVFrame *iframe = av_frame_alloc();
        AVPacket *img_pkt = av_packet_alloc();
        av_read_frame(ic, img_pkt);
        avcodec_send_packet(ictx, img_pkt);
        avcodec_receive_frame(ictx, iframe);
        struct SwsContext *sws = sws_getContext(ictx->width, ictx->height, ictx->pix_fmt, WIDTH, HEIGHT, AV_PIX_FMT_YUV420P, SWS_BICUBIC, NULL, NULL, NULL);
        sws_scale(sws, (const uint8_t * const *)iframe->data, iframe->linesize, 0, ictx->height, vframe->data, vframe->linesize);

        for (int f = 0; f < num_frames; f++) {
            vframe->pts = v_pts_offset + f;
            avcodec_send_frame(vctx, vframe);
            while (avcodec_receive_packet(vctx, pkt) == 0) {
                av_packet_rescale_ts(pkt, vctx->time_base, vst->time_base);
                pkt->stream_index = vst->index;
                av_interleaved_write_frame(oc, pkt);
                av_packet_unref(pkt);
            }

            while (av_rescale_q(a_pts, (AVRational){1, actx->sample_rate}, vctx->time_base) < vframe->pts + 1) {
                if (av_read_frame(ac, ipkt) >= 0) {
                    avcodec_send_packet(a_in_ctx, ipkt);
                    if (avcodec_receive_frame(a_in_ctx, a_in_frame) >= 0) {
                        swr_convert(swr, a_out_frame->data, actx->frame_size, (const uint8_t **)a_in_frame->data, a_in_frame->nb_samples);
                        a_out_frame->pts = a_pts; a_pts += actx->frame_size;
                        avcodec_send_frame(actx, a_out_frame);
                        while (avcodec_receive_packet(actx, pkt) == 0) {
                            av_packet_rescale_ts(pkt, actx->time_base, ast->time_base);
                            pkt->stream_index = ast->index;
                            av_interleaved_write_frame(oc, pkt);
                            av_packet_unref(pkt);
                        }
                    }
                    av_packet_unref(ipkt);
                } else {
                    for (int ch = 0; ch < actx->ch_layout.nb_channels; ch++) memset(a_out_frame->data[ch], 0, actx->frame_size * sizeof(float));
                    a_out_frame->pts = a_pts; a_pts += actx->frame_size;
                    avcodec_send_frame(actx, a_out_frame);
                    while (avcodec_receive_packet(actx, pkt) == 0) {
                        av_packet_rescale_ts(pkt, actx->time_base, ast->time_base);
                        pkt->stream_index = ast->index;
                        av_interleaved_write_frame(oc, pkt);
                        av_packet_unref(pkt);
                    }
                }
            }
        }
        v_pts_offset += num_frames;

        sws_freeContext(sws); av_frame_free(&iframe); av_packet_free(&img_pkt);
        avcodec_free_context(&ictx); avformat_close_input(&ic);
cleanup_audio:
        swr_free(&swr); av_frame_free(&a_in_frame); av_packet_free(&ipkt);
        avcodec_free_context(&a_in_ctx); avformat_close_input(&ac);
    }

    av_write_trailer(oc);
    avio_closep(&oc->pb);
    avformat_free_context(oc);
    return 0;
}