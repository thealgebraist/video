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
#define DURATION 10

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
    avformat_write_header(oc, NULL);

    // Load Image using FFmpeg pipe/format
    AVFormatContext *ic = NULL;
    avformat_open_input(&ic, "../aigen/airport/assets_airport/images/01_security_line.png", NULL, NULL);
    avformat_find_stream_info(ic, NULL);
    const AVCodec *icodec = avcodec_find_decoder(ic->streams[0]->codecpar->codec_id);
    AVCodecContext *ictx = avcodec_alloc_context3(icodec);
    avcodec_parameters_to_context(ictx, ic->streams[0]->codecpar);
    avcodec_open2(ictx, icodec, NULL);

    AVFrame *iframe = av_frame_alloc();
    AVPacket *ipkt = av_packet_alloc();
    av_read_frame(ic, ipkt);
    avcodec_send_packet(ictx, ipkt);
    avcodec_receive_frame(ictx, iframe);

    // Convert to YUV420P
    struct SwsContext *sws = sws_getContext(ictx->width, ictx->height, ictx->pix_fmt, WIDTH, HEIGHT, AV_PIX_FMT_YUV420P, SWS_BICUBIC, NULL, NULL, NULL);
    AVFrame *vframe = av_frame_alloc();
    vframe->format = vctx->pix_fmt; vframe->width = WIDTH; vframe->height = HEIGHT;
    av_frame_get_buffer(vframe, 0);
    sws_scale(sws, (const uint8_t * const *)iframe->data, iframe->linesize, 0, ictx->height, vframe->data, vframe->linesize);

    AVFrame *aframe = av_frame_alloc();
    aframe->format = actx->sample_fmt; aframe->sample_rate = actx->sample_rate;
    av_channel_layout_copy(&aframe->ch_layout, &actx->ch_layout);
    aframe->nb_samples = actx->frame_size;
    av_frame_get_buffer(aframe, 0);
    for (int ch = 0; ch < actx->ch_layout.nb_channels; ch++) memset(aframe->data[ch], 0, aframe->nb_samples * sizeof(float));

    AVPacket *pkt = av_packet_alloc();
    int64_t v_pts = 0, a_pts = 0;
    while (v_pts < DURATION * FPS) {
        vframe->pts = v_pts++;
        avcodec_send_frame(vctx, vframe);
        while (avcodec_receive_packet(vctx, pkt) == 0) {
            av_packet_rescale_ts(pkt, vctx->time_base, vst->time_base);
            pkt->stream_index = vst->index;
            av_interleaved_write_frame(oc, pkt);
            av_packet_unref(pkt);
        }
        while (av_rescale_q(a_pts, actx->time_base, vctx->time_base) < v_pts) {
            aframe->pts = a_pts; a_pts += aframe->nb_samples;
            avcodec_send_frame(actx, aframe);
            while (avcodec_receive_packet(actx, pkt) == 0) {
                av_packet_rescale_ts(pkt, actx->time_base, ast->time_base);
                pkt->stream_index = ast->index;
                av_interleaved_write_frame(oc, pkt);
                av_packet_unref(pkt);
            }
        }
    }

    av_write_trailer(oc);
    avio_closep(&oc->pb);
    avformat_free_context(oc);
    return 0;
}