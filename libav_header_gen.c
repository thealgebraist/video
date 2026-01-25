#include <libavcodec/avcodec.h>
#include <stdio.h>

int main() {
    const AVCodec *codec = avcodec_find_encoder_by_name("mpeg2video");
    AVCodecContext *c = avcodec_alloc_context3(codec);
    c->width = 1280;
    c->height = 720;
    c->time_base = (AVRational){1, 25};
    c->framerate = (AVRational){25, 1};
    c->pix_fmt = AV_PIX_FMT_YUV420P;
    c->bit_rate = 4000000;
    c->gop_size = 1; // Force header every frame
    avcodec_open2(c, codec, NULL);

    AVFrame *frame = av_frame_alloc();
    frame->format = c->pix_fmt;
    frame->width  = c->width;
    frame->height = c->height;
    av_frame_get_buffer(frame, 0);

    AVPacket *pkt = av_packet_alloc();
    int found = 0;
    for (int fr=0; fr<5 && !found; fr++) {
        avcodec_send_frame(c, frame);
        while (avcodec_receive_packet(c, pkt) == 0) {
            for (int i = 0; i < pkt->size - 12; i++) {
                if (pkt->data[i] == 0x00 && pkt->data[i+1] == 0x00 && 
                    pkt->data[i+2] == 0x01 && pkt->data[i+3] == 0xb3) {
                    for (int j=0; j<12; j++) printf("%d ", pkt->data[i+j]);
                    printf("\n");
                    found = 1;
                    break;
                }
            }
            av_packet_unref(pkt);
        }
    }

    av_packet_free(&pkt);
    av_frame_free(&frame);
    avcodec_free_context(&c);
    return 0;
}