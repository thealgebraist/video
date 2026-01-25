#include <libavformat/avformat.h>
#include <libavcodec/avcodec.h>
#include <stdio.h>

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <input_file>\n", argv[0]);
        return 1;
    }

    const char *filename = argv[1];
    AVFormatContext *fmt_ctx = NULL;

    // Open input stream and read the header
    if (avformat_open_input(&fmt_ctx, filename, NULL, NULL) < 0) {
        fprintf(stderr, "Could not open input file '%s'\n", filename);
        return 1;
    }

    // Read packets from the file to get stream information
    if (avformat_find_stream_info(fmt_ctx, NULL) < 0) {
        fprintf(stderr, "Could not find stream information\n");
        // Don't exit yet, we want to see what it *did* find
    }

    printf("Format: %s\n", fmt_ctx->iformat->name);
    printf("Duration: %ld microseconds\n", fmt_ctx->duration);
    printf("Number of streams: %u\n", fmt_ctx->nb_streams);

    for (int i = 0; i < fmt_ctx->nb_streams; i++) {
        AVStream *st = fmt_ctx->streams[i];
        AVCodecParameters *codecpar = st->codecpar;
        const AVCodec *codec = avcodec_find_decoder(codecpar->codec_id);

        printf("Stream #%d:\n", i);
        printf("  Type: %s\n", av_get_media_type_string(codecpar->codec_type));
        printf("  Codec: %s (%s)\n", 
               codec ? codec->name : "unknown",
               avcodec_get_name(codecpar->codec_id));
        printf("  ID: 0x%x\n", st->id);
        
        if (codecpar->codec_type == AVMEDIA_TYPE_VIDEO) {
            printf("  Dimensions: %dx%d\n", codecpar->width, codecpar->height);
        } else if (codecpar->codec_type == AVMEDIA_TYPE_AUDIO) {
            printf("  Sample Rate: %d\n", codecpar->sample_rate);
            printf("  Channels: %d\n", codecpar->ch_layout.nb_channels);
            printf("  Format: %s\n", av_get_sample_fmt_name(codecpar->format));
        }
    }

    AVPacket *pkt = av_packet_alloc();
    int count = 0;
    printf("\n--- Packet Log (First 20) ---\n");
    while (av_read_frame(fmt_ctx, pkt) >= 0 && count < 20) {
        printf("Packet %d: Stream %d, Size %d, PTS %ld, DTS %ld\n", 
               count, pkt->stream_index, pkt->size, pkt->pts, pkt->dts);
        av_packet_unref(pkt);
        count++;
    }

    av_packet_free(&pkt);
    avformat_close_input(&fmt_ctx);
    return 0;
}
