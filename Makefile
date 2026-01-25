CC=clang
CFLAGS=-O3 -Wall -Wextra -std=c99 $(shell pkg-config --cflags libavcodec libavformat libavutil libswresample libswscale)
LDFLAGS=$(shell pkg-config --libs libavcodec libavformat libavutil libswresample libswscale) -lm

assemble_video: assemble_video.c
	$(CC) $(CFLAGS) -o assemble_video assemble_video.c $(LDFLAGS)

clean:
	rm -f assemble_video
