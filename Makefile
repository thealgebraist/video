CC=clang
CFLAGS=-O3 -Wall -Wextra -std=c99 $(shell pkg-config --cflags libavcodec libavformat libavutil libswresample libswscale)
LDFLAGS=$(shell pkg-config --libs libavcodec libavformat libavutil libswresample libswscale) -lm

assemble_video: assemble_video.c
	$(CC) $(CFLAGS) -o assemble_video assemble_video.c $(LDFLAGS)

still2mpg: still2mpg.c
	$(CC) -O3 -Wall -Wextra -std=c99 -o still2mpg still2mpg.c -lm

clean:
	rm -f assemble_video still2mpg
