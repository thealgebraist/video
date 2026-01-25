Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition START_CODE_PREFIX := [0; 0; 1].

Inductive start_code : Type :=
  | PACK_HEADER_CODE     : start_code
  | SYSTEM_HEADER_CODE   : start_code
  | VIDEO_PES_CODE       : start_code
  | AUDIO_PES_CODE       : start_code
  | PRIVATE_STREAM_1_CODE : start_code
  | SEQUENCE_HEADER_CODE : start_code
  | GOP_HEADER_CODE      : start_code
  | PICTURE_START_CODE   : start_code
  | SEQUENCE_END_CODE    : start_code.

Definition start_code_to_byte (sc : start_code) : nat :=
  match sc with
  | PACK_HEADER_CODE     => 186 (* 0xBA *)
  | SYSTEM_HEADER_CODE   => 187 (* 0xBB *)
  | VIDEO_PES_CODE       => 224 (* 0xE0 *)
  | AUDIO_PES_CODE       => 192 (* 0xC0 *)
  | PRIVATE_STREAM_1_CODE => 189 (* 0xBD *)
  | SEQUENCE_HEADER_CODE => 179 (* 0xB3 *)
  | GOP_HEADER_CODE      => 184 (* 0xB8 *)
  | PICTURE_START_CODE   => 0   (* 0x00 *)
  | SEQUENCE_END_CODE    => 183 (* 0xB7 *)
  end.

Record sequence_header := {
  horizontal_size : nat;
  vertical_size   : nat;
  aspect_ratio    : nat;
  frame_rate      : nat;
  bit_rate        : nat;
  vbv_buffer_size : nat;
}.

Definition encode_gop_header : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte GOP_HEADER_CODE] ++
  [0; 8; 0; 0].

Definition encode_pic_header (temp_ref : nat) : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte PICTURE_START_CODE] ++
  [(temp_ref / 4); ((temp_ref mod 4) * 64 + 8); 255; 248].

Definition encode_sequence_header (s : sequence_header) : list nat :=
  let w := s.(horizontal_size) in
  let h := s.(vertical_size) in
  let ar := s.(aspect_ratio) in
  let fr := s.(frame_rate) in
  let br := s.(bit_rate) / 400 in 
  let vbv := s.(vbv_buffer_size) / 16384 in 
  START_CODE_PREFIX ++ [start_code_to_byte SEQUENCE_HEADER_CODE] ++ [
    (w / 16);
    ((w mod 16) * 16 + (h / 256));
    (h mod 256);
    (ar * 16 + fr);
    (br / 1024);
    ((br mod 1024) / 4);
    ((br mod 4) * 64 + 32 + (vbv / 32));
    ((vbv mod 32) * 8 + 0)
  ].

Definition encode_pes_header (sid : nat) (len : nat) (pts : nat) : list nat :=
  START_CODE_PREFIX ++ [sid] ++
  [(len + 8) / 256; (len + 8) mod 256] ++
  [128; 128; 5] ++ 
  [33 + (pts / 1073741824) * 2;
   (pts / 4194304) mod 256;
   (pts / 16384) mod 128 * 2 + 1;
   (pts / 64) mod 256;
   (pts mod 64) * 2 + 1].

Record lpcm_header := {
  lpcm_substream_id : nat;
  lpcm_frames : nat;
  lpcm_ptr : nat;
  lpcm_sample_rate : nat;
  lpcm_bits : nat;
  lpcm_channels : nat;
}.

Definition encode_lpcm_header (l : lpcm_header) : list nat :=
  [ l.(lpcm_substream_id);
    l.(lpcm_frames);
    (l.(lpcm_ptr) / 256); (l.(lpcm_ptr) mod 256);
    (l.(lpcm_bits) * 64 + l.(lpcm_sample_rate) * 16 + l.(lpcm_channels))
  ].