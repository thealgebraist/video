Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(* Formal definition of MPEG-2 Start Codes *)
Definition START_CODE_PREFIX := [0; 0; 1].

Inductive start_code : Type :=
  | PACK_HEADER_CODE     : start_code
  | SYSTEM_HEADER_CODE   : start_code
  | VIDEO_PES_CODE       : start_code
  | AUDIO_PES_CODE       : start_code
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
  | SEQUENCE_HEADER_CODE => 179 (* 0xB3 *)
  | GOP_HEADER_CODE      => 184 (* 0xB8 *)
  | PICTURE_START_CODE   => 0   (* 0x00 *)
  | SEQUENCE_END_CODE    => 183 (* 0xB7 *)
  end.

(* Records must be defined before use *)
Record sequence_header := {
  horizontal_size : nat;
  vertical_size   : nat;
  aspect_ratio    : nat;
  frame_rate      : nat;
  bit_rate        : nat;
  vbv_buffer_size : nat;
}.

Record picture_header := {
  temporal_reference : nat;
  picture_coding_type : nat; (* 1 for I-frame *)
  vbv_delay : nat;
}.

Definition encode_gop_header : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte GOP_HEADER_CODE] ++
  [0; 8; 0; 0]. (* Standard 25fps time code *)

Definition encode_pic_header (temp_ref : nat) : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte PICTURE_START_CODE] ++
  [(temp_ref / 4); ((temp_ref mod 4) * 64 + 8); 255; 248]. (* temporal ref and I-frame bits *)

(* Bit-accurate Sequence Header Encoding following standard/libavcodec *)
Definition encode_sequence_header (s : sequence_header) : list nat :=
  let w := s.(horizontal_size) in
  let h := s.(vertical_size) in
  let ar := s.(aspect_ratio) in
  let fr := s.(frame_rate) in
  let br := s.(bit_rate) / 400 in (* libavcodec unit *)
  let vbv := s.(vbv_buffer_size) / 16384 in (* libavcodec unit *)
  
  START_CODE_PREFIX ++ [start_code_to_byte SEQUENCE_HEADER_CODE] ++ [
    (w / 16); (* w high 8 bits *)
    ((w mod 16) * 16 + (h / 256)); (* w low 4, h high 4 *)
    (h mod 256); (* h low 8 bits *)
    (ar * 16 + fr); (* aspect 4, rate 4 *)
    (br / 1024); (* bitrate high 8 of 18 *)
    ((br mod 1024) / 4); (* bitrate middle 8 *)
    ((br mod 4) * 64 + 32 + (vbv / 32)); (* br low 2, marker 1, vbv high 5 *)
    ((vbv mod 32) * 8 + 0) (* vbv low 5, constrained 1, matrices 2 *)
  ].