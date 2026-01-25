Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Import ListNotations.

Definition my_seq := {|
  horizontal_size := 1280;
  vertical_size   := 720;
  aspect_ratio    := 1;
  frame_rate      := 3;
  bit_rate        := 10000;
  vbv_buffer_size := 20;
|}.

Definition my_pic := {|
  temporal_reference := 0;
  picture_coding_type := 1;
  vbv_delay := 65535;
|}.

(* Compute the actual bytes for the minimal header *)
Definition binary_header := minimal_still_stream my_seq my_pic.

(* Output for extraction *)
Compute binary_header.
