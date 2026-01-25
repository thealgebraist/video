Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Import ListNotations.

Definition my_seq := {|
  horizontal_size := 1280;
  vertical_size   := 720;
  aspect_ratio    := 1;
  frame_rate      := 3;
  bit_rate        := 4000000; (* 400,000 bps *)
  vbv_buffer_size := 327680;  (* 20 * 16384 *)
|}.

Definition compliant_header := encode_sequence_header my_seq.

Compute compliant_header.