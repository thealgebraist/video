Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Import ListNotations.

Definition my_seq := {|
  width := 1280;
  height := 720;
  aspect := 1;
  rate := 3;
  bitrate := 10000;
  vbv := 20;
|}.

Definition binary_seq_header := bits_to_bytes (encode_sequence_header my_seq).

(* Extract exactly for the Python generator *)
Compute binary_seq_header.