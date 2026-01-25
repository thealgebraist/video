Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Import ListNotations.

Definition my_lpcm := {|
  lpcm_substream_id := 160; (* 0xA0 *)
  lpcm_frames := 1;
  lpcm_ptr := 0;
  lpcm_sample_rate := 2; (* 10: 44.1k *)
  lpcm_bits := 0;        (* 00: 16b *)
  lpcm_channels := 1;    (* 001: stereo *)
|}.

Compute (encode_lpcm_header my_lpcm).
Compute (encode_pes_header 224 0 90000).