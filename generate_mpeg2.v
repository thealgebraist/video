Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition my_lpcm := {|
  lpcm_subid := 160;
  lpcm_frames := 1;
  lpcm_ptr := 0;
  lpcm_sample_rate := 0; (* 48k *)
  lpcm_bits := 0;        (* 16b *)
  lpcm_channels := 1;    (* stereo *)
|}.

Compute (encode_lpcm_header my_lpcm).
Compute (encode_pes_header 224 0 90000).