Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(* Bytes obtained from libavcodec execution:
   0 0 1 179 80 2 208 51 255 255 226 40 
*)
Definition libav_bin_header : list Z := 
  [0; 0; 1; 179; 80; 2; 208; 51; 255; 255; 226; 40].

Definition my_seq := {|
  horizontal_size := 1280;
  vertical_size   := 720;
  aspect_ratio    := 1; (* 4:3 in index? No, 1 is 1:1 *)
  frame_rate      := 3; (* 25fps index is 3 *)
  bit_rate        := 4000000;
  vbv_buffer_size := 327680;
|}.

Definition coq_bin_header := encode_sequence_header my_seq.

Theorem find_header_differences : 
  coq_bin_header = libav_bin_header.
Proof.
  unfold coq_bin_header, encode_sequence_header, my_seq.
  simpl.
  (* 
     This proof will fail, allowing us to see the diffs.
     Coq:   [0; 0; 1; 179; 80; 2; 208; 19; 9; 196; 32; 160]
     Libav: [0; 0; 1; 179; 80; 2; 208; 51; 255; 255; 226; 40]
  *)
Abort.
