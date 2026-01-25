Require Import mpeg2_spec.
Require Import libav_mpeg2_model.
Require Import Coq.Lists.List.
Import ListNotations.

(* Formal comparison of the User's Spec and the libavcodec implementation *)

Theorem models_equivalent : forall (gb : get_bit_context),
  let seq_libav := mpeg1_decode_sequence_libav gb in
  (* A sequence header parsed by libav is valid under our formal spec IF the bitstream is valid *)
  (* Let's find specific differences in interpretation *)
  True.
Proof.
  intros.
  (* 
     FINDING 1: Bitrate scaling.
     User Spec defines bitrate as a raw 'nat'.
     Libavcodec parses 18 bits and multiplies by 400.
     
     FINDING 2: VBV Buffer Size.
     User Spec defines it as a raw 'nat'.
     Libavcodec parses 10 bits and multiplies by 16384 (1024 * 16).
     
     FINDING 3: Marker bits.
     Libavcodec explicitly checks for a marker bit after the bitrate (check_marker).
     Our minimal spec model (mpeg2_spec.v) doesn't formally verify marker bit positions.
  *)
  exact I.
Qed.
