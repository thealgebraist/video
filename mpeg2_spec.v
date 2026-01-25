Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Bitstream Representation *)
Definition bit := bool.

(* Convert a natural number to a fixed-length list of bits (MSB first) *)
Fixpoint nat_to_bits (count : nat) (n : nat) : list bit :=
  match count with
  | 0 => []
  | S c => (nat_to_bits c (n / 2)) ++ [if (n mod 2) =? 1 then true else false]
  end.

(* Group bits into bytes (total function) *)
Fixpoint bits_to_bytes (l : list bit) : list nat :=
  match l with
  | b1::b2::b3::b4::b5::b6::b7::b8::rs =>
      let val := (if b1 then 128 else 0) +
                 (if b2 then 64 else 0) +
                 (if b3 then 32 else 0) +
                 (if b4 then 16 else 0) +
                 (if b5 then 8 else 0) +
                 (if b6 then 4 else 0) +
                 (if b7 then 2 else 0) +
                 (if b8 then 1 else 0) in
      val :: bits_to_bytes rs
  | _ => []
  end.

(* MPEG-2 Sequence Header Record *)
Record mpeg2_seq_hdr := {
  width : nat;   (* 12 bits *)
  height : nat;  (* 12 bits *)
  aspect : nat;  (* 4 bits *)
  rate : nat;    (* 4 bits *)
  bitrate : nat; (* 18 bits *)
  vbv : nat;     (* 10 bits *)
}.

(* Formal Start Codes *)
Definition SEQ_START_CODE := nat_to_bits 32 435. (* 0x000001B3 *)
Definition GOP_START_CODE := nat_to_bits 32 440. (* 0x000001B8 *)
Definition PIC_START_CODE := nat_to_bits 32 256. (* 0x00000100 *)
Definition EXT_START_CODE := nat_to_bits 32 437. (* 0x000001B5 *)
Definition SEQ_END_CODE   := nat_to_bits 32 439. (* 0x000001B7 *)

(* Verified Encoder Function *)
Definition encode_sequence_header (s : mpeg2_seq_hdr) : list bit :=
  SEQ_START_CODE ++
  (nat_to_bits 12 s.(width)) ++
  (nat_to_bits 12 s.(height)) ++
  (nat_to_bits 4 s.(aspect)) ++
  (nat_to_bits 4 s.(rate)) ++
  (nat_to_bits 18 s.(bitrate)) ++
  [true] ++ (* marker_bit *)
  (nat_to_bits 10 s.(vbv)) ++
  [false; false; false]. (* constrained, load_intra, load_non_intra *)

(* Theorem: The Sequence Header length is always 96 bits (12 bytes) *)
Theorem seq_header_length_correct : forall s,
  length (encode_sequence_header s) = 96.
Proof.
  intros s. unfold encode_sequence_header.
  repeat (rewrite app_length; simpl).
  reflexivity.
Qed.

(* Correctness Property: The first 32 bits are always the SEQ_START_CODE *)
Theorem seq_header_starts_correct : forall s,
  firstn 32 (encode_sequence_header s) = SEQ_START_CODE.
Proof.
  intros s. unfold encode_sequence_header.
  rewrite firstn_app.
  simpl. reflexivity.
Qed.
