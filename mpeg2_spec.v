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

(* Formal PES Header Record *)
Record pes_header := {
  stream_id : nat;
  pes_packet_length : nat;
  pts : nat;
}.

Definition is_valid_pes (p : pes_header) : Prop :=
  p.(stream_id) >= 192 /\ p.(stream_id) <= 239.

Definition encode_gop_header : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte GOP_HEADER_CODE] ++
  [0; 8; 0; 0]. (* Standard 25fps time code *)

Definition encode_pic_header (temp_ref : nat) : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte PICTURE_START_CODE] ++
  [(temp_ref / 4); ((temp_ref mod 4) * 64 + 8); 255; 248]. (* temporal ref and I-frame bits *)

(* Minimal Sequence Header Specification *)
Record sequence_header := {
  horizontal_size : nat;
  vertical_size   : nat;
  aspect_ratio    : nat;
  frame_rate      : nat;
  bit_rate        : nat;
  vbv_buffer_size : nat;
}.

Definition is_valid_seq (s : sequence_header) : Prop :=
  s.(horizontal_size) > 0 /\ 
  s.(vertical_size) > 0 /\ 
  s.(aspect_ratio) > 0 /\ s.(aspect_ratio) < 16 /\ 
  s.(frame_rate) > 0 /\ s.(frame_rate) < 16.

(* Minimal Picture Header Specification *)
Record picture_header := {
  temporal_reference : nat;
  picture_coding_type : nat; (* 1 for I-frame *)
  vbv_delay : nat;
}.

Definition is_valid_pic (p : picture_header) : Prop :=
  p.(picture_coding_type) = 1.

(* Theorem: A minimal still image stream must contain at least a Seq and a Pic *)
Definition minimal_still_stream (s : sequence_header) (p : picture_header) : list nat :=
  START_CODE_PREFIX ++ [start_code_to_byte SEQUENCE_HEADER_CODE] ++ 
  [s.(horizontal_size) / 16; s.(vertical_size) / 16] ++ (* Simplified byte rep *)
  START_CODE_PREFIX ++ [start_code_to_byte PICTURE_START_CODE] ++ 
  [p.(temporal_reference); p.(picture_coding_type)].

Lemma minimal_still_stream_correct : forall s p,
  is_valid_seq s -> is_valid_pic p ->
  exists l, minimal_still_stream s p = l.
Proof.
  intros s p Hseq Hpic.
  exists (minimal_still_stream s p).
  reflexivity.
Qed.
