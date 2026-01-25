Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition START_CODE_PREFIX := [0%Z; 0%Z; 1%Z].

Inductive start_code : Type :=
  | PACK_HEADER_CODE     : start_code
  | SYSTEM_HEADER_CODE   : start_code
  | VIDEO_PES_CODE       : start_code
  | AUDIO_PES_CODE       : start_code
  | PRIVATE_STREAM_1_CODE : start_code
  | SEQUENCE_HEADER_CODE : start_code
  | GOP_HEADER_CODE      : start_code
  | PICTURE_START_CODE   : start_code
  | SEQUENCE_END_CODE    : start_code.

Definition start_code_to_byte (sc : start_code) : Z :=
  match sc with
  | PACK_HEADER_CODE     => 186 (* 0xBA *)
  | SYSTEM_HEADER_CODE   => 187 (* 0xBB *)
  | VIDEO_PES_CODE       => 224 (* 0xE0 *)
  | AUDIO_PES_CODE       => 192 (* 0xC0 *)
  | PRIVATE_STREAM_1_CODE => 189 (* 0xBD *)
  | SEQUENCE_HEADER_CODE => 179 (* 0xB3 *)
  | GOP_HEADER_CODE      => 184 (* 0xB8 *)
  | PICTURE_START_CODE   => 0   (* 0x00 *)
  | SEQUENCE_END_CODE    => 183 (* 0xB7 *)
  end.

(* Convert Z to bits (total function) *)
Fixpoint z_to_bits (count : nat) (val : Z) : list bool :=
  match count with
  | O => []
  | S c => (z_to_bits c (val / 2)) ++ [if (val mod 2) =? 1 then true else false]
  end.

(* Group bits into Z bytes *)
Fixpoint bits_to_z (l : list bool) : list Z :=
  match l with
  | b1::b2::b3::b4::b5::b6::b7::b8::rs =>
      let val := (if b1 then 128 else 0) + (if b2 then 64 else 0) + (if b3 then 32 else 0) +
                 (if b4 then 16 else 0) + (if b5 then 8 else 0) + (if b6 then 4 else 0) +
                 (if b7 then 2 else 0) + (if b8 then 1 else 0) in
      val%Z :: bits_to_z rs
  | _ => []
  end.

Record sequence_header := {
  horizontal_size : Z;
  vertical_size   : Z;
  aspect_ratio    : Z;
  frame_rate      : Z;
  bit_rate        : Z;
  vbv_buffer_size : Z;
}.

Definition encode_sequence_header (s : sequence_header) : list Z :=
  let w := s.(horizontal_size) in
  let h := s.(vertical_size) in
  let br := s.(bit_rate) / 400 in
  let vbv := s.(vbv_buffer_size) / 16384 in
  START_CODE_PREFIX ++ [start_code_to_byte SEQUENCE_HEADER_CODE] ++ [
    (w / 16);
    ((w mod 16) * 16 + (h / 256));
    (h mod 256);
    (s.(aspect_ratio) * 16 + s.(frame_rate));
    (br / 1024);
    ((br mod 1024) / 4);
    ((br mod 4) * 64 + 32 + (vbv / 32));
    ((vbv mod 32) * 8)
  ].

Definition encode_pes_header (sid : Z) (len : Z) (pts : Z) : list Z :=
  START_CODE_PREFIX ++ [sid] ++
  [(len + 8) / 256; (len + 8) mod 256] ++
  [128; 128; 5] ++
  [33 + (pts / 1073741824) * 2;
   (pts / 4194304) mod 256;
   (pts / 16384) mod 128 * 2 + 1;
   (pts / 64) mod 256;
   (pts mod 64) * 2 + 1].

Record lpcm_header := {
  lpcm_subid : Z;
  lpcm_frames : Z;
  lpcm_ptr : Z;
  lpcm_sample_rate : Z; (* 0=48k, 1=96k, 2=44.1k, 3=32k *)
  lpcm_bits : Z;        (* 0=16b, 1=20b, 2=24b *)
  lpcm_channels : Z;    (* 0=mono, 1=stereo *)
}.

Definition encode_lpcm_header (l : lpcm_header) : list Z :=
  [ l.(lpcm_subid);
    l.(lpcm_frames);
    (l.(lpcm_ptr) / 256); (l.(lpcm_ptr) mod 256);
    (l.(lpcm_bits) * 64 + l.(lpcm_sample_rate) * 16 + l.(lpcm_channels))
  ].

Theorem seq_len_z : forall s, length (encode_sequence_header s) = 12%nat.
Proof. intros. reflexivity. Qed.
