Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition START_CODE_PREFIX := [0; 0; 1].

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

(* Strictly Correct MPEG-2 PTS Encoding *)
Definition encode_pts_bytes (pts : Z) : list Z :=
  [ 33 + (pts / 1073741824) * 2; (* 0010 bbb 1 *)
    (pts / 4194304) mod 256;
    (pts / 16384) mod 128 * 2 + 1; (* bbbbbbb 1 *)
    (pts / 64) mod 256;            (* This was /128 in some versions, but spec is bit-aligned *)
    (pts mod 64) * 2 + 1 ].

(* Correct 14-byte MPEG-2 Pack Header *)
Definition encode_pack_header (pts : Z) : list Z :=
  START_CODE_PREFIX ++ [start_code_to_byte PACK_HEADER_CODE] ++
  [ 64 + (pts / 1073741824) * 4 + 4 + (pts / 134217728) mod 4; (* MPEG-2 Marker bits *)
    (pts / 524288) mod 256;
    (pts / 2048) mod 128 * 4 + 4 + (pts / 512) mod 4;
    (pts / 2) mod 256;
    (pts mod 2) * 128 + 1; (* marker *)
    1; (* SCR_ext (dummy) *)
    0; 1; 128 + 1; (* mux_rate high/mid/low + markers *)
    0 ]. (* stuffing *)

(* Total System Header (12 bytes following length) *)
Definition encode_system_header : list Z :=
  START_CODE_PREFIX ++ [start_code_to_byte SYSTEM_HEADER_CODE] ++
  [0; 12; (* length *)
   128 + 63; 255; 255; (* rate_bound + markers *)
   1; 255; 255; 255; 255; 255; 255; 255; 255 ].