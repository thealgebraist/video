Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Compute (encode_pack_header 90000).
Compute (encode_pts_bytes 90000).
Compute encode_system_header.
