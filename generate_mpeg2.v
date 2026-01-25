Require Import mpeg2_spec.
Require Import Coq.Lists.List.
Import ListNotations.

Compute encode_gop_header.
Compute (encode_pic_header 0).
