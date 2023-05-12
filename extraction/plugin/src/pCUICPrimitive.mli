open Byte
open Primitive
open Specif
open Bytestring

type 'term prim_model =
| Coq_primIntModel of Uint63.t
| Coq_primFloatModel of Float64.t

type 'term prim_val = (prim_tag, 'term prim_model) sigT

val string_of_prim : ('a1 -> String.t) -> 'a1 prim_val -> String.t
