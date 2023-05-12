open Byte
open Primitive
open Specif
open Bytestring

type 'term prim_model =
| Coq_primIntModel of Uint63.t
| Coq_primFloatModel of Float64.t

type 'term prim_val = (prim_tag, 'term prim_model) sigT

(** val string_of_prim : ('a1 -> String.t) -> 'a1 prim_val -> String.t **)

let string_of_prim _ p =
  match projT2 p with
  | Coq_primIntModel f ->
    String.append (String.String (Coq_x28, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
      (Coq_x3a, (String.String (Coq_x20, String.EmptyString))))))))))))
      (String.append (string_of_prim_int f) (String.String (Coq_x29,
        String.EmptyString)))
  | Coq_primFloatModel f ->
    String.append (String.String (Coq_x28, (String.String (Coq_x66,
      (String.String (Coq_x6c, (String.String (Coq_x6f, (String.String
      (Coq_x61, (String.String (Coq_x74, (String.String (Coq_x3a,
      (String.String (Coq_x20, String.EmptyString))))))))))))))))
      (String.append (string_of_float f) (String.String (Coq_x29,
        String.EmptyString)))
