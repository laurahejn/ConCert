open BasicAst
open Classes0
open Datatypes
open EAst
open Kernames
open List0
open PCUICAst
open PCUICPrimitive
open Primitive
open Specif
open Universes0

type __ = Obj.t

module E = EAst

(** val erase_context : PCUICEnvironment.context -> name list **)

let erase_context _UU0393_ =
  map (fun d -> d.BasicAst.decl_name.binder_name) _UU0393_

(** val erase_prim_model :
    prim_tag -> term prim_model -> E.term prim_model **)

let erase_prim_model _ = function
| Coq_primIntModel i -> Coq_primIntModel i
| Coq_primFloatModel f -> Coq_primFloatModel f

(** val erase_prim_val : term prim_val -> E.term prim_val **)

let erase_prim_val p =
  Coq_existT ((projT1 p), (erase_prim_model (projT1 p) (projT2 p)))
