open Datatypes
open Kernames
open PCUICAst
open Universes0

(** val type_of_constructor :
    PCUICEnvironment.mutual_inductive_body ->
    PCUICEnvironment.constructor_body -> (inductive * nat) -> Level.t list ->
    term **)

let type_of_constructor mdecl cdecl c u =
  let mind = (fst c).inductive_mind in
  subst (inds mind u (PCUICEnvironment.ind_bodies mdecl)) O
    (subst_instance subst_instance_constr u
      (PCUICEnvironment.cstr_type cdecl))

type coq_FixCoFix =
| Fix
| CoFix
