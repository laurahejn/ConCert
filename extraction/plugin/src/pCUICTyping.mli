open Datatypes
open Kernames
open PCUICAst
open Universes0

val type_of_constructor :
  PCUICEnvironment.mutual_inductive_body -> PCUICEnvironment.constructor_body
  -> (inductive * nat) -> Level.t list -> term

type coq_FixCoFix =
| Fix
| CoFix
