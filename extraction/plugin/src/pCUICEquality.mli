open Datatypes
open Kernames
open Nat0
open PCUICAst
open PeanoNat
open Universes0

val global_variance :
  PCUICEnvironment.global_env -> global_reference -> nat -> Variance.t list
  option
