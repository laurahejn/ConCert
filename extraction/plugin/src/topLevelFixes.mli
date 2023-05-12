open Ascii
open Datatypes
open EAst
open ELiftSubst
open ExAst
open Kernames
open List0
open MCList
open ResultMonad
open String0
open Transform0
open Utils

val optimize_aux : term -> kername -> nat -> term

val optimize : term -> kername -> term

val optimize_decl :
  ((kername * bool) * global_decl) -> (kername * bool) * global_decl

val optimize_env : global_env -> global_env

val transform : coq_ExtractTransform
