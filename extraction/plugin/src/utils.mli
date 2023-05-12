open Ast0
open AstUtils
open BasicAst
open Datatypes
open List0
open String0
open TermEquality
open Typing0

val map_fst : ('a1 -> 'a2) -> ('a1 * 'a3) -> 'a2 * 'a3

val timed : string -> (unit -> 'a1) -> 'a1

val map_subterms : (term -> term) -> term -> term

val beta_body : term -> term list -> term

val iota_body : Env.global_env -> term -> term
