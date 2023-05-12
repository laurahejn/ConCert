open BasicAst
open Byte
open Datatypes
open EAst
open Kernames
open List0
open MCString
open PCUICPrimitive
open Bytestring

val decompose_app_rec : term -> term list -> term * term list

val decompose_app : term -> term * term list

val isBox : term -> bool

val string_of_def : ('a1 -> String.t) -> 'a1 def -> String.t

val maybe_string_of_list : ('a1 -> String.t) -> 'a1 list -> String.t

val string_of_term : term -> String.t

val term_global_deps : term -> KernameSet.t
