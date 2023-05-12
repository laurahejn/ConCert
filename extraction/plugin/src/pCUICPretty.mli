open BasicAst
open Byte
open Datatypes
open Kernames
open List0
open MCList
open MCString
open Nat0
open PCUICAst
open PCUICAstUtils
open PCUICPrimitive
open Primitive
open ReflectEq
open Specif
open Universes0
open Bytestring

val lookup_ind_decl :
  PCUICEnvironment.global_env -> kername -> nat ->
  ((PCUICEnvironment.one_inductive_body
  list * universes_decl) * PCUICEnvironment.one_inductive_body) option

val is_fresh : ident list -> ident -> bool

val name_from_term : PCUICEnvironment.global_env_ext -> term -> String.t

val fresh_id_from : ident list -> nat -> String.t -> String.t

val fresh_name :
  PCUICEnvironment.global_env_ext -> ident list -> name -> term option ->
  ident

val fresh_names :
  PCUICEnvironment.global_env_ext -> ident list -> PCUICEnvironment.context
  -> ident list

module PrintTermTree :
 sig
  val print_prim : ('a1 -> Tree.t) -> term prim_val -> Tree.t

  val print_def : ('a1 -> Tree.t) -> ('a1 -> Tree.t) -> 'a1 def -> Tree.t

  val print_defs :
    PCUICEnvironment.global_env_ext -> (ident list -> bool -> bool -> term ->
    Tree.t) -> ident list -> term mfixpoint -> Tree.t

  val pr_context_decl :
    PCUICEnvironment.global_env_ext -> (ident list -> bool -> bool -> term ->
    Tree.t) -> ident list -> term context_decl -> ident * Tree.t

  val print_context_gen :
    PCUICEnvironment.global_env_ext -> (ident list -> bool -> bool -> term ->
    Tree.t) -> ident list -> term context_decl list -> ident list * Tree.t

  val print_context_names :
    PCUICEnvironment.global_env_ext -> ident list -> term context_decl list
    -> ident list * Tree.t

  val print_term :
    PCUICEnvironment.global_env_ext -> bool -> ident list -> bool -> bool ->
    term -> Tree.t
 end

val print_term :
  PCUICEnvironment.global_env_ext -> bool -> ident list -> bool -> bool ->
  term -> String.t

val print_context :
  PCUICEnvironment.global_env_ext -> ident list -> term context_decl list ->
  String.t
