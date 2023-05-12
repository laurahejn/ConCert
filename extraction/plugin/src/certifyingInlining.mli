open Ascii
open Ast0
open AstUtils
open BasicAst
open CertifyingBeta
open Datatypes
open Kernames
open List0
open ResultMonad
open String0
open Transform0
open Universes0
open Utils

val inline_aux :
  (kername -> bool) -> Env.global_env -> term list -> term -> term

val inline : (kername -> bool) -> Env.global_env -> term -> term

val inline_in_constant_body :
  (kername -> bool) -> Env.global_env -> Env.constant_body ->
  Env.constant_body

val inline_oib :
  (kername -> bool) -> Env.global_env -> nat -> nat -> Env.one_inductive_body
  -> Env.one_inductive_body

val inline_context_decl :
  (kername -> bool) -> Env.global_env -> term context_decl -> term
  context_decl

val inline_in_decl :
  (kername -> bool) -> Env.global_env -> Env.global_decl -> Env.global_decl

val inline_globals :
  (kername -> bool) -> Env.global_declarations -> Env.global_declarations

val template_inline : (kername -> bool) -> coq_TemplateTransform
