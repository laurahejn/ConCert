open Datatypes
open EAst
open Kernames
open List0
open Monad_utils

module GlobalContextMap :
 sig
  type t = { global_decls : global_declarations;
             map : global_decl EnvMap.EnvMap.t }

  val map : t -> global_decl EnvMap.EnvMap.t

  val lookup_env : t -> kername -> global_decl option

  val lookup_minductive : t -> kername -> mutual_inductive_body option

  val lookup_inductive :
    t -> inductive -> (mutual_inductive_body * one_inductive_body) option

  val inductive_isprop_and_pars : t -> inductive -> (bool * nat) option

  val make : global_declarations -> t
 end
