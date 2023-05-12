open Ascii
open Ast0
open Erasure
open ExAst
open Kernames
open Optimize
open OptimizePropDiscr
open PCUICAst
open PCUICProgram
open ResultMonad
open String0
open TemplateToPCUIC
open Transform0
open Utils
open Bytestring
open Monad_utils

type __ = Obj.t

val is_empty_type_decl : global_decl -> bool

type extract_pcuic_params = { optimize_prop_discr : bool;
                              extract_transforms : coq_ExtractTransform list }

val extract_pcuic_env :
  extract_pcuic_params -> PCUICEnvironment.global_env -> KernameSet.t ->
  (kername -> bool) -> (global_env, String.t) result

type extract_template_env_params = { template_transforms : coq_TemplateTransform
                                                           list;
                                     check_wf_env_func : (PCUICEnvironment.global_env
                                                         -> (__, String.t)
                                                         result);
                                     pcuic_args : extract_pcuic_params }

val check_wf_and_extract :
  extract_template_env_params -> PCUICEnvironment.global_env -> KernameSet.t
  -> (kername -> bool) -> (global_env, String.t) result

val extract_template_env_general :
  (PCUICEnvironment.global_env -> (PCUICEnvironment.global_env, String.t)
  result) -> extract_template_env_params -> Env.global_env -> KernameSet.t ->
  (kername -> bool) -> (global_env, String.t) result

val extract_template_env :
  extract_template_env_params -> Env.global_env -> KernameSet.t -> (kername
  -> bool) -> (global_env, String.t) result

val extract_within_coq : extract_template_env_params
