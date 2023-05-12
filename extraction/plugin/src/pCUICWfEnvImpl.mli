open BasicAst
open PCUICAst
open PCUICEqualityDec
open PCUICTyping
open PCUICWfEnv
open PCUICWfUniverses
open Specif
open Universes0
open Config0
open UGraph0

type __ = Obj.t

val wf_gc_of_uctx :
  checker_flags -> PCUICEnvironment.global_env ->
  (VSet.t * GoodConstraintSet.t, __) sigT

val graph_of_wf :
  checker_flags -> PCUICEnvironment.global_env -> (universes_graph, __) sigT

val wf_ext_gc_of_uctx :
  checker_flags -> PCUICEnvironment.global_env_ext ->
  (VSet.t * GoodConstraintSet.t, __) sigT

val graph_of_wf_ext :
  checker_flags -> PCUICEnvironment.global_env_ext -> (universes_graph, __)
  sigT

type abstract_guard_impl =
  coq_FixCoFix -> PCUICEnvironment.global_env_ext -> PCUICEnvironment.context
  -> term mfixpoint -> bool
  (* singleton inductive, whose constructor was Build_abstract_guard_impl *)

val guard_impl :
  abstract_guard_impl -> coq_FixCoFix -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> term mfixpoint -> bool

type referenced_impl_ext =
  PCUICEnvironment.global_env_ext
  (* singleton inductive, whose constructor was Build_referenced_impl_ext *)

val referenced_impl_env_ext :
  checker_flags -> abstract_guard_impl -> referenced_impl_ext ->
  PCUICEnvironment.global_env_ext

val referenced_impl_ext_graph :
  checker_flags -> abstract_guard_impl -> referenced_impl_ext ->
  universes_graph

type referenced_impl =
  PCUICEnvironment.global_env
  (* singleton inductive, whose constructor was Build_referenced_impl *)

val referenced_impl_env :
  checker_flags -> referenced_impl -> PCUICEnvironment.global_env

val referenced_impl_graph :
  checker_flags -> referenced_impl -> universes_graph

val init_env : PCUICEnvironment.global_env

val referenced_pop : checker_flags -> referenced_impl -> referenced_impl

val make_wf_env_ext :
  checker_flags -> abstract_guard_impl -> referenced_impl -> universes_decl
  -> referenced_impl_ext

val canonical_abstract_env_struct :
  checker_flags -> abstract_guard_impl -> (referenced_impl,
  referenced_impl_ext) abstract_env_struct

val canonical_abstract_env_impl :
  checker_flags -> abstract_guard_impl -> abstract_env_impl
