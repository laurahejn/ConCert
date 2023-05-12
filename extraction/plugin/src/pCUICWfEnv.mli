open BasicAst
open Datatypes
open Kernames
open PCUICAst
open PCUICTyping
open Specif
open Universes0
open Config0
open UGraph0

type __ = Obj.t

val level_mem : PCUICEnvironment.global_env_ext -> Level.t -> bool

type ('abstract_env_impl, 'abstract_env_ext_impl) abstract_env_struct = { 
abstract_env_lookup : ('abstract_env_ext_impl -> kername ->
                      PCUICEnvironment.global_decl option);
abstract_env_ext_retroknowledge : ('abstract_env_ext_impl ->
                                  Environment.Retroknowledge.t);
abstract_env_conv_pb_relb : ('abstract_env_ext_impl -> conv_pb -> Universe.t
                            -> Universe.t -> bool);
abstract_env_compare_global_instance : ('abstract_env_ext_impl -> (Universe.t
                                       -> Universe.t -> bool) ->
                                       global_reference -> nat -> Level.t
                                       list -> Level.t list -> bool);
abstract_env_level_mem : ('abstract_env_ext_impl -> Level.t -> bool);
abstract_env_ext_wf_universeb : ('abstract_env_ext_impl -> Universe.t -> bool);
abstract_env_check_constraints : ('abstract_env_ext_impl -> ConstraintSet.t
                                 -> bool);
abstract_env_guard : ('abstract_env_ext_impl -> coq_FixCoFix ->
                     PCUICEnvironment.context -> term mfixpoint -> bool);
abstract_env_empty : 'abstract_env_impl;
abstract_env_init : (ContextSet.t -> Environment.Retroknowledge.t -> __ ->
                    'abstract_env_impl);
abstract_env_univ : ('abstract_env_impl -> ContextSet.t);
abstract_env_global_declarations : ('abstract_env_impl ->
                                   PCUICEnvironment.global_declarations);
abstract_env_retroknowledge : ('abstract_env_impl ->
                              Environment.Retroknowledge.t);
abstract_env_add_decl : ('abstract_env_impl -> kername ->
                        PCUICEnvironment.global_decl -> __ ->
                        'abstract_env_impl);
abstract_env_empty_ext : ('abstract_env_impl -> 'abstract_env_ext_impl);
abstract_env_is_consistent : ((VSet.t * GoodConstraintSet.t) -> bool);
abstract_env_is_consistent_uctx : ('abstract_env_impl ->
                                  (VSet.t * GoodConstraintSet.t) -> bool);
abstract_env_add_uctx : ('abstract_env_impl -> (VSet.t * GoodConstraintSet.t)
                        -> universes_decl -> __ -> __ ->
                        'abstract_env_ext_impl);
abstract_pop_decls : ('abstract_env_impl -> 'abstract_env_impl);
abstract_make_wf_env_ext : ('abstract_env_impl -> universes_decl -> __ ->
                           'abstract_env_ext_impl) }

type abstract_env_impl =
  (__, (__, ((__, __) abstract_env_struct, __) sigT) sigT) sigT

val abstract_env_impl_abstract_env_struct :
  checker_flags -> abstract_env_impl -> (__, __) abstract_env_struct
