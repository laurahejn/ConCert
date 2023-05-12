open BasicAst
open Datatypes
open EAstUtils
open Extract
open Kernames
open PCUICAst
open PCUICCases
open PCUICErrors
open PCUICSafeReduce
open PCUICSafeRetyping
open PCUICWfEnv
open Specif
open Universes0
open Config0

type __ = Obj.t

val is_arity :
  checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
  term -> bool

val inspect : 'a1 -> 'a1

val inspect_bool : bool -> bool

val is_erasableb :
  abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> bool

val erase :
  abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> E.term

val erase_constant_body :
  abstract_env_impl -> __ -> PCUICEnvironment.constant_body ->
  E.constant_body * KernameSet.t
