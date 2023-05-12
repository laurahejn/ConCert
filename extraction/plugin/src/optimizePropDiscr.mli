open Datatypes
open EEnvMap
open EOptimizePropDiscr
open ExAst
open List0
open MCProd

val optimize_constant_body :
  GlobalContextMap.t -> constant_body -> constant_body

val optimize_decl : GlobalContextMap.t -> global_decl -> global_decl

val optimize_env : global_env -> global_env
