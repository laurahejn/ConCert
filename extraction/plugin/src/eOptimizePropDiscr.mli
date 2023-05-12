open Datatypes
open EAst
open ECSubst
open EEnvMap
open Kernames
open List0
open MCProd

val optimize : GlobalContextMap.t -> term -> term
