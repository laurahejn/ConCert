open Datatypes
open EEnvMap
open EOptimizePropDiscr
open ExAst
open List0
open MCProd

(** val optimize_constant_body :
    GlobalContextMap.t -> constant_body -> constant_body **)

let optimize_constant_body _UU03a3_ cst =
  { cst_type = cst.cst_type; cst_body =
    (option_map (optimize _UU03a3_) cst.cst_body) }

(** val optimize_decl : GlobalContextMap.t -> global_decl -> global_decl **)

let optimize_decl _UU03a3_ d = match d with
| ConstantDecl cst -> ConstantDecl (optimize_constant_body _UU03a3_ cst)
| _ -> d

(** val optimize_env : global_env -> global_env **)

let optimize_env _UU03a3_ =
  map (on_snd (optimize_decl (GlobalContextMap.make (trans_env _UU03a3_))))
    _UU03a3_
