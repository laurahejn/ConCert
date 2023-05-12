open PCUICAst
open Universes0

(** val wf_universeb :
    PCUICEnvironment.global_env_ext -> Universe.t -> bool **)

let wf_universeb _UU03a3_ = function
| Universe.Coq_lType l ->
  LevelExprSet.for_all (fun l0 ->
    LevelSet.mem (LevelExpr.get_level l0) (global_ext_levels _UU03a3_))
    (t_set l)
| _ -> true
