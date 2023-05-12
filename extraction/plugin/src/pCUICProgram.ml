open Kernames
open List0
open PCUICAst

type global_env_map = { trans_env_env : PCUICEnvironment.global_env;
                        trans_env_map : PCUICEnvironment.global_decl
                                        EnvMap.EnvMap.t }

module TransLookup =
 struct
  (** val lookup_minductive :
      global_env_map -> kername -> PCUICEnvironment.mutual_inductive_body
      option **)

  let lookup_minductive _UU03a3_ mind =
    match EnvMap.EnvMap.lookup mind _UU03a3_.trans_env_map with
    | Some g ->
      (match g with
       | PCUICEnvironment.ConstantDecl _ -> None
       | PCUICEnvironment.InductiveDecl decl -> Some decl)
    | None -> None

  (** val lookup_inductive :
      global_env_map -> inductive ->
      (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
      option **)

  let lookup_inductive _UU03a3_ ind =
    match lookup_minductive _UU03a3_ ind.inductive_mind with
    | Some mdecl ->
      (match nth_error (PCUICEnvironment.ind_bodies mdecl) ind.inductive_ind with
       | Some idecl -> Some (mdecl, idecl)
       | None -> None)
    | None -> None
 end
