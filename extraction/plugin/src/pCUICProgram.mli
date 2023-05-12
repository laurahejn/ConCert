open Kernames
open List0
open PCUICAst

type global_env_map = { trans_env_env : PCUICEnvironment.global_env;
                        trans_env_map : PCUICEnvironment.global_decl
                                        EnvMap.EnvMap.t }

module TransLookup :
 sig
  val lookup_minductive :
    global_env_map -> kername -> PCUICEnvironment.mutual_inductive_body option

  val lookup_inductive :
    global_env_map -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option
 end
