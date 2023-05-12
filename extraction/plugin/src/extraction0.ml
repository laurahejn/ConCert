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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val is_empty_type_decl : global_decl -> bool **)

let is_empty_type_decl = function
| InductiveDecl mib ->
  (match mib.ind_bodies with
   | [] -> false
   | oib :: _ -> (match oib.ind_ctors with
                  | [] -> true
                  | _ :: _ -> false))
| _ -> false

type extract_pcuic_params = { optimize_prop_discr : bool;
                              extract_transforms : coq_ExtractTransform list }

(** val extract_pcuic_env :
    extract_pcuic_params -> PCUICEnvironment.global_env -> KernameSet.t ->
    (kername -> bool) -> (global_env, String.t) result **)

let extract_pcuic_env params _UU03a3_ seeds ignore =
  let _UU03a3_0 =
    timed (String ((Ascii (true, false, true, false, false, false, true,
      false)), (String ((Ascii (false, true, false, false, true, true, true,
      false)), (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (true, true, false, false, true, true, true,
      false)), (String ((Ascii (true, false, true, false, true, true, true,
      false)), (String ((Ascii (false, true, false, false, true, true, true,
      false)), (String ((Ascii (true, false, true, false, false, true, true,
      false)), EmptyString)))))))))))))) (fun _ ->
      erase_global_decls_deps_recursive
        (PCUICEnvironment.declarations _UU03a3_)
        (PCUICEnvironment.universes _UU03a3_)
        (PCUICEnvironment.retroknowledge _UU03a3_) seeds ignore)
  in
  if params.optimize_prop_discr
  then let _UU03a3_1 =
         timed (String ((Ascii (false, true, false, false, true, false, true,
           false)), (String ((Ascii (true, false, true, false, false, true,
           true, false)), (String ((Ascii (true, false, true, true, false,
           true, true, false)), (String ((Ascii (true, true, true, true,
           false, true, true, false)), (String ((Ascii (false, true, true,
           false, true, true, true, false)), (String ((Ascii (true, false,
           false, false, false, true, true, false)), (String ((Ascii (false,
           false, true, true, false, true, true, false)), (String ((Ascii
           (false, false, false, false, false, true, false, false)), (String
           ((Ascii (true, true, true, true, false, true, true, false)),
           (String ((Ascii (false, true, true, false, false, true, true,
           false)), (String ((Ascii (false, false, false, false, false, true,
           false, false)), (String ((Ascii (false, false, false, false, true,
           true, true, false)), (String ((Ascii (false, true, false, false,
           true, true, true, false)), (String ((Ascii (true, true, true,
           true, false, true, true, false)), (String ((Ascii (false, false,
           false, false, true, true, true, false)), (String ((Ascii (false,
           false, false, false, false, true, false, false)), (String ((Ascii
           (false, false, true, false, false, true, true, false)), (String
           ((Ascii (true, false, false, true, false, true, true, false)),
           (String ((Ascii (true, true, false, false, true, true, true,
           false)), (String ((Ascii (true, true, false, false, false, true,
           true, false)), (String ((Ascii (false, true, false, false, true,
           true, true, false)), (String ((Ascii (true, false, false, true,
           false, true, true, false)), (String ((Ascii (true, false, true,
           true, false, true, true, false)), (String ((Ascii (true, false,
           false, true, false, true, true, false)), (String ((Ascii (false,
           true, true, true, false, true, true, false)), (String ((Ascii
           (true, false, false, false, false, true, true, false)), (String
           ((Ascii (false, false, true, false, true, true, true, false)),
           (String ((Ascii (true, false, false, true, false, true, true,
           false)), (String ((Ascii (true, true, true, true, false, true,
           true, false)), (String ((Ascii (false, true, true, true, false,
           true, true, false)),
           EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           (fun _ -> optimize_env _UU03a3_0)
       in
       compose_transforms params.extract_transforms _UU03a3_1
  else Ok _UU03a3_0

type extract_template_env_params = { template_transforms : coq_TemplateTransform
                                                           list;
                                     check_wf_env_func : (PCUICEnvironment.global_env
                                                         -> (__, String.t)
                                                         result);
                                     pcuic_args : extract_pcuic_params }

(** val check_wf_and_extract :
    extract_template_env_params -> PCUICEnvironment.global_env ->
    KernameSet.t -> (kername -> bool) -> (global_env, String.t) result **)

let check_wf_and_extract params _UU03a3_ seeds ignore =
  bind (Obj.magic coq_Monad_result)
    (Obj.magic params.check_wf_env_func _UU03a3_) (fun _ ->
    extract_pcuic_env params.pcuic_args _UU03a3_ seeds ignore)

(** val extract_template_env_general :
    (PCUICEnvironment.global_env -> (PCUICEnvironment.global_env, String.t)
    result) -> extract_template_env_params -> Env.global_env -> KernameSet.t
    -> (kername -> bool) -> (global_env, String.t) result **)

let extract_template_env_general pcuic_trans params _UU03a3_ seeds ignore =
  let _UU03a3_0 = trans_global_env _UU03a3_ in
  bind (Obj.magic coq_Monad_result)
    (Obj.magic pcuic_trans _UU03a3_0.trans_env_env) (fun _UU03a3_1 ->
    check_wf_and_extract params _UU03a3_1 seeds ignore)

(** val extract_template_env :
    extract_template_env_params -> Env.global_env -> KernameSet.t -> (kername
    -> bool) -> (global_env, String.t) result **)

let extract_template_env =
  extract_template_env_general (ret (Obj.magic coq_Monad_result))

(** val extract_within_coq : extract_template_env_params **)

let extract_within_coq =
  { template_transforms = []; check_wf_env_func = (fun _ -> Ok __);
    pcuic_args = { optimize_prop_discr = true; extract_transforms =
    ((dearg_transform (fun _ -> None) true true true true true) :: []) } }
