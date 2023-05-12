open Ascii
open Ast0
open AstUtils
open BasicAst
open CertifyingBeta
open Datatypes
open Kernames
open List0
open ResultMonad
open String0
open Transform0
open Universes0
open Utils

(** val inline_aux :
    (kername -> bool) -> Env.global_env -> term list -> term -> term **)

let rec inline_aux should_inline _UU03a3_ args t = match t with
| Coq_tRel _ ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tVar _ ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tEvar (_, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tSort _ ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tCast (t0, _, _) -> inline_aux should_inline _UU03a3_ args t0
| Coq_tProd (_, _, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tLambda (_, _, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tLetIn (_, _, _, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tApp (hd, args0) ->
  inline_aux should_inline _UU03a3_
    (app (map (inline_aux should_inline _UU03a3_ []) args0) args) hd
| Coq_tConst (kn, u) ->
  if should_inline kn
  then (match Env.lookup_env _UU03a3_ kn with
        | Some g ->
          (match g with
           | Env.ConstantDecl cst ->
             (match Env.cst_body cst with
              | Some body ->
                let (hd, args0) = decompose_app (beta_body body args) in
                let res = beta_body (iota_body _UU03a3_ hd) args0 in
                betared res
              | None -> mkApps (Coq_tConst (kn, u)) args)
           | Env.InductiveDecl _ -> mkApps (Coq_tConst (kn, u)) args)
        | None -> mkApps (Coq_tConst (kn, u)) args)
  else mkApps (Coq_tConst (kn, u)) args
| Coq_tInd (_, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tConstruct (_, _, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tCase (_, _, _, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tProj (_, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tFix (_, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tCoFix (_, _) ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tInt _ ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args
| Coq_tFloat _ ->
  mkApps (map_subterms (inline_aux should_inline _UU03a3_ []) t) args

(** val inline : (kername -> bool) -> Env.global_env -> term -> term **)

let inline should_inline _UU03a3_ =
  inline_aux should_inline _UU03a3_ []

(** val inline_in_constant_body :
    (kername -> bool) -> Env.global_env -> Env.constant_body ->
    Env.constant_body **)

let inline_in_constant_body should_inline _UU03a3_ cst =
  { Env.cst_type = (inline should_inline _UU03a3_ (Env.cst_type cst));
    Env.cst_body =
    (option_map (inline should_inline _UU03a3_) (Env.cst_body cst));
    Env.cst_universes = (Env.cst_universes cst); Env.cst_relevance =
    (Env.cst_relevance cst) }

(** val inline_oib :
    (kername -> bool) -> Env.global_env -> nat -> nat ->
    Env.one_inductive_body -> Env.one_inductive_body **)

let inline_oib should_inline _UU03a3_ npars arities oib =
  { Env.ind_name = (Env.ind_name oib); Env.ind_indices =
    (Env.ind_indices oib); Env.ind_sort = (Env.ind_sort oib); Env.ind_type =
    (inline should_inline _UU03a3_ (Env.ind_type oib)); Env.ind_kelim =
    (Env.ind_kelim oib); Env.ind_ctors =
    (map
      (Env.map_constructor_body npars arities (fun _ ->
        inline should_inline _UU03a3_)) (Env.ind_ctors oib)); Env.ind_projs =
    (map (fun pat ->
      let { Env.proj_name = p_nm; Env.proj_relevance = p_rel; Env.proj_type =
        p_ty } = pat
      in
      { Env.proj_name = p_nm; Env.proj_relevance = p_rel; Env.proj_type =
      (inline should_inline _UU03a3_ p_ty) }) (Env.ind_projs oib));
    Env.ind_relevance = (Env.ind_relevance oib) }

(** val inline_context_decl :
    (kername -> bool) -> Env.global_env -> term context_decl -> term
    context_decl **)

let inline_context_decl should_inline _UU03a3_ cd =
  { decl_name = cd.decl_name; decl_body =
    (option_map (inline should_inline _UU03a3_) cd.decl_body); decl_type =
    cd.decl_type }

(** val inline_in_decl :
    (kername -> bool) -> Env.global_env -> Env.global_decl -> Env.global_decl **)

let inline_in_decl should_inline _UU03a3_ = function
| Env.ConstantDecl cst ->
  Env.ConstantDecl (inline_in_constant_body should_inline _UU03a3_ cst)
| Env.InductiveDecl mib ->
  Env.InductiveDecl { Env.ind_finite = (Env.ind_finite mib); Env.ind_npars =
    (Env.ind_npars mib); Env.ind_params =
    (map (inline_context_decl should_inline _UU03a3_) (Env.ind_params mib));
    Env.ind_bodies =
    (let arities = Datatypes.length (Env.arities_context (Env.ind_bodies mib))
     in
     let npars = Env.context_assumptions (Env.ind_params mib) in
     map (inline_oib should_inline _UU03a3_ npars arities)
       (Env.ind_bodies mib)); Env.ind_universes = (Env.ind_universes mib);
    Env.ind_variance = (Env.ind_variance mib) }

(** val inline_globals :
    (kername -> bool) -> Env.global_declarations -> Env.global_declarations **)

let inline_globals should_inline _UU03a3_ =
  let new_UU03a3_ =
    fold_right (fun pat decls ->
      let (kn, decl) = pat in
      let _UU03a3_0 = { Env.universes = ContextSet.empty; Env.declarations =
        decls; Env.retroknowledge = Environment.Retroknowledge.empty }
      in
      (kn, (inline_in_decl should_inline _UU03a3_0 decl)) :: decls) []
      _UU03a3_
  in
  filter (fun pat -> let (kn, _) = pat in negb (should_inline kn)) new_UU03a3_

(** val template_inline : (kername -> bool) -> coq_TemplateTransform **)

let template_inline should_inline _UU03a3_ =
  Ok
    (timed (String ((Ascii (true, false, false, true, false, false, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (false, false, true, true, false, true, true,
      false)), (String ((Ascii (true, false, false, true, false, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (true, false, false, true, false, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (true, true, true, false, false, true, true,
      false)), EmptyString)))))))))))))))) (fun _ -> { Env.universes =
      (Env.universes _UU03a3_); Env.declarations =
      (inline_globals should_inline (Env.declarations _UU03a3_));
      Env.retroknowledge = (Env.retroknowledge _UU03a3_) }))
