open BasicAst
open Byte
open Datatypes
open Kernames
open List0
open MCList
open MCString
open Nat0
open PCUICAst
open PCUICAstUtils
open PCUICPrimitive
open Primitive
open ReflectEq
open Specif
open Universes0
open Bytestring

(** val lookup_ind_decl :
    PCUICEnvironment.global_env -> kername -> nat ->
    ((PCUICEnvironment.one_inductive_body
    list * universes_decl) * PCUICEnvironment.one_inductive_body) option **)

let lookup_ind_decl _UU03a3_ ind i =
  match PCUICEnvironment.lookup_env _UU03a3_ ind with
  | Some g ->
    (match g with
     | PCUICEnvironment.ConstantDecl _ -> None
     | PCUICEnvironment.InductiveDecl m ->
       let { PCUICEnvironment.ind_finite = _; PCUICEnvironment.ind_npars = _;
         PCUICEnvironment.ind_params = _; PCUICEnvironment.ind_bodies = l;
         PCUICEnvironment.ind_universes = uctx;
         PCUICEnvironment.ind_variance = _ } = m
       in
       (match nth_error l i with
        | Some body -> Some ((l, uctx), body)
        | None -> None))
  | None -> None

(** val is_fresh : ident list -> ident -> bool **)

let is_fresh _UU0393_ id =
  forallb (fun id' -> negb (eqb IdentOT.reflect_eq_string id id')) _UU0393_

(** val name_from_term :
    PCUICEnvironment.global_env_ext -> term -> String.t **)

let rec name_from_term _UU03a3_ = function
| Coq_tRel _ -> String.String (Coq_x48, String.EmptyString)
| Coq_tVar _ -> String.String (Coq_x48, String.EmptyString)
| Coq_tEvar (_, _) -> String.String (Coq_x48, String.EmptyString)
| Coq_tSort _ -> String.String (Coq_x58, String.EmptyString)
| Coq_tProd (_, _, _) -> String.String (Coq_x66, String.EmptyString)
| Coq_tLambda (_, _, _) -> String.String (Coq_x66, String.EmptyString)
| Coq_tLetIn (_, _, _, t') -> name_from_term _UU03a3_ t'
| Coq_tApp (f, _) -> name_from_term _UU03a3_ f
| Coq_tConst (_, _) -> String.String (Coq_x78, String.EmptyString)
| Coq_tInd (ind, _) ->
  let { inductive_mind = i; inductive_ind = k } = ind in
  (match lookup_ind_decl (PCUICEnvironment.fst_ctx _UU03a3_) i k with
   | Some p ->
     let (_, body) = p in
     String.substring O (S O) (PCUICEnvironment.ind_name body)
   | None -> String.String (Coq_x58, String.EmptyString))
| _ -> String.String (Coq_x55, String.EmptyString)

(** val fresh_id_from : ident list -> nat -> String.t -> String.t **)

let fresh_id_from _UU0393_ n id =
  let rec aux i = match i with
  | O -> id
  | S i' ->
    let id' = String.append id (string_of_nat (sub n i)) in
    if is_fresh _UU0393_ id' then id' else aux i'
  in aux n

(** val fresh_name :
    PCUICEnvironment.global_env_ext -> ident list -> name -> term option ->
    ident **)

let fresh_name _UU03a3_ _UU0393_ na t0 =
  let id =
    match na with
    | Coq_nAnon ->
      (match t0 with
       | Some t1 -> name_from_term _UU03a3_ t1
       | None -> String.String (Coq_x5f, String.EmptyString))
    | Coq_nNamed id -> id
  in
  if is_fresh _UU0393_ id
  then id
  else fresh_id_from _UU0393_ (S (S (S (S (S (S (S (S (S (S O)))))))))) id

(** val fresh_names :
    PCUICEnvironment.global_env_ext -> ident list -> PCUICEnvironment.context
    -> ident list **)

let fresh_names _UU03a3_ _UU0393_ _UU0393_' =
  let rec aux _UU0393_ids = function
  | [] -> _UU0393_ids
  | decl :: _UU0393_1 ->
    aux
      ((fresh_name _UU03a3_ _UU0393_ids decl.decl_name.binder_name (Some
         decl.decl_type)) :: _UU0393_ids) _UU0393_1
  in aux _UU0393_ (rev _UU0393_')

module PrintTermTree =
 struct
  (** val print_prim : ('a1 -> Tree.t) -> term prim_val -> Tree.t **)

  let print_prim _ p =
    match projT2 p with
    | Coq_primIntModel f ->
      Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
        (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
        (Coq_x74, (String.String (Coq_x3a, (String.String (Coq_x20,
        String.EmptyString))))))))))))), (Tree.Coq_append ((Tree.Coq_string
        (string_of_prim_int f)), (Tree.Coq_string (String.String (Coq_x29,
        String.EmptyString))))))
    | Coq_primFloatModel f ->
      Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
        (String.String (Coq_x66, (String.String (Coq_x6c, (String.String
        (Coq_x6f, (String.String (Coq_x61, (String.String (Coq_x74,
        (String.String (Coq_x3a, (String.String (Coq_x20,
        String.EmptyString))))))))))))))))), (Tree.Coq_append
        ((Tree.Coq_string (string_of_float f)), (Tree.Coq_string
        (String.String (Coq_x29, String.EmptyString))))))

  (** val print_def :
      ('a1 -> Tree.t) -> ('a1 -> Tree.t) -> 'a1 def -> Tree.t **)

  let print_def f g def0 =
    Tree.Coq_append ((Tree.Coq_string
      (string_of_name def0.dname.binder_name)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x7b,
      (String.String (Coq_x20, (String.String (Coq_x73, (String.String
      (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x75,
      (String.String (Coq_x63, (String.String (Coq_x74, (String.String
      (Coq_x20, String.EmptyString))))))))))))))))))))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_nat def0.rarg)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x7d,
      String.EmptyString))))), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x20, (String.String (Coq_x3a, (String.String
      (Coq_x20, String.EmptyString))))))), (Tree.Coq_append ((f def0.dtype),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
      (String.String (Coq_x3a, (String.String (Coq_x3d, (String.String
      (Coq_x20, String.EmptyString))))))))), (Tree.Coq_append
      ((Tree.Coq_string nl), (g def0.dbody))))))))))))))))

  (** val print_defs :
      PCUICEnvironment.global_env_ext -> (ident list -> bool -> bool -> term
      -> Tree.t) -> ident list -> term mfixpoint -> Tree.t **)

  let print_defs _UU03a3_ print_term0 _UU0393_ defs =
    let ctx' = PCUICEnvironment.fix_context defs in
    Tree.print_list
      (print_def (print_term0 _UU0393_ true false)
        (print_term0 (fresh_names _UU03a3_ _UU0393_ ctx') true false))
      (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_string (String.String
      (Coq_x20, (String.String (Coq_x77, (String.String (Coq_x69,
      (String.String (Coq_x74, (String.String (Coq_x68, (String.String
      (Coq_x20, String.EmptyString))))))))))))))) defs

  (** val pr_context_decl :
      PCUICEnvironment.global_env_ext -> (ident list -> bool -> bool -> term
      -> Tree.t) -> ident list -> term context_decl -> ident * Tree.t **)

  let pr_context_decl _UU03a3_ print_term0 _UU0393_ c =
    let { decl_name = na; decl_body = decl_body0; decl_type = ty } = c in
    (match decl_body0 with
     | Some b ->
       let na' = fresh_name _UU03a3_ _UU0393_ na.binder_name (Some ty) in
       (na', (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
       String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string na'),
       (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
       (String.String (Coq_x3a, (String.String (Coq_x20,
       String.EmptyString))))))), (Tree.Coq_append
       ((print_term0 _UU0393_ true false ty), (Tree.Coq_append
       ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x3a,
       (String.String (Coq_x3d, (String.String (Coq_x20,
       String.EmptyString))))))))), (Tree.Coq_append
       ((print_term0 _UU0393_ true false b), (Tree.Coq_string (String.String
       (Coq_x29, String.EmptyString))))))))))))))))
     | None ->
       let na' = fresh_name _UU03a3_ _UU0393_ na.binder_name (Some ty) in
       (na', (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
       String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string na'),
       (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
       (String.String (Coq_x3a, (String.String (Coq_x20,
       String.EmptyString))))))), (Tree.Coq_append
       ((print_term0 _UU0393_ true false ty), (Tree.Coq_string (String.String
       (Coq_x29, String.EmptyString)))))))))))))

  (** val print_context_gen :
      PCUICEnvironment.global_env_ext -> (ident list -> bool -> bool -> term
      -> Tree.t) -> ident list -> term context_decl list -> ident
      list * Tree.t **)

  let rec print_context_gen _UU03a3_ print_term0 _UU0393_ = function
  | [] -> (_UU0393_, (Tree.Coq_string String.EmptyString))
  | d :: decls ->
    let (_UU0393_0, s) = print_context_gen _UU03a3_ print_term0 _UU0393_ decls
    in
    let (na, s') = pr_context_decl _UU03a3_ print_term0 _UU0393_0 d in
    (match decls with
     | [] -> ((na :: _UU0393_0), (Tree.Coq_append (s, s')))
     | _ :: _ ->
       ((na :: _UU0393_0), (Tree.Coq_append (s, (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x20, String.EmptyString))),
         s'))))))

  (** val print_context_names :
      PCUICEnvironment.global_env_ext -> ident list -> term context_decl list
      -> ident list * Tree.t **)

  let rec print_context_names _UU03a3_ _UU0393_ = function
  | [] -> (_UU0393_, (Tree.Coq_string String.EmptyString))
  | d :: decls ->
    let (_UU0393_0, s) = print_context_names _UU03a3_ _UU0393_ decls in
    let na =
      fresh_name _UU03a3_ _UU0393_0 d.decl_name.binder_name (Some d.decl_type)
    in
    (match decls with
     | [] -> ((na :: _UU0393_0), (Tree.Coq_append (s, (Tree.Coq_string na))))
     | _ :: _ ->
       ((na :: _UU0393_0), (Tree.Coq_append (s, (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x20, String.EmptyString))),
         (Tree.Coq_string na)))))))

  (** val print_term :
      PCUICEnvironment.global_env_ext -> bool -> ident list -> bool -> bool
      -> term -> Tree.t **)

  let rec print_term _UU03a3_ all _UU0393_ top inapp = function
  | Coq_tRel n ->
    (match nth_error _UU0393_ n with
     | Some id -> Tree.Coq_string id
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x52, (String.String
         (Coq_x65, (String.String (Coq_x6c, (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_nat n)), (Tree.Coq_string
         (String.String (Coq_x29, String.EmptyString)))))))
  | Coq_tVar n ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x56, (String.String
      (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string n),
      (Tree.Coq_string (String.String (Coq_x29, String.EmptyString))))))
  | Coq_tEvar (ev, _) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x45, (String.String
      (Coq_x76, (String.String (Coq_x61, (String.String (Coq_x72,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_nat ev)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x5b,
      (String.String (Coq_x5d, String.EmptyString))))), (Tree.Coq_string
      (String.String (Coq_x29, String.EmptyString))))))))
  | Coq_tSort s -> Tree.Coq_string (string_of_sort s)
  | Coq_tProd (na, dom, codom) ->
    let na' = fresh_name _UU03a3_ _UU0393_ na.binder_name (Some dom) in
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_xe2, (String.String (Coq_x88, (String.String (Coq_x80,
      (String.String (Coq_x20, String.EmptyString))))))))), (Tree.Coq_append
      ((Tree.Coq_string na'), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x20, (String.String (Coq_x3a, (String.String
      (Coq_x20, String.EmptyString))))))), (Tree.Coq_append
      ((print_term _UU03a3_ all _UU0393_ true false dom), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, (String.String (Coq_x20,
      String.EmptyString))))),
      (print_term _UU03a3_ all (na' :: _UU0393_) true false codom)))))))))))
  | Coq_tLambda (na, dom, body) ->
    let na' = fresh_name _UU03a3_ _UU0393_ na.binder_name (Some dom) in
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x66, (String.String (Coq_x75, (String.String (Coq_x6e,
      (String.String (Coq_x20, String.EmptyString))))))))), (Tree.Coq_append
      ((Tree.Coq_string na'), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x20, (String.String (Coq_x3a, (String.String
      (Coq_x20, String.EmptyString))))))), (Tree.Coq_append
      ((print_term _UU03a3_ all _UU0393_ true false dom), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x3d,
      (String.String (Coq_x3e, (String.String (Coq_x20,
      String.EmptyString))))))))),
      (print_term _UU03a3_ all (na' :: _UU0393_) true false body)))))))))))
  | Coq_tLetIn (na, def0, dom, body) ->
    let na' = fresh_name _UU03a3_ _UU0393_ na.binder_name (Some dom) in
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x74,
      String.EmptyString))))))), (Tree.Coq_append ((Tree.Coq_string na'),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
      (String.String (Coq_x3a, (String.String (Coq_x20,
      String.EmptyString))))))), (Tree.Coq_append
      ((print_term _UU03a3_ all _UU0393_ true false dom), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x3a,
      (String.String (Coq_x3d, (String.String (Coq_x20,
      String.EmptyString))))))))), (Tree.Coq_append
      ((print_term _UU03a3_ all _UU0393_ true false def0), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x20,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string nl),
      (print_term _UU03a3_ all (na' :: _UU0393_) true false body)))))))))))))))))
  | Coq_tApp (f, l) ->
    Tree.parens ((||) top inapp) (Tree.Coq_append
      ((print_term _UU03a3_ all _UU0393_ false true f), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, String.EmptyString))),
      (print_term _UU03a3_ all _UU0393_ false false l)))))
  | Coq_tConst (c, u) ->
    Tree.Coq_append ((Tree.Coq_string (string_of_kername c)),
      (Tree.Coq_string (print_universe_instance u)))
  | Coq_tInd (ind, u) ->
    let { inductive_mind = i; inductive_ind = k } = ind in
    (match lookup_ind_decl (PCUICEnvironment.fst_ctx _UU03a3_) i k with
     | Some p ->
       let (_, oib) = p in
       Tree.Coq_append ((Tree.Coq_string (PCUICEnvironment.ind_name oib)),
       (Tree.Coq_string (print_universe_instance u)))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x49, (String.String
         (Coq_x6e, (String.String (Coq_x64, (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))), (Tree.Coq_append
         ((Tree.Coq_string
         (string_of_inductive { inductive_mind = i; inductive_ind = k })),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_universe_instance u)), (Tree.Coq_string (String.String
         (Coq_x29, String.EmptyString)))))))))))
  | Coq_tConstruct (ind, l, u) ->
    let { inductive_mind = i; inductive_ind = k } = ind in
    (match lookup_ind_decl (PCUICEnvironment.fst_ctx _UU03a3_) i k with
     | Some p ->
       let (_, oib) = p in
       (match nth_error (PCUICEnvironment.ind_ctors oib) l with
        | Some cdecl ->
          Tree.Coq_append ((Tree.Coq_string
            (PCUICEnvironment.cstr_name cdecl)), (Tree.Coq_string
            (print_universe_instance u)))
        | None ->
          Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
            (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
            (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
            (String.String (Coq_x64, (String.String (Coq_x43, (String.String
            (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
            (String.String (Coq_x74, (String.String (Coq_x72, (String.String
            (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
            (String.String (Coq_x28,
            String.EmptyString))))))))))))))))))))))))))))))))))),
            (Tree.Coq_append ((Tree.Coq_string (string_of_inductive ind)),
            (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
            String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
            (string_of_nat l)), (Tree.Coq_append ((Tree.Coq_string
            (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
            ((Tree.Coq_string (string_of_universe_instance u)),
            (Tree.Coq_string (String.String (Coq_x29,
            String.EmptyString)))))))))))))))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x43, (String.String
         (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
         (String.String (Coq_x74, (String.String (Coq_x72, (String.String
         (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
         (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))))))))))))))),
         (Tree.Coq_append ((Tree.Coq_string (string_of_inductive ind)),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_nat l)), (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_universe_instance u)), (Tree.Coq_string
         (String.String (Coq_x29, String.EmptyString)))))))))))))))
  | Coq_tCase (indn, p, t1, brs) ->
    let { ci_ind = ind; ci_npar = _; ci_relevance = _ } = indn in
    let { inductive_mind = mind; inductive_ind = i } = ind in
    (match lookup_ind_decl (PCUICEnvironment.fst_ctx _UU03a3_) mind i with
     | Some p0 ->
       let (_, oib) = p0 in
       let _UU0393_ret = p.pcontext in
       let _UU0393_ret0 = fresh_names _UU03a3_ _UU0393_ _UU0393_ret in
       let ret_binders = firstn (length p.pcontext) _UU0393_ret0 in
       let as_name =
         hd (String.String (Coq_x5f, String.EmptyString)) ret_binders
       in
       let indices = rev (tl ret_binders) in
       let in_args =
         app
           (repeat (String.String (Coq_x5f, String.EmptyString))
             (length p.pparams)) indices
       in
       let in_str = Tree.Coq_append ((Tree.Coq_string
         (PCUICEnvironment.ind_name oib)),
         (Tree.concat (Tree.Coq_string String.EmptyString)
           (map (fun a -> Tree.Coq_append ((Tree.Coq_string (String.String
             (Coq_x20, String.EmptyString))), (Tree.Coq_string a))) in_args)))
       in
       let brs0 =
         map (fun br ->
           let (_UU0393_ctx, pctx) =
             if all
             then print_context_gen _UU03a3_ (print_term _UU03a3_ all)
                    _UU0393_ br.bcontext
             else print_context_names _UU03a3_ _UU0393_ br.bcontext
           in
           Tree.Coq_append (pctx, (Tree.Coq_append ((Tree.Coq_string
           (String.String (Coq_x20, (String.String (Coq_xe2, (String.String
           (Coq_x87, (String.String (Coq_x92, (String.String (Coq_x20,
           String.EmptyString))))))))))),
           (print_term _UU03a3_ all _UU0393_ctx true false br.bbody))))) brs
       in
       let brs1 = combine brs0 (PCUICEnvironment.ind_ctors oib) in
       Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
         (Coq_x6d, (String.String (Coq_x61, (String.String (Coq_x74,
         (String.String (Coq_x63, (String.String (Coq_x68, (String.String
         (Coq_x20, String.EmptyString))))))))))))), (Tree.Coq_append
         ((print_term _UU03a3_ all _UU0393_ true false t1), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x61,
         (String.String (Coq_x73, (String.String (Coq_x20,
         String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string
         as_name), (Tree.Coq_append ((Tree.Coq_string (String.String
         (Coq_x20, (String.String (Coq_x69, (String.String (Coq_x6e,
         (String.String (Coq_x20, String.EmptyString))))))))),
         (Tree.Coq_append (in_str, (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x20, (String.String (Coq_x72, (String.String
         (Coq_x65, (String.String (Coq_x74, (String.String (Coq_x75,
         (String.String (Coq_x72, (String.String (Coq_x6e, (String.String
         (Coq_x20, String.EmptyString))))))))))))))))), (Tree.Coq_append
         ((print_term _UU03a3_ all _UU0393_ret0 true false p.preturn),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x20,
         (String.String (Coq_x77, (String.String (Coq_x69, (String.String
         (Coq_x74, (String.String (Coq_x68, (String.String (Coq_x20,
         String.EmptyString))))))))))))), (Tree.Coq_append ((Tree.Coq_string
         nl), (Tree.Coq_append
         ((Tree.print_list (fun pat ->
            let (b, cdecl) = pat in
            Tree.Coq_append ((Tree.Coq_string
            (PCUICEnvironment.cstr_name cdecl)), (Tree.Coq_append
            ((Tree.Coq_string (String.String (Coq_x20, String.EmptyString))),
            b)))) (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_string
            (String.String (Coq_x20, (String.String (Coq_x7c, (String.String
            (Coq_x20, String.EmptyString))))))))) brs1), (Tree.Coq_append
         ((Tree.Coq_string nl), (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
         (Coq_x64, String.EmptyString))))))), (Tree.Coq_string
         nl)))))))))))))))))))))))))))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43,
         (String.String (Coq_x61, (String.String (Coq_x73, (String.String
         (Coq_x65, (String.String (Coq_x28, String.EmptyString))))))))))),
         (Tree.Coq_append ((Tree.Coq_string (string_of_inductive ind)),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_nat i)), (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_term t1)), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
         (Tree.Coq_append ((Tree.Coq_string
         (string_of_predicate string_of_term p)), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
         (Tree.Coq_append
         ((Tree.string_of_list (fun b -> Tree.Coq_string
            (pretty_string_of_branch string_of_term b)) brs),
         (Tree.Coq_string (String.String (Coq_x29,
         String.EmptyString)))))))))))))))))))))))
  | Coq_tProj (p, c) ->
    (match lookup_projection (PCUICEnvironment.fst_ctx _UU03a3_) p with
     | Some p0 ->
       let (_, pdecl) = p0 in
       Tree.Coq_append ((print_term _UU03a3_ all _UU0393_ false false c),
       (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2e,
       (String.String (Coq_x28, String.EmptyString))))), (Tree.Coq_append
       ((Tree.Coq_string (PCUICEnvironment.proj_name pdecl)),
       (Tree.Coq_string (String.String (Coq_x29, String.EmptyString))))))))
     | None ->
       Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x55,
         (String.String (Coq_x6e, (String.String (Coq_x62, (String.String
         (Coq_x6f, (String.String (Coq_x75, (String.String (Coq_x6e,
         (String.String (Coq_x64, (String.String (Coq_x50, (String.String
         (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x6a,
         (String.String (Coq_x28,
         String.EmptyString))))))))))))))))))))))))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_inductive p.proj_ind)),
         (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
         (string_of_nat p.proj_npars)), (Tree.Coq_append ((Tree.Coq_string
         (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
         ((Tree.Coq_string (string_of_nat p.proj_arg)), (Tree.Coq_append
         ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
         (Tree.Coq_append ((print_term _UU03a3_ all _UU0393_ true false c),
         (Tree.Coq_string (String.String (Coq_x29,
         String.EmptyString)))))))))))))))))))
  | Coq_tFix (l, n) ->
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x74,
      (String.String (Coq_x20, (String.String (Coq_x66, (String.String
      (Coq_x69, (String.String (Coq_x78, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))), (Tree.Coq_append
      ((print_defs _UU03a3_ (print_term _UU03a3_ all) _UU0393_ l),
      (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x20,
      String.EmptyString))))))))), (Tree.Coq_string
      (nth_default (string_of_nat n)
        (map (let f0 = fun d -> d.dname in fun x -> string_of_aname (f0 x)) l)
        n))))))))))
  | Coq_tCoFix (l, n) ->
    Tree.parens top (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x74,
      (String.String (Coq_x20, (String.String (Coq_x63, (String.String
      (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x69,
      (String.String (Coq_x78, (String.String (Coq_x20,
      String.EmptyString))))))))))))))))))))), (Tree.Coq_append
      ((print_defs _UU03a3_ (print_term _UU03a3_ all) _UU0393_ l),
      (Tree.Coq_append ((Tree.Coq_string nl), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x20, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x20,
      String.EmptyString))))))))), (Tree.Coq_string
      (nth_default (string_of_nat n)
        (map (let f0 = fun d -> d.dname in fun x -> string_of_aname (f0 x)) l)
        n))))))))))
  | Coq_tPrim i ->
    Tree.parens top
      (print_prim (print_term _UU03a3_ all _UU0393_ true false) i)
 end

(** val print_term :
    PCUICEnvironment.global_env_ext -> bool -> ident list -> bool -> bool ->
    term -> String.t **)

let print_term _UU03a3_ all _UU0393_ top inapp t0 =
  Tree.to_string (PrintTermTree.print_term _UU03a3_ all _UU0393_ top inapp t0)

(** val print_context :
    PCUICEnvironment.global_env_ext -> ident list -> term context_decl list
    -> String.t **)

let print_context _UU03a3_ _UU0393_ _UU0394_ =
  Tree.to_string
    (snd
      (PrintTermTree.print_context_gen _UU03a3_
        (PrintTermTree.print_term _UU03a3_ true) _UU0393_ _UU0394_))
