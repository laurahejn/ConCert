open BasicAst
open PCUICAst
open PCUICEqualityDec
open PCUICTyping
open PCUICWfEnv
open PCUICWfUniverses
open Specif
open Universes0
open Config0
open UGraph0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val wf_gc_of_uctx :
    checker_flags -> PCUICEnvironment.global_env ->
    (VSet.t * GoodConstraintSet.t, __) sigT **)

let wf_gc_of_uctx cf _UU03a3_ =
  let o = gc_of_constraints cf (global_constraints _UU03a3_) in
  (match o with
   | Some a ->
     Coq_existT (((global_levels (PCUICEnvironment.universes _UU03a3_)), a),
       __)
   | None -> assert false (* absurd case *))

(** val graph_of_wf :
    checker_flags -> PCUICEnvironment.global_env -> (universes_graph, __) sigT **)

let graph_of_wf cf _UU03a3_ =
  let s = wf_gc_of_uctx cf _UU03a3_ in
  let Coq_existT (x, _) = s in Coq_existT ((make_graph x), __)

(** val wf_ext_gc_of_uctx :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    (VSet.t * GoodConstraintSet.t, __) sigT **)

let wf_ext_gc_of_uctx cf _UU03a3_ =
  let o = gc_of_constraints cf (global_ext_constraints _UU03a3_) in
  (match o with
   | Some a -> Coq_existT (((global_ext_levels _UU03a3_), a), __)
   | None -> assert false (* absurd case *))

(** val graph_of_wf_ext :
    checker_flags -> PCUICEnvironment.global_env_ext -> (universes_graph, __)
    sigT **)

let graph_of_wf_ext cf _UU03a3_ =
  let s = wf_ext_gc_of_uctx cf _UU03a3_ in
  let Coq_existT (x, _) = s in Coq_existT ((make_graph x), __)

type abstract_guard_impl =
  coq_FixCoFix -> PCUICEnvironment.global_env_ext -> PCUICEnvironment.context
  -> term mfixpoint -> bool
  (* singleton inductive, whose constructor was Build_abstract_guard_impl *)

(** val guard_impl :
    abstract_guard_impl -> coq_FixCoFix -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.context -> term mfixpoint -> bool **)

let guard_impl abstract_guard_impl0 =
  abstract_guard_impl0

type referenced_impl_ext =
  PCUICEnvironment.global_env_ext
  (* singleton inductive, whose constructor was Build_referenced_impl_ext *)

(** val referenced_impl_env_ext :
    checker_flags -> abstract_guard_impl -> referenced_impl_ext ->
    PCUICEnvironment.global_env_ext **)

let referenced_impl_env_ext _ _ r =
  r

(** val referenced_impl_ext_graph :
    checker_flags -> abstract_guard_impl -> referenced_impl_ext ->
    universes_graph **)

let referenced_impl_ext_graph cf guard r =
  projT1 (graph_of_wf_ext cf (referenced_impl_env_ext cf guard r))

type referenced_impl =
  PCUICEnvironment.global_env
  (* singleton inductive, whose constructor was Build_referenced_impl *)

(** val referenced_impl_env :
    checker_flags -> referenced_impl -> PCUICEnvironment.global_env **)

let referenced_impl_env _ r =
  r

(** val referenced_impl_graph :
    checker_flags -> referenced_impl -> universes_graph **)

let referenced_impl_graph cf r =
  projT1 (graph_of_wf cf (referenced_impl_env cf r))

(** val init_env : PCUICEnvironment.global_env **)

let init_env =
  { PCUICEnvironment.universes = ((LS.singleton Level.Coq_lzero), CS.empty);
    PCUICEnvironment.declarations = []; PCUICEnvironment.retroknowledge =
    Environment.Retroknowledge.empty }

(** val referenced_pop :
    checker_flags -> referenced_impl -> referenced_impl **)

let referenced_pop cf _UU03a3_ =
  let filtered_var =
    PCUICEnvironment.declarations (referenced_impl_env cf _UU03a3_)
  in
  (match filtered_var with
   | [] -> _UU03a3_
   | _ :: decls ->
     { PCUICEnvironment.universes =
       (PCUICEnvironment.universes (referenced_impl_env cf _UU03a3_));
       PCUICEnvironment.declarations = decls;
       PCUICEnvironment.retroknowledge =
       (PCUICEnvironment.retroknowledge (referenced_impl_env cf _UU03a3_)) })

(** val make_wf_env_ext :
    checker_flags -> abstract_guard_impl -> referenced_impl -> universes_decl
    -> referenced_impl_ext **)

let make_wf_env_ext cf _ _UU03a3_ univs =
  ((referenced_impl_env cf _UU03a3_), univs)

(** val canonical_abstract_env_struct :
    checker_flags -> abstract_guard_impl -> (referenced_impl,
    referenced_impl_ext) abstract_env_struct **)

let canonical_abstract_env_struct cf guard =
  { abstract_env_lookup = (fun _UU03a3_ ->
    PCUICEnvironment.lookup_env
      (PCUICEnvironment.fst_ctx (referenced_impl_env_ext cf guard _UU03a3_)));
    abstract_env_ext_retroknowledge = (fun _UU03a3_ ->
    PCUICEnvironment.retroknowledge
      (PCUICEnvironment.fst_ctx (referenced_impl_env_ext cf guard _UU03a3_)));
    abstract_env_conv_pb_relb = (fun _UU03a3_ conv_pb ->
    conv_pb_relb cf (referenced_impl_ext_graph cf guard _UU03a3_) conv_pb);
    abstract_env_compare_global_instance = (fun _UU03a3_ ->
    compare_global_instance
      (PCUICEnvironment.fst_ctx (referenced_impl_env_ext cf guard _UU03a3_))
      (check_eqb_universe cf (referenced_impl_ext_graph cf guard _UU03a3_)));
    abstract_env_level_mem = (fun _UU03a3_ ->
    level_mem (referenced_impl_env_ext cf guard _UU03a3_));
    abstract_env_ext_wf_universeb = (fun _UU03a3_ u ->
    wf_universeb (referenced_impl_env_ext cf guard _UU03a3_) u);
    abstract_env_check_constraints = (fun _UU03a3_ ->
    check_constraints cf (referenced_impl_ext_graph cf guard _UU03a3_));
    abstract_env_guard = (fun _UU03a3_ fix_cofix ->
    guard_impl guard fix_cofix (referenced_impl_env_ext cf guard _UU03a3_));
    abstract_env_empty = { PCUICEnvironment.universes =
    (PCUICEnvironment.universes init_env); PCUICEnvironment.declarations =
    []; PCUICEnvironment.retroknowledge = Environment.Retroknowledge.empty };
    abstract_env_init = (fun cs retro _ -> { PCUICEnvironment.universes = cs;
    PCUICEnvironment.declarations = []; PCUICEnvironment.retroknowledge =
    retro }); abstract_env_univ = (fun x ->
    PCUICEnvironment.universes (referenced_impl_env cf x));
    abstract_env_global_declarations = (fun x ->
    PCUICEnvironment.declarations (referenced_impl_env cf x));
    abstract_env_retroknowledge = (fun x ->
    PCUICEnvironment.retroknowledge (referenced_impl_env cf x));
    abstract_env_add_decl = (fun x kn d _ ->
    PCUICEnvironment.add_global_decl (referenced_impl_env cf x) (kn, d));
    abstract_env_empty_ext = (fun x -> ((referenced_impl_env cf x),
    Monomorphic_ctx)); abstract_env_is_consistent = (fun uctx ->
    Coq_wGraph.is_acyclic (make_graph uctx));
    abstract_env_is_consistent_uctx = (fun x uctx ->
    let g = referenced_impl_graph cf x in
    let g' = add_uctx uctx g in
    (&&) (Coq_wGraph.is_acyclic g')
      (Coq_wGraph.IsFullSubgraph.is_full_extension g g'));
    abstract_env_add_uctx = (fun x _ udecl _ _ ->
    ((referenced_impl_env cf x), udecl)); abstract_pop_decls =
    (referenced_pop cf); abstract_make_wf_env_ext = (fun x x0 _ ->
    make_wf_env_ext cf guard x x0) }

(** val canonical_abstract_env_impl :
    checker_flags -> abstract_guard_impl -> abstract_env_impl **)

let canonical_abstract_env_impl cf guard =
  Coq_existT (__, (Coq_existT (__, (Coq_existT
    ((Obj.magic canonical_abstract_env_struct cf guard), __)))))
