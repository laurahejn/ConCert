open All_Forall
open BasicAst
open Basics
open CRelationClasses
open Classes0
open Datatypes
open EAst
open EAstUtils
open EqDecInstances
open ErasureFunction
open ExAst
open Kernames
open List0
open MCList
open MCProd
open MCReflect
open PCUICAst
open PCUICAstUtils
open PCUICErrors
open PCUICNormal
open PCUICPrimitive
open PCUICSafeReduce
open PCUICSafeRetyping
open PCUICTyping
open PCUICWfEnv
open PCUICWfEnvImpl
open Primitive
open ReflectEq
open Signature
open Specif
open Universes0
open Vector
open VectorDef
open Bytestring
open Config0

type __ = Obj.t

module P :
 sig
  type 'term predicate = 'term PCUICAst.predicate = { pparams : 'term list;
                                                      puinst : Instance.t;
                                                      pcontext : 'term
                                                                 BasicAst.context_decl
                                                                 list;
                                                      preturn : 'term }

  val pparams : 'a1 predicate -> 'a1 list

  val puinst : 'a1 predicate -> Instance.t

  val pcontext : 'a1 predicate -> 'a1 BasicAst.context_decl list

  val preturn : 'a1 predicate -> 'a1

  val coq_NoConfusionPackage_predicate : 'a1 predicate coq_NoConfusionPackage

  val map_predicate :
    (Instance.t -> Instance.t) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1
    BasicAst.context_decl list -> 'a2 BasicAst.context_decl list) -> 'a1
    predicate -> 'a2 predicate

  val shiftf : (nat -> 'a1 -> 'a2) -> nat -> nat -> 'a1 -> 'a2

  val map_predicate_k :
    (Instance.t -> Instance.t) -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 predicate
    -> 'a1 predicate

  val test_predicate :
    (Instance.t -> bool) -> ('a1 -> bool) -> 'a1 predicate -> bool

  val test_predicate_k :
    (Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1 predicate ->
    bool

  val test_predicate_ku :
    (nat -> Instance.t -> bool) -> (nat -> 'a1 -> bool) -> nat -> 'a1
    predicate -> bool

  type 'term branch = 'term PCUICAst.branch = { bcontext : 'term
                                                           BasicAst.context_decl
                                                           list; bbody : 
                                                'term }

  val bcontext : 'a1 branch -> 'a1 BasicAst.context_decl list

  val bbody : 'a1 branch -> 'a1

  val coq_NoConfusionPackage_branch : 'a1 branch coq_NoConfusionPackage

  val string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t

  val pretty_string_of_branch : ('a1 -> String.t) -> 'a1 branch -> String.t

  val test_branch : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 branch -> bool

  val test_branch_k :
    'a1 predicate -> (nat -> 'a1 -> bool) -> nat -> 'a1 branch -> bool

  val map_branch :
    ('a1 -> 'a2) -> ('a1 BasicAst.context_decl list -> 'a2
    BasicAst.context_decl list) -> 'a1 branch -> 'a2 branch

  val map_branches :
    ('a1 -> 'a2) -> ('a1 BasicAst.context_decl list -> 'a2
    BasicAst.context_decl list) -> 'a1 branch list -> 'a2 branch list

  val map_branch_k :
    (nat -> 'a1 -> 'a2) -> ('a1 BasicAst.context_decl list -> 'a2
    BasicAst.context_decl list) -> nat -> 'a1 branch -> 'a2 branch

  module Coq__1 : sig
   type term = PCUICAst.term =
   | Coq_tRel of nat
   | Coq_tVar of ident
   | Coq_tEvar of nat * term list
   | Coq_tSort of Universe.t
   | Coq_tProd of aname * term * term
   | Coq_tLambda of aname * term * term
   | Coq_tLetIn of aname * term * term * term
   | Coq_tApp of term * term
   | Coq_tConst of kername * Instance.t
   | Coq_tInd of inductive * Instance.t
   | Coq_tConstruct of inductive * nat * Instance.t
   | Coq_tCase of case_info * term predicate * term * term branch list
   | Coq_tProj of projection * term
   | Coq_tFix of term BasicAst.mfixpoint * nat
   | Coq_tCoFix of term BasicAst.mfixpoint * nat
   | Coq_tPrim of term prim_val
  end
  include module type of struct include Coq__1 end

  val term_rect :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (Universe.t -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
    (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 ->
    term -> 'a1 -> term -> 'a1 -> 'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1)
    -> (kername -> Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) ->
    (inductive -> nat -> Instance.t -> 'a1) -> (case_info -> term predicate
    -> term -> 'a1 -> term branch list -> 'a1) -> (projection -> term -> 'a1
    -> 'a1) -> (term BasicAst.mfixpoint -> nat -> 'a1) -> (term
    BasicAst.mfixpoint -> nat -> 'a1) -> (term prim_val -> 'a1) -> term -> 'a1

  val term_rec :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (Universe.t -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
    (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 ->
    term -> 'a1 -> term -> 'a1 -> 'a1) -> (term -> 'a1 -> term -> 'a1 -> 'a1)
    -> (kername -> Instance.t -> 'a1) -> (inductive -> Instance.t -> 'a1) ->
    (inductive -> nat -> Instance.t -> 'a1) -> (case_info -> term predicate
    -> term -> 'a1 -> term branch list -> 'a1) -> (projection -> term -> 'a1
    -> 'a1) -> (term BasicAst.mfixpoint -> nat -> 'a1) -> (term
    BasicAst.mfixpoint -> nat -> 'a1) -> (term prim_val -> 'a1) -> term -> 'a1

  val coq_NoConfusionPackage_term : term coq_NoConfusionPackage

  val mkApps : term -> term list -> term

  val isApp : term -> bool

  val isLambda : term -> bool

  type parameter_entry = PCUICAst.parameter_entry = { parameter_entry_type : 
                                                      term;
                                                      parameter_entry_universes : 
                                                      universes_decl }

  val parameter_entry_type : parameter_entry -> term

  val parameter_entry_universes : parameter_entry -> universes_decl

  type definition_entry = PCUICAst.definition_entry = { definition_entry_type : 
                                                        term;
                                                        definition_entry_body : 
                                                        term;
                                                        definition_entry_universes : 
                                                        universes_decl;
                                                        definition_entry_opaque : 
                                                        bool }

  val definition_entry_type : definition_entry -> term

  val definition_entry_body : definition_entry -> term

  val definition_entry_universes : definition_entry -> universes_decl

  val definition_entry_opaque : definition_entry -> bool

  type constant_entry = PCUICAst.constant_entry =
  | ParameterEntry of parameter_entry
  | DefinitionEntry of definition_entry

  val constant_entry_rect :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1

  val constant_entry_rec :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1

  val coq_NoConfusionPackage_parameter_entry :
    parameter_entry coq_NoConfusionPackage

  val coq_NoConfusionPackage_definition_entry :
    definition_entry coq_NoConfusionPackage

  val coq_NoConfusionPackage_constant_entry :
    constant_entry coq_NoConfusionPackage

  type local_entry = PCUICAst.local_entry =
  | LocalDef of term
  | LocalAssum of term

  val local_entry_rect : (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1

  val local_entry_rec : (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1

  type one_inductive_entry = PCUICAst.one_inductive_entry = { mind_entry_typename : 
                                                              ident;
                                                              mind_entry_arity : 
                                                              term;
                                                              mind_entry_template : 
                                                              bool;
                                                              mind_entry_consnames : 
                                                              ident list;
                                                              mind_entry_lc : 
                                                              term list }

  val mind_entry_typename : one_inductive_entry -> ident

  val mind_entry_arity : one_inductive_entry -> term

  val mind_entry_template : one_inductive_entry -> bool

  val mind_entry_consnames : one_inductive_entry -> ident list

  val mind_entry_lc : one_inductive_entry -> term list

  type mutual_inductive_entry = PCUICAst.mutual_inductive_entry = { mind_entry_record : 
                                                                    ident
                                                                    option
                                                                    option;
                                                                    mind_entry_finite : 
                                                                    recursivity_kind;
                                                                    mind_entry_params : 
                                                                    (ident * local_entry)
                                                                    list;
                                                                    mind_entry_inds : 
                                                                    one_inductive_entry
                                                                    list;
                                                                    mind_entry_universes : 
                                                                    universes_decl;
                                                                    mind_entry_private : 
                                                                    bool
                                                                    option }

  val mind_entry_record : mutual_inductive_entry -> ident option option

  val mind_entry_finite : mutual_inductive_entry -> recursivity_kind

  val mind_entry_params : mutual_inductive_entry -> (ident * local_entry) list

  val mind_entry_inds : mutual_inductive_entry -> one_inductive_entry list

  val mind_entry_universes : mutual_inductive_entry -> universes_decl

  val mind_entry_private : mutual_inductive_entry -> bool option

  val coq_NoConfusionPackage_local_entry : local_entry coq_NoConfusionPackage

  val coq_NoConfusionPackage_one_inductive_entry :
    one_inductive_entry coq_NoConfusionPackage

  val coq_NoConfusionPackage_mutual_inductive_entry :
    mutual_inductive_entry coq_NoConfusionPackage

  val lift : nat -> nat -> term -> term

  val subst : term list -> nat -> term -> term

  val subst1 : term -> nat -> term -> term

  val closedn : nat -> term -> bool

  val test_context_nlict :
    (term -> bool) -> term BasicAst.context_decl list -> bool

  val test_branch_nlict : (term -> bool) -> term branch -> bool

  val test_branches_nlict : (term -> bool) -> term branch list -> bool

  val nlict : term -> bool

  val noccur_between : nat -> nat -> term -> bool

  val subst_instance_constr : term coq_UnivSubst

  val closedu : nat -> term -> bool

  module PCUICTerm :
   sig
    type term = Coq__1.term

    val tRel : nat -> Coq__1.term

    val tSort : Universe.t -> Coq__1.term

    val tProd : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term

    val tLambda : aname -> Coq__1.term -> Coq__1.term -> Coq__1.term

    val tLetIn :
      aname -> Coq__1.term -> Coq__1.term -> Coq__1.term -> Coq__1.term

    val tInd : inductive -> Instance.t -> Coq__1.term

    val tProj : projection -> Coq__1.term -> Coq__1.term

    val mkApps : Coq__1.term -> Coq__1.term list -> Coq__1.term

    val lift : nat -> nat -> Coq__1.term -> Coq__1.term

    val subst : Coq__1.term list -> nat -> Coq__1.term -> Coq__1.term

    val closedn : nat -> Coq__1.term -> bool

    val noccur_between : nat -> nat -> Coq__1.term -> bool

    val subst_instance_constr : Instance.t -> Coq__1.term -> Coq__1.term
   end

  module PCUICEnvironment :
   sig
    type typ_or_sort = term typ_or_sort_

    val vass : aname -> term -> term BasicAst.context_decl

    val vdef : aname -> term -> term -> term BasicAst.context_decl

    type context = term BasicAst.context_decl list

    val lift_decl :
      nat -> nat -> term BasicAst.context_decl -> term BasicAst.context_decl

    val lift_context : nat -> nat -> context -> context

    val subst_context : term list -> nat -> context -> context

    val subst_decl :
      term list -> nat -> term BasicAst.context_decl -> term
      BasicAst.context_decl

    val subst_telescope : term list -> nat -> context -> context

    val subst_instance_decl : term BasicAst.context_decl coq_UnivSubst

    val subst_instance_context : context coq_UnivSubst

    val set_binder_name :
      aname -> term BasicAst.context_decl -> term BasicAst.context_decl

    val context_assumptions : context -> nat

    val is_assumption_context : context -> bool

    val smash_context : context -> context -> context

    val extended_subst : context -> nat -> term list

    val expand_lets_k : context -> nat -> term -> term

    val expand_lets : context -> term -> term

    val expand_lets_k_ctx : context -> nat -> context -> context

    val expand_lets_ctx : context -> context -> context

    val fix_context : term BasicAst.mfixpoint -> context

    type constructor_body = PCUICEnvironment.constructor_body = { cstr_name : 
                                                                  ident;
                                                                  cstr_args : 
                                                                  context;
                                                                  cstr_indices : 
                                                                  term list;
                                                                  cstr_type : 
                                                                  term;
                                                                  cstr_arity : 
                                                                  nat }

    val cstr_name : constructor_body -> ident

    val cstr_args : constructor_body -> context

    val cstr_indices : constructor_body -> term list

    val cstr_type : constructor_body -> term

    val cstr_arity : constructor_body -> nat

    type projection_body = PCUICEnvironment.projection_body = { proj_name : 
                                                                ident;
                                                                proj_relevance : 
                                                                relevance;
                                                                proj_type : 
                                                                term }

    val proj_name : projection_body -> ident

    val proj_relevance : projection_body -> relevance

    val proj_type : projection_body -> term

    val map_constructor_body :
      nat -> nat -> (nat -> term -> term) -> constructor_body ->
      constructor_body

    val map_projection_body :
      nat -> (nat -> term -> term) -> projection_body -> projection_body

    type one_inductive_body = PCUICEnvironment.one_inductive_body = { 
    ind_name : ident; ind_indices : context; ind_sort : Universe.t;
    ind_type : term; ind_kelim : allowed_eliminations;
    ind_ctors : constructor_body list; ind_projs : projection_body list;
    ind_relevance : relevance }

    val ind_name : one_inductive_body -> ident

    val ind_indices : one_inductive_body -> context

    val ind_sort : one_inductive_body -> Universe.t

    val ind_type : one_inductive_body -> term

    val ind_kelim : one_inductive_body -> allowed_eliminations

    val ind_ctors : one_inductive_body -> constructor_body list

    val ind_projs : one_inductive_body -> projection_body list

    val ind_relevance : one_inductive_body -> relevance

    val map_one_inductive_body :
      nat -> nat -> (nat -> term -> term) -> one_inductive_body ->
      one_inductive_body

    type mutual_inductive_body = PCUICEnvironment.mutual_inductive_body = { 
    ind_finite : recursivity_kind; ind_npars : nat; ind_params : context;
    ind_bodies : one_inductive_body list; ind_universes : universes_decl;
    ind_variance : Variance.t list option }

    val ind_finite : mutual_inductive_body -> recursivity_kind

    val ind_npars : mutual_inductive_body -> nat

    val ind_params : mutual_inductive_body -> context

    val ind_bodies : mutual_inductive_body -> one_inductive_body list

    val ind_universes : mutual_inductive_body -> universes_decl

    val ind_variance : mutual_inductive_body -> Variance.t list option

    type constant_body = PCUICEnvironment.constant_body = { cst_type : 
                                                            term;
                                                            cst_body : 
                                                            term option;
                                                            cst_universes : 
                                                            universes_decl;
                                                            cst_relevance : 
                                                            relevance }

    val cst_type : constant_body -> term

    val cst_body : constant_body -> term option

    val cst_universes : constant_body -> universes_decl

    val cst_relevance : constant_body -> relevance

    val map_constant_body : (term -> term) -> constant_body -> constant_body

    type global_decl = PCUICEnvironment.global_decl =
    | ConstantDecl of constant_body
    | InductiveDecl of mutual_inductive_body

    val global_decl_rect :
      (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
      -> 'a1

    val global_decl_rec :
      (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) -> global_decl
      -> 'a1

    val coq_NoConfusionPackage_global_decl :
      global_decl coq_NoConfusionPackage

    type global_declarations = (kername * global_decl) list

    type global_env = PCUICEnvironment.global_env = { universes : ContextSet.t;
                                                      declarations : 
                                                      global_declarations;
                                                      retroknowledge : 
                                                      Environment.Retroknowledge.t }

    val universes : global_env -> ContextSet.t

    val declarations : global_env -> global_declarations

    val retroknowledge : global_env -> Environment.Retroknowledge.t

    val empty_global_env : global_env

    val add_global_decl : global_env -> (kername * global_decl) -> global_env

    val set_declarations : global_env -> global_declarations -> global_env

    val lookup_global : global_declarations -> kername -> global_decl option

    val lookup_env : global_env -> kername -> global_decl option

    type extends = (__, ((kername * global_decl) list, __) sigT, __) and3

    type extends_decls =
      (__, ((kername * global_decl) list, __) sigT, __) and3

    val extends_decls_extends :
      global_env -> global_env -> extends_decls -> extends

    val extends_decls_refl : (global_env, extends_decls) coq_Reflexive

    val extends_refl : (global_env, extends) coq_Reflexive

    val primitive_constant : global_env -> prim_tag -> kername option

    type primitive_invariants = (Universe.t, __) sigT

    type global_env_ext = global_env * universes_decl

    val fst_ctx : global_env_ext -> global_env

    val empty_ext : global_env -> global_env_ext

    type program = global_env * term

    val app_context : context -> context -> context

    val mkLambda_or_LetIn : term BasicAst.context_decl -> term -> term

    val it_mkLambda_or_LetIn : context -> term -> term

    val mkProd_or_LetIn : term BasicAst.context_decl -> term -> term

    val it_mkProd_or_LetIn : context -> term -> term

    val reln :
      term list -> nat -> term BasicAst.context_decl list -> term list

    val to_extended_list_k :
      term BasicAst.context_decl list -> nat -> term list

    val to_extended_list : term BasicAst.context_decl list -> term list

    val reln_alt : nat -> context -> term list

    val arities_context :
      one_inductive_body list -> term BasicAst.context_decl list

    val map_mutual_inductive_body :
      (nat -> term -> term) -> mutual_inductive_body -> mutual_inductive_body

    val projs : inductive -> nat -> nat -> term list

    type 'p coq_All_decls = 'p PCUICEnvironment.coq_All_decls =
    | Coq_on_vass of aname * term * term * 'p
    | Coq_on_vdef of aname * term * term * term * term * 'p * 'p

    val coq_All_decls_rect :
      (aname -> term -> term -> 'a1 -> 'a2) -> (aname -> term -> term -> term
      -> term -> 'a1 -> 'a1 -> 'a2) -> term BasicAst.context_decl -> term
      BasicAst.context_decl -> 'a1 coq_All_decls -> 'a2

    val coq_All_decls_rec :
      (aname -> term -> term -> 'a1 -> 'a2) -> (aname -> term -> term -> term
      -> term -> 'a1 -> 'a1 -> 'a2) -> term BasicAst.context_decl -> term
      BasicAst.context_decl -> 'a1 coq_All_decls -> 'a2

    type 'p coq_All_decls_sig = 'p coq_All_decls

    val coq_All_decls_sig_pack :
      term BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls -> (term BasicAst.context_decl * term
      BasicAst.context_decl) * 'a1 coq_All_decls

    val coq_All_decls_Signature :
      term BasicAst.context_decl -> term BasicAst.context_decl -> ('a1
      coq_All_decls, term BasicAst.context_decl * term BasicAst.context_decl,
      'a1 coq_All_decls_sig) coq_Signature

    val coq_NoConfusionPackage_All_decls :
      ((term BasicAst.context_decl * term BasicAst.context_decl) * 'a1
      coq_All_decls) coq_NoConfusionPackage

    type 'p coq_All_decls_alpha = 'p PCUICEnvironment.coq_All_decls_alpha =
    | Coq_on_vass_alpha of name binder_annot * name binder_annot * term
       * term * 'p
    | Coq_on_vdef_alpha of name binder_annot * name binder_annot * term
       * term * term * term * 'p * 'p

    val coq_All_decls_alpha_rect :
      (name binder_annot -> name binder_annot -> term -> term -> __ -> 'a1 ->
      'a2) -> (name binder_annot -> name binder_annot -> term -> term -> term
      -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term BasicAst.context_decl ->
      term BasicAst.context_decl -> 'a1 coq_All_decls_alpha -> 'a2

    val coq_All_decls_alpha_rec :
      (name binder_annot -> name binder_annot -> term -> term -> __ -> 'a1 ->
      'a2) -> (name binder_annot -> name binder_annot -> term -> term -> term
      -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term BasicAst.context_decl ->
      term BasicAst.context_decl -> 'a1 coq_All_decls_alpha -> 'a2

    type 'p coq_All_decls_alpha_sig = 'p coq_All_decls_alpha

    val coq_All_decls_alpha_sig_pack :
      term BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls_alpha -> (term BasicAst.context_decl * term
      BasicAst.context_decl) * 'a1 coq_All_decls_alpha

    val coq_All_decls_alpha_Signature :
      term BasicAst.context_decl -> term BasicAst.context_decl -> ('a1
      coq_All_decls_alpha, term BasicAst.context_decl * term
      BasicAst.context_decl, 'a1 coq_All_decls_alpha_sig) coq_Signature

    val coq_NoConfusionPackage_All_decls_alpha :
      ((term BasicAst.context_decl * term BasicAst.context_decl) * 'a1
      coq_All_decls_alpha) coq_NoConfusionPackage

    val coq_All_decls_impl :
      term BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls -> (term -> term -> 'a1 -> 'a2) -> 'a2 coq_All_decls

    val coq_All_decls_alpha_impl :
      term BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls_alpha -> (term -> term -> 'a1 -> 'a2) -> 'a2
      coq_All_decls_alpha

    val coq_All_decls_to_alpha :
      term BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls -> 'a1 coq_All_decls_alpha

    type 'p coq_All2_fold_over =
      (term BasicAst.context_decl, (term BasicAst.context_decl, term
      BasicAst.context_decl, 'p) coq_All_over) coq_All2_fold
   end

  val destArity :
    term BasicAst.context_decl list -> term -> (term BasicAst.context_decl
    list * Universe.t) option

  val inds :
    kername -> Instance.t -> PCUICEnvironment.one_inductive_body list -> term
    list

  module PCUICTermUtils :
   sig
    val destArity :
      term BasicAst.context_decl list -> term -> (term BasicAst.context_decl
      list * Universe.t) option

    val inds :
      kername -> Instance.t -> PCUICEnvironment.one_inductive_body list ->
      term list
   end

  module PCUICEnvTyping :
   sig
    type 'typing coq_All_local_env = 'typing PCUICEnvTyping.coq_All_local_env =
    | Coq_localenv_nil
    | Coq_localenv_cons_abs of PCUICEnvironment.context * aname * term
       * 'typing coq_All_local_env * 'typing
    | Coq_localenv_cons_def of PCUICEnvironment.context * aname * term * 
       term * 'typing coq_All_local_env * 'typing * 'typing

    val coq_All_local_env_rect :
      'a2 -> (PCUICEnvironment.context -> aname -> term -> 'a1
      coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> (PCUICEnvironment.context ->
      aname -> term -> term -> 'a1 coq_All_local_env -> 'a2 -> 'a1 -> 'a1 ->
      'a2) -> PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a2

    val coq_All_local_env_rec :
      'a2 -> (PCUICEnvironment.context -> aname -> term -> 'a1
      coq_All_local_env -> 'a2 -> 'a1 -> 'a2) -> (PCUICEnvironment.context ->
      aname -> term -> term -> 'a1 coq_All_local_env -> 'a2 -> 'a1 -> 'a1 ->
      'a2) -> PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a2

    type 'typing coq_All_local_env_sig = 'typing coq_All_local_env

    val coq_All_local_env_sig_pack :
      PCUICEnvironment.context -> 'a1 coq_All_local_env ->
      PCUICEnvironment.context * 'a1 coq_All_local_env

    val coq_All_local_env_Signature :
      PCUICEnvironment.context -> ('a1 coq_All_local_env,
      PCUICEnvironment.context, 'a1 coq_All_local_env_sig) coq_Signature

    val coq_NoConfusionPackage_All_local_env :
      (PCUICEnvironment.context * 'a1 coq_All_local_env)
      coq_NoConfusionPackage

    val coq_All_local_env_fold :
      (nat -> term -> term) -> PCUICEnvironment.context -> ('a1
      coq_All_local_env, 'a1 coq_All_local_env) iffT

    val coq_All_local_env_impl :
      PCUICEnvironment.context -> 'a1 coq_All_local_env ->
      (PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort ->
      'a1 -> 'a2) -> 'a2 coq_All_local_env

    val coq_All_local_env_impl_ind :
      PCUICEnvironment.context -> 'a1 coq_All_local_env ->
      (PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort ->
      'a2 coq_All_local_env -> 'a1 -> 'a2) -> 'a2 coq_All_local_env

    val coq_All_local_env_skipn :
      PCUICEnvironment.context -> 'a1 coq_All_local_env -> nat -> 'a1
      coq_All_local_env

    type 'p coq_All_local_rel = 'p coq_All_local_env

    val coq_All_local_rel_nil :
      PCUICEnvironment.context -> 'a1 coq_All_local_rel

    val coq_All_local_rel_abs :
      PCUICEnvironment.context -> PCUICEnvironment.context -> term -> aname
      -> 'a1 coq_All_local_rel -> 'a1 -> 'a1 coq_All_local_rel

    val coq_All_local_rel_def :
      PCUICEnvironment.context -> PCUICEnvironment.context -> term -> term ->
      aname -> 'a1 coq_All_local_rel -> 'a1 -> 'a1 -> 'a1 coq_All_local_rel

    val coq_All_local_rel_local :
      PCUICEnvironment.context -> 'a1 coq_All_local_env -> 'a1
      coq_All_local_rel

    val coq_All_local_local_rel :
      PCUICEnvironment.context -> 'a1 coq_All_local_rel -> 'a1
      coq_All_local_env

    val coq_All_local_app_rel :
      PCUICEnvironment.context -> PCUICEnvironment.context -> 'a1
      coq_All_local_env -> 'a1 coq_All_local_env * 'a1 coq_All_local_rel

    val coq_All_local_rel_app :
      PCUICEnvironment.context -> PCUICEnvironment.context -> 'a1
      coq_All_local_env -> 'a1 coq_All_local_rel -> 'a1 coq_All_local_env

    type 'p on_local_decl = __

    type 'p on_def_type = 'p

    type 'p on_def_body = 'p

    type ('check, 'infer_sort) lift_judgment = __

    val lift_judgment_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> PCUICEnvironment.context -> term -> term ->
      PCUICEnvironment.typ_or_sort -> ('a1, 'a2) lift_judgment -> (term ->
      'a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3, 'a4) lift_judgment

    type 'wf_term lift_wf_term = ('wf_term * 'wf_term, 'wf_term) lift_judgment

    type 'sorting infer_sort = (Universe.t, 'sorting) sigT

    type 'typing lift_typing = ('typing, 'typing infer_sort) lift_judgment

    type ('checking, 'sorting) lift_sorting =
      ('checking, 'sorting infer_sort) lift_judgment

    type ('p, 'q) lift_typing2 = ('p * 'q) lift_typing

    val infer_sort_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> PCUICEnvironment.context -> term -> term ->
      (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2) -> 'a2
      infer_sort

    val infer_typing_sort_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> PCUICEnvironment.context -> term -> term ->
      (Universe.t -> Universe.t) -> 'a1 infer_sort -> ('a1 -> 'a2) -> 'a2
      infer_sort

    val lift_typing_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> PCUICEnvironment.context -> term -> term ->
      PCUICEnvironment.typ_or_sort -> 'a1 lift_typing -> (term -> 'a1 -> 'a2)
      -> 'a2 lift_typing

    type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen = (
    'checking, 'sorting, 'cproperty, 'sproperty) PCUICEnvTyping.coq_All_local_env_over_gen =
    | Coq_localenv_over_nil
    | Coq_localenv_over_cons_abs of PCUICEnvironment.context * aname * 
       term * ('checking, 'sorting) lift_judgment coq_All_local_env
       * ('checking, 'sorting, 'cproperty, 'sproperty)
         coq_All_local_env_over_gen * ('checking, 'sorting) lift_judgment
       * 'sproperty
    | Coq_localenv_over_cons_def of PCUICEnvironment.context * aname * 
       term * term * ('checking, 'sorting) lift_judgment coq_All_local_env
       * 'checking
       * ('checking, 'sorting, 'cproperty, 'sproperty)
         coq_All_local_env_over_gen * 'cproperty
       * ('checking, 'sorting) lift_judgment * 'sproperty

    val coq_All_local_env_over_gen_rect :
      PCUICEnvironment.global_env_ext -> 'a5 -> (PCUICEnvironment.context ->
      aname -> term -> ('a1, 'a2) lift_judgment coq_All_local_env -> ('a1,
      'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2)
      lift_judgment -> 'a4 -> 'a5) -> (PCUICEnvironment.context -> aname ->
      term -> term -> ('a1, 'a2) lift_judgment coq_All_local_env -> 'a1 ->
      ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1,
      'a2) lift_judgment -> 'a4 -> 'a5) -> PCUICEnvironment.context -> ('a1,
      'a2) lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> 'a5

    val coq_All_local_env_over_gen_rec :
      PCUICEnvironment.global_env_ext -> 'a5 -> (PCUICEnvironment.context ->
      aname -> term -> ('a1, 'a2) lift_judgment coq_All_local_env -> ('a1,
      'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 -> ('a1, 'a2)
      lift_judgment -> 'a4 -> 'a5) -> (PCUICEnvironment.context -> aname ->
      term -> term -> ('a1, 'a2) lift_judgment coq_All_local_env -> 'a1 ->
      ('a1, 'a2, 'a3, 'a4) coq_All_local_env_over_gen -> 'a5 -> 'a3 -> ('a1,
      'a2) lift_judgment -> 'a4 -> 'a5) -> PCUICEnvironment.context -> ('a1,
      'a2) lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> 'a5

    type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen_sig =
      ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_gen

    val coq_All_local_env_over_gen_sig_pack :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> ('a1,
      'a2) lift_judgment coq_All_local_env -> ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen -> (PCUICEnvironment.context * ('a1, 'a2)
      lift_judgment coq_All_local_env) * ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen

    val coq_All_local_env_over_gen_Signature :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> ('a1,
      'a2) lift_judgment coq_All_local_env -> (('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen, PCUICEnvironment.context * ('a1, 'a2)
      lift_judgment coq_All_local_env, ('a1, 'a2, 'a3, 'a4)
      coq_All_local_env_over_gen_sig) coq_Signature

    type ('typing, 'property) coq_All_local_env_over =
      ('typing, 'typing infer_sort, 'property, 'property)
      coq_All_local_env_over_gen

    type ('checking, 'sorting, 'cproperty, 'sproperty) coq_All_local_env_over_sorting =
      ('checking, 'sorting infer_sort, 'cproperty, 'sproperty)
      coq_All_local_env_over_gen

    type 'typing ctx_inst = 'typing PCUICEnvTyping.ctx_inst =
    | Coq_ctx_inst_nil
    | Coq_ctx_inst_ass of aname * term * term * term list
       * PCUICEnvironment.context * 'typing * 'typing ctx_inst
    | Coq_ctx_inst_def of aname * term * term * term list
       * PCUICEnvironment.context * 'typing ctx_inst

    val ctx_inst_rect :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> 'a2 ->
      (aname -> term -> term -> term list -> PCUICEnvironment.context -> 'a1
      -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> term -> term -> term list
      -> PCUICEnvironment.context -> 'a1 ctx_inst -> 'a2 -> 'a2) -> term list
      -> PCUICEnvironment.context -> 'a1 ctx_inst -> 'a2

    val ctx_inst_rec :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> 'a2 ->
      (aname -> term -> term -> term list -> PCUICEnvironment.context -> 'a1
      -> 'a1 ctx_inst -> 'a2 -> 'a2) -> (aname -> term -> term -> term list
      -> PCUICEnvironment.context -> 'a1 ctx_inst -> 'a2 -> 'a2) -> term list
      -> PCUICEnvironment.context -> 'a1 ctx_inst -> 'a2

    type 'typing ctx_inst_sig = 'typing ctx_inst

    val ctx_inst_sig_pack :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term
      list -> PCUICEnvironment.context -> 'a1 ctx_inst -> (term
      list * PCUICEnvironment.context) * 'a1 ctx_inst

    val ctx_inst_Signature :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term
      list -> PCUICEnvironment.context -> ('a1 ctx_inst, term
      list * PCUICEnvironment.context, 'a1 ctx_inst_sig) coq_Signature

    val coq_NoConfusionPackage_ctx_inst :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> ((term
      list * PCUICEnvironment.context) * 'a1 ctx_inst) coq_NoConfusionPackage

    val ctx_inst_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term
      list -> PCUICEnvironment.context -> 'a1 ctx_inst -> (term -> term ->
      'a1 -> 'a2) -> 'a2 ctx_inst

    val coq_All_local_env_size_gen :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      PCUICEnvironment.typ_or_sort -> 'a1 -> size) -> size ->
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> 'a1
      coq_All_local_env -> size

    val lift_judgment_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> (PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> term -> 'a2 -> size) ->
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      PCUICEnvironment.typ_or_sort -> ('a1, 'a2) lift_judgment -> size

    val lift_typing_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort ->
      ('a1, 'a1 infer_sort) lift_judgment -> size

    val coq_All_local_env_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> ('a1, 'a1 infer_sort) lift_judgment
      coq_All_local_env -> size

    val coq_All_local_rel_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> PCUICEnvironment.context -> ('a1, 'a1
      infer_sort) lift_judgment coq_All_local_rel -> size

    val lift_sorting_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> (PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> term -> Universe.t -> 'a2 -> size) ->
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      PCUICEnvironment.typ_or_sort -> ('a1, 'a2 infer_sort) lift_judgment ->
      size

    val coq_All_local_env_sorting_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> (PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> term -> Universe.t -> 'a2 -> size) ->
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> ('a1,
      'a2 infer_sort) lift_judgment coq_All_local_env -> size

    val coq_All_local_rel_sorting_size :
      (PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
      term -> 'a1 -> size) -> (PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.context -> term -> Universe.t -> 'a2 -> size) ->
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
      PCUICEnvironment.context -> ('a1, 'a2 infer_sort) lift_judgment
      coq_All_local_rel -> size
   end

  module PCUICConversion :
   sig
    type 'p coq_All_decls_alpha_pb = 'p PCUICConversion.coq_All_decls_alpha_pb =
    | Coq_all_decls_alpha_vass of name binder_annot * name binder_annot
       * term * term * 'p
    | Coq_all_decls_alpha_vdef of name binder_annot * name binder_annot
       * term * term * term * term * 'p * 'p

    val coq_All_decls_alpha_pb_rect :
      conv_pb -> (name binder_annot -> name binder_annot -> term -> term ->
      __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term ->
      term -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term
      BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls_alpha_pb -> 'a2

    val coq_All_decls_alpha_pb_rec :
      conv_pb -> (name binder_annot -> name binder_annot -> term -> term ->
      __ -> 'a1 -> 'a2) -> (name binder_annot -> name binder_annot -> term ->
      term -> term -> term -> __ -> 'a1 -> 'a1 -> 'a2) -> term
      BasicAst.context_decl -> term BasicAst.context_decl -> 'a1
      coq_All_decls_alpha_pb -> 'a2

    type 'p coq_All_decls_alpha_pb_sig = 'p coq_All_decls_alpha_pb

    val coq_All_decls_alpha_pb_sig_pack :
      conv_pb -> term BasicAst.context_decl -> term BasicAst.context_decl ->
      'a1 coq_All_decls_alpha_pb -> (term BasicAst.context_decl * term
      BasicAst.context_decl) * 'a1 coq_All_decls_alpha_pb

    val coq_All_decls_alpha_pb_Signature :
      conv_pb -> term BasicAst.context_decl -> term BasicAst.context_decl ->
      ('a1 coq_All_decls_alpha_pb, term BasicAst.context_decl * term
      BasicAst.context_decl, 'a1 coq_All_decls_alpha_pb_sig) coq_Signature

    val coq_NoConfusionPackage_All_decls_alpha_pb :
      conv_pb -> ((term BasicAst.context_decl * term
      BasicAst.context_decl) * 'a1 coq_All_decls_alpha_pb)
      coq_NoConfusionPackage

    type 'cumul_gen cumul_pb_decls = 'cumul_gen coq_All_decls_alpha_pb

    type 'cumul_gen cumul_pb_context =
      (term BasicAst.context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold

    type 'cumul_gen cumul_ctx_rel =
      (term BasicAst.context_decl, 'cumul_gen cumul_pb_decls) coq_All2_fold
   end

  val context_reflect :
    term coq_ReflectEq -> term BasicAst.context_decl list coq_ReflectEq

  val string_of_predicate : ('a1 -> String.t) -> 'a1 predicate -> String.t

  val eqb_predicate_gen :
    (Instance.t -> Instance.t -> bool) -> (term BasicAst.context_decl -> term
    BasicAst.context_decl -> bool) -> (term -> term -> bool) -> term
    predicate -> term predicate -> bool

  val eqb_predicate :
    (term -> term -> bool) -> term predicate -> term predicate -> bool

  type 'p tCasePredProp_k = (term, 'p) coq_All * ((term, 'p) onctx_k * 'p)

  type ('term, 'pparams, 'preturn) tCasePredProp =
    ('term, 'pparams) coq_All * (('term BasicAst.context_decl, ('term,
    'pparams) ondecl) coq_All * 'preturn)

  type ('a, 'p) tCaseBrsProp =
    ('a branch, ('a BasicAst.context_decl, ('a, 'p) ondecl) coq_All * 'p)
    coq_All

  type 'p tCaseBrsProp_k = (term branch, (term, 'p) onctx_k * 'p) coq_All

  val onctx_k_rev :
    nat -> term BasicAst.context_decl list -> ((term, 'a1) onctx_k, (term
    BasicAst.context_decl, (term, 'a1) ondecl) coq_Alli) iffT

  val onctx_k_shift :
    nat -> term BasicAst.context_decl list -> (term, 'a1) onctx_k -> (term,
    'a1) onctx_k

  val onctx_k_P :
    (nat -> term -> bool) -> nat -> PCUICEnvironment.context -> (nat -> term
    -> 'a1 reflectT) -> (term, 'a1) onctx_k reflectT

  module PCUICLookup :
   sig
    val lookup_constant :
      PCUICEnvironment.global_env -> kername ->
      PCUICEnvironment.constant_body option

    val lookup_minductive :
      PCUICEnvironment.global_env -> kername ->
      PCUICEnvironment.mutual_inductive_body option

    val lookup_inductive :
      PCUICEnvironment.global_env -> inductive ->
      (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
      option

    val lookup_constructor :
      PCUICEnvironment.global_env -> inductive -> nat ->
      ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
      option

    val lookup_projection :
      PCUICEnvironment.global_env -> projection ->
      (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
      option

    val on_udecl_decl :
      (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1

    val universes_decl_of_decl :
      PCUICEnvironment.global_decl -> universes_decl

    val global_levels : ContextSet.t -> LevelSet.t

    val global_constraints : PCUICEnvironment.global_env -> ConstraintSet.t

    val global_uctx : PCUICEnvironment.global_env -> ContextSet.t

    val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t

    val global_ext_constraints :
      PCUICEnvironment.global_env_ext -> ConstraintSet.t

    val global_ext_uctx : PCUICEnvironment.global_env_ext -> ContextSet.t
   end

  val lookup_constant :
    PCUICEnvironment.global_env -> kername -> PCUICEnvironment.constant_body
    option

  val lookup_minductive :
    PCUICEnvironment.global_env -> kername ->
    PCUICEnvironment.mutual_inductive_body option

  val lookup_inductive :
    PCUICEnvironment.global_env -> inductive ->
    (PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body)
    option

  val lookup_constructor :
    PCUICEnvironment.global_env -> inductive -> nat ->
    ((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body)
    option

  val lookup_projection :
    PCUICEnvironment.global_env -> projection ->
    (((PCUICEnvironment.mutual_inductive_body * PCUICEnvironment.one_inductive_body) * PCUICEnvironment.constructor_body) * PCUICEnvironment.projection_body)
    option

  val on_udecl_decl :
    (universes_decl -> 'a1) -> PCUICEnvironment.global_decl -> 'a1

  val universes_decl_of_decl : PCUICEnvironment.global_decl -> universes_decl

  val global_levels : ContextSet.t -> LevelSet.t

  val global_constraints : PCUICEnvironment.global_env -> ConstraintSet.t

  val global_uctx : PCUICEnvironment.global_env -> ContextSet.t

  val global_ext_levels : PCUICEnvironment.global_env_ext -> LevelSet.t

  val global_ext_constraints :
    PCUICEnvironment.global_env_ext -> ConstraintSet.t

  val global_ext_uctx : PCUICEnvironment.global_env_ext -> ContextSet.t

  val coq_NoConfusionPackage_global_decl :
    PCUICEnvironment.global_decl coq_NoConfusionPackage

  module PCUICGlobalMaps :
   sig
    type 'p on_context = 'p PCUICEnvTyping.coq_All_local_env

    type 'p type_local_ctx = __

    type 'p sorts_local_ctx = __

    type 'p on_type = 'p

    val univs_ext_constraints :
      ConstraintSet.t -> universes_decl -> ConstraintSet.t

    val ind_realargs : PCUICEnvironment.one_inductive_body -> nat

    type positive_cstr_arg = PCUICGlobalMaps.positive_cstr_arg =
    | Coq_positive_cstr_arg_closed of term
    | Coq_positive_cstr_arg_concl of term list * nat
       * PCUICEnvironment.one_inductive_body * (term, __) coq_All
    | Coq_positive_cstr_arg_let of aname * term * term * term
       * positive_cstr_arg
    | Coq_positive_cstr_arg_ass of aname * term * term * positive_cstr_arg

    val positive_cstr_arg_rect :
      PCUICEnvironment.mutual_inductive_body -> (term BasicAst.context_decl
      list -> term -> __ -> 'a1) -> (term BasicAst.context_decl list -> term
      list -> nat -> PCUICEnvironment.one_inductive_body -> __ -> __ ->
      (term, __) coq_All -> __ -> __ -> 'a1) -> (term BasicAst.context_decl
      list -> aname -> term -> term -> term -> positive_cstr_arg -> 'a1 ->
      'a1) -> (term BasicAst.context_decl list -> aname -> term -> term -> __
      -> positive_cstr_arg -> 'a1 -> 'a1) -> term BasicAst.context_decl list
      -> term -> positive_cstr_arg -> 'a1

    val positive_cstr_arg_rec :
      PCUICEnvironment.mutual_inductive_body -> (term BasicAst.context_decl
      list -> term -> __ -> 'a1) -> (term BasicAst.context_decl list -> term
      list -> nat -> PCUICEnvironment.one_inductive_body -> __ -> __ ->
      (term, __) coq_All -> __ -> __ -> 'a1) -> (term BasicAst.context_decl
      list -> aname -> term -> term -> term -> positive_cstr_arg -> 'a1 ->
      'a1) -> (term BasicAst.context_decl list -> aname -> term -> term -> __
      -> positive_cstr_arg -> 'a1 -> 'a1) -> term BasicAst.context_decl list
      -> term -> positive_cstr_arg -> 'a1

    type positive_cstr = PCUICGlobalMaps.positive_cstr =
    | Coq_positive_cstr_concl of term list * (term, __) coq_All
    | Coq_positive_cstr_let of aname * term * term * term * positive_cstr
    | Coq_positive_cstr_ass of aname * term * term * positive_cstr_arg
       * positive_cstr

    val positive_cstr_rect :
      PCUICEnvironment.mutual_inductive_body -> nat ->
      (PCUICEnvironment.context -> term list -> (term, __) coq_All -> 'a1) ->
      (PCUICEnvironment.context -> aname -> term -> term -> term ->
      positive_cstr -> 'a1 -> 'a1) -> (PCUICEnvironment.context -> aname ->
      term -> term -> positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) ->
      PCUICEnvironment.context -> term -> positive_cstr -> 'a1

    val positive_cstr_rec :
      PCUICEnvironment.mutual_inductive_body -> nat ->
      (PCUICEnvironment.context -> term list -> (term, __) coq_All -> 'a1) ->
      (PCUICEnvironment.context -> aname -> term -> term -> term ->
      positive_cstr -> 'a1 -> 'a1) -> (PCUICEnvironment.context -> aname ->
      term -> term -> positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) ->
      PCUICEnvironment.context -> term -> positive_cstr -> 'a1

    val lift_level : nat -> Level.t_ -> Level.t_

    val lift_instance : nat -> Level.t_ list -> Level.t_ list

    val lift_constraint :
      nat -> ((Level.t * ConstraintType.t) * Level.t) ->
      (Level.t_ * ConstraintType.t) * Level.t_

    val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

    val level_var_instance : nat -> name list -> Level.t_ list

    val variance_cstrs :
      Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

    val variance_universes :
      universes_decl -> Variance.t list -> ((universes_decl * Level.t_
      list) * Level.t_ list) option

    val ind_arities :
      PCUICEnvironment.mutual_inductive_body -> term BasicAst.context_decl
      list

    type 'pcmp ind_respects_variance = __

    type 'pcmp cstr_respects_variance = __

    val cstr_concl_head :
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.constructor_body -> term

    val cstr_concl :
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.constructor_body -> term

    type ('pcmp, 'p) on_constructor = ('pcmp, 'p) PCUICGlobalMaps.on_constructor = { 
    on_ctype : 'p on_type; on_cargs : 'p sorts_local_ctx;
    on_cindices : 'p PCUICEnvTyping.ctx_inst;
    on_ctype_positive : positive_cstr;
    on_ctype_variance : (Variance.t list -> __ -> 'pcmp
                        cstr_respects_variance) }

    val on_ctype :
      checker_flags -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
      PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
      on_constructor -> 'a2 on_type

    val on_cargs :
      checker_flags -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
      PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
      on_constructor -> 'a2 sorts_local_ctx

    val on_cindices :
      checker_flags -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
      PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
      on_constructor -> 'a2 PCUICEnvTyping.ctx_inst

    val on_ctype_positive :
      checker_flags -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
      PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
      on_constructor -> positive_cstr

    val on_ctype_variance :
      checker_flags -> PCUICEnvironment.global_env_ext ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
      PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
      on_constructor -> Variance.t list -> 'a1 cstr_respects_variance

    type ('pcmp, 'p) on_constructors =
      (PCUICEnvironment.constructor_body, Universe.t list, ('pcmp, 'p)
      on_constructor) coq_All2

    type on_projections =
      (PCUICEnvironment.projection_body, __) coq_Alli
      (* singleton inductive, whose constructor was Build_on_projections *)

    val on_projs :
      PCUICEnvironment.mutual_inductive_body -> kername -> nat ->
      PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
      PCUICEnvironment.constructor_body -> on_projections ->
      (PCUICEnvironment.projection_body, __) coq_Alli

    type constructor_univs = Universe.t list

    val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

    val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

    type 'p check_ind_sorts = __

    type ('pcmp, 'p) on_ind_body = ('pcmp, 'p) PCUICGlobalMaps.on_ind_body = { 
    onArity : 'p on_type; ind_cunivs : constructor_univs list;
    onConstructors : ('pcmp, 'p) on_constructors; onProjections : (__ -> __);
    ind_sorts : 'p check_ind_sorts;
    onIndices : (Variance.t list -> __ -> 'pcmp ind_respects_variance) }

    val onArity :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
      on_type

    val ind_cunivs :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
      constructor_univs list

    val onConstructors :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1,
      'a2) on_constructors

    val onProjections :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

    val ind_sorts :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
      check_ind_sorts

    val onIndices :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> nat ->
      PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
      Variance.t list -> 'a1 ind_respects_variance

    type on_variance = __

    type ('pcmp, 'p) on_inductive = ('pcmp, 'p) PCUICGlobalMaps.on_inductive = { 
    onInductives : (PCUICEnvironment.one_inductive_body, ('pcmp, 'p)
                   on_ind_body) coq_Alli; onParams : 'p on_context;
    onVariance : on_variance }

    val onInductives :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
      (PCUICEnvironment.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli

    val onParams :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
      'a2 on_context

    val onVariance :
      checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
      PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
      on_variance

    type 'p on_constant_decl = __

    type ('pcmp, 'p) on_global_decl = __

    type ('pcmp, 'p) on_global_decls_data =
      ('pcmp, 'p) on_global_decl
      (* singleton inductive, whose constructor was Build_on_global_decls_data *)

    val udecl :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      PCUICEnvironment.global_declarations -> kername ->
      PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data ->
      universes_decl

    val on_global_decl_d :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      PCUICEnvironment.global_declarations -> kername ->
      PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data ->
      ('a1, 'a2) on_global_decl

    type ('pcmp, 'p) on_global_decls = ('pcmp, 'p) PCUICGlobalMaps.on_global_decls =
    | Coq_globenv_nil
    | Coq_globenv_decl of PCUICEnvironment.global_declarations * kername
       * PCUICEnvironment.global_decl * ('pcmp, 'p) on_global_decls
       * ('pcmp, 'p) on_global_decls_data

    val on_global_decls_rect :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
      (PCUICEnvironment.global_declarations -> kername ->
      PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
      ('a1, 'a2) on_global_decls_data -> 'a3) ->
      PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
      'a3

    val on_global_decls_rec :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
      (PCUICEnvironment.global_declarations -> kername ->
      PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
      ('a1, 'a2) on_global_decls_data -> 'a3) ->
      PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
      'a3

    type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

    val on_global_decls_sig_pack :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
      PCUICEnvironment.global_declarations * ('a1, 'a2) on_global_decls

    val on_global_decls_Signature :
      checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
      PCUICEnvironment.global_declarations -> (('a1, 'a2) on_global_decls,
      PCUICEnvironment.global_declarations, ('a1, 'a2) on_global_decls_sig)
      coq_Signature

    type ('pcmp, 'p) on_global_env = __ * ('pcmp, 'p) on_global_decls

    type ('pcmp, 'p) on_global_env_ext = ('pcmp, 'p) on_global_env * __

    val type_local_ctx_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
      PCUICEnvironment.context -> Universe.t -> 'a1 type_local_ctx ->
      (PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort ->
      'a1 -> 'a2) -> 'a2 type_local_ctx

    val sorts_local_ctx_impl :
      PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
      PCUICEnvironment.context -> Universe.t list -> 'a1 sorts_local_ctx ->
      (PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort ->
      'a1 -> 'a2) -> 'a2 sorts_local_ctx

    val on_global_env_impl :
      checker_flags -> ((PCUICEnvironment.global_env * universes_decl) ->
      PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort ->
      ('a1, 'a2) on_global_env -> ('a1, 'a3) on_global_env -> 'a2 -> 'a3) ->
      PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
      on_global_env
   end

  type 'p on_context = 'p PCUICEnvTyping.coq_All_local_env

  type 'p type_local_ctx = __

  type 'p sorts_local_ctx = __

  type 'p on_type = 'p

  val univs_ext_constraints :
    ConstraintSet.t -> universes_decl -> ConstraintSet.t

  val ind_realargs : PCUICEnvironment.one_inductive_body -> nat

  type positive_cstr_arg = PCUICAst.PCUICGlobalMaps.positive_cstr_arg =
  | Coq_positive_cstr_arg_closed of term
  | Coq_positive_cstr_arg_concl of term list * nat
     * PCUICEnvironment.one_inductive_body * (term, __) coq_All
  | Coq_positive_cstr_arg_let of aname * term * term * term
     * positive_cstr_arg
  | Coq_positive_cstr_arg_ass of aname * term * term * positive_cstr_arg

  val positive_cstr_arg_rect :
    PCUICEnvironment.mutual_inductive_body -> (term BasicAst.context_decl
    list -> term -> __ -> 'a1) -> (term BasicAst.context_decl list -> term
    list -> nat -> PCUICEnvironment.one_inductive_body -> __ -> __ -> (term,
    __) coq_All -> __ -> __ -> 'a1) -> (term BasicAst.context_decl list ->
    aname -> term -> term -> term -> positive_cstr_arg -> 'a1 -> 'a1) ->
    (term BasicAst.context_decl list -> aname -> term -> term -> __ ->
    positive_cstr_arg -> 'a1 -> 'a1) -> term BasicAst.context_decl list ->
    term -> positive_cstr_arg -> 'a1

  val positive_cstr_arg_rec :
    PCUICEnvironment.mutual_inductive_body -> (term BasicAst.context_decl
    list -> term -> __ -> 'a1) -> (term BasicAst.context_decl list -> term
    list -> nat -> PCUICEnvironment.one_inductive_body -> __ -> __ -> (term,
    __) coq_All -> __ -> __ -> 'a1) -> (term BasicAst.context_decl list ->
    aname -> term -> term -> term -> positive_cstr_arg -> 'a1 -> 'a1) ->
    (term BasicAst.context_decl list -> aname -> term -> term -> __ ->
    positive_cstr_arg -> 'a1 -> 'a1) -> term BasicAst.context_decl list ->
    term -> positive_cstr_arg -> 'a1

  type positive_cstr = PCUICAst.PCUICGlobalMaps.positive_cstr =
  | Coq_positive_cstr_concl of term list * (term, __) coq_All
  | Coq_positive_cstr_let of aname * term * term * term * positive_cstr
  | Coq_positive_cstr_ass of aname * term * term * positive_cstr_arg
     * positive_cstr

  val positive_cstr_rect :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    (PCUICEnvironment.context -> term list -> (term, __) coq_All -> 'a1) ->
    (PCUICEnvironment.context -> aname -> term -> term -> term ->
    positive_cstr -> 'a1 -> 'a1) -> (PCUICEnvironment.context -> aname ->
    term -> term -> positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) ->
    PCUICEnvironment.context -> term -> positive_cstr -> 'a1

  val positive_cstr_rec :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    (PCUICEnvironment.context -> term list -> (term, __) coq_All -> 'a1) ->
    (PCUICEnvironment.context -> aname -> term -> term -> term ->
    positive_cstr -> 'a1 -> 'a1) -> (PCUICEnvironment.context -> aname ->
    term -> term -> positive_cstr_arg -> positive_cstr -> 'a1 -> 'a1) ->
    PCUICEnvironment.context -> term -> positive_cstr -> 'a1

  val lift_level : nat -> Level.t_ -> Level.t_

  val lift_instance : nat -> Level.t_ list -> Level.t_ list

  val lift_constraint :
    nat -> ((Level.t * ConstraintType.t) * Level.t) ->
    (Level.t_ * ConstraintType.t) * Level.t_

  val lift_constraints : nat -> ConstraintSet.t -> ConstraintSet.t

  val level_var_instance : nat -> name list -> Level.t_ list

  val variance_cstrs :
    Variance.t list -> Instance.t -> Instance.t -> ConstraintSet.t

  val variance_universes :
    universes_decl -> Variance.t list -> ((universes_decl * Level.t_
    list) * Level.t_ list) option

  val ind_arities :
    PCUICEnvironment.mutual_inductive_body -> term BasicAst.context_decl list

  type 'pcmp ind_respects_variance = __

  type 'pcmp cstr_respects_variance = __

  val cstr_concl_head :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.constructor_body -> term

  val cstr_concl :
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.constructor_body -> term

  type ('pcmp, 'p) on_constructor = ('pcmp, 'p) PCUICAst.PCUICGlobalMaps.on_constructor = { 
  on_ctype : 'p on_type; on_cargs : 'p sorts_local_ctx;
  on_cindices : 'p PCUICEnvTyping.ctx_inst;
  on_ctype_positive : positive_cstr;
  on_ctype_variance : (Variance.t list -> __ -> 'pcmp cstr_respects_variance) }

  val on_ctype :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
    on_constructor -> 'a2 on_type

  val on_cargs :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
    on_constructor -> 'a2 sorts_local_ctx

  val on_cindices :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
    on_constructor -> 'a2 PCUICEnvTyping.ctx_inst

  val on_ctype_positive :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
    on_constructor -> positive_cstr

  val on_ctype_variance :
    checker_flags -> PCUICEnvironment.global_env_ext ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> Universe.t list -> ('a1, 'a2)
    on_constructor -> Variance.t list -> 'a1 cstr_respects_variance

  type ('pcmp, 'p) on_constructors =
    (PCUICEnvironment.constructor_body, Universe.t list, ('pcmp, 'p)
    on_constructor) coq_All2

  type on_projections =
    (PCUICEnvironment.projection_body, __) coq_Alli
    (* singleton inductive, whose constructor was Build_on_projections *)

  val on_projs :
    PCUICEnvironment.mutual_inductive_body -> kername -> nat ->
    PCUICEnvironment.one_inductive_body -> PCUICEnvironment.context ->
    PCUICEnvironment.constructor_body -> on_projections ->
    (PCUICEnvironment.projection_body, __) coq_Alli

  type constructor_univs = Universe.t list

  val elim_sort_prop_ind : constructor_univs list -> allowed_eliminations

  val elim_sort_sprop_ind : constructor_univs list -> allowed_eliminations

  type 'p check_ind_sorts = __

  type ('pcmp, 'p) on_ind_body = ('pcmp, 'p) PCUICAst.PCUICGlobalMaps.on_ind_body = { 
  onArity : 'p on_type; ind_cunivs : constructor_univs list;
  onConstructors : ('pcmp, 'p) on_constructors; onProjections : (__ -> __);
  ind_sorts : 'p check_ind_sorts;
  onIndices : (Variance.t list -> __ -> 'pcmp ind_respects_variance) }

  val onArity :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    on_type

  val ind_cunivs :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    constructor_univs list

  val onConstructors :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> ('a1,
    'a2) on_constructors

  val onProjections :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> __

  val ind_sorts :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body -> 'a2
    check_ind_sorts

  val onIndices :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> nat ->
    PCUICEnvironment.one_inductive_body -> ('a1, 'a2) on_ind_body ->
    Variance.t list -> 'a1 ind_respects_variance

  type on_variance = __

  type ('pcmp, 'p) on_inductive = ('pcmp, 'p) PCUICAst.PCUICGlobalMaps.on_inductive = { 
  onInductives : (PCUICEnvironment.one_inductive_body, ('pcmp, 'p)
                 on_ind_body) coq_Alli; onParams : 'p on_context;
  onVariance : on_variance }

  val onInductives :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    (PCUICEnvironment.one_inductive_body, ('a1, 'a2) on_ind_body) coq_Alli

  val onParams :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive -> 'a2
    on_context

  val onVariance :
    checker_flags -> PCUICEnvironment.global_env_ext -> kername ->
    PCUICEnvironment.mutual_inductive_body -> ('a1, 'a2) on_inductive ->
    on_variance

  type 'p on_constant_decl = __

  type ('pcmp, 'p) on_global_decl = __

  type ('pcmp, 'p) on_global_decls_data =
    ('pcmp, 'p) on_global_decl
    (* singleton inductive, whose constructor was Build_on_global_decls_data *)

  val udecl :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data ->
    universes_decl

  val on_global_decl_d :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls_data -> ('a1,
    'a2) on_global_decl

  type ('pcmp, 'p) on_global_decls = ('pcmp, 'p) PCUICAst.PCUICGlobalMaps.on_global_decls =
  | Coq_globenv_nil
  | Coq_globenv_decl of PCUICEnvironment.global_declarations * kername
     * PCUICEnvironment.global_decl * ('pcmp, 'p) on_global_decls
     * ('pcmp, 'p) on_global_decls_data

  val on_global_decls_rect :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
    ('a1, 'a2) on_global_decls_data -> 'a3) ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  val on_global_decls_rec :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t -> 'a3 ->
    (PCUICEnvironment.global_declarations -> kername ->
    PCUICEnvironment.global_decl -> ('a1, 'a2) on_global_decls -> 'a3 ->
    ('a1, 'a2) on_global_decls_data -> 'a3) ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls -> 'a3

  type ('pcmp, 'p) on_global_decls_sig = ('pcmp, 'p) on_global_decls

  val on_global_decls_sig_pack :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> ('a1, 'a2) on_global_decls ->
    PCUICEnvironment.global_declarations * ('a1, 'a2) on_global_decls

  val on_global_decls_Signature :
    checker_flags -> ContextSet.t -> Environment.Retroknowledge.t ->
    PCUICEnvironment.global_declarations -> (('a1, 'a2) on_global_decls,
    PCUICEnvironment.global_declarations, ('a1, 'a2) on_global_decls_sig)
    coq_Signature

  type ('pcmp, 'p) on_global_env = __ * ('pcmp, 'p) on_global_decls

  type ('pcmp, 'p) on_global_env_ext = ('pcmp, 'p) on_global_env * __

  val type_local_ctx_impl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> Universe.t -> 'a1 type_local_ctx ->
    (PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort -> 'a1
    -> 'a2) -> 'a2 type_local_ctx

  val sorts_local_ctx_impl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context ->
    PCUICEnvironment.context -> Universe.t list -> 'a1 sorts_local_ctx ->
    (PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort -> 'a1
    -> 'a2) -> 'a2 sorts_local_ctx

  val on_global_env_impl :
    checker_flags -> ((PCUICEnvironment.global_env * universes_decl) ->
    PCUICEnvironment.context -> term -> PCUICEnvironment.typ_or_sort -> ('a1,
    'a2) on_global_env -> ('a1, 'a3) on_global_env -> 'a2 -> 'a3) ->
    PCUICEnvironment.global_env -> ('a1, 'a2) on_global_env -> ('a1, 'a3)
    on_global_env
 end

module Ex :
 sig
  type box_type = ExAst.box_type =
  | TBox
  | TAny
  | TArr of box_type * box_type
  | TApp of box_type * box_type
  | TVar of nat
  | TInd of inductive
  | TConst of kername

  val box_type_rect :
    'a1 -> 'a1 -> (box_type -> 'a1 -> box_type -> 'a1 -> 'a1) -> (box_type ->
    'a1 -> box_type -> 'a1 -> 'a1) -> (nat -> 'a1) -> (inductive -> 'a1) ->
    (kername -> 'a1) -> box_type -> 'a1

  val box_type_rec :
    'a1 -> 'a1 -> (box_type -> 'a1 -> box_type -> 'a1 -> 'a1) -> (box_type ->
    'a1 -> box_type -> 'a1 -> 'a1) -> (nat -> 'a1) -> (inductive -> 'a1) ->
    (kername -> 'a1) -> box_type -> 'a1

  val decompose_arr : box_type -> box_type list * box_type

  val can_have_args : box_type -> bool

  val mkTApps : box_type -> box_type list -> box_type

  type constant_body = ExAst.constant_body = { cst_type : (name
                                                          list * box_type);
                                               cst_body : EAst.term option }

  val cst_type : constant_body -> name list * box_type

  val cst_body : constant_body -> EAst.term option

  type type_var_info = ExAst.type_var_info = { tvar_name : name;
                                               tvar_is_logical : bool;
                                               tvar_is_arity : bool;
                                               tvar_is_sort : bool }

  val tvar_name : type_var_info -> name

  val tvar_is_logical : type_var_info -> bool

  val tvar_is_arity : type_var_info -> bool

  val tvar_is_sort : type_var_info -> bool

  type one_inductive_body = ExAst.one_inductive_body = { ind_name : ident;
                                                         ind_propositional : 
                                                         bool;
                                                         ind_kelim : 
                                                         allowed_eliminations;
                                                         ind_type_vars : 
                                                         type_var_info list;
                                                         ind_ctors : 
                                                         ((ident * (name * box_type)
                                                         list) * nat) list;
                                                         ind_projs : 
                                                         (ident * box_type)
                                                         list }

  val ind_name : one_inductive_body -> ident

  val ind_propositional : one_inductive_body -> bool

  val ind_kelim : one_inductive_body -> allowed_eliminations

  val ind_type_vars : one_inductive_body -> type_var_info list

  val ind_ctors :
    one_inductive_body -> ((ident * (name * box_type) list) * nat) list

  val ind_projs : one_inductive_body -> (ident * box_type) list

  type mutual_inductive_body = ExAst.mutual_inductive_body = { ind_finite : 
                                                               recursivity_kind;
                                                               ind_npars : 
                                                               nat;
                                                               ind_bodies : 
                                                               one_inductive_body
                                                               list }

  val ind_finite : mutual_inductive_body -> recursivity_kind

  val ind_npars : mutual_inductive_body -> nat

  val ind_bodies : mutual_inductive_body -> one_inductive_body list

  type global_decl = ExAst.global_decl =
  | ConstantDecl of constant_body
  | InductiveDecl of mutual_inductive_body
  | TypeAliasDecl of (type_var_info list * box_type) option

  val global_decl_rect :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) ->
    ((type_var_info list * box_type) option -> 'a1) -> global_decl -> 'a1

  val global_decl_rec :
    (constant_body -> 'a1) -> (mutual_inductive_body -> 'a1) ->
    ((type_var_info list * box_type) option -> 'a1) -> global_decl -> 'a1

  type global_env = ((kername * bool) * global_decl) list

  val lookup_env : global_env -> kername -> global_decl option

  val lookup_constant : global_env -> kername -> constant_body option

  val lookup_minductive :
    global_env -> kername -> mutual_inductive_body option

  val lookup_inductive : global_env -> inductive -> one_inductive_body option

  val lookup_constructor :
    global_env -> inductive -> nat -> ((ident * (name * box_type)
    list) * nat) option

  val lookup_constructor_full :
    global_env -> inductive -> nat ->
    ((mutual_inductive_body * one_inductive_body) * ((ident * (name * box_type)
    list) * nat)) option

  val trans_cst : constant_body -> EAst.constant_body

  val trans_ctors :
    ((ident * (name * box_type) list) * nat) list -> constructor_body list

  val trans_oib : one_inductive_body -> EAst.one_inductive_body

  val trans_mib : mutual_inductive_body -> EAst.mutual_inductive_body

  val trans_global_decl : global_decl -> EAst.global_decl

  val trans_env : global_env -> global_declarations

  val print_term : global_env -> EAst.term -> String.t
 end

type fot_view =
| Coq_fot_view_prod of aname * term * term
| Coq_fot_view_sort of Universe.t
| Coq_fot_view_other of term

val fot_viewc : term -> fot_view

type arity_ass = aname * term

type conv_arity = { conv_ar_context : arity_ass list;
                    conv_ar_univ : Universe.t }

type conv_arity_or_not = (conv_arity, __) sum

val is_sort :
  PCUICEnvironment.global_env_ext -> term BasicAst.context_decl list -> term
  -> conv_arity_or_not -> __ option

val is_arity :
  PCUICEnvironment.global_env_ext -> term BasicAst.context_decl list -> term
  -> conv_arity_or_not -> bool

type type_flag = { is_logical : bool; conv_ar : conv_arity_or_not }

val flag_of_type_obligations_obligation_8 :
  abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> term -> term
  -> abstract_env_impl

val flag_of_type_obligations_obligation_9 :
  abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> term -> term
  -> __

val flag_of_type :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> term -> type_flag

type erase_type_view =
| Coq_et_view_rel of nat
| Coq_et_view_sort of Universe.t
| Coq_et_view_prod of aname * term * term
| Coq_et_view_app of term * term
| Coq_et_view_const of kername * Instance.t
| Coq_et_view_ind of inductive * Instance.t
| Coq_et_view_other of term

val erase_type_viewc : term -> erase_type_view

type tRel_kind =
| RelTypeVar of nat
| RelInductive of inductive
| RelOther

val erase_type_aux :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> tRel_kind Vector.t -> term -> nat option ->
  name list * box_type

val erase_type :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> term -> name
  list * box_type

type erase_type_scheme_view =
| Coq_erase_type_scheme_view_lam of aname * term * term
| Coq_erase_type_scheme_view_other of term

val erase_type_scheme_viewc : term -> erase_type_scheme_view

val type_var_info_of_flag :
  aname -> PCUICEnvironment.global_env_ext -> term BasicAst.context_decl list
  -> term -> type_flag -> type_var_info

val erase_type_scheme_eta :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> tRel_kind Vector.t -> term -> arity_ass list ->
  Universe.t -> nat -> type_var_info list * box_type

val erase_type_scheme :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.context -> tRel_kind Vector.t -> term -> arity_ass list ->
  Universe.t -> nat -> type_var_info list * box_type

val erase_arity :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.constant_body -> conv_arity -> (type_var_info
  list * box_type) option

val erase_constant_decl :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  PCUICEnvironment.constant_body -> (constant_body, (type_var_info
  list * box_type) option) sum

val erase_ind_arity :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  P.PCUICEnvironment.context -> P.term -> type_var_info list

val ind_aname : P.PCUICEnvironment.one_inductive_body -> name binder_annot

val arities_contexts :
  kername -> P.PCUICEnvironment.one_inductive_body list -> (P.term
  BasicAst.context_decl list, tRel_kind Vector.t) sigT

type view_prod =
| Coq_view_prod_prod of aname * P.term * P.term
| Coq_view_prod_other of term

val view_prodc : P.term -> view_prod

val erase_ind_ctor :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext ->
  P.PCUICEnvironment.context -> tRel_kind Vector.t -> P.term -> nat ->
  type_var_info list -> box_type

val erase_ind_body :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> kername ->
  P.PCUICEnvironment.mutual_inductive_body ->
  P.PCUICEnvironment.one_inductive_body -> one_inductive_body

val erase_ind :
  abstract_env_impl -> __ -> PCUICEnvironment.global_env_ext -> kername ->
  P.PCUICEnvironment.mutual_inductive_body -> mutual_inductive_body

val fake_guard_impl :
  coq_FixCoFix -> PCUICEnvironment.global_env_ext -> PCUICEnvironment.context
  -> term BasicAst.mfixpoint -> bool

val fake_guard_impl_instance : abstract_guard_impl

val erase_global_decl_obligation_1 : PCUICEnvironment.global_env_ext -> __

val erase_global_decl_obligation_4 : PCUICEnvironment.global_env_ext -> __

val erase_global_decl :
  PCUICEnvironment.global_env_ext -> kername -> PCUICEnvironment.global_decl
  -> global_decl

val box_type_deps : box_type -> KernameSet.t

val decl_deps : global_decl -> KernameSet.t

val erase_global_decls_deps_recursive :
  PCUICEnvironment.global_declarations -> ContextSet.t ->
  Environment.Retroknowledge.t -> KernameSet.t -> (kername -> bool) ->
  global_env
