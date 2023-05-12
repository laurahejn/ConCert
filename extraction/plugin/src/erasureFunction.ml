open BasicAst
open Datatypes
open EAstUtils
open Extract
open Kernames
open PCUICAst
open PCUICCases
open PCUICErrors
open PCUICSafeReduce
open PCUICSafeRetyping
open PCUICWfEnv
open Specif
open Universes0
open Config0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val is_arity :
    checker_flags -> abstract_env_impl -> __ -> PCUICEnvironment.context ->
    term -> bool **)

let is_arity cf x_type x a a0 =
  let rec fix_F x0 =
    let _UU0393_ = let pr1,_ = x0 in pr1 in
    let t0 = let pr1,_ = let _,pr2 = let _,pr2 = x0 in pr2 in pr2 in pr1 in
    (match inspect (reduce_to_sort cf x_type x _UU0393_ t0) with
     | Checked_comp _ -> true
     | TypeError_comp _ ->
       (match inspect (reduce_to_prod cf x_type x _UU0393_ t0) with
        | Checked_comp a1 ->
          let Coq_existT (x1, s) = a1 in
          let Coq_existT (x2, s0) = s in
          let Coq_existT (x3, _) = s0 in
          let y = (snoc _UU0393_ (PCUICEnvironment.vass x1 x2)),(__,(x3,__))
          in
          fix_F y
        | TypeError_comp _ -> false))
  in fix_F (a,(__,(a0,__)))

(** val inspect : 'a1 -> 'a1 **)

let inspect x =
  x

(** val inspect_bool : bool -> bool **)

let inspect_bool = function
| true -> true
| false -> false

(** val is_erasableb :
    abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> bool **)

let is_erasableb x_type x _UU0393_ t0 =
  let t1 = type_of_typing extraction_checker_flags x_type x _UU0393_ t0 in
  if is_arity extraction_checker_flags x_type x _UU0393_ (projT1 t1)
  then true
  else let s =
         sort_of_type extraction_checker_flags x_type x _UU0393_ (projT1 t1)
       in
       is_propositional (projT1 s)

(** val erase :
    abstract_env_impl -> __ -> PCUICEnvironment.context -> term -> E.term **)

let rec erase x_type x _UU0393_ t0 =
  if inspect_bool (is_erasableb x_type x _UU0393_ t0)
  then E.Coq_tBox
  else (match t0 with
        | Coq_tRel n -> E.Coq_tRel n
        | Coq_tVar i -> E.Coq_tVar i
        | Coq_tEvar (n, l) ->
          E.Coq_tEvar (n,
            (let rec erase_terms _UU0393_0 = function
             | [] -> []
             | t1 :: l1 ->
               let t' = erase x_type x _UU0393_0 t1 in
               let ts' = erase_terms _UU0393_0 l1 in t' :: ts'
             in erase_terms _UU0393_ l))
        | Coq_tLambda (na, a, t1) ->
          let t' =
            erase x_type x ((PCUICEnvironment.vass na a) :: _UU0393_) t1
          in
          E.Coq_tLambda (na.binder_name, t')
        | Coq_tLetIn (na, b, b0, t1) ->
          let b' = erase x_type x _UU0393_ b in
          let t1' =
            erase x_type x ((PCUICEnvironment.vdef na b b0) :: _UU0393_) t1
          in
          E.Coq_tLetIn (na.binder_name, b', t1')
        | Coq_tApp (u, v) ->
          let f' = erase x_type x _UU0393_ u in
          let l' = erase x_type x _UU0393_ v in E.Coq_tApp (f', l')
        | Coq_tConst (k, _) -> E.Coq_tConst k
        | Coq_tConstruct (ind, n, _) -> E.Coq_tConstruct (ind, n, [])
        | Coq_tCase (indn, p, c, brs) ->
          let c' = erase x_type x _UU0393_ c in
          let brs' =
            let rec erase_brs _UU0393_0 p0 = function
            | [] -> []
            | b :: l ->
              let br' =
                erase x_type x
                  (PCUICEnvironment.app_context _UU0393_0
                    (inst_case_branch_context p0 b)) b.bbody
              in
              let brs' = erase_brs _UU0393_0 p0 l in
              ((erase_context b.bcontext), br') :: brs'
            in erase_brs _UU0393_ p brs
          in
          E.Coq_tCase ((indn.ci_ind, indn.ci_npar), c', brs')
        | Coq_tProj (p, c) ->
          let c' = erase x_type x _UU0393_ c in E.Coq_tProj (p, c')
        | Coq_tFix (mfix, idx) ->
          let _UU0393_' = app (PCUICEnvironment.fix_context mfix) _UU0393_ in
          let mfix' =
            let rec erase_fix _UU0393_0 = function
            | [] -> []
            | d :: l ->
              let dbody' = erase x_type x _UU0393_0 d.dbody in
              let dbody'0 =
                if isBox dbody'
                then (match d.dbody with
                      | Coq_tLambda (na, _, _) ->
                        E.Coq_tLambda (na.binder_name, E.Coq_tBox)
                      | _ -> dbody')
                else dbody'
              in
              let d' = { E.dname = d.dname.binder_name; E.dbody = dbody'0;
                E.rarg = d.rarg }
              in
              d' :: (erase_fix _UU0393_0 l)
            in erase_fix _UU0393_' mfix
          in
          E.Coq_tFix (mfix', idx)
        | Coq_tCoFix (mfix, idx) ->
          let _UU0393_' = app (PCUICEnvironment.fix_context mfix) _UU0393_ in
          let mfix' =
            let rec erase_cofix _UU0393_0 = function
            | [] -> []
            | d :: l ->
              let dbody' = erase x_type x _UU0393_0 d.dbody in
              let d' = { E.dname = d.dname.binder_name; E.dbody = dbody';
                E.rarg = d.rarg }
              in
              d' :: (erase_cofix _UU0393_0 l)
            in erase_cofix _UU0393_' mfix
          in
          E.Coq_tCoFix (mfix', idx)
        | Coq_tPrim prim -> E.Coq_tPrim (erase_prim_val prim)
        | _ -> assert false (* absurd case *))

(** val erase_constant_body :
    abstract_env_impl -> __ -> PCUICEnvironment.constant_body ->
    E.constant_body * KernameSet.t **)

let erase_constant_body x_type x cb =
  let filtered_var =
    let filtered_var = PCUICEnvironment.cst_body cb in
    (match filtered_var with
     | Some b ->
       let b' = erase x_type x [] b in ((Some b'), (term_global_deps b'))
     | None -> (None, KernameSet.empty))
  in
  let (body, deps) = filtered_var in (body, deps)
