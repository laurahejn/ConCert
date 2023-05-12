open Datatypes
open EAst
open ECSubst
open EEnvMap
open Kernames
open List0
open MCProd

(** val optimize : GlobalContextMap.t -> term -> term **)

let rec optimize _UU03a3_ t0 = match t0 with
| Coq_tRel i -> Coq_tRel i
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (optimize _UU03a3_) args))
| Coq_tLambda (na, m) -> Coq_tLambda (na, (optimize _UU03a3_ m))
| Coq_tLetIn (na, b, b') ->
  Coq_tLetIn (na, (optimize _UU03a3_ b), (optimize _UU03a3_ b'))
| Coq_tApp (u, v) -> Coq_tApp ((optimize _UU03a3_ u), (optimize _UU03a3_ v))
| Coq_tConstruct (ind, i, args) ->
  Coq_tConstruct (ind, i, (map (optimize _UU03a3_) args))
| Coq_tCase (ind, c, brs) ->
  let brs' = map (on_snd (optimize _UU03a3_)) brs in
  (match GlobalContextMap.inductive_isprop_and_pars _UU03a3_ (fst ind) with
   | Some p ->
     let (b, _) = p in
     if b
     then (match brs' with
           | [] -> Coq_tCase (ind, (optimize _UU03a3_ c), brs')
           | p0 :: l ->
             let (a, b0) = p0 in
             (match l with
              | [] -> substl (repeat Coq_tBox (length a)) b0
              | _ :: _ -> Coq_tCase (ind, (optimize _UU03a3_ c), brs')))
     else Coq_tCase (ind, (optimize _UU03a3_ c), brs')
   | None -> Coq_tCase (ind, (optimize _UU03a3_ c), brs'))
| Coq_tProj (p, c) ->
  (match GlobalContextMap.inductive_isprop_and_pars _UU03a3_ p.proj_ind with
   | Some p0 ->
     let (b, _) = p0 in
     if b then Coq_tBox else Coq_tProj (p, (optimize _UU03a3_ c))
   | None -> Coq_tProj (p, (optimize _UU03a3_ c)))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def (optimize _UU03a3_)) mfix in Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def (optimize _UU03a3_)) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> t0
