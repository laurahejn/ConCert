open Ast0
open AstUtils
open BasicAst
open Datatypes
open List0
open String0
open TermEquality
open Typing0

(** val map_fst : ('a1 -> 'a2) -> ('a1 * 'a3) -> 'a2 * 'a3 **)

let map_fst f p =
  ((f (fst p)), (snd p))

(** val timed : string -> (unit -> 'a1) -> 'a1 **)

let timed _ f =
  f ()

(** val map_subterms : (term -> term) -> term -> term **)

let map_subterms f t = match t with
| Coq_tEvar (n, ts) -> Coq_tEvar (n, (map f ts))
| Coq_tCast (t0, kind, ty) -> Coq_tCast ((f t0), kind, (f ty))
| Coq_tProd (na, ty, body) -> Coq_tProd (na, (f ty), (f body))
| Coq_tLambda (na, ty, body) -> Coq_tLambda (na, (f ty), (f body))
| Coq_tLetIn (na, val0, ty, body) ->
  Coq_tLetIn (na, (f val0), (f ty), (f body))
| Coq_tApp (hd, arg) -> Coq_tApp ((f hd), (map f arg))
| Coq_tCase (ci, p, disc, brs) ->
  Coq_tCase (ci, (map_predicate (Obj.magic id) f f p), (f disc),
    (map (map_branch f) brs))
| Coq_tProj (p, t0) -> Coq_tProj (p, (f t0))
| Coq_tFix (def, i) -> Coq_tFix ((map (map_def f f) def), i)
| Coq_tCoFix (def, i) -> Coq_tCoFix ((map (map_def f f) def), i)
| _ -> t

(** val beta_body : term -> term list -> term **)

let rec beta_body body = function
| [] -> body
| a :: args0 ->
  (match body with
   | Coq_tLambda (_, _, body0) -> beta_body (subst1 a O body0) args0
   | _ -> mkApps body (a :: args0))

(** val iota_body : Env.global_env -> term -> term **)

let iota_body _UU03a3_ body = match body with
| Coq_tCase (ci, p, discr, brs) ->
  let (hd, args) = decompose_app discr in
  (match hd with
   | Coq_tConstruct (_, c, _) ->
     (match nth_error brs c with
      | Some br ->
        (match lookup_constructor _UU03a3_ ci.ci_ind c with
         | Some p0 ->
           let (p1, cb) = p0 in
           let (mib, _) = p1 in
           let bctx = case_branch_context ci.ci_ind mib cb p br in
           iota_red ci.ci_npar args bctx br
         | None -> body)
      | None -> body)
   | _ -> body)
| _ -> body
