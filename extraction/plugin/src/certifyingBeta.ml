open Ast0
open Datatypes
open List0
open Utils

(** val betared_aux : term list -> term -> term **)

let rec betared_aux args t = match t with
| Coq_tCast (t0, _, _) -> betared_aux args t0
| Coq_tLambda (na, ty, body) ->
  let b = betared_aux [] body in beta_body (Coq_tLambda (na, ty, b)) args
| Coq_tApp (hd, args0) ->
  betared_aux (app (map (betared_aux []) args0) args) hd
| _ -> mkApps (map_subterms (betared_aux []) t) args

(** val betared : term -> term **)

let betared =
  betared_aux []
