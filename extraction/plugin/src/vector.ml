open Datatypes
open Fin
open VectorDef

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a t = 'a VectorDef.t =
| Coq_nil
| Coq_cons of 'a * nat * 'a t

(** val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2 **)

let caseS h _ = function
| Coq_nil -> Obj.magic __
| Coq_cons (h0, n0, t0) -> h h0 n0 t0

(** val nth : nat -> 'a1 t -> Fin.t -> 'a1 **)

let rec nth _ v' = function
| F1 n -> caseS (fun h _ _ -> h) n v'
| FS (n, p') -> caseS (fun _ -> nth) n v' p'

(** val nth_order : nat -> 'a1 t -> nat -> 'a1 **)

let nth_order n v p =
  nth n v (of_nat_lt p n)
