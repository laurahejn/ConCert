open Monad_utils

type __ = Obj.t

type ('t, 'e) result =
| Ok of 't
| Err of 'e

(** val result_rect :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) result -> 'a3 **)

let result_rect f f0 = function
| Ok t -> f t
| Err e -> f0 e

(** val result_rec :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) result -> 'a3 **)

let result_rec f f0 = function
| Ok t -> f t
| Err e -> f0 e

(** val coq_Monad_result : (__, 'a1) result coq_Monad **)

let coq_Monad_result =
  { ret = (fun _ t -> Ok t); bind = (fun _ _ mt f ->
    match mt with
    | Ok t -> f t
    | Err e -> Err e) }

(** val map_error : ('a2 -> 'a3) -> ('a1, 'a2) result -> ('a1, 'a3) result **)

let map_error f = function
| Ok t -> Ok t
| Err e -> Err (f e)
