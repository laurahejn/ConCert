open Datatypes
open Kernames
open Nat0
open PCUICAst
open PeanoNat
open Universes0

(** val global_variance :
    PCUICEnvironment.global_env -> global_reference -> nat -> Variance.t list
    option **)

let global_variance _UU03a3_ gr napp =
  match gr with
  | IndRef ind ->
    (match lookup_inductive _UU03a3_ ind with
     | Some p ->
       let (mdecl, idecl) = p in
       (match destArity [] (PCUICEnvironment.ind_type idecl) with
        | Some p0 ->
          let (ctx, _) = p0 in
          if Nat.leb (PCUICEnvironment.context_assumptions ctx) napp
          then PCUICEnvironment.ind_variance mdecl
          else None
        | None -> None)
     | None -> None)
  | ConstructRef (ind, k) ->
    (match lookup_constructor _UU03a3_ ind k with
     | Some p ->
       let (p0, cdecl) = p in
       let (mdecl, _) = p0 in
       if Nat.leb
            (add (PCUICEnvironment.cstr_arity cdecl)
              (PCUICEnvironment.ind_npars mdecl)) napp
       then Some []
       else None
     | None -> None)
  | _ -> None
