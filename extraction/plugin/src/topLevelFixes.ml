open Ascii
open Datatypes
open EAst
open ELiftSubst
open ExAst
open Kernames
open List0
open MCList
open ResultMonad
open String0
open Transform0
open Utils

(** val optimize_aux : term -> kername -> nat -> term **)

let rec optimize_aux t kn lams =
  match t with
  | Coq_tLambda (na, body) ->
    Coq_tLambda (na, (optimize_aux body kn (S lams)))
  | Coq_tFix (m, n) ->
    (match m with
     | [] -> t
     | def :: l ->
       (match l with
        | [] ->
          (match n with
           | O ->
             subst1
               (mkApps (Coq_tConst kn)
                 (rev_map (fun x -> Coq_tRel x) (seq O lams))) O def.dbody
           | S _ -> t)
        | _ :: _ -> t))
  | _ -> t

(** val optimize : term -> kername -> term **)

let optimize t kn =
  optimize_aux t kn O

(** val optimize_decl :
    ((kername * bool) * global_decl) -> (kername * bool) * global_decl **)

let optimize_decl = function
| (p0, decl) ->
  let (kn, includes_deps) = p0 in
  let new_decl =
    match decl with
    | ConstantDecl cst ->
      ConstantDecl { cst_type = cst.cst_type; cst_body =
        (option_map (fun t -> optimize t kn) cst.cst_body) }
    | _ -> decl
  in
  ((kn, includes_deps), new_decl)

(** val optimize_env : global_env -> global_env **)

let optimize_env _UU03a3_ =
  map optimize_decl _UU03a3_

(** val transform : coq_ExtractTransform **)

let transform _UU03a3_ =
  Ok
    (timed (String ((Ascii (true, true, false, false, true, false, true,
      false)), (String ((Ascii (true, false, true, false, true, true, true,
      false)), (String ((Ascii (false, true, false, false, false, true, true,
      false)), (String ((Ascii (true, true, false, false, true, true, true,
      false)), (String ((Ascii (false, false, true, false, true, true, true,
      false)), (String ((Ascii (true, false, false, true, false, true, true,
      false)), (String ((Ascii (false, false, true, false, true, true, true,
      false)), (String ((Ascii (true, false, true, false, true, true, true,
      false)), (String ((Ascii (false, false, true, false, true, true, true,
      false)), (String ((Ascii (true, false, false, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, false, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (false, false, false, false, false, true,
      false, false)), (String ((Ascii (true, true, true, true, false, true,
      true, false)), (String ((Ascii (false, true, true, false, false, true,
      true, false)), (String ((Ascii (false, false, false, false, false,
      true, false, false)), (String ((Ascii (false, false, true, false, true,
      true, true, false)), (String ((Ascii (true, true, true, true, false,
      true, true, false)), (String ((Ascii (false, false, false, false, true,
      true, true, false)), (String ((Ascii (false, false, false, false,
      false, true, false, false)), (String ((Ascii (false, false, true, true,
      false, true, true, false)), (String ((Ascii (true, false, true, false,
      false, true, true, false)), (String ((Ascii (false, true, true, false,
      true, true, true, false)), (String ((Ascii (true, false, true, false,
      false, true, true, false)), (String ((Ascii (false, false, true, true,
      false, true, true, false)), (String ((Ascii (false, false, false,
      false, false, true, false, false)), (String ((Ascii (false, true, true,
      false, false, true, true, false)), (String ((Ascii (true, false, false,
      true, false, true, true, false)), (String ((Ascii (false, false, false,
      true, true, true, true, false)), (String ((Ascii (true, false, true,
      false, false, true, true, false)), (String ((Ascii (true, true, false,
      false, true, true, true, false)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (fun _ -> optimize_env _UU03a3_))
