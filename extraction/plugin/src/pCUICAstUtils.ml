open BasicAst
open Byte
open Kernames
open MCString
open PCUICAst
open PCUICPrimitive
open Universes0
open Bytestring

(** val string_of_aname : name binder_annot -> String.t **)

let string_of_aname b =
  string_of_name b.binder_name

(** val string_of_term : term -> String.t **)

let rec string_of_term = function
| Coq_tRel n ->
  String.append (String.String (Coq_x52, (String.String (Coq_x65,
    (String.String (Coq_x6c, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_nat n) (String.String (Coq_x29,
      String.EmptyString)))
| Coq_tVar n ->
  String.append (String.String (Coq_x56, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append n (String.String (Coq_x29, String.EmptyString)))
| Coq_tEvar (ev, args) ->
  String.append (String.String (Coq_x45, (String.String (Coq_x76,
    (String.String (Coq_x61, (String.String (Coq_x72, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_nat ev)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_list string_of_term args) (String.String
          (Coq_x29, String.EmptyString)))))
| Coq_tSort s ->
  String.append (String.String (Coq_x53, (String.String (Coq_x6f,
    (String.String (Coq_x72, (String.String (Coq_x74, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_sort s) (String.String (Coq_x29,
      String.EmptyString)))
| Coq_tProd (na, b, t1) ->
  String.append (String.String (Coq_x50, (String.String (Coq_x72,
    (String.String (Coq_x6f, (String.String (Coq_x64, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_aname na)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term b)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_term t1) (String.String (Coq_x29,
              String.EmptyString)))))))
| Coq_tLambda (na, b, t1) ->
  String.append (String.String (Coq_x4c, (String.String (Coq_x61,
    (String.String (Coq_x6d, (String.String (Coq_x62, (String.String
    (Coq_x64, (String.String (Coq_x61, (String.String (Coq_x28,
    String.EmptyString))))))))))))))
    (String.append (string_of_aname na)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term b)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_term t1) (String.String (Coq_x29,
              String.EmptyString)))))))
| Coq_tLetIn (na, b, t', t1) ->
  String.append (String.String (Coq_x4c, (String.String (Coq_x65,
    (String.String (Coq_x74, (String.String (Coq_x49, (String.String
    (Coq_x6e, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_aname na)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term b)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_term t')
              (String.append (String.String (Coq_x2c, String.EmptyString))
                (String.append (string_of_term t1) (String.String (Coq_x29,
                  String.EmptyString)))))))))
| Coq_tApp (f, l) ->
  String.append (String.String (Coq_x41, (String.String (Coq_x70,
    (String.String (Coq_x70, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_term f)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term l) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tConst (c, u) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_kername c)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_universe_instance u) (String.String
          (Coq_x29, String.EmptyString)))))
| Coq_tInd (i, u) ->
  String.append (String.String (Coq_x49, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_inductive i)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_universe_instance u) (String.String
          (Coq_x29, String.EmptyString)))))
| Coq_tConstruct (i, n, u) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x75,
    (String.String (Coq_x63, (String.String (Coq_x74, (String.String
    (Coq_x28, String.EmptyString))))))))))))))))))))
    (String.append (string_of_inductive i)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat n)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_universe_instance u) (String.String
              (Coq_x29, String.EmptyString)))))))
| Coq_tCase (ci, p, t1, brs) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x61,
    (String.String (Coq_x73, (String.String (Coq_x65, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_case_info ci)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_term t1)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_predicate string_of_term p)
              (String.append (String.String (Coq_x2c, String.EmptyString))
                (String.append
                  (string_of_list (string_of_branch string_of_term) brs)
                  (String.String (Coq_x29, String.EmptyString)))))))))
| Coq_tProj (p, c) ->
  String.append (String.String (Coq_x50, (String.String (Coq_x72,
    (String.String (Coq_x6f, (String.String (Coq_x6a, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append (string_of_inductive p.proj_ind)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat p.proj_npars)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_nat p.proj_arg)
              (String.append (String.String (Coq_x2c, String.EmptyString))
                (String.append (string_of_term c) (String.String (Coq_x29,
                  String.EmptyString)))))))))
| Coq_tFix (l, n) ->
  String.append (String.String (Coq_x46, (String.String (Coq_x69,
    (String.String (Coq_x78, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_list (string_of_def string_of_term) l)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat n) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tCoFix (l, n) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x46, (String.String (Coq_x69, (String.String
    (Coq_x78, (String.String (Coq_x28, String.EmptyString))))))))))))
    (String.append (string_of_list (string_of_def string_of_term) l)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat n) (String.String (Coq_x29,
          String.EmptyString)))))
| Coq_tPrim i ->
  String.append (String.String (Coq_x49, (String.String (Coq_x6e,
    (String.String (Coq_x74, (String.String (Coq_x28,
    String.EmptyString))))))))
    (String.append (string_of_prim string_of_term i) (String.String (Coq_x29,
      String.EmptyString)))

(** val decompose_app_rec : term -> term list -> term * term list **)

let rec decompose_app_rec t0 l =
  match t0 with
  | Coq_tApp (f, a) -> decompose_app_rec f (a :: l)
  | _ -> (t0, l)

(** val decompose_app : term -> term * term list **)

let decompose_app t0 =
  decompose_app_rec t0 []

type view_sort =
| Coq_view_sort_sort of Universe.t
| Coq_view_sort_other of term

(** val view_sortc : term -> view_sort **)

let view_sortc = function
| Coq_tSort u -> Coq_view_sort_sort u
| x -> Coq_view_sort_other x

type view_prod =
| Coq_view_prod_prod of aname * term * term
| Coq_view_prod_other of term

(** val view_prodc : term -> view_prod **)

let view_prodc = function
| Coq_tProd (na, a, b) -> Coq_view_prod_prod (na, a, b)
| x -> Coq_view_prod_other x

type view_ind =
| Coq_view_ind_tInd of inductive * Instance.t
| Coq_view_ind_other of term

(** val view_indc : term -> view_ind **)

let view_indc = function
| Coq_tInd (ind, ui) -> Coq_view_ind_tInd (ind, ui)
| x -> Coq_view_ind_other x
