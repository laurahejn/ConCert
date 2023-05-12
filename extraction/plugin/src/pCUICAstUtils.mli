open BasicAst
open Byte
open Kernames
open MCString
open PCUICAst
open PCUICPrimitive
open Universes0
open Bytestring

val string_of_aname : name binder_annot -> String.t

val string_of_term : term -> String.t

val decompose_app_rec : term -> term list -> term * term list

val decompose_app : term -> term * term list

type view_sort =
| Coq_view_sort_sort of Universe.t
| Coq_view_sort_other of term

val view_sortc : term -> view_sort

type view_prod =
| Coq_view_prod_prod of aname * term * term
| Coq_view_prod_other of term

val view_prodc : term -> view_prod

type view_ind =
| Coq_view_ind_tInd of inductive * Instance.t
| Coq_view_ind_other of term

val view_indc : term -> view_ind
