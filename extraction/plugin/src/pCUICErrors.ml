open BasicAst
open Byte
open Datatypes
open Kernames
open MCString
open PCUICAst
open PCUICPretty
open Universes0
open Bytestring
open Monad_utils

type __ = Obj.t

type coq_ConversionError =
| NotFoundConstants of kername * kername
| NotFoundConstant of kername
| LambdaNotConvertibleTypes of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
   * coq_ConversionError
| LambdaNotConvertibleAnn of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
| ProdNotConvertibleDomains of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
   * coq_ConversionError
| ProdNotConvertibleAnn of PCUICEnvironment.context * aname * term * 
   term * PCUICEnvironment.context * aname * term * term
| ContextNotConvertibleAnn of PCUICEnvironment.context * term context_decl
   * PCUICEnvironment.context * term context_decl
| ContextNotConvertibleType of PCUICEnvironment.context * term context_decl
   * PCUICEnvironment.context * term context_decl
| ContextNotConvertibleBody of PCUICEnvironment.context * term context_decl
   * PCUICEnvironment.context * term context_decl
| ContextNotConvertibleLength
| CaseOnDifferentInd of PCUICEnvironment.context * case_info * term predicate
   * term * term branch list * PCUICEnvironment.context * case_info
   * term predicate * term * term branch list
| CasePredParamsUnequalLength of PCUICEnvironment.context * case_info
   * term predicate * term * term branch list * PCUICEnvironment.context
   * case_info * term predicate * term * term branch list
| CasePredUnequalUniverseInstances of PCUICEnvironment.context * case_info
   * term predicate * term * term branch list * PCUICEnvironment.context
   * case_info * term predicate * term * term branch list
| DistinctStuckProj of PCUICEnvironment.context * projection * term
   * PCUICEnvironment.context * projection * term
| CannotUnfoldFix of PCUICEnvironment.context * term mfixpoint * nat
   * PCUICEnvironment.context * term mfixpoint * nat
| FixRargMismatch of nat * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint
| FixMfixMismatch of nat * PCUICEnvironment.context * term mfixpoint
   * PCUICEnvironment.context * term mfixpoint
| DistinctCoFix of PCUICEnvironment.context * term mfixpoint * nat
   * PCUICEnvironment.context * term mfixpoint * nat
| CoFixRargMismatch of nat * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint * PCUICEnvironment.context * term def
   * term mfixpoint * term mfixpoint
| CoFixMfixMismatch of nat * PCUICEnvironment.context * term mfixpoint
   * PCUICEnvironment.context * term mfixpoint
| StackHeadError of conv_pb * PCUICEnvironment.context * term * term list
   * term * term list * PCUICEnvironment.context * term * term * term list
   * coq_ConversionError
| StackTailError of conv_pb * PCUICEnvironment.context * term * term list
   * term * term list * PCUICEnvironment.context * term * term * term list
   * coq_ConversionError
| StackMismatch of PCUICEnvironment.context * term * term list * term list
   * PCUICEnvironment.context * term * term list
| HeadMismatch of conv_pb * PCUICEnvironment.context * term
   * PCUICEnvironment.context * term

type type_error =
| UnboundRel of nat
| UnboundVar of String.t
| UnboundEvar of nat
| UndeclaredConstant of kername
| UndeclaredInductive of inductive
| UndeclaredConstructor of inductive * nat
| NotCumulSmaller of bool * __ * PCUICEnvironment.context * term * term
   * term * term * coq_ConversionError
| NotConvertible of __ * PCUICEnvironment.context * term * term
| NotASort of term
| NotAProduct of term * term
| NotAnInductive of term
| NotAnArity of term
| IllFormedFix of term mfixpoint * nat
| UnsatisfiedConstraints of ConstraintSet.t
| Msg of String.t

(** val string_of_conv_pb : conv_pb -> String.t **)

let string_of_conv_pb = function
| Conv ->
  String.String (Coq_x63, (String.String (Coq_x6f, (String.String (Coq_x6e,
    (String.String (Coq_x76, (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x73, (String.String (Coq_x69,
    (String.String (Coq_x6f, (String.String (Coq_x6e,
    String.EmptyString)))))))))))))))))))
| Cumul ->
  String.String (Coq_x63, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x75, (String.String (Coq_x6c, (String.String
    (Coq_x61, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x76, (String.String (Coq_x69, (String.String
    (Coq_x74, (String.String (Coq_x79,
    String.EmptyString)))))))))))))))))))))))

(** val print_term :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
    String.t **)

let print_term _UU03a3_ _UU0393_ t0 =
  let ids = fresh_names _UU03a3_ [] _UU0393_ in
  print_term _UU03a3_ true ids true false t0

(** val print_context_decl :
    PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term
    context_decl -> String.t **)

let print_context_decl _UU03a3_ _UU0393_ decl =
  String.append
    (fresh_name _UU03a3_ [] decl.decl_name.binder_name (Some decl.decl_type))
    (String.append (String.String (Coq_x20, (String.String (Coq_x3a,
      (String.String (Coq_x20, String.EmptyString))))))
      (String.append (print_term _UU03a3_ _UU0393_ decl.decl_type)
        (match decl.decl_body with
         | Some body ->
           String.append (String.String (Coq_x20, (String.String (Coq_x3a,
             (String.String (Coq_x3d, (String.String (Coq_x20,
             String.EmptyString)))))))) (print_term _UU03a3_ _UU0393_ body)
         | None -> String.EmptyString)))

(** val string_of_conv_error :
    PCUICEnvironment.global_env_ext -> coq_ConversionError -> String.t **)

let rec string_of_conv_error _UU03a3_ = function
| NotFoundConstants (c1, c2) ->
  String.append (String.String (Coq_x42, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x68, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x74, (String.String (Coq_x73, (String.String
    (Coq_x20, String.EmptyString))))))))))))))))))))))))))))))
    (String.append (string_of_kername c1)
      (String.append (String.String (Coq_x20, (String.String (Coq_x61,
        (String.String (Coq_x6e, (String.String (Coq_x64, (String.String
        (Coq_x20, String.EmptyString))))))))))
        (String.append (string_of_kername c2) (String.String (Coq_x20,
          (String.String (Coq_x61, (String.String (Coq_x72, (String.String
          (Coq_x65, (String.String (Coq_x20, (String.String (Coq_x6e,
          (String.String (Coq_x6f, (String.String (Coq_x74, (String.String
          (Coq_x20, (String.String (Coq_x66, (String.String (Coq_x6f,
          (String.String (Coq_x75, (String.String (Coq_x6e, (String.String
          (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x69,
          (String.String (Coq_x6e, (String.String (Coq_x20, (String.String
          (Coq_x74, (String.String (Coq_x68, (String.String (Coq_x65,
          (String.String (Coq_x20, (String.String (Coq_x65, (String.String
          (Coq_x6e, (String.String (Coq_x76, (String.String (Coq_x69,
          (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
          (Coq_x6e, (String.String (Coq_x6d, (String.String (Coq_x65,
          (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
          (Coq_x2e,
          String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| NotFoundConstant c ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x61, (String.String (Coq_x6e,
    (String.String (Coq_x74, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))
    (String.append (string_of_kername c) (String.String (Coq_x20,
      (String.String (Coq_x63, (String.String (Coq_x6f, (String.String
      (Coq_x6d, (String.String (Coq_x6d, (String.String (Coq_x6f,
      (String.String (Coq_x6e, (String.String (Coq_x20, (String.String
      (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x20,
      (String.String (Coq_x62, (String.String (Coq_x6f, (String.String
      (Coq_x74, (String.String (Coq_x68, (String.String (Coq_x20,
      (String.String (Coq_x74, (String.String (Coq_x65, (String.String
      (Coq_x72, (String.String (Coq_x6d, (String.String (Coq_x73,
      (String.String (Coq_x20, (String.String (Coq_x69, (String.String
      (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x6e,
      (String.String (Coq_x6f, (String.String (Coq_x74, (String.String
      (Coq_x20, (String.String (Coq_x66, (String.String (Coq_x6f,
      (String.String (Coq_x75, (String.String (Coq_x6e, (String.String
      (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x69,
      (String.String (Coq_x6e, (String.String (Coq_x20, (String.String
      (Coq_x74, (String.String (Coq_x68, (String.String (Coq_x65,
      (String.String (Coq_x20, (String.String (Coq_x65, (String.String
      (Coq_x6e, (String.String (Coq_x76, (String.String (Coq_x69,
      (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
      (Coq_x6e, (String.String (Coq_x6d, (String.String (Coq_x65,
      (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
      (Coq_x2e,
      String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| LambdaNotConvertibleTypes (_UU0393_1, na, a1, t1, _UU0393_2, na', a2, t2, e0) ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67,
    String.EmptyString))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_1 (Coq_tLambda (na, a1, t1)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_2 (Coq_tLambda (na', a2, t2)))
                (String.append nl
                  (String.append (String.String (Coq_x74, (String.String
                    (Coq_x79, (String.String (Coq_x70, (String.String
                    (Coq_x65, (String.String (Coq_x73, (String.String
                    (Coq_x20, (String.String (Coq_x61, (String.String
                    (Coq_x72, (String.String (Coq_x65, (String.String
                    (Coq_x20, (String.String (Coq_x6e, (String.String
                    (Coq_x6f, (String.String (Coq_x74, (String.String
                    (Coq_x20, (String.String (Coq_x63, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x76, (String.String (Coq_x65, (String.String
                    (Coq_x72, (String.String (Coq_x74, (String.String
                    (Coq_x69, (String.String (Coq_x62, (String.String
                    (Coq_x6c, (String.String (Coq_x65, (String.String
                    (Coq_x3a,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))
                    (String.append nl (string_of_conv_error _UU03a3_ e0))))))))))
| LambdaNotConvertibleAnn (_UU0393_1, na, a1, t1, _UU0393_2, na', a2, t2) ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67,
    String.EmptyString))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_1 (Coq_tLambda (na, a1, t1)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_2 (Coq_tLambda (na', a2, t2)))
                (String.append nl
                  (String.append (String.String (Coq_x62, (String.String
                    (Coq_x69, (String.String (Coq_x6e, (String.String
                    (Coq_x64, (String.String (Coq_x69, (String.String
                    (Coq_x6e, (String.String (Coq_x67, (String.String
                    (Coq_x20, (String.String (Coq_x61, (String.String
                    (Coq_x6e, (String.String (Coq_x6e, (String.String
                    (Coq_x6f, (String.String (Coq_x74, (String.String
                    (Coq_x61, (String.String (Coq_x74, (String.String
                    (Coq_x69, (String.String (Coq_x6f, (String.String
                    (Coq_x6e, (String.String (Coq_x73, (String.String
                    (Coq_x20, (String.String (Coq_x61, (String.String
                    (Coq_x72, (String.String (Coq_x65, (String.String
                    (Coq_x20, (String.String (Coq_x6e, (String.String
                    (Coq_x6f, (String.String (Coq_x74, (String.String
                    (Coq_x20, (String.String (Coq_x63, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x76, (String.String (Coq_x65, (String.String
                    (Coq_x72, (String.String (Coq_x74, (String.String
                    (Coq_x69, (String.String (Coq_x62, (String.String
                    (Coq_x6c, (String.String (Coq_x65,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    nl))))))))
| ProdNotConvertibleDomains (_UU0393_1, na, a1, b1, _UU0393_2, na', a2, b2, e0) ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67,
    String.EmptyString))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_1 (Coq_tProd (na, a1, b1)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_2 (Coq_tProd (na', a2, b2)))
                (String.append nl
                  (String.append (String.String (Coq_x64, (String.String
                    (Coq_x6f, (String.String (Coq_x6d, (String.String
                    (Coq_x61, (String.String (Coq_x69, (String.String
                    (Coq_x6e, (String.String (Coq_x73, (String.String
                    (Coq_x20, (String.String (Coq_x61, (String.String
                    (Coq_x72, (String.String (Coq_x65, (String.String
                    (Coq_x20, (String.String (Coq_x6e, (String.String
                    (Coq_x6f, (String.String (Coq_x74, (String.String
                    (Coq_x20, (String.String (Coq_x63, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x76, (String.String (Coq_x65, (String.String
                    (Coq_x72, (String.String (Coq_x74, (String.String
                    (Coq_x69, (String.String (Coq_x62, (String.String
                    (Coq_x6c, (String.String (Coq_x65, (String.String
                    (Coq_x3a,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    (String.append nl (string_of_conv_error _UU03a3_ e0))))))))))
| ProdNotConvertibleAnn (_UU0393_1, na, a1, b1, _UU0393_2, na', a2, b2) ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67,
    String.EmptyString))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_1 (Coq_tProd (na, a1, b1)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_2 (Coq_tProd (na', a2, b2)))
                (String.append nl
                  (String.append (String.String (Coq_x62, (String.String
                    (Coq_x69, (String.String (Coq_x6e, (String.String
                    (Coq_x64, (String.String (Coq_x69, (String.String
                    (Coq_x6e, (String.String (Coq_x67, (String.String
                    (Coq_x20, (String.String (Coq_x61, (String.String
                    (Coq_x6e, (String.String (Coq_x6e, (String.String
                    (Coq_x6f, (String.String (Coq_x74, (String.String
                    (Coq_x61, (String.String (Coq_x74, (String.String
                    (Coq_x69, (String.String (Coq_x6f, (String.String
                    (Coq_x6e, (String.String (Coq_x73, (String.String
                    (Coq_x20, (String.String (Coq_x61, (String.String
                    (Coq_x72, (String.String (Coq_x65, (String.String
                    (Coq_x20, (String.String (Coq_x6e, (String.String
                    (Coq_x6f, (String.String (Coq_x74, (String.String
                    (Coq_x20, (String.String (Coq_x63, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x76, (String.String (Coq_x65, (String.String
                    (Coq_x72, (String.String (Coq_x74, (String.String
                    (Coq_x69, (String.String (Coq_x62, (String.String
                    (Coq_x6c, (String.String (Coq_x65, (String.String
                    (Coq_x3a,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    nl))))))))
| ContextNotConvertibleAnn (_UU0393_, decl, _UU0393_', decl') ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67, (String.String
    (Coq_x20, (String.String (Coq_x74, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x64, (String.String (Coq_x65, (String.String (Coq_x63,
    (String.String (Coq_x6c, (String.String (Coq_x61, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x6f, (String.String
    (Coq_x6e, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_context_decl _UU03a3_ _UU0393_ decl)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append (print_context_decl _UU03a3_ _UU0393_' decl')
                (String.append nl (String.String (Coq_x74, (String.String
                  (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x62, (String.String (Coq_x69,
                  (String.String (Coq_x6e, (String.String (Coq_x64,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x6e, (String.String (Coq_x6e,
                  (String.String (Coq_x6f, (String.String (Coq_x74,
                  (String.String (Coq_x61, (String.String (Coq_x74,
                  (String.String (Coq_x69, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x73,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x72, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x6e,
                  (String.String (Coq_x6f, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x65,
                  (String.String (Coq_x71, (String.String (Coq_x75,
                  (String.String (Coq_x61, (String.String (Coq_x6c,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| ContextNotConvertibleType (_UU0393_, decl, _UU0393_', decl') ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67, (String.String
    (Coq_x20, (String.String (Coq_x74, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x64, (String.String (Coq_x65, (String.String (Coq_x63,
    (String.String (Coq_x6c, (String.String (Coq_x61, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x6f, (String.String
    (Coq_x6e, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_context_decl _UU03a3_ _UU0393_ decl)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append (print_context_decl _UU03a3_ _UU0393_' decl')
                (String.append nl (String.String (Coq_x74, (String.String
                  (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x74, (String.String (Coq_x79,
                  (String.String (Coq_x70, (String.String (Coq_x65,
                  (String.String (Coq_x73, (String.String (Coq_x20,
                  (String.String (Coq_x61, (String.String (Coq_x72,
                  (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x6e, (String.String (Coq_x6f,
                  (String.String (Coq_x74, (String.String (Coq_x20,
                  (String.String (Coq_x63, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x76,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x62, (String.String (Coq_x6c,
                  (String.String (Coq_x65,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| ContextNotConvertibleBody (_UU0393_, decl, _UU0393_', decl') ->
  String.append (String.String (Coq_x57, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
    (String.String (Coq_x6d, (String.String (Coq_x70, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x67, (String.String
    (Coq_x20, (String.String (Coq_x74, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x64, (String.String (Coq_x65, (String.String (Coq_x63,
    (String.String (Coq_x6c, (String.String (Coq_x61, (String.String
    (Coq_x72, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x6f, (String.String
    (Coq_x6e, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_context_decl _UU03a3_ _UU0393_ decl)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append (print_context_decl _UU03a3_ _UU0393_' decl')
                (String.append nl (String.String (Coq_x74, (String.String
                  (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x62, (String.String (Coq_x6f,
                  (String.String (Coq_x64, (String.String (Coq_x69,
                  (String.String (Coq_x65, (String.String (Coq_x73,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x72, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x6e,
                  (String.String (Coq_x6f, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x63,
                  (String.String (Coq_x6f, (String.String (Coq_x6e,
                  (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x74,
                  (String.String (Coq_x69, (String.String (Coq_x62,
                  (String.String (Coq_x6c, (String.String (Coq_x65,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| ContextNotConvertibleLength ->
  String.String (Coq_x54, (String.String (Coq_x68, (String.String (Coq_x65,
    (String.String (Coq_x20, (String.String (Coq_x63, (String.String
    (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x74,
    (String.String (Coq_x65, (String.String (Coq_x78, (String.String
    (Coq_x74, (String.String (Coq_x73, (String.String (Coq_x20,
    (String.String (Coq_x68, (String.String (Coq_x61, (String.String
    (Coq_x76, (String.String (Coq_x65, (String.String (Coq_x20,
    (String.String (Coq_x75, (String.String (Coq_x6e, (String.String
    (Coq_x65, (String.String (Coq_x71, (String.String (Coq_x75,
    (String.String (Coq_x61, (String.String (Coq_x6c, (String.String
    (Coq_x20, (String.String (Coq_x6c, (String.String (Coq_x65,
    (String.String (Coq_x6e, (String.String (Coq_x67, (String.String
    (Coq_x74, (String.String (Coq_x68,
    String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| CaseOnDifferentInd (_UU0393_, ci, p, c, brs, _UU0393_', ci', p', c', brs') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x6b, (String.String (Coq_x20, (String.String
    (Coq_x70, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x74, (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x6e, (String.String (Coq_x2d,
    (String.String (Coq_x6d, (String.String (Coq_x61, (String.String
    (Coq_x74, (String.String (Coq_x63, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_ (Coq_tCase (ci, p, c, brs)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tCase (ci', p', c',
                  brs')))
                (String.append nl (String.String (Coq_x61, (String.String
                  (Coq_x72, (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x69,
                  (String.String (Coq_x73, (String.String (Coq_x74,
                  (String.String (Coq_x69, (String.String (Coq_x6e,
                  (String.String (Coq_x63, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x69,
                  (String.String (Coq_x6e, (String.String (Coq_x64,
                  (String.String (Coq_x75, (String.String (Coq_x63,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x79, (String.String (Coq_x70,
                  (String.String (Coq_x65, (String.String (Coq_x73,
                  (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| CasePredParamsUnequalLength (_UU0393_, ci, p, c, brs, _UU0393_', ci', p',
                               c', brs') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x70, (String.String (Coq_x72, (String.String (Coq_x65,
    (String.String (Coq_x64, (String.String (Coq_x69, (String.String
    (Coq_x63, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x65, (String.String (Coq_x73, (String.String
    (Coq_x20, (String.String (Coq_x6f, (String.String (Coq_x66,
    (String.String (Coq_x20, (String.String (Coq_x74, (String.String
    (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x20,
    (String.String (Coq_x74, (String.String (Coq_x77, (String.String
    (Coq_x6f, (String.String (Coq_x20, (String.String (Coq_x73,
    (String.String (Coq_x74, (String.String (Coq_x75, (String.String
    (Coq_x63, (String.String (Coq_x6b, (String.String (Coq_x20,
    (String.String (Coq_x70, (String.String (Coq_x61, (String.String
    (Coq_x74, (String.String (Coq_x74, (String.String (Coq_x65,
    (String.String (Coq_x72, (String.String (Coq_x6e, (String.String
    (Coq_x2d, (String.String (Coq_x6d, (String.String (Coq_x61,
    (String.String (Coq_x74, (String.String (Coq_x63, (String.String
    (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_ (Coq_tCase (ci, p, c, brs)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tCase (ci', p', c',
                  brs')))
                (String.append nl (String.String (Coq_x68, (String.String
                  (Coq_x61, (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x6e, (String.String (Coq_x20,
                  (String.String (Coq_x75, (String.String (Coq_x6e,
                  (String.String (Coq_x65, (String.String (Coq_x71,
                  (String.String (Coq_x75, (String.String (Coq_x61,
                  (String.String (Coq_x6c, (String.String (Coq_x20,
                  (String.String (Coq_x6e, (String.String (Coq_x75,
                  (String.String (Coq_x6d, (String.String (Coq_x62,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x20, (String.String (Coq_x6f,
                  (String.String (Coq_x66, (String.String (Coq_x20,
                  (String.String (Coq_x70, (String.String (Coq_x61,
                  (String.String (Coq_x72, (String.String (Coq_x61,
                  (String.String (Coq_x6d, (String.String (Coq_x65,
                  (String.String (Coq_x74, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x73,
                  (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| CasePredUnequalUniverseInstances (_UU0393_, ci, p, c, brs, _UU0393_', ci',
                                    p', c', brs') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x70, (String.String (Coq_x72, (String.String (Coq_x65,
    (String.String (Coq_x64, (String.String (Coq_x69, (String.String
    (Coq_x63, (String.String (Coq_x61, (String.String (Coq_x74,
    (String.String (Coq_x65, (String.String (Coq_x73, (String.String
    (Coq_x20, (String.String (Coq_x6f, (String.String (Coq_x66,
    (String.String (Coq_x20, (String.String (Coq_x74, (String.String
    (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x20,
    (String.String (Coq_x74, (String.String (Coq_x77, (String.String
    (Coq_x6f, (String.String (Coq_x20, (String.String (Coq_x73,
    (String.String (Coq_x74, (String.String (Coq_x75, (String.String
    (Coq_x63, (String.String (Coq_x6b, (String.String (Coq_x20,
    (String.String (Coq_x70, (String.String (Coq_x61, (String.String
    (Coq_x74, (String.String (Coq_x74, (String.String (Coq_x65,
    (String.String (Coq_x72, (String.String (Coq_x6e, (String.String
    (Coq_x2d, (String.String (Coq_x6d, (String.String (Coq_x61,
    (String.String (Coq_x74, (String.String (Coq_x63, (String.String
    (Coq_x68, (String.String (Coq_x65, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_ (Coq_tCase (ci, p, c, brs)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tCase (ci', p', c',
                  brs')))
                (String.append nl (String.String (Coq_x68, (String.String
                  (Coq_x61, (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x75,
                  (String.String (Coq_x6e, (String.String (Coq_x65,
                  (String.String (Coq_x71, (String.String (Coq_x75,
                  (String.String (Coq_x61, (String.String (Coq_x6c,
                  (String.String (Coq_x20, (String.String (Coq_x75,
                  (String.String (Coq_x6e, (String.String (Coq_x69,
                  (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x73,
                  (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x69, (String.String (Coq_x6e,
                  (String.String (Coq_x73, (String.String (Coq_x74,
                  (String.String (Coq_x61, (String.String (Coq_x6e,
                  (String.String (Coq_x63, (String.String (Coq_x65,
                  (String.String (Coq_x73, (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| DistinctStuckProj (_UU0393_, p, c, _UU0393_', p', c') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x6b, (String.String (Coq_x20, (String.String
    (Coq_x70, (String.String (Coq_x72, (String.String (Coq_x6f,
    (String.String (Coq_x6a, (String.String (Coq_x65, (String.String
    (Coq_x63, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x6f, (String.String (Coq_x6e, (String.String
    (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_ (Coq_tProj (p, c)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tProj (p', c')))
                (String.append nl (String.String (Coq_x61, (String.String
                  (Coq_x72, (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x73, (String.String (Coq_x79,
                  (String.String (Coq_x6e, (String.String (Coq_x74,
                  (String.String (Coq_x61, (String.String (Coq_x63,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x63, (String.String (Coq_x61,
                  (String.String (Coq_x6c, (String.String (Coq_x6c,
                  (String.String (Coq_x79, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x69,
                  (String.String (Coq_x66, (String.String (Coq_x66,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x65, (String.String (Coq_x6e,
                  (String.String (Coq_x74, (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| CannotUnfoldFix (_UU0393_, mfix, idx, _UU0393_', mfix', idx') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x66, (String.String
    (Coq_x69, (String.String (Coq_x78, (String.String (Coq_x65,
    (String.String (Coq_x64, (String.String (Coq_x2d, (String.String
    (Coq_x70, (String.String (Coq_x6f, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
    (Coq_x73, String.EmptyString))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_ (Coq_tFix (mfix, idx)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tFix (mfix', idx')))
                (String.append nl (String.String (Coq_x63, (String.String
                  (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x72,
                  (String.String (Coq_x65, (String.String (Coq_x73,
                  (String.String (Coq_x70, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x64,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x6f, (String.String (Coq_x20,
                  (String.String (Coq_x73, (String.String (Coq_x79,
                  (String.String (Coq_x6e, (String.String (Coq_x74,
                  (String.String (Coq_x61, (String.String (Coq_x63,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x63, (String.String (Coq_x61,
                  (String.String (Coq_x6c, (String.String (Coq_x6c,
                  (String.String (Coq_x79, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x69,
                  (String.String (Coq_x73, (String.String (Coq_x74,
                  (String.String (Coq_x69, (String.String (Coq_x6e,
                  (String.String (Coq_x63, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x6d, (String.String (Coq_x73,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x68, (String.String (Coq_x61,
                  (String.String (Coq_x74, (String.String (Coq_x20,
                  (String.String (Coq_x63, (String.String (Coq_x61,
                  (String.String (Coq_x6e, (String.String (Coq_x27,
                  (String.String (Coq_x74, (String.String (Coq_x20,
                  (String.String (Coq_x62, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x75,
                  (String.String (Coq_x6e, (String.String (Coq_x66,
                  (String.String (Coq_x6f, (String.String (Coq_x6c,
                  (String.String (Coq_x64, (String.String (Coq_x65,
                  (String.String (Coq_x64, (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| FixRargMismatch (idx, _UU0393_, u, mfix1, mfix2, _UU0393_', v, mfix1',
                   mfix2') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x66, (String.String
    (Coq_x69, (String.String (Coq_x78, (String.String (Coq_x65,
    (String.String (Coq_x64, (String.String (Coq_x2d, (String.String
    (Coq_x70, (String.String (Coq_x6f, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
    (Coq_x73, String.EmptyString))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_ (Coq_tFix ((app mfix1 (u :: mfix2)),
          idx)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tFix
                  ((app mfix1' (v :: mfix2')), idx)))
                (String.append nl
                  (String.append (String.String (Coq_x68, (String.String
                    (Coq_x61, (String.String (Coq_x76, (String.String
                    (Coq_x65, (String.String (Coq_x20, (String.String
                    (Coq_x61, (String.String (Coq_x20, (String.String
                    (Coq_x6d, (String.String (Coq_x69, (String.String
                    (Coq_x73, (String.String (Coq_x6d, (String.String
                    (Coq_x61, (String.String (Coq_x74, (String.String
                    (Coq_x63, (String.String (Coq_x68, (String.String
                    (Coq_x20, (String.String (Coq_x69, (String.String
                    (Coq_x6e, (String.String (Coq_x20, (String.String
                    (Coq_x74, (String.String (Coq_x68, (String.String
                    (Coq_x65, (String.String (Coq_x20, (String.String
                    (Coq_x66, (String.String (Coq_x75, (String.String
                    (Coq_x6e, (String.String (Coq_x63, (String.String
                    (Coq_x74, (String.String (Coq_x69, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x20, (String.String (Coq_x6e, (String.String
                    (Coq_x75, (String.String (Coq_x6d, (String.String
                    (Coq_x62, (String.String (Coq_x65, (String.String
                    (Coq_x72, (String.String (Coq_x20,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    (String.append (string_of_nat (length mfix1))
                      (String.append (String.String (Coq_x3a, (String.String
                        (Coq_x20, (String.String (Coq_x61, (String.String
                        (Coq_x72, (String.String (Coq_x67, (String.String
                        (Coq_x75, (String.String (Coq_x6d, (String.String
                        (Coq_x65, (String.String (Coq_x6e, (String.String
                        (Coq_x74, (String.String (Coq_x73, (String.String
                        (Coq_x20, String.EmptyString))))))))))))))))))))))))
                        (String.append (string_of_nat u.rarg)
                          (String.append (String.String (Coq_x20,
                            (String.String (Coq_x61, (String.String (Coq_x6e,
                            (String.String (Coq_x64, (String.String (Coq_x20,
                            String.EmptyString))))))))))
                            (String.append (string_of_nat v.rarg)
                              (String.String (Coq_x61, (String.String
                              (Coq_x72, (String.String (Coq_x65,
                              (String.String (Coq_x20, (String.String
                              (Coq_x64, (String.String (Coq_x69,
                              (String.String (Coq_x66, (String.String
                              (Coq_x66, (String.String (Coq_x65,
                              (String.String (Coq_x72, (String.String
                              (Coq_x65, (String.String (Coq_x6e,
                              (String.String (Coq_x74, (String.String
                              (Coq_x2e,
                              String.EmptyString)))))))))))))))))))))))))))))))))))))))))
| FixMfixMismatch (idx, _UU0393_, mfix, _UU0393_', mfix') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x66, (String.String
    (Coq_x69, (String.String (Coq_x78, (String.String (Coq_x65,
    (String.String (Coq_x64, (String.String (Coq_x2d, (String.String
    (Coq_x70, (String.String (Coq_x6f, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
    (Coq_x73, String.EmptyString))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_ (Coq_tFix (mfix, idx)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tFix (mfix', idx)))
                (String.append nl (String.String (Coq_x68, (String.String
                  (Coq_x61, (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x20, (String.String (Coq_x64,
                  (String.String (Coq_x69, (String.String (Coq_x66,
                  (String.String (Coq_x66, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x65,
                  (String.String (Coq_x6e, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x6e,
                  (String.String (Coq_x75, (String.String (Coq_x6d,
                  (String.String (Coq_x62, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x20,
                  (String.String (Coq_x6f, (String.String (Coq_x66,
                  (String.String (Coq_x20, (String.String (Coq_x6d,
                  (String.String (Coq_x75, (String.String (Coq_x74,
                  (String.String (Coq_x75, (String.String (Coq_x61,
                  (String.String (Coq_x6c, (String.String (Coq_x6c,
                  (String.String (Coq_x79, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x65,
                  (String.String (Coq_x66, (String.String (Coq_x69,
                  (String.String (Coq_x6e, (String.String (Coq_x65,
                  (String.String (Coq_x64, (String.String (Coq_x20,
                  (String.String (Coq_x66, (String.String (Coq_x75,
                  (String.String (Coq_x6e, (String.String (Coq_x63,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x6f, (String.String (Coq_x6e,
                  (String.String (Coq_x73, (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| DistinctCoFix (_UU0393_, mfix, idx, _UU0393_', mfix', idx') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x63, (String.String
    (Coq_x6f, (String.String (Coq_x66, (String.String (Coq_x69,
    (String.String (Coq_x78, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x2d, (String.String (Coq_x70,
    (String.String (Coq_x6f, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x74, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_ (Coq_tCoFix (mfix, idx)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tCoFix (mfix', idx')))
                (String.append nl (String.String (Coq_x63, (String.String
                  (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x72,
                  (String.String (Coq_x65, (String.String (Coq_x73,
                  (String.String (Coq_x70, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x64,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x6f, (String.String (Coq_x20,
                  (String.String (Coq_x73, (String.String (Coq_x79,
                  (String.String (Coq_x6e, (String.String (Coq_x74,
                  (String.String (Coq_x61, (String.String (Coq_x63,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x63, (String.String (Coq_x61,
                  (String.String (Coq_x6c, (String.String (Coq_x6c,
                  (String.String (Coq_x79, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x69,
                  (String.String (Coq_x73, (String.String (Coq_x74,
                  (String.String (Coq_x69, (String.String (Coq_x6e,
                  (String.String (Coq_x63, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x6d, (String.String (Coq_x73,
                  (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| CoFixRargMismatch (idx, _UU0393_, u, mfix1, mfix2, _UU0393_', v, mfix1',
                     mfix2') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x63, (String.String
    (Coq_x6f, (String.String (Coq_x2d, (String.String (Coq_x66,
    (String.String (Coq_x69, (String.String (Coq_x78, (String.String
    (Coq_x65, (String.String (Coq_x64, (String.String (Coq_x2d,
    (String.String (Coq_x70, (String.String (Coq_x6f, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
    (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append
        (print_term _UU03a3_ _UU0393_ (Coq_tCoFix ((app mfix1 (u :: mfix2)),
          idx)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tCoFix
                  ((app mfix1' (v :: mfix2')), idx)))
                (String.append nl
                  (String.append (String.String (Coq_x68, (String.String
                    (Coq_x61, (String.String (Coq_x76, (String.String
                    (Coq_x65, (String.String (Coq_x20, (String.String
                    (Coq_x61, (String.String (Coq_x20, (String.String
                    (Coq_x6d, (String.String (Coq_x69, (String.String
                    (Coq_x73, (String.String (Coq_x6d, (String.String
                    (Coq_x61, (String.String (Coq_x74, (String.String
                    (Coq_x63, (String.String (Coq_x68, (String.String
                    (Coq_x20, (String.String (Coq_x69, (String.String
                    (Coq_x6e, (String.String (Coq_x20, (String.String
                    (Coq_x74, (String.String (Coq_x68, (String.String
                    (Coq_x65, (String.String (Coq_x20, (String.String
                    (Coq_x66, (String.String (Coq_x75, (String.String
                    (Coq_x6e, (String.String (Coq_x63, (String.String
                    (Coq_x74, (String.String (Coq_x69, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x20, (String.String (Coq_x6e, (String.String
                    (Coq_x75, (String.String (Coq_x6d, (String.String
                    (Coq_x62, (String.String (Coq_x65, (String.String
                    (Coq_x72, (String.String (Coq_x20,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    (String.append (string_of_nat (length mfix1))
                      (String.append (String.String (Coq_x3a, (String.String
                        (Coq_x20, (String.String (Coq_x61, (String.String
                        (Coq_x72, (String.String (Coq_x67, (String.String
                        (Coq_x75, (String.String (Coq_x6d, (String.String
                        (Coq_x65, (String.String (Coq_x6e, (String.String
                        (Coq_x74, (String.String (Coq_x73, (String.String
                        (Coq_x20, String.EmptyString))))))))))))))))))))))))
                        (String.append (string_of_nat u.rarg)
                          (String.append (String.String (Coq_x20,
                            (String.String (Coq_x61, (String.String (Coq_x6e,
                            (String.String (Coq_x64, (String.String (Coq_x20,
                            String.EmptyString))))))))))
                            (String.append (string_of_nat v.rarg)
                              (String.String (Coq_x61, (String.String
                              (Coq_x72, (String.String (Coq_x65,
                              (String.String (Coq_x20, (String.String
                              (Coq_x64, (String.String (Coq_x69,
                              (String.String (Coq_x66, (String.String
                              (Coq_x66, (String.String (Coq_x65,
                              (String.String (Coq_x72, (String.String
                              (Coq_x65, (String.String (Coq_x6e,
                              (String.String (Coq_x74, (String.String
                              (Coq_x2e,
                              String.EmptyString)))))))))))))))))))))))))))))))))))))))))
| CoFixMfixMismatch (idx, _UU0393_, mfix, _UU0393_', mfix') ->
  String.append (String.String (Coq_x54, (String.String (Coq_x68,
    (String.String (Coq_x65, (String.String (Coq_x20, (String.String
    (Coq_x74, (String.String (Coq_x77, (String.String (Coq_x6f,
    (String.String (Coq_x20, (String.String (Coq_x63, (String.String
    (Coq_x6f, (String.String (Coq_x2d, (String.String (Coq_x66,
    (String.String (Coq_x69, (String.String (Coq_x78, (String.String
    (Coq_x65, (String.String (Coq_x64, (String.String (Coq_x2d,
    (String.String (Coq_x70, (String.String (Coq_x6f, (String.String
    (Coq_x69, (String.String (Coq_x6e, (String.String (Coq_x74,
    (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_ (Coq_tCoFix (mfix, idx)))
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append
                (print_term _UU03a3_ _UU0393_' (Coq_tCoFix (mfix', idx)))
                (String.append nl (String.String (Coq_x68, (String.String
                  (Coq_x61, (String.String (Coq_x76, (String.String (Coq_x65,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x20, (String.String (Coq_x64,
                  (String.String (Coq_x69, (String.String (Coq_x66,
                  (String.String (Coq_x66, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x65,
                  (String.String (Coq_x6e, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x6e,
                  (String.String (Coq_x75, (String.String (Coq_x6d,
                  (String.String (Coq_x62, (String.String (Coq_x65,
                  (String.String (Coq_x72, (String.String (Coq_x20,
                  (String.String (Coq_x6f, (String.String (Coq_x66,
                  (String.String (Coq_x20, (String.String (Coq_x6d,
                  (String.String (Coq_x75, (String.String (Coq_x74,
                  (String.String (Coq_x75, (String.String (Coq_x61,
                  (String.String (Coq_x6c, (String.String (Coq_x6c,
                  (String.String (Coq_x79, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x65,
                  (String.String (Coq_x66, (String.String (Coq_x69,
                  (String.String (Coq_x6e, (String.String (Coq_x65,
                  (String.String (Coq_x64, (String.String (Coq_x20,
                  (String.String (Coq_x66, (String.String (Coq_x75,
                  (String.String (Coq_x6e, (String.String (Coq_x63,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x6f, (String.String (Coq_x6e,
                  (String.String (Coq_x73, (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| StackHeadError (_, _, _, _, _, _, _, _, _, _, e0) ->
  String.append (String.String (Coq_x54, (String.String (Coq_x4f,
    (String.String (Coq_x44, (String.String (Coq_x4f, (String.String
    (Coq_x20, (String.String (Coq_x73, (String.String (Coq_x74,
    (String.String (Coq_x61, (String.String (Coq_x63, (String.String
    (Coq_x6b, (String.String (Coq_x68, (String.String (Coq_x65,
    (String.String (Coq_x61, (String.String (Coq_x64, (String.String
    (Coq_x65, (String.String (Coq_x72, (String.String (Coq_x72,
    (String.String (Coq_x6f, (String.String (Coq_x72,
    String.EmptyString))))))))))))))))))))))))))))))))))))))
    (String.append nl (string_of_conv_error _UU03a3_ e0))
| StackTailError (_, _, _, _, _, _, _, _, _, _, e0) ->
  String.append (String.String (Coq_x54, (String.String (Coq_x4f,
    (String.String (Coq_x44, (String.String (Coq_x4f, (String.String
    (Coq_x20, (String.String (Coq_x73, (String.String (Coq_x74,
    (String.String (Coq_x61, (String.String (Coq_x63, (String.String
    (Coq_x6b, (String.String (Coq_x74, (String.String (Coq_x61,
    (String.String (Coq_x69, (String.String (Coq_x6c, (String.String
    (Coq_x65, (String.String (Coq_x72, (String.String (Coq_x72,
    (String.String (Coq_x6f, (String.String (Coq_x72,
    String.EmptyString))))))))))))))))))))))))))))))))))))))
    (String.append nl (string_of_conv_error _UU03a3_ e0))
| StackMismatch (_UU0393_1, t1, _, _, _UU0393_2, t2, _) ->
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x76, (String.String
    (Coq_x65, (String.String (Coq_x72, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x62, (String.String
    (Coq_x6c, (String.String (Coq_x65, (String.String (Coq_x20,
    (String.String (Coq_x74, (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x6d, (String.String (Coq_x73,
    String.EmptyString))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_1 t1)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append (print_term _UU03a3_ _UU0393_2 t2)
                (String.append (String.String (Coq_x61, (String.String
                  (Coq_x72, (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x63, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x76,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x62, (String.String (Coq_x6c,
                  (String.String (Coq_x65, (String.String (Coq_x2f,
                  (String.String (Coq_x63, (String.String (Coq_x6f,
                  (String.String (Coq_x6e, (String.String (Coq_x76,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x74, (String.String (Coq_x69,
                  (String.String (Coq_x62, (String.String (Coq_x6c,
                  (String.String (Coq_x65, (String.String (Coq_x20,
                  (String.String (Coq_x28, (String.String (Coq_x54,
                  (String.String (Coq_x4f, (String.String (Coq_x44,
                  (String.String (Coq_x4f, (String.String (Coq_x29,
                  (String.String (Coq_x20, (String.String (Coq_x62,
                  (String.String (Coq_x75, (String.String (Coq_x74,
                  (String.String (Coq_x20, (String.String (Coq_x61,
                  (String.String (Coq_x70, (String.String (Coq_x70,
                  (String.String (Coq_x6c, (String.String (Coq_x69,
                  (String.String (Coq_x65, (String.String (Coq_x64,
                  (String.String (Coq_x20, (String.String (Coq_x74,
                  (String.String (Coq_x6f, (String.String (Coq_x20,
                  (String.String (Coq_x61, (String.String (Coq_x20,
                  (String.String (Coq_x64, (String.String (Coq_x69,
                  (String.String (Coq_x66, (String.String (Coq_x66,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  (String.String (Coq_x65, (String.String (Coq_x6e,
                  (String.String (Coq_x74, (String.String (Coq_x20,
                  (String.String (Coq_x6e, (String.String (Coq_x75,
                  (String.String (Coq_x6d, (String.String (Coq_x62,
                  (String.String (Coq_x65, (String.String (Coq_x72,
                  String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                  (String.String (Coq_x20, (String.String (Coq_x6f,
                  (String.String (Coq_x66, (String.String (Coq_x20,
                  (String.String (Coq_x61, (String.String (Coq_x72,
                  (String.String (Coq_x67, (String.String (Coq_x75,
                  (String.String (Coq_x6d, (String.String (Coq_x65,
                  (String.String (Coq_x6e, (String.String (Coq_x74,
                  (String.String (Coq_x73, (String.String (Coq_x2e,
                  String.EmptyString)))))))))))))))))))))))))))))))))))
| HeadMismatch (leq, _UU0393_1, t1, _UU0393_2, t2) ->
  String.append (String.String (Coq_x54, (String.String (Coq_x65,
    (String.String (Coq_x72, (String.String (Coq_x6d, (String.String
    (Coq_x73, String.EmptyString))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_1 t1)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, String.EmptyString))))))
            (String.append nl
              (String.append (print_term _UU03a3_ _UU0393_2 t2)
                (String.append nl
                  (String.append (String.String (Coq_x64, (String.String
                    (Coq_x6f, (String.String (Coq_x20, (String.String
                    (Coq_x6e, (String.String (Coq_x6f, (String.String
                    (Coq_x74, (String.String (Coq_x20, (String.String
                    (Coq_x68, (String.String (Coq_x61, (String.String
                    (Coq_x76, (String.String (Coq_x65, (String.String
                    (Coq_x20, (String.String (Coq_x74, (String.String
                    (Coq_x68, (String.String (Coq_x65, (String.String
                    (Coq_x20, (String.String (Coq_x73, (String.String
                    (Coq_x61, (String.String (Coq_x6d, (String.String
                    (Coq_x65, (String.String (Coq_x20, (String.String
                    (Coq_x68, (String.String (Coq_x65, (String.String
                    (Coq_x61, (String.String (Coq_x64, (String.String
                    (Coq_x20, (String.String (Coq_x77, (String.String
                    (Coq_x68, (String.String (Coq_x65, (String.String
                    (Coq_x6e, (String.String (Coq_x20, (String.String
                    (Coq_x63, (String.String (Coq_x6f, (String.String
                    (Coq_x6d, (String.String (Coq_x70, (String.String
                    (Coq_x61, (String.String (Coq_x72, (String.String
                    (Coq_x69, (String.String (Coq_x6e, (String.String
                    (Coq_x67, (String.String (Coq_x20, (String.String
                    (Coq_x66, (String.String (Coq_x6f, (String.String
                    (Coq_x72, (String.String (Coq_x20,
                    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    (string_of_conv_pb leq)))))))))

(** val string_of_type_error :
    PCUICEnvironment.global_env_ext -> type_error -> String.t **)

let string_of_type_error _UU03a3_ = function
| UnboundRel n ->
  String.append (String.String (Coq_x55, (String.String (Coq_x6e,
    (String.String (Coq_x62, (String.String (Coq_x6f, (String.String
    (Coq_x75, (String.String (Coq_x6e, (String.String (Coq_x64,
    (String.String (Coq_x20, (String.String (Coq_x72, (String.String
    (Coq_x65, (String.String (Coq_x6c, (String.String (Coq_x20,
    String.EmptyString)))))))))))))))))))))))) (string_of_nat n)
| UnboundVar id ->
  String.append (String.String (Coq_x55, (String.String (Coq_x6e,
    (String.String (Coq_x62, (String.String (Coq_x6f, (String.String
    (Coq_x75, (String.String (Coq_x6e, (String.String (Coq_x64,
    (String.String (Coq_x20, (String.String (Coq_x76, (String.String
    (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x20,
    String.EmptyString)))))))))))))))))))))))) id
| UnboundEvar ev ->
  String.append (String.String (Coq_x55, (String.String (Coq_x6e,
    (String.String (Coq_x62, (String.String (Coq_x6f, (String.String
    (Coq_x75, (String.String (Coq_x6e, (String.String (Coq_x64,
    (String.String (Coq_x20, (String.String (Coq_x65, (String.String
    (Coq_x76, (String.String (Coq_x61, (String.String (Coq_x72,
    (String.String (Coq_x20, String.EmptyString))))))))))))))))))))))))))
    (string_of_nat ev)
| UndeclaredConstant c ->
  String.append (String.String (Coq_x55, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x65, (String.String
    (Coq_x63, (String.String (Coq_x6c, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x63,
    (String.String (Coq_x6f, (String.String (Coq_x6e, (String.String
    (Coq_x73, (String.String (Coq_x74, (String.String (Coq_x61,
    (String.String (Coq_x6e, (String.String (Coq_x74, (String.String
    (Coq_x20, String.EmptyString))))))))))))))))))))))))))))))))))))))))
    (string_of_kername c)
| UndeclaredInductive c ->
  String.append (String.String (Coq_x55, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x65, (String.String
    (Coq_x63, (String.String (Coq_x6c, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x64, (String.String
    (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x76, (String.String
    (Coq_x65, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))
    (string_of_kername c.inductive_mind)
| UndeclaredConstructor (c, _) ->
  String.append (String.String (Coq_x55, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x65, (String.String
    (Coq_x63, (String.String (Coq_x6c, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x69,
    (String.String (Coq_x6e, (String.String (Coq_x64, (String.String
    (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x76, (String.String
    (Coq_x65, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))
    (string_of_kername c.inductive_mind)
| NotCumulSmaller (le, _, _UU0393_, t0, u, t', u', e0) ->
  String.append (String.String (Coq_x54, (String.String (Coq_x79,
    (String.String (Coq_x70, (String.String (Coq_x65, (String.String
    (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x20, (String.String (Coq_x6e, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))
    (String.append
      (if le
       then String.append (String.String (Coq_x3c, (String.String (Coq_x3d,
              (String.String (Coq_x20, (String.String (Coq_x66,
              (String.String (Coq_x6f, (String.String (Coq_x72,
              (String.String (Coq_x20, (String.String (Coq_x63,
              (String.String (Coq_x75, (String.String (Coq_x6d,
              (String.String (Coq_x75, (String.String (Coq_x6c,
              (String.String (Coq_x61, (String.String (Coq_x74,
              (String.String (Coq_x69, (String.String (Coq_x76,
              (String.String (Coq_x69, (String.String (Coq_x74,
              (String.String (Coq_x79, (String.String (Coq_x3a,
              String.EmptyString)))))))))))))))))))))))))))))))))))))))) nl
       else String.append (String.String (Coq_x63, (String.String (Coq_x6f,
              (String.String (Coq_x6e, (String.String (Coq_x76,
              (String.String (Coq_x65, (String.String (Coq_x72,
              (String.String (Coq_x74, (String.String (Coq_x69,
              (String.String (Coq_x62, (String.String (Coq_x6c,
              (String.String (Coq_x65, (String.String (Coq_x3a,
              String.EmptyString)))))))))))))))))))))))) nl)
      (String.append (print_term _UU03a3_ _UU0393_ t0)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, (String.String (Coq_x3a,
            String.EmptyString))))))))
            (String.append nl
              (String.append (print_term _UU03a3_ _UU0393_ u)
                (String.append nl
                  (String.append (String.String (Coq_x61, (String.String
                    (Coq_x66, (String.String (Coq_x74, (String.String
                    (Coq_x65, (String.String (Coq_x72, (String.String
                    (Coq_x20, (String.String (Coq_x72, (String.String
                    (Coq_x65, (String.String (Coq_x64, (String.String
                    (Coq_x75, (String.String (Coq_x63, (String.String
                    (Coq_x74, (String.String (Coq_x69, (String.String
                    (Coq_x6f, (String.String (Coq_x6e, (String.String
                    (Coq_x3a,
                    String.EmptyString))))))))))))))))))))))))))))))))
                    (String.append nl
                      (String.append (print_term _UU03a3_ _UU0393_ t')
                        (String.append nl
                          (String.append (String.String (Coq_x61,
                            (String.String (Coq_x6e, (String.String (Coq_x64,
                            (String.String (Coq_x3a,
                            String.EmptyString))))))))
                            (String.append nl
                              (String.append
                                (print_term _UU03a3_ _UU0393_ u')
                                (String.append nl
                                  (String.append (String.String (Coq_x65,
                                    (String.String (Coq_x72, (String.String
                                    (Coq_x72, (String.String (Coq_x6f,
                                    (String.String (Coq_x72, (String.String
                                    (Coq_x3a, String.EmptyString))))))))))))
                                    (String.append nl
                                      (String.append
                                        (string_of_conv_error _UU03a3_ e0)
                                        (String.append (String.String
                                          (Coq_x20, (String.String (Coq_x61,
                                          (String.String (Coq_x6e,
                                          (String.String (Coq_x64,
                                          (String.String (Coq_x20,
                                          (String.String (Coq_x63,
                                          (String.String (Coq_x6f,
                                          (String.String (Coq_x6e,
                                          (String.String (Coq_x74,
                                          (String.String (Coq_x65,
                                          (String.String (Coq_x78,
                                          (String.String (Coq_x74,
                                          (String.String (Coq_x3a,
                                          (String.String (Coq_x20,
                                          String.EmptyString))))))))))))))))))))))))))))
                                          (String.append nl
                                            (print_context _UU03a3_ []
                                              _UU0393_)))))))))))))))))))))
| NotConvertible (_, _UU0393_, t0, u) ->
  String.append (String.String (Coq_x54, (String.String (Coq_x65,
    (String.String (Coq_x72, (String.String (Coq_x6d, (String.String
    (Coq_x73, (String.String (Coq_x20, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x20, (String.String (Coq_x6e, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x20, (String.String
    (Coq_x63, (String.String (Coq_x6f, (String.String (Coq_x6e,
    (String.String (Coq_x76, (String.String (Coq_x65, (String.String
    (Coq_x72, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x62, (String.String (Coq_x6c, (String.String
    (Coq_x65, (String.String (Coq_x3a,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))
    (String.append nl
      (String.append (print_term _UU03a3_ _UU0393_ t0)
        (String.append nl
          (String.append (String.String (Coq_x61, (String.String (Coq_x6e,
            (String.String (Coq_x64, (String.String (Coq_x3a,
            String.EmptyString))))))))
            (String.append nl
              (String.append (print_term _UU03a3_ _UU0393_ u)
                (String.append (String.String (Coq_x20, (String.String
                  (Coq_x61, (String.String (Coq_x6e, (String.String (Coq_x64,
                  (String.String (Coq_x20, (String.String (Coq_x63,
                  (String.String (Coq_x6f, (String.String (Coq_x6e,
                  (String.String (Coq_x74, (String.String (Coq_x65,
                  (String.String (Coq_x78, (String.String (Coq_x74,
                  (String.String (Coq_x3a, (String.String (Coq_x20,
                  String.EmptyString))))))))))))))))))))))))))))
                  (String.append nl (print_context _UU03a3_ [] _UU0393_)))))))))
| NotASort t0 ->
  String.append (String.String (Coq_x4e, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x20, (String.String
    (Coq_x61, (String.String (Coq_x20, (String.String (Coq_x73,
    (String.String (Coq_x6f, (String.String (Coq_x72, (String.String
    (Coq_x74, (String.String (Coq_x3a, (String.String (Coq_x20,
    String.EmptyString)))))))))))))))))))))))) (print_term _UU03a3_ [] t0)
| NotAProduct (t0, t') ->
  String.append (String.String (Coq_x4e, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x20, (String.String
    (Coq_x61, (String.String (Coq_x20, (String.String (Coq_x70,
    (String.String (Coq_x72, (String.String (Coq_x6f, (String.String
    (Coq_x64, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x74, String.EmptyString))))))))))))))))))))))))))
    (String.append (print_term _UU03a3_ [] t0)
      (String.append nl
        (String.append (String.String (Coq_x28, (String.String (Coq_x61,
          (String.String (Coq_x66, (String.String (Coq_x74, (String.String
          (Coq_x65, (String.String (Coq_x72, (String.String (Coq_x20,
          (String.String (Coq_x72, (String.String (Coq_x65, (String.String
          (Coq_x64, (String.String (Coq_x75, (String.String (Coq_x63,
          (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
          (Coq_x67, (String.String (Coq_x20, (String.String (Coq_x74,
          (String.String (Coq_x6f, (String.String (Coq_x20,
          String.EmptyString))))))))))))))))))))))))))))))))))))))
          (print_term _UU03a3_ [] t'))))
| NotAnInductive t0 ->
  String.append (String.String (Coq_x4e, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x20, (String.String
    (Coq_x61, (String.String (Coq_x6e, (String.String (Coq_x20,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x64, (String.String (Coq_x75, (String.String (Coq_x63,
    (String.String (Coq_x74, (String.String (Coq_x69, (String.String
    (Coq_x76, (String.String (Coq_x65, (String.String (Coq_x3a,
    (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))))))))))
    (print_term _UU03a3_ [] t0)
| NotAnArity t0 ->
  String.append (print_term _UU03a3_ [] t0) (String.String (Coq_x20,
    (String.String (Coq_x69, (String.String (Coq_x73, (String.String
    (Coq_x20, (String.String (Coq_x6e, (String.String (Coq_x6f,
    (String.String (Coq_x74, (String.String (Coq_x20, (String.String
    (Coq_x61, (String.String (Coq_x6e, (String.String (Coq_x20,
    (String.String (Coq_x61, (String.String (Coq_x72, (String.String
    (Coq_x69, (String.String (Coq_x74, (String.String (Coq_x79,
    String.EmptyString))))))))))))))))))))))))))))))))
| IllFormedFix (_, _) ->
  String.String (Coq_x49, (String.String (Coq_x6c, (String.String (Coq_x6c,
    (String.String (Coq_x2d, (String.String (Coq_x66, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x6d,
    (String.String (Coq_x65, (String.String (Coq_x64, (String.String
    (Coq_x20, (String.String (Coq_x72, (String.String (Coq_x65,
    (String.String (Coq_x63, (String.String (Coq_x75, (String.String
    (Coq_x72, (String.String (Coq_x73, (String.String (Coq_x69,
    (String.String (Coq_x76, (String.String (Coq_x65, (String.String
    (Coq_x20, (String.String (Coq_x64, (String.String (Coq_x65,
    (String.String (Coq_x66, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x69, (String.String (Coq_x74,
    (String.String (Coq_x69, (String.String (Coq_x6f, (String.String
    (Coq_x6e,
    String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| UnsatisfiedConstraints _ ->
  String.String (Coq_x55, (String.String (Coq_x6e, (String.String (Coq_x73,
    (String.String (Coq_x61, (String.String (Coq_x74, (String.String
    (Coq_x69, (String.String (Coq_x73, (String.String (Coq_x66,
    (String.String (Coq_x69, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20, (String.String (Coq_x63,
    (String.String (Coq_x6f, (String.String (Coq_x6e, (String.String
    (Coq_x73, (String.String (Coq_x74, (String.String (Coq_x72,
    (String.String (Coq_x61, (String.String (Coq_x69, (String.String
    (Coq_x6e, (String.String (Coq_x74, (String.String (Coq_x73,
    String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))
| Msg s ->
  String.append (String.String (Coq_x4d, (String.String (Coq_x73,
    (String.String (Coq_x67, (String.String (Coq_x3a, (String.String
    (Coq_x20, String.EmptyString)))))))))) s

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

type 'a typing_result_comp =
| Checked_comp of 'a
| TypeError_comp of type_error

(** val monad_exc : (type_error, __ typing_result) coq_MonadExc **)

let monad_exc =
  { raise = (fun _ e -> TypeError e); catch = (fun _ m f ->
    match m with
    | Checked _ -> m
    | TypeError t0 -> f t0) }

type env_error =
| IllFormedDecl of String.t * type_error
| AlreadyDeclared of String.t
