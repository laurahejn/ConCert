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

val string_of_conv_pb : conv_pb -> String.t

val print_term :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term ->
  String.t

val print_context_decl :
  PCUICEnvironment.global_env_ext -> PCUICEnvironment.context -> term
  context_decl -> String.t

val string_of_conv_error :
  PCUICEnvironment.global_env_ext -> coq_ConversionError -> String.t

val string_of_type_error :
  PCUICEnvironment.global_env_ext -> type_error -> String.t

type 'a typing_result =
| Checked of 'a
| TypeError of type_error

type 'a typing_result_comp =
| Checked_comp of 'a
| TypeError_comp of type_error

val monad_exc : (type_error, __ typing_result) coq_MonadExc

type env_error =
| IllFormedDecl of String.t * type_error
| AlreadyDeclared of String.t
