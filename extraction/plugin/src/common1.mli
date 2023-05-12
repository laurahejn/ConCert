open Ascii
open Ast0
open BinInt
open BinNums
open Byte
open Datatypes
open EAst
open Kernames
open Nat0
open PCUICAst
open PCUICErrors
open ReflectEq
open ResultMonad
open String0
open Bytestring

val to_kername : Ast0.term -> kername option

val to_globref : Ast0.term -> global_reference option

val result_of_typing_result :
  PCUICEnvironment.global_env_ext -> 'a1 typing_result -> ('a1, String.t)
  result

val string_of_env_error :
  PCUICEnvironment.global_env_ext -> env_error -> String.t

val result_of_option : 'a1 option -> String.t -> ('a1, String.t) result

val to_string_name : Ast0.term -> String.t

val remap : kername -> string -> kername * string

val nat_syn_to_nat : EAst.term -> nat option

val _xI : EAst.term

val _xO : EAst.term

val _xH : EAst.term

val _N0 : EAst.term

val _Npos : EAst.term

val _Z0 : EAst.term

val _Zpos : EAst.term

val _Zneg : EAst.term

val pos_syn_to_nat_aux : nat -> EAst.term -> nat option

val pos_syn_to_nat : EAst.term -> nat option

val coq_N_syn_to_nat : EAst.term -> nat option

val coq_Z_syn_to_Z : EAst.term -> coq_Z option

val parens : bool -> string -> string

val nl : string

val string_of_list_aux : ('a1 -> string) -> string -> 'a1 list -> string

val string_of_list : ('a1 -> string) -> 'a1 list -> string

val print_list : ('a1 -> string) -> string -> 'a1 list -> string
