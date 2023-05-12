open Ascii
open BinNat
open BinNums
open BinPos
open Datatypes
open String0

val coq_Nlog2up_nat : coq_N -> nat

val string_of_N : coq_N -> string

val string_of_nat : nat -> string

val replace_char : ascii -> ascii -> string -> string

val remove_char : ascii -> string -> string

val starts_with_cont :
  ascii -> string -> (string -> 'a1) -> string -> 'a1 option

val replace : string -> string -> string -> string

val is_letter : ascii -> bool

val char_to_upper : ascii -> ascii

val capitalize : string -> string
