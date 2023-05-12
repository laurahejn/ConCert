open Ascii
open Decimal
open String0

module NilEmpty :
 sig
  val string_of_uint : uint -> string
 end

module NilZero :
 sig
  val string_of_uint : uint -> string

  val string_of_int : unit -> string
 end
