open Ascii
open Decimal
open String0

module NilEmpty =
 struct
  (** val string_of_uint : uint -> string **)

  let rec string_of_uint = function
  | Nil -> EmptyString
  | D0 d0 ->
    String ((Ascii (false, false, false, false, true, true, false, false)),
      (string_of_uint d0))
  | D1 d0 ->
    String ((Ascii (true, false, false, false, true, true, false, false)),
      (string_of_uint d0))
  | D2 d0 ->
    String ((Ascii (false, true, false, false, true, true, false, false)),
      (string_of_uint d0))
  | D3 d0 ->
    String ((Ascii (true, true, false, false, true, true, false, false)),
      (string_of_uint d0))
  | D4 d0 ->
    String ((Ascii (false, false, true, false, true, true, false, false)),
      (string_of_uint d0))
  | D5 d0 ->
    String ((Ascii (true, false, true, false, true, true, false, false)),
      (string_of_uint d0))
  | D6 d0 ->
    String ((Ascii (false, true, true, false, true, true, false, false)),
      (string_of_uint d0))
  | D7 d0 ->
    String ((Ascii (true, true, true, false, true, true, false, false)),
      (string_of_uint d0))
  | D8 d0 ->
    String ((Ascii (false, false, false, true, true, true, false, false)),
      (string_of_uint d0))
  | D9 d0 ->
    String ((Ascii (true, false, false, true, true, true, false, false)),
      (string_of_uint d0))
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> string **)

  let string_of_uint d = match d with
  | Nil ->
    String ((Ascii (false, false, false, false, true, true, false, false)),
      EmptyString)
  | _ -> NilEmpty.string_of_uint d

  (** val string_of_int : unit -> string **)

  let string_of_int d =
    (fun _ _ _ -> assert false)
      (fun d0 -> string_of_uint d0)
      (fun d0 -> String ((Ascii (true, false, true, true, false, true, false,
      false)), (string_of_uint d0)))
      d
 end
