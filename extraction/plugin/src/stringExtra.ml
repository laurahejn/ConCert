open Ascii
open BinNat
open BinNums
open BinPos
open Datatypes
open String0

(** val coq_Nlog2up_nat : coq_N -> nat **)

let coq_Nlog2up_nat = function
| N0 -> S O
| Npos p -> Pos.size_nat p

(** val string_of_N : coq_N -> string **)

let string_of_N n =
  let rec f n0 num acc =
    let (q, r) = N.div_eucl num (Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))) in
    let char =
      match r with
      | N0 -> Ascii (false, false, false, false, true, true, false, false)
      | Npos p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xH ->
                 Ascii (true, true, true, false, true, true, false, false)
               | _ ->
                 Ascii (false, false, false, true, true, true, true, false))
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI _ ->
                 Ascii (false, false, false, true, true, true, true, false)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xH ->
                    Ascii (true, false, false, true, true, true, false, false)
                  | _ ->
                    Ascii (false, false, false, true, true, true, true, false))
               | Coq_xH ->
                 Ascii (true, false, true, false, true, true, false, false))
            | Coq_xH ->
              Ascii (true, true, false, false, true, true, false, false))
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xH ->
                 Ascii (false, true, true, false, true, true, false, false)
               | _ ->
                 Ascii (false, false, false, true, true, true, true, false))
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI _ ->
                 Ascii (false, false, false, true, true, true, true, false)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xH ->
                    Ascii (false, false, false, true, true, true, false,
                      false)
                  | _ ->
                    Ascii (false, false, false, true, true, true, true, false))
               | Coq_xH ->
                 Ascii (false, false, true, false, true, true, false, false))
            | Coq_xH ->
              Ascii (false, true, false, false, true, true, false, false))
         | Coq_xH ->
           Ascii (true, false, false, false, true, true, false, false))
    in
    let acc0 = String (char, acc) in
    if N.eqb q N0
    then acc0
    else (match n0 with
          | O -> EmptyString
          | S n1 -> f n1 q acc0)
  in f (coq_Nlog2up_nat n) n EmptyString

(** val string_of_nat : nat -> string **)

let string_of_nat n =
  string_of_N (N.of_nat n)

(** val replace_char : ascii -> ascii -> string -> string **)

let rec replace_char orig new0 = function
| EmptyString -> EmptyString
| String (c, s0) ->
  if Ascii.eqb c orig
  then String (new0, (replace_char orig new0 s0))
  else String (c, (replace_char orig new0 s0))

(** val remove_char : ascii -> string -> string **)

let rec remove_char c = function
| EmptyString -> EmptyString
| String (c', s0) ->
  if Ascii.eqb c' c then remove_char c s0 else String (c', (remove_char c s0))

(** val starts_with_cont :
    ascii -> string -> (string -> 'a1) -> string -> 'a1 option **)

let rec starts_with_cont with_char with_str cont = function
| EmptyString -> None
| String (sc, s0) ->
  if Ascii.eqb sc with_char
  then (match with_str with
        | EmptyString -> Some (cont s0)
        | String (wsc, ws) -> starts_with_cont wsc ws cont s0)
  else None

(** val replace : string -> string -> string -> string **)

let replace orig new0 =
  match orig with
  | EmptyString -> (fun s -> s)
  | String (origc, origs) ->
    let rec replace0 s =
      match starts_with_cont origc origs replace0 s with
      | Some s0 -> append new0 s0
      | None ->
        (match s with
         | EmptyString -> EmptyString
         | String (c, s0) -> String (c, (replace0 s0)))
    in replace0

(** val is_letter : ascii -> bool **)

let is_letter c =
  let n = coq_N_of_ascii c in
  (||)
    ((&&)
      (N.leb (Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH))))))) n)
      (N.leb n (Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
        Coq_xH)))))))))
    ((&&)
      (N.leb (Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
        Coq_xH))))))) n)
      (N.leb n (Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
        Coq_xH)))))))))

(** val char_to_upper : ascii -> ascii **)

let char_to_upper c =
  if is_letter c
  then let Ascii (b0, b1, b2, b3, b4, _, b6, b7) = c in
       Ascii (b0, b1, b2, b3, b4, false, b6, b7)
  else c

(** val capitalize : string -> string **)

let capitalize = function
| EmptyString -> EmptyString
| String (c, s0) -> String ((char_to_upper c), s0)
