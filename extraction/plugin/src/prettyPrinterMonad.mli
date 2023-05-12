open Ascii
open Common1
open Datatypes
open Kernames
open List0
open MCList
open Nat0
open ResultMonad
open String0
open Monad_utils

type __ = Obj.t

type coq_PrettyPrinterState = { indent_stack : nat list;
                                used_names : ident list;
                                output_lines : (nat * string) list;
                                cur_output_line : (nat * string) }

type 'a coq_PrettyPrinter =
  coq_PrettyPrinterState -> ('a * coq_PrettyPrinterState, string) result

val coq_Monad_PrettyPrinter : __ coq_PrettyPrinter coq_Monad

val map_pps :
  (nat list -> nat list) -> (ident list -> ident list) -> ((nat * string)
  list -> (nat * string) list) -> ((nat * string) -> nat * string) -> unit
  coq_PrettyPrinter

val prefix_spaces : nat -> string -> string

val collect_output_lines : coq_PrettyPrinterState -> string list

type 'a result_string_err = ('a, string) result

val finish_print_lines :
  'a1 coq_PrettyPrinter -> ('a1 * string list) result_string_err

val collect_output : coq_PrettyPrinterState -> string

val printer_fail : string -> 'a1 coq_PrettyPrinter

val map_indent_stack : (nat list -> nat list) -> unit coq_PrettyPrinter

val push_indent : nat -> unit coq_PrettyPrinter

val pop_indent : unit coq_PrettyPrinter

val get_used_names : ident list coq_PrettyPrinter

val map_used_names : (ident list -> ident list) -> unit coq_PrettyPrinter

val push_use : ident -> unit coq_PrettyPrinter

val get_current_line_length : nat coq_PrettyPrinter

val map_cur_output_line :
  ((nat * string) -> nat * string) -> unit coq_PrettyPrinter

val append : string -> unit coq_PrettyPrinter

val append_nl : unit coq_PrettyPrinter

val monad_append_join :
  unit coq_PrettyPrinter -> unit coq_PrettyPrinter list -> unit
  coq_PrettyPrinter

val append_join : string -> string list -> unit coq_PrettyPrinter

val monad_append_concat :
  unit coq_PrettyPrinter list -> unit coq_PrettyPrinter

val append_concat : string list -> unit coq_PrettyPrinter

val wrap_option : 'a1 option -> string -> 'a1 coq_PrettyPrinter

val wrap_result :
  ('a1, 'a2) result -> ('a2 -> string) -> 'a1 coq_PrettyPrinter
