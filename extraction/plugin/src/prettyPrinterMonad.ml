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

(** val coq_Monad_PrettyPrinter : __ coq_PrettyPrinter coq_Monad **)

let coq_Monad_PrettyPrinter =
  { ret = (fun _ a pps -> Ok (a, pps)); bind = (fun _ _ m f pps ->
    match m pps with
    | Ok t -> let (a, pps0) = t in f a pps0
    | Err err -> Err err) }

(** val map_pps :
    (nat list -> nat list) -> (ident list -> ident list) -> ((nat * string)
    list -> (nat * string) list) -> ((nat * string) -> nat * string) -> unit
    coq_PrettyPrinter **)

let map_pps f g h i pps =
  Ok ((),
    (let { indent_stack = a; used_names = b; output_lines = c;
       cur_output_line = d } = pps
     in
     { indent_stack = (f a); used_names = (g b); output_lines = (h c);
     cur_output_line = (i d) }))

(** val prefix_spaces : nat -> string -> string **)

let rec prefix_spaces n s =
  match n with
  | O -> s
  | S n0 ->
    prefix_spaces n0 (String ((Ascii (false, false, false, false, false,
      true, false, false)), s))

(** val collect_output_lines : coq_PrettyPrinterState -> string list **)

let collect_output_lines pps =
  rev_map (fun pat -> let (n, l) = pat in prefix_spaces n l)
    (pps.cur_output_line :: pps.output_lines)

type 'a result_string_err = ('a, string) result

(** val finish_print_lines :
    'a1 coq_PrettyPrinter -> ('a1 * string list) result_string_err **)

let finish_print_lines pp =
  bind (Obj.magic coq_Monad_result)
    (Obj.magic pp { indent_stack = []; used_names = []; output_lines = [];
      cur_output_line = (O, EmptyString) }) (fun x ->
    let (a, pps) = x in
    ret (Obj.magic coq_Monad_result) (a, (collect_output_lines pps)))

(** val collect_output : coq_PrettyPrinterState -> string **)

let collect_output pps =
  concat nl (collect_output_lines pps)

(** val printer_fail : string -> 'a1 coq_PrettyPrinter **)

let printer_fail str pps =
  Err
    (append str
      (append nl
        (append (String ((Ascii (false, true, true, false, false, true, true,
          false)), (String ((Ascii (true, false, false, false, false, true,
          true, false)), (String ((Ascii (true, false, false, true, false,
          true, true, false)), (String ((Ascii (false, false, true, true,
          false, true, true, false)), (String ((Ascii (true, false, true,
          false, false, true, true, false)), (String ((Ascii (false, false,
          true, false, false, true, true, false)), (String ((Ascii (false,
          false, false, false, false, true, false, false)), (String ((Ascii
          (true, false, false, false, false, true, true, false)), (String
          ((Ascii (false, true, true, false, false, true, true, false)),
          (String ((Ascii (false, false, true, false, true, true, true,
          false)), (String ((Ascii (true, false, true, false, false, true,
          true, false)), (String ((Ascii (false, true, false, false, true,
          true, true, false)), (String ((Ascii (false, false, false, false,
          false, true, false, false)), (String ((Ascii (false, false, false,
          false, true, true, true, false)), (String ((Ascii (false, true,
          false, false, true, true, true, false)), (String ((Ascii (true,
          false, false, true, false, true, true, false)), (String ((Ascii
          (false, true, true, true, false, true, true, false)), (String
          ((Ascii (false, false, true, false, true, true, true, false)),
          (String ((Ascii (true, false, false, true, false, true, true,
          false)), (String ((Ascii (false, true, true, true, false, true,
          true, false)), (String ((Ascii (true, true, true, false, false,
          true, true, false)),
          EmptyString))))))))))))))))))))))))))))))))))))))))))
          (append nl (collect_output pps)))))

(** val map_indent_stack :
    (nat list -> nat list) -> unit coq_PrettyPrinter **)

let map_indent_stack f =
  map_pps f (Obj.magic id) (Obj.magic id) (Obj.magic id)

(** val push_indent : nat -> unit coq_PrettyPrinter **)

let push_indent n =
  map_indent_stack (fun x -> n :: x)

(** val pop_indent : unit coq_PrettyPrinter **)

let pop_indent =
  map_indent_stack tl

(** val get_used_names : ident list coq_PrettyPrinter **)

let get_used_names pps =
  Ok (pps.used_names, pps)

(** val map_used_names :
    (ident list -> ident list) -> unit coq_PrettyPrinter **)

let map_used_names f =
  map_pps (Obj.magic id) f (Obj.magic id) (Obj.magic id)

(** val push_use : ident -> unit coq_PrettyPrinter **)

let push_use n =
  map_used_names (fun x -> n :: x)

(** val get_current_line_length : nat coq_PrettyPrinter **)

let get_current_line_length pps =
  Ok ((add (fst pps.cur_output_line) (length (snd pps.cur_output_line))), pps)

(** val map_cur_output_line :
    ((nat * string) -> nat * string) -> unit coq_PrettyPrinter **)

let map_cur_output_line f =
  map_pps (Obj.magic id) (Obj.magic id) (Obj.magic id) f

(** val append : string -> unit coq_PrettyPrinter **)

let append s =
  map_cur_output_line (fun pat -> let (n, prev) = pat in (n, (append prev s)))

(** val append_nl : unit coq_PrettyPrinter **)

let append_nl pps =
  Ok ((), { indent_stack = pps.indent_stack; used_names = pps.used_names;
    output_lines = (pps.cur_output_line :: pps.output_lines);
    cur_output_line = ((hd O pps.indent_stack), EmptyString) })

(** val monad_append_join :
    unit coq_PrettyPrinter -> unit coq_PrettyPrinter list -> unit
    coq_PrettyPrinter **)

let monad_append_join sep xs =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter) (fun sep' x ->
      bind (Obj.magic coq_Monad_PrettyPrinter) (Obj.magic sep') (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter) x (fun _ ->
          ret (Obj.magic coq_Monad_PrettyPrinter) sep))) xs
      (ret coq_Monad_PrettyPrinter ())) (fun _ ->
    ret (Obj.magic coq_Monad_PrettyPrinter) ())

(** val append_join : string -> string list -> unit coq_PrettyPrinter **)

let append_join sep s =
  monad_append_join (append sep) (map append s)

(** val monad_append_concat :
    unit coq_PrettyPrinter list -> unit coq_PrettyPrinter **)

let monad_append_concat xs =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (monad_map (Obj.magic coq_Monad_PrettyPrinter) (Obj.magic id) xs)
    (fun _ -> ret (Obj.magic coq_Monad_PrettyPrinter) ())

(** val append_concat : string list -> unit coq_PrettyPrinter **)

let append_concat xs =
  monad_append_concat (map append xs)

(** val wrap_option : 'a1 option -> string -> 'a1 coq_PrettyPrinter **)

let wrap_option o err =
  match o with
  | Some a -> ret (Obj.magic coq_Monad_PrettyPrinter) a
  | None -> printer_fail err

(** val wrap_result :
    ('a1, 'a2) result -> ('a2 -> string) -> 'a1 coq_PrettyPrinter **)

let wrap_result r err_string =
  match r with
  | Ok t -> ret (Obj.magic coq_Monad_PrettyPrinter) t
  | Err e -> printer_fail (err_string e)
