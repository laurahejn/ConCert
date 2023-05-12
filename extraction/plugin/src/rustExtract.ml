open Ascii
open BasicAst
open Basics
open CertifyingInlining
open Classes0
open Datatypes
open EAst
open ExAst
open Extraction0
open Kernames
open List0
open MCList
open MCProd
open MCString
open Nat0
open Optimize
open PCUICPrimitive
open PeanoNat
open PrettyPrinterMonad
open Printing
open ResultMonad
open String0
open StringExtra
open TopLevelFixes
open Universes0
open Bytestring
open Monad_utils

type __ = Obj.t

module E = EAst

module Ex = ExAst

(** val indent_size : nat **)

let indent_size =
  S (S O)

type coq_RustPrintConfig = { term_box_symbol : string;
                             type_box_symbol : string;
                             any_type_symbol : string; print_full_names : 
                             bool }

type ind_attr_map = inductive -> string

(** val lookup_ind_decl :
    Ex.global_env -> inductive -> (Ex.one_inductive_body, string) result **)

let lookup_ind_decl _UU03a3_ ind =
  match Ex.lookup_env _UU03a3_ ind.inductive_mind with
  | Some g ->
    (match g with
     | Ex.InductiveDecl m ->
       let { Ex.ind_finite = _; Ex.ind_npars = _; Ex.ind_bodies = oibs } = m
       in
       (match nth_error oibs ind.inductive_ind with
        | Some body -> Ok body
        | None ->
          Err
            (append (String ((Ascii (true, true, false, false, false, false,
              true, false)), (String ((Ascii (true, true, true, true, false,
              true, true, false)), (String ((Ascii (true, false, true, false,
              true, true, true, false)), (String ((Ascii (false, false, true,
              true, false, true, true, false)), (String ((Ascii (false,
              false, true, false, false, true, true, false)), (String ((Ascii
              (false, false, false, false, false, true, false, false)),
              (String ((Ascii (false, true, true, true, false, true, true,
              false)), (String ((Ascii (true, true, true, true, false, true,
              true, false)), (String ((Ascii (false, false, true, false,
              true, true, true, false)), (String ((Ascii (false, false,
              false, false, false, true, false, false)), (String ((Ascii
              (false, true, true, false, false, true, true, false)), (String
              ((Ascii (true, false, false, true, false, true, true, false)),
              (String ((Ascii (false, true, true, true, false, true, true,
              false)), (String ((Ascii (false, false, true, false, false,
              true, true, false)), (String ((Ascii (false, false, false,
              false, false, true, false, false)), (String ((Ascii (true,
              false, false, true, false, true, true, false)), (String ((Ascii
              (false, true, true, true, false, true, true, false)), (String
              ((Ascii (false, false, true, false, false, true, true, false)),
              (String ((Ascii (true, false, true, false, true, true, true,
              false)), (String ((Ascii (true, true, false, false, false,
              true, true, false)), (String ((Ascii (false, false, true,
              false, true, true, true, false)), (String ((Ascii (true, false,
              false, true, false, true, true, false)), (String ((Ascii
              (false, true, true, false, true, true, true, false)), (String
              ((Ascii (true, false, true, false, false, true, true, false)),
              (String ((Ascii (false, false, false, false, false, true,
              false, false)),
              EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
              (append
                (String.to_string
                  (String.of_string (string_of_nat ind.inductive_ind)))
                (append (String ((Ascii (false, false, false, false, false,
                  true, false, false)), (String ((Ascii (true, false, false,
                  true, false, true, true, false)), (String ((Ascii (false,
                  true, true, true, false, true, true, false)), (String
                  ((Ascii (false, false, false, false, false, true, false,
                  false)), (String ((Ascii (true, false, true, true, false,
                  true, true, false)), (String ((Ascii (true, false, true,
                  false, true, true, true, false)), (String ((Ascii (false,
                  false, true, false, true, true, true, false)), (String
                  ((Ascii (true, false, true, false, true, true, true,
                  false)), (String ((Ascii (true, false, false, false, false,
                  true, true, false)), (String ((Ascii (false, false, true,
                  true, false, true, true, false)), (String ((Ascii (false,
                  false, false, false, false, true, false, false)), (String
                  ((Ascii (true, false, false, true, false, true, true,
                  false)), (String ((Ascii (false, true, true, true, false,
                  true, true, false)), (String ((Ascii (false, false, true,
                  false, false, true, true, false)), (String ((Ascii (true,
                  false, true, false, true, true, true, false)), (String
                  ((Ascii (true, true, false, false, false, true, true,
                  false)), (String ((Ascii (false, false, true, false, true,
                  true, true, false)), (String ((Ascii (true, false, false,
                  true, false, true, true, false)), (String ((Ascii (false,
                  true, true, false, true, true, true, false)), (String
                  ((Ascii (true, false, true, false, false, true, true,
                  false)), (String ((Ascii (false, false, false, false,
                  false, true, false, false)),
                  EmptyString))))))))))))))))))))))))))))))))))))))))))
                  (String.to_string (string_of_kername ind.inductive_mind))))))
     | _ ->
       Err
         (append (String ((Ascii (true, true, false, false, false, false,
           true, false)), (String ((Ascii (true, true, true, true, false,
           true, true, false)), (String ((Ascii (true, false, true, false,
           true, true, true, false)), (String ((Ascii (false, false, true,
           true, false, true, true, false)), (String ((Ascii (false, false,
           true, false, false, true, true, false)), (String ((Ascii (false,
           false, false, false, false, true, false, false)), (String ((Ascii
           (false, true, true, true, false, true, true, false)), (String
           ((Ascii (true, true, true, true, false, true, true, false)),
           (String ((Ascii (false, false, true, false, true, true, true,
           false)), (String ((Ascii (false, false, false, false, false, true,
           false, false)), (String ((Ascii (false, true, true, false, false,
           true, true, false)), (String ((Ascii (true, false, false, true,
           false, true, true, false)), (String ((Ascii (false, true, true,
           true, false, true, true, false)), (String ((Ascii (false, false,
           true, false, false, true, true, false)), (String ((Ascii (false,
           false, false, false, false, true, false, false)), (String ((Ascii
           (true, false, false, true, false, true, true, false)), (String
           ((Ascii (false, true, true, true, false, true, true, false)),
           (String ((Ascii (false, false, true, false, false, true, true,
           false)), (String ((Ascii (true, false, true, false, true, true,
           true, false)), (String ((Ascii (true, true, false, false, false,
           true, true, false)), (String ((Ascii (false, false, true, false,
           true, true, true, false)), (String ((Ascii (true, false, false,
           true, false, true, true, false)), (String ((Ascii (false, true,
           true, false, true, true, true, false)), (String ((Ascii (true,
           false, true, false, false, true, true, false)), (String ((Ascii
           (false, false, false, false, false, true, false, false)),
           EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
           (append (String.to_string (string_of_kername ind.inductive_mind))
             (String ((Ascii (false, false, false, false, false, true, false,
             false)), (String ((Ascii (true, false, false, true, false, true,
             true, false)), (String ((Ascii (false, true, true, true, false,
             true, true, false)), (String ((Ascii (false, false, false,
             false, false, true, false, false)), (String ((Ascii (true,
             false, true, false, false, true, true, false)), (String ((Ascii
             (false, true, true, true, false, true, true, false)), (String
             ((Ascii (false, true, true, false, true, true, true, false)),
             (String ((Ascii (true, false, false, true, false, true, true,
             false)), (String ((Ascii (false, true, false, false, true, true,
             true, false)), (String ((Ascii (true, true, true, true, false,
             true, true, false)), (String ((Ascii (false, true, true, true,
             false, true, true, false)), (String ((Ascii (true, false, true,
             true, false, true, true, false)), (String ((Ascii (true, false,
             true, false, false, true, true, false)), (String ((Ascii (false,
             true, true, true, false, true, true, false)), (String ((Ascii
             (false, false, true, false, true, true, true, false)),
             EmptyString)))))))))))))))))))))))))))))))))
  | None ->
    Err
      (append (String ((Ascii (true, true, false, false, false, false, true,
        false)), (String ((Ascii (true, true, true, true, false, true, true,
        false)), (String ((Ascii (true, false, true, false, true, true, true,
        false)), (String ((Ascii (false, false, true, true, false, true,
        true, false)), (String ((Ascii (false, false, true, false, false,
        true, true, false)), (String ((Ascii (false, false, false, false,
        false, true, false, false)), (String ((Ascii (false, true, true,
        true, false, true, true, false)), (String ((Ascii (true, true, true,
        true, false, true, true, false)), (String ((Ascii (false, false,
        true, false, true, true, true, false)), (String ((Ascii (false,
        false, false, false, false, true, false, false)), (String ((Ascii
        (false, true, true, false, false, true, true, false)), (String
        ((Ascii (true, false, false, true, false, true, true, false)),
        (String ((Ascii (false, true, true, true, false, true, true, false)),
        (String ((Ascii (false, false, true, false, false, true, true,
        false)), (String ((Ascii (false, false, false, false, false, true,
        false, false)), (String ((Ascii (true, false, false, true, false,
        true, true, false)), (String ((Ascii (false, true, true, true, false,
        true, true, false)), (String ((Ascii (false, false, true, false,
        false, true, true, false)), (String ((Ascii (true, false, true,
        false, true, true, true, false)), (String ((Ascii (true, true, false,
        false, false, true, true, false)), (String ((Ascii (false, false,
        true, false, true, true, true, false)), (String ((Ascii (true, false,
        false, true, false, true, true, false)), (String ((Ascii (false,
        true, true, false, true, true, true, false)), (String ((Ascii (true,
        false, true, false, false, true, true, false)), (String ((Ascii
        (false, false, false, false, false, true, false, false)),
        EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
        (append (String.to_string (string_of_kername ind.inductive_mind))
          (String ((Ascii (false, false, false, false, false, true, false,
          false)), (String ((Ascii (true, false, false, true, false, true,
          true, false)), (String ((Ascii (false, true, true, true, false,
          true, true, false)), (String ((Ascii (false, false, false, false,
          false, true, false, false)), (String ((Ascii (true, false, true,
          false, false, true, true, false)), (String ((Ascii (false, true,
          true, true, false, true, true, false)), (String ((Ascii (false,
          true, true, false, true, true, true, false)), (String ((Ascii
          (true, false, false, true, false, true, true, false)), (String
          ((Ascii (false, true, false, false, true, true, true, false)),
          (String ((Ascii (true, true, true, true, false, true, true,
          false)), (String ((Ascii (false, true, true, true, false, true,
          true, false)), (String ((Ascii (true, false, true, true, false,
          true, true, false)), (String ((Ascii (true, false, true, false,
          false, true, true, false)), (String ((Ascii (false, true, true,
          true, false, true, true, false)), (String ((Ascii (false, false,
          true, false, true, true, true, false)),
          EmptyString))))))))))))))))))))))))))))))))

(** val clean_global_ident : string -> string **)

let clean_global_ident s =
  replace_char (Ascii (false, true, true, true, false, true, false, false))
    (Ascii (true, true, true, true, true, false, true, false))
    (replace_char (Ascii (true, true, true, false, false, true, false,
      false)) (Ascii (true, true, true, true, true, false, true, false)) s)

(** val const_global_ident_of_kername :
    coq_RustPrintConfig -> kername -> string **)

let const_global_ident_of_kername h kn =
  clean_global_ident
    (if h.print_full_names
     then String.to_string (string_of_kername kn)
     else String.to_string (snd kn))

(** val ty_const_global_ident_of_kername :
    coq_RustPrintConfig -> kername -> String.t **)

let ty_const_global_ident_of_kername h kn =
  String.of_string
    (capitalize
      (clean_global_ident
        (String.to_string
          (if h.print_full_names then string_of_kername kn else snd kn))))

(** val get_ty_const_ident :
    remaps -> coq_RustPrintConfig -> kername -> String.t **)

let get_ty_const_ident remaps0 h name0 =
  match remaps0.remap_inline_constant name0 with
  | Some s -> s
  | None -> ty_const_global_ident_of_kername h name0

(** val get_ind_ident :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> inductive -> String.t
    coq_PrettyPrinter **)

let get_ind_ident _UU03a3_ remaps0 h ind =
  match remaps0.remap_inductive ind with
  | Some rem -> ret (Obj.magic coq_Monad_PrettyPrinter) rem.re_ind_name
  | None ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (wrap_result (Obj.magic lookup_ind_decl _UU03a3_ ind) (Obj.magic id))
      (fun oib ->
      let kn = ((fst ind.inductive_mind), (Ex.ind_name oib)) in
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (ty_const_global_ident_of_kername h kn))

(** val clean_local_ident : ident -> string **)

let clean_local_ident name0 =
  remove_char (Ascii (true, true, true, false, false, true, false, false))
    (String.to_string name0)

(** val print_ind :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> inductive -> unit
    coq_PrettyPrinter **)

let print_ind _UU03a3_ remaps0 h ind =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_ind_ident _UU03a3_ remaps0 h ind) (fun x ->
    PrettyPrinterMonad.append (String.to_string x))

(** val print_parenthesized :
    bool -> unit coq_PrettyPrinter -> unit coq_PrettyPrinter **)

let print_parenthesized parenthesize print =
  if parenthesize
  then bind (Obj.magic coq_Monad_PrettyPrinter)
         (PrettyPrinterMonad.append (String ((Ascii (false, false, false,
           true, false, true, false, false)), EmptyString))) (fun _ ->
         bind (Obj.magic coq_Monad_PrettyPrinter) print (fun _ ->
           PrettyPrinterMonad.append (String ((Ascii (true, false, false,
             true, false, true, false, false)), EmptyString))))
  else print

(** val print_parenthesized_with :
    string -> string -> bool -> unit coq_PrettyPrinter -> unit
    coq_PrettyPrinter **)

let print_parenthesized_with par_start par_end parenthesize print =
  if parenthesize
  then bind (Obj.magic coq_Monad_PrettyPrinter)
         (PrettyPrinterMonad.append par_start) (fun _ ->
         bind (Obj.magic coq_Monad_PrettyPrinter) print (fun _ ->
           PrettyPrinterMonad.append par_end))
  else print

(** val fresh : ident -> ident list -> ident **)

let fresh name0 used =
  if existsb (String.eqb name0) used
  then let rec f n i =
         match n with
         | O ->
           String.of_string (String ((Ascii (true, false, true, false, true,
             true, true, false)), (String ((Ascii (false, true, true, true,
             false, true, true, false)), (String ((Ascii (false, true, false,
             false, true, true, true, false)), (String ((Ascii (true, false,
             true, false, false, true, true, false)), (String ((Ascii (true,
             false, false, false, false, true, true, false)), (String ((Ascii
             (true, true, false, false, false, true, true, false)), (String
             ((Ascii (false, false, false, true, false, true, true, false)),
             (String ((Ascii (true, false, false, false, false, true, true,
             false)), (String ((Ascii (false, true, false, false, false,
             true, true, false)), (String ((Ascii (false, false, true, true,
             false, true, true, false)), (String ((Ascii (true, false, true,
             false, false, true, true, false)),
             EmptyString))))))))))))))))))))))
         | S n0 ->
           let numbered_name = String.append name0 (MCString.string_of_nat i)
           in
           if existsb (String.eqb numbered_name) used
           then f n0 (S i)
           else numbered_name
       in f (S (Datatypes.length used)) (S (S O))
  else name0

(** val fresh_ident : name -> ident list -> ident coq_PrettyPrinter **)

let fresh_ident name0 _UU0393_ =
  bind (Obj.magic coq_Monad_PrettyPrinter) (Obj.magic get_used_names)
    (fun used_names ->
    match name0 with
    | Coq_nAnon ->
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (fresh
          (String.of_string (String ((Ascii (false, false, false, true, true,
            true, true, false)), EmptyString))) (app _UU0393_ used_names))
    | Coq_nNamed name1 ->
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (fresh (String.of_string (clean_local_ident name1))
          (app _UU0393_ used_names)))

(** val fresh_ty_arg_name : name -> ident list -> ident coq_PrettyPrinter **)

let fresh_ty_arg_name name0 _UU0393_ =
  bind (Obj.magic coq_Monad_PrettyPrinter) (Obj.magic get_used_names)
    (fun used_names ->
    match name0 with
    | Coq_nAnon ->
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (fresh
          (String.of_string (String ((Ascii (true, false, false, false,
            false, true, true, false)), EmptyString)))
          (app _UU0393_ used_names))
    | Coq_nNamed name1 ->
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (fresh (String.of_string (clean_local_ident name1))
          (app _UU0393_ used_names)))

(** val print_type_aux :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ident list -> box_type
    -> unit coq_PrettyPrinter list -> unit coq_PrettyPrinter **)

let rec print_type_aux _UU03a3_ remaps0 h _UU0393_ t0 args =
  match t0 with
  | TBox -> PrettyPrinterMonad.append h.type_box_symbol
  | TAny -> PrettyPrinterMonad.append h.any_type_symbol
  | TArr (dom, cod) ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (PrettyPrinterMonad.append (String ((Ascii (false, true, true, false,
        false, true, false, false)), (String ((Ascii (true, true, true,
        false, false, true, false, false)), (String ((Ascii (true, false,
        false, false, false, true, true, false)), (String ((Ascii (false,
        false, false, false, false, true, false, false)), (String ((Ascii
        (false, false, true, false, false, true, true, false)), (String
        ((Ascii (true, false, false, true, true, true, true, false)), (String
        ((Ascii (false, true, true, true, false, true, true, false)), (String
        ((Ascii (false, false, false, false, false, true, false, false)),
        (String ((Ascii (false, true, true, false, false, false, true,
        false)), (String ((Ascii (false, true, true, true, false, true, true,
        false)), (String ((Ascii (false, false, false, true, false, true,
        false, false)), EmptyString))))))))))))))))))))))) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (print_type_aux _UU03a3_ remaps0 h _UU0393_ dom []) (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (PrettyPrinterMonad.append (String ((Ascii (true, false, false,
            true, false, true, false, false)), (String ((Ascii (false, false,
            false, false, false, true, false, false)), (String ((Ascii (true,
            false, true, true, false, true, false, false)), (String ((Ascii
            (false, true, true, true, true, true, false, false)), (String
            ((Ascii (false, false, false, false, false, true, false, false)),
            EmptyString))))))))))) (fun _ ->
          print_type_aux _UU03a3_ remaps0 h _UU0393_ cod [])))
  | TApp (head, arg) ->
    print_type_aux _UU03a3_ remaps0 h _UU0393_ head
      ((print_type_aux _UU03a3_ remaps0 h _UU0393_ arg []) :: args)
  | TVar n ->
    (match nth_error _UU0393_ n with
     | Some name0 -> PrettyPrinterMonad.append (String.to_string name0)
     | None ->
       printer_fail
         (append (String ((Ascii (true, false, true, false, true, true, true,
           false)), (String ((Ascii (false, true, true, true, false, true,
           true, false)), (String ((Ascii (false, true, false, false, false,
           true, true, false)), (String ((Ascii (true, true, true, true,
           false, true, true, false)), (String ((Ascii (true, false, true,
           false, true, true, true, false)), (String ((Ascii (false, true,
           true, true, false, true, true, false)), (String ((Ascii (false,
           false, true, false, false, true, true, false)), (String ((Ascii
           (false, false, false, false, false, true, false, false)), (String
           ((Ascii (false, false, true, false, true, false, true, false)),
           (String ((Ascii (false, true, true, false, true, false, true,
           false)), (String ((Ascii (true, false, false, false, false, true,
           true, false)), (String ((Ascii (false, true, false, false, true,
           true, true, false)), (String ((Ascii (false, false, false, false,
           false, true, false, false)), EmptyString))))))))))))))))))))))))))
           (string_of_nat n)))
  | TInd ind ->
    (match remaps0.remap_inductive ind with
     | Some _ ->
       bind (Obj.magic coq_Monad_PrettyPrinter)
         (print_ind _UU03a3_ remaps0 h ind) (fun _ ->
         print_parenthesized_with (String ((Ascii (false, false, true, true,
           true, true, false, false)), EmptyString)) (String ((Ascii (false,
           true, true, true, true, true, false, false)), EmptyString))
           (Nat.ltb O (Datatypes.length args))
           (monad_append_join
             (PrettyPrinterMonad.append (String ((Ascii (false, false, true,
               true, false, true, false, false)), (String ((Ascii (false,
               false, false, false, false, true, false, false)),
               EmptyString))))) args))
     | None ->
       bind (Obj.magic coq_Monad_PrettyPrinter)
         (PrettyPrinterMonad.append (String ((Ascii (false, true, true,
           false, false, true, false, false)), (String ((Ascii (true, true,
           true, false, false, true, false, false)), (String ((Ascii (true,
           false, false, false, false, true, true, false)), (String ((Ascii
           (false, false, false, false, false, true, false, false)),
           EmptyString))))))))) (fun _ ->
         bind (Obj.magic coq_Monad_PrettyPrinter)
           (print_ind _UU03a3_ remaps0 h ind) (fun _ ->
           bind (Obj.magic coq_Monad_PrettyPrinter)
             (PrettyPrinterMonad.append (String ((Ascii (false, false, true,
               true, true, true, false, false)), EmptyString))) (fun _ ->
             bind (Obj.magic coq_Monad_PrettyPrinter)
               (monad_append_join
                 (PrettyPrinterMonad.append (String ((Ascii (false, false,
                   true, true, false, true, false, false)), (String ((Ascii
                   (false, false, false, false, false, true, false, false)),
                   EmptyString)))))
                 ((PrettyPrinterMonad.append (String ((Ascii (true, true,
                    true, false, false, true, false, false)), (String ((Ascii
                    (true, false, false, false, false, true, true, false)),
                    EmptyString))))) :: args)) (fun _ ->
               PrettyPrinterMonad.append (String ((Ascii (false, true, true,
                 true, true, true, false, false)), EmptyString)))))))
  | TConst name0 ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (PrettyPrinterMonad.append
        (append (String.to_string (get_ty_const_ident remaps0 h name0))
          (String ((Ascii (false, false, true, true, true, true, false,
          false)), EmptyString)))) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (monad_append_join
          (PrettyPrinterMonad.append (String ((Ascii (false, false, true,
            true, false, true, false, false)), (String ((Ascii (false, false,
            false, false, false, true, false, false)), EmptyString)))))
          ((PrettyPrinterMonad.append (String ((Ascii (true, true, true,
             false, false, true, false, false)), (String ((Ascii (true,
             false, false, false, false, true, true, false)), EmptyString))))) :: args))
        (fun _ ->
        PrettyPrinterMonad.append (String ((Ascii (false, true, true, true,
          true, true, false, false)), EmptyString))))

(** val print_type :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ident list -> box_type
    -> unit coq_PrettyPrinter **)

let print_type _UU03a3_ remaps0 h _UU0393_ t0 =
  print_type_aux _UU03a3_ remaps0 h _UU0393_ t0 []

(** val get_num_inline_args :
    Ex.global_env -> kername -> nat coq_PrettyPrinter **)

let get_num_inline_args _UU03a3_ kn =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (wrap_option (Obj.magic Ex.lookup_constant _UU03a3_ kn)
      (append (String ((Ascii (true, true, false, false, false, false, true,
        false)), (String ((Ascii (true, true, true, true, false, true, true,
        false)), (String ((Ascii (true, false, true, false, true, true, true,
        false)), (String ((Ascii (false, false, true, true, false, true,
        true, false)), (String ((Ascii (false, false, true, false, false,
        true, true, false)), (String ((Ascii (false, false, false, false,
        false, true, false, false)), (String ((Ascii (false, true, true,
        true, false, true, true, false)), (String ((Ascii (true, true, true,
        true, false, true, true, false)), (String ((Ascii (false, false,
        true, false, true, true, true, false)), (String ((Ascii (false,
        false, false, false, false, true, false, false)), (String ((Ascii
        (false, true, true, false, false, true, true, false)), (String
        ((Ascii (true, false, false, true, false, true, true, false)),
        (String ((Ascii (false, true, true, true, false, true, true, false)),
        (String ((Ascii (false, false, true, false, false, true, true,
        false)), (String ((Ascii (false, false, false, false, false, true,
        false, false)), (String ((Ascii (true, true, false, false, false,
        true, true, false)), (String ((Ascii (true, true, true, true, false,
        true, true, false)), (String ((Ascii (false, true, true, true, false,
        true, true, false)), (String ((Ascii (true, true, false, false, true,
        true, true, false)), (String ((Ascii (false, false, true, false,
        true, true, true, false)), (String ((Ascii (true, false, false,
        false, false, true, true, false)), (String ((Ascii (false, true,
        true, true, false, true, true, false)), (String ((Ascii (false,
        false, true, false, true, true, true, false)), (String ((Ascii
        (false, false, false, false, false, true, false, false)),
        EmptyString))))))))))))))))))))))))))))))))))))))))))))))))
        (String.to_string (string_of_kername kn)))) (fun cst ->
    match Ex.cst_body cst with
    | Some body ->
      let count =
        let rec count body0 ty =
          match body0 with
          | Coq_tLambda (_, body1) ->
            (match ty with
             | TArr (_, cod) -> S (count body1 cod)
             | _ -> O)
          | _ -> O
        in count
      in
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (count body (snd (Ex.cst_type cst)))
    | None ->
      ret (Obj.magic coq_Monad_PrettyPrinter)
        (Datatypes.length (fst (decompose_arr (snd (Ex.cst_type cst))))))

(** val print_app :
    unit coq_PrettyPrinter -> unit coq_PrettyPrinter list -> unit
    coq_PrettyPrinter **)

let print_app head args =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) head (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (push_indent (add col indent_size)) (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (PrettyPrinterMonad.append (String ((Ascii (false, false, false,
            true, false, true, false, false)), EmptyString))) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (if Nat.ltb O (Datatypes.length args)
             then append_nl
             else ret (Obj.magic coq_Monad_PrettyPrinter) ()) (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (monad_append_join
                (bind (Obj.magic coq_Monad_PrettyPrinter)
                  (PrettyPrinterMonad.append (String ((Ascii (false, false,
                    true, true, false, true, false, false)), EmptyString)))
                  (fun _ -> append_nl)) args) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (PrettyPrinterMonad.append (String ((Ascii (true, false,
                  false, true, false, true, false, false)), EmptyString)))
                (fun _ -> pop_indent)))))))

(** val print_constructor :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> inductive -> nat ->
    unit coq_PrettyPrinter list -> unit coq_PrettyPrinter **)

let print_constructor _UU03a3_ remaps0 h ind c args =
  match remaps0.remap_inductive ind with
  | Some rem ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (wrap_option (nth_error (Obj.magic rem.re_ind_ctors) c)
        (append (String.to_string (string_of_inductive ind)) (String ((Ascii
          (true, true, true, false, false, true, false, false)), (String
          ((Ascii (false, false, false, false, false, true, false, false)),
          (String ((Ascii (false, false, true, false, false, true, true,
          false)), (String ((Ascii (true, true, true, true, false, true,
          true, false)), (String ((Ascii (true, false, true, false, false,
          true, true, false)), (String ((Ascii (true, true, false, false,
          true, true, true, false)), (String ((Ascii (false, false, false,
          false, false, true, false, false)), (String ((Ascii (false, true,
          true, true, false, true, true, false)), (String ((Ascii (true,
          true, true, true, false, true, true, false)), (String ((Ascii
          (false, false, true, false, true, true, true, false)), (String
          ((Ascii (false, false, false, false, false, true, false, false)),
          (String ((Ascii (false, true, false, false, true, true, true,
          false)), (String ((Ascii (true, false, true, false, false, true,
          true, false)), (String ((Ascii (true, false, true, true, false,
          true, true, false)), (String ((Ascii (true, false, false, false,
          false, true, true, false)), (String ((Ascii (false, false, false,
          false, true, true, true, false)), (String ((Ascii (false, false,
          false, false, false, true, false, false)), (String ((Ascii (true,
          false, true, false, false, true, true, false)), (String ((Ascii
          (false, true, true, true, false, true, true, false)), (String
          ((Ascii (true, true, true, true, false, true, true, false)),
          (String ((Ascii (true, false, true, false, true, true, true,
          false)), (String ((Ascii (true, true, true, false, false, true,
          true, false)), (String ((Ascii (false, false, false, true, false,
          true, true, false)), (String ((Ascii (false, false, false, false,
          false, true, false, false)), (String ((Ascii (true, true, false,
          false, false, true, true, false)), (String ((Ascii (true, true,
          true, true, false, true, true, false)), (String ((Ascii (false,
          true, true, true, false, true, true, false)), (String ((Ascii
          (true, true, false, false, true, true, true, false)), (String
          ((Ascii (false, false, true, false, true, true, true, false)),
          (String ((Ascii (false, true, false, false, true, true, true,
          false)), (String ((Ascii (true, false, true, false, true, true,
          true, false)), (String ((Ascii (true, true, false, false, false,
          true, true, false)), (String ((Ascii (false, false, true, false,
          true, true, true, false)), (String ((Ascii (true, true, true, true,
          false, true, true, false)), (String ((Ascii (false, true, false,
          false, true, true, true, false)), (String ((Ascii (true, true,
          false, false, true, true, true, false)), (String ((Ascii (false,
          false, false, false, false, true, false, false)),
          EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (fun s ->
      if Nat.ltb O (Datatypes.length args)
      then print_app (PrettyPrinterMonad.append (String.to_string s)) args
      else PrettyPrinterMonad.append (String.to_string s))
  | None ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (wrap_result (Obj.magic lookup_ind_decl _UU03a3_ ind) (Obj.magic id))
      (fun oib ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (wrap_option (nth_error (Obj.magic Ex.ind_ctors oib) c)
          (append (String ((Ascii (true, true, false, false, false, false,
            true, false)), (String ((Ascii (true, true, true, true, false,
            true, true, false)), (String ((Ascii (true, false, true, false,
            true, true, true, false)), (String ((Ascii (false, false, true,
            true, false, true, true, false)), (String ((Ascii (false, false,
            true, false, false, true, true, false)), (String ((Ascii (false,
            false, false, false, false, true, false, false)), (String ((Ascii
            (false, true, true, true, false, true, true, false)), (String
            ((Ascii (true, true, true, true, false, true, true, false)),
            (String ((Ascii (false, false, true, false, true, true, true,
            false)), (String ((Ascii (false, false, false, false, false,
            true, false, false)), (String ((Ascii (false, true, true, false,
            false, true, true, false)), (String ((Ascii (true, false, false,
            true, false, true, true, false)), (String ((Ascii (false, true,
            true, true, false, true, true, false)), (String ((Ascii (false,
            false, true, false, false, true, true, false)), (String ((Ascii
            (false, false, false, false, false, true, false, false)), (String
            ((Ascii (true, true, false, false, false, true, true, false)),
            (String ((Ascii (false, false, true, false, true, true, true,
            false)), (String ((Ascii (true, true, true, true, false, true,
            true, false)), (String ((Ascii (false, true, false, false, true,
            true, true, false)), (String ((Ascii (false, false, false, false,
            false, true, false, false)),
            EmptyString))))))))))))))))))))))))))))))))))))))))
            (append (string_of_nat c)
              (append (String ((Ascii (false, false, false, false, false,
                true, false, false)), (String ((Ascii (false, true, true,
                false, false, true, true, false)), (String ((Ascii (true,
                true, true, true, false, true, true, false)), (String ((Ascii
                (false, true, false, false, true, true, true, false)),
                (String ((Ascii (false, false, false, false, false, true,
                false, false)), (String ((Ascii (true, false, false, true,
                false, true, true, false)), (String ((Ascii (false, true,
                true, true, false, true, true, false)), (String ((Ascii
                (false, false, true, false, false, true, true, false)),
                (String ((Ascii (true, false, true, false, true, true, true,
                false)), (String ((Ascii (true, true, false, false, false,
                true, true, false)), (String ((Ascii (false, false, true,
                false, true, true, true, false)), (String ((Ascii (true,
                false, false, true, false, true, true, false)), (String
                ((Ascii (false, true, true, false, true, true, true, false)),
                (String ((Ascii (true, false, true, false, false, true, true,
                false)), (String ((Ascii (false, false, false, false, false,
                true, false, false)),
                EmptyString))))))))))))))))))))))))))))))
                (String.to_string (string_of_inductive ind)))))) (fun x ->
        let (p, _) = x in
        let (ctor, _) = p in
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (Obj.magic get_current_line_length) (fun col ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (push_indent (add col indent_size)) (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (PrettyPrinterMonad.append (String ((Ascii (true, true, false,
                false, true, true, true, false)), (String ((Ascii (true,
                false, true, false, false, true, true, false)), (String
                ((Ascii (false, false, true, true, false, true, true,
                false)), (String ((Ascii (false, true, true, false, false,
                true, true, false)), (String ((Ascii (false, true, true,
                true, false, true, false, false)), (String ((Ascii (true,
                false, false, false, false, true, true, false)), (String
                ((Ascii (false, false, true, true, false, true, true,
                false)), (String ((Ascii (false, false, true, true, false,
                true, true, false)), (String ((Ascii (true, true, true, true,
                false, true, true, false)), (String ((Ascii (true, true,
                false, false, false, true, true, false)), (String ((Ascii
                (false, false, false, true, false, true, false, false)),
                EmptyString))))))))))))))))))))))) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
                let head =
                  bind (Obj.magic coq_Monad_PrettyPrinter)
                    (print_ind _UU03a3_ remaps0 h ind) (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (PrettyPrinterMonad.append (String ((Ascii (false,
                        true, false, true, true, true, false, false)),
                        (String ((Ascii (false, true, false, true, true,
                        true, false, false)), EmptyString))))) (fun _ ->
                      PrettyPrinterMonad.append
                        (clean_global_ident (String.to_string ctor))))
                in
                let final_args =
                  (PrettyPrinterMonad.append (String ((Ascii (false, false,
                    false, false, true, false, true, false)), (String ((Ascii
                    (false, false, false, true, false, true, true, false)),
                    (String ((Ascii (true, false, false, false, false, true,
                    true, false)), (String ((Ascii (false, true, true, true,
                    false, true, true, false)), (String ((Ascii (false,
                    false, true, false, true, true, true, false)), (String
                    ((Ascii (true, true, true, true, false, true, true,
                    false)), (String ((Ascii (true, false, true, true, false,
                    true, true, false)), (String ((Ascii (false, false, true,
                    false, false, false, true, false)), (String ((Ascii
                    (true, false, false, false, false, true, true, false)),
                    (String ((Ascii (false, false, true, false, true, true,
                    true, false)), (String ((Ascii (true, false, false,
                    false, false, true, true, false)),
                    EmptyString))))))))))))))))))))))) :: args
                in
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (print_app head final_args) (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter)
                    (PrettyPrinterMonad.append (String ((Ascii (true, false,
                      false, true, false, true, false, false)), EmptyString)))
                    (fun _ -> pop_indent))))))))

(** val print_const :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> kername -> unit
    coq_PrettyPrinter list -> unit coq_PrettyPrinter **)

let print_const _UU03a3_ remaps0 h kn args =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_num_inline_args _UU03a3_ kn) (fun num_inline_args ->
    if Nat.ltb (Datatypes.length args) num_inline_args
    then let expr =
           append (String ((Ascii (true, true, false, false, true, true,
             true, false)), (String ((Ascii (true, false, true, false, false,
             true, true, false)), (String ((Ascii (false, false, true, true,
             false, true, true, false)), (String ((Ascii (false, true, true,
             false, false, true, true, false)), (String ((Ascii (false, true,
             true, true, false, true, false, false)), EmptyString))))))))))
             (append (const_global_ident_of_kername h kn) (String ((Ascii
               (true, true, true, true, true, false, true, false)), (String
               ((Ascii (true, true, true, true, true, false, true, false)),
               (String ((Ascii (true, true, false, false, false, true, true,
               false)), (String ((Ascii (true, false, true, false, true,
               true, true, false)), (String ((Ascii (false, true, false,
               false, true, true, true, false)), (String ((Ascii (false,
               true, false, false, true, true, true, false)), (String ((Ascii
               (true, false, false, true, false, true, true, false)), (String
               ((Ascii (true, false, true, false, false, true, true, false)),
               (String ((Ascii (false, false, true, false, false, true, true,
               false)), EmptyString)))))))))))))))))))
         in
         let num_inline_args0 = O in
         bind (Obj.magic coq_Monad_PrettyPrinter)
           (Obj.magic get_current_line_length) (fun head_col ->
           let head = PrettyPrinterMonad.append expr in
           let args_in_head = firstn num_inline_args0 args in
           let args_in_tail = skipn num_inline_args0 args in
           bind (Obj.magic coq_Monad_PrettyPrinter)
             (print_app head args_in_head) (fun _ ->
             bind (Obj.magic coq_Monad_PrettyPrinter)
               (push_indent (add head_col indent_size)) (fun _ ->
               let it_app = fun a ->
                 bind (Obj.magic coq_Monad_PrettyPrinter)
                   (PrettyPrinterMonad.append (String ((Ascii (false, false,
                     false, true, false, true, false, false)), EmptyString)))
                   (fun _ ->
                   bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                     (fun _ ->
                     bind (Obj.magic coq_Monad_PrettyPrinter) a (fun _ ->
                       PrettyPrinterMonad.append (String ((Ascii (true,
                         false, false, true, false, true, false, false)),
                         EmptyString)))))
               in
               bind (Obj.magic coq_Monad_PrettyPrinter)
                 (monad_append_concat (map it_app args_in_tail)) (fun _ ->
                 pop_indent))))
    else let expr =
           match remaps0.remap_inline_constant kn with
           | Some s -> String.to_string s
           | None ->
             append (String ((Ascii (true, true, false, false, true, true,
               true, false)), (String ((Ascii (true, false, true, false,
               false, true, true, false)), (String ((Ascii (false, false,
               true, true, false, true, true, false)), (String ((Ascii
               (false, true, true, false, false, true, true, false)), (String
               ((Ascii (false, true, true, true, false, true, false, false)),
               EmptyString)))))))))) (const_global_ident_of_kername h kn)
         in
         bind (Obj.magic coq_Monad_PrettyPrinter)
           (Obj.magic get_current_line_length) (fun head_col ->
           let head = PrettyPrinterMonad.append expr in
           let args_in_head = firstn num_inline_args args in
           let args_in_tail = skipn num_inline_args args in
           bind (Obj.magic coq_Monad_PrettyPrinter)
             (print_app head args_in_head) (fun _ ->
             bind (Obj.magic coq_Monad_PrettyPrinter)
               (push_indent (add head_col indent_size)) (fun _ ->
               let it_app = fun a ->
                 bind (Obj.magic coq_Monad_PrettyPrinter)
                   (PrettyPrinterMonad.append (String ((Ascii (false, false,
                     false, true, false, true, false, false)), EmptyString)))
                   (fun _ ->
                   bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                     (fun _ ->
                     bind (Obj.magic coq_Monad_PrettyPrinter) a (fun _ ->
                       PrettyPrinterMonad.append (String ((Ascii (true,
                         false, false, true, false, true, false, false)),
                         EmptyString)))))
               in
               bind (Obj.magic coq_Monad_PrettyPrinter)
                 (monad_append_concat (map it_app args_in_tail)) (fun _ ->
                 pop_indent)))))

(** val print_case :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> (ident list -> term ->
    unit coq_PrettyPrinter) -> ident list -> inductive -> nat -> term ->
    (name list * term) list -> unit coq_PrettyPrinter **)

let print_case _UU03a3_ remaps0 h print_term0 _UU0393_ ind npars discr brs =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent col) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (PrettyPrinterMonad.append (String ((Ascii (true, false, true, true,
          false, true, true, false)), (String ((Ascii (true, false, false,
          false, false, true, true, false)), (String ((Ascii (false, false,
          true, false, true, true, true, false)), (String ((Ascii (true,
          true, false, false, false, true, true, false)), (String ((Ascii
          (false, false, false, true, false, true, true, false)), (String
          ((Ascii (false, false, false, false, false, true, false, false)),
          EmptyString))))))))))))) (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter) (print_term0 _UU0393_ discr)
          (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (PrettyPrinterMonad.append (String ((Ascii (false, false, false,
              false, false, true, false, false)), (String ((Ascii (true,
              true, false, true, true, true, true, false)), EmptyString)))))
            (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (wrap_result (Obj.magic lookup_ind_decl _UU03a3_ ind)
                (Obj.magic id)) (fun oib ->
              let rem = remaps0.remap_inductive ind in
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (push_indent (add col indent_size)) (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (let rec print_cases brs0 ctors c =
                     match brs0 with
                     | [] ->
                       (match ctors with
                        | [] -> ret (Obj.magic coq_Monad_PrettyPrinter) ()
                        | _ :: _ ->
                          printer_fail (String ((Ascii (true, true, true,
                            false, true, true, true, false)), (String ((Ascii
                            (false, true, false, false, true, true, true,
                            false)), (String ((Ascii (true, true, true, true,
                            false, true, true, false)), (String ((Ascii
                            (false, true, true, true, false, true, true,
                            false)), (String ((Ascii (true, true, true,
                            false, false, true, true, false)), (String
                            ((Ascii (false, false, false, false, false, true,
                            false, false)), (String ((Ascii (false, true,
                            true, true, false, true, true, false)), (String
                            ((Ascii (true, false, true, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            true, true, false, true, true, false)), (String
                            ((Ascii (false, true, false, false, false, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (false, true, false, false, true, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, false, true, false, false)),
                            (String ((Ascii (true, true, true, true, false,
                            true, true, false)), (String ((Ascii (false,
                            true, true, false, false, true, true, false)),
                            (String ((Ascii (false, false, false, false,
                            false, true, false, false)), (String ((Ascii
                            (true, true, false, false, false, true, true,
                            false)), (String ((Ascii (true, false, false,
                            false, false, true, true, false)), (String
                            ((Ascii (true, true, false, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (false, false, false, false, false, true,
                            false, false)), (String ((Ascii (false, true,
                            false, false, false, true, true, false)), (String
                            ((Ascii (false, true, false, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            false, false, false, true, true, false)), (String
                            ((Ascii (false, true, true, true, false, true,
                            true, false)), (String ((Ascii (true, true,
                            false, false, false, true, true, false)), (String
                            ((Ascii (false, false, false, true, false, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (true, true, false, false, true, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, false, true, false, false)),
                            (String ((Ascii (true, true, false, false, false,
                            true, true, false)), (String ((Ascii (true, true,
                            true, true, false, true, true, false)), (String
                            ((Ascii (true, false, true, true, false, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, true, true, true, false)), (String
                            ((Ascii (true, false, false, false, false, true,
                            true, false)), (String ((Ascii (false, true,
                            false, false, true, true, true, false)), (String
                            ((Ascii (true, false, true, false, false, true,
                            true, false)), (String ((Ascii (false, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (false, false, false, false, false, true,
                            false, false)), (String ((Ascii (false, false,
                            true, false, true, true, true, false)), (String
                            ((Ascii (true, true, true, true, false, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, false, true, false, false)),
                            (String ((Ascii (true, false, false, true, false,
                            true, true, false)), (String ((Ascii (false,
                            true, true, true, false, true, true, false)),
                            (String ((Ascii (false, false, true, false,
                            false, true, true, false)), (String ((Ascii
                            (true, false, true, false, true, true, true,
                            false)), (String ((Ascii (true, true, false,
                            false, false, true, true, false)), (String
                            ((Ascii (false, false, true, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            false, true, false, true, true, false)), (String
                            ((Ascii (false, true, true, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)),
                            EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     | p :: branches ->
                       let (bctx, t0) = p in
                       (match ctors with
                        | [] ->
                          printer_fail (String ((Ascii (true, true, true,
                            false, true, true, true, false)), (String ((Ascii
                            (false, true, false, false, true, true, true,
                            false)), (String ((Ascii (true, true, true, true,
                            false, true, true, false)), (String ((Ascii
                            (false, true, true, true, false, true, true,
                            false)), (String ((Ascii (true, true, true,
                            false, false, true, true, false)), (String
                            ((Ascii (false, false, false, false, false, true,
                            false, false)), (String ((Ascii (false, true,
                            true, true, false, true, true, false)), (String
                            ((Ascii (true, false, true, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            true, true, false, true, true, false)), (String
                            ((Ascii (false, true, false, false, false, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (false, true, false, false, true, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, false, true, false, false)),
                            (String ((Ascii (true, true, true, true, false,
                            true, true, false)), (String ((Ascii (false,
                            true, true, false, false, true, true, false)),
                            (String ((Ascii (false, false, false, false,
                            false, true, false, false)), (String ((Ascii
                            (true, true, false, false, false, true, true,
                            false)), (String ((Ascii (true, false, false,
                            false, false, true, true, false)), (String
                            ((Ascii (true, true, false, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (false, false, false, false, false, true,
                            false, false)), (String ((Ascii (false, true,
                            false, false, false, true, true, false)), (String
                            ((Ascii (false, true, false, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            false, false, false, true, true, false)), (String
                            ((Ascii (false, true, true, true, false, true,
                            true, false)), (String ((Ascii (true, true,
                            false, false, false, true, true, false)), (String
                            ((Ascii (false, false, false, true, false, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (true, true, false, false, true, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, false, true, false, false)),
                            (String ((Ascii (true, true, false, false, false,
                            true, true, false)), (String ((Ascii (true, true,
                            true, true, false, true, true, false)), (String
                            ((Ascii (true, false, true, true, false, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, true, true, true, false)), (String
                            ((Ascii (true, false, false, false, false, true,
                            true, false)), (String ((Ascii (false, true,
                            false, false, true, true, true, false)), (String
                            ((Ascii (true, false, true, false, false, true,
                            true, false)), (String ((Ascii (false, false,
                            true, false, false, true, true, false)), (String
                            ((Ascii (false, false, false, false, false, true,
                            false, false)), (String ((Ascii (false, false,
                            true, false, true, true, true, false)), (String
                            ((Ascii (true, true, true, true, false, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, false, true, false, false)),
                            (String ((Ascii (true, false, false, true, false,
                            true, true, false)), (String ((Ascii (false,
                            true, true, true, false, true, true, false)),
                            (String ((Ascii (false, false, true, false,
                            false, true, true, false)), (String ((Ascii
                            (true, false, true, false, true, true, true,
                            false)), (String ((Ascii (true, true, false,
                            false, false, true, true, false)), (String
                            ((Ascii (false, false, true, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            false, true, false, true, true, false)), (String
                            ((Ascii (false, true, true, false, true, true,
                            true, false)), (String ((Ascii (true, false,
                            true, false, false, true, true, false)),
                            EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        | p0 :: ctors0 ->
                          let (p1, _) = p0 in
                          let (ctor_name, _) = p1 in
                          bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                            (fun _ ->
                            bind (Obj.magic coq_Monad_PrettyPrinter)
                              (match rem with
                               | Some rem0 ->
                                 bind (Obj.magic coq_Monad_PrettyPrinter)
                                   (wrap_option
                                     (nth_error (Obj.magic rem0.re_ind_ctors)
                                       c)
                                     (append
                                       (String.to_string
                                         (string_of_inductive ind)) (String
                                       ((Ascii (true, true, true, false,
                                       false, true, false, false)), (String
                                       ((Ascii (false, false, false, false,
                                       false, true, false, false)), (String
                                       ((Ascii (false, false, true, false,
                                       false, true, true, false)), (String
                                       ((Ascii (true, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (true, false, true, false,
                                       false, true, true, false)), (String
                                       ((Ascii (true, true, false, false,
                                       true, true, true, false)), (String
                                       ((Ascii (false, false, false, false,
                                       false, true, false, false)), (String
                                       ((Ascii (false, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (true, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (false, false, true, false,
                                       true, true, true, false)), (String
                                       ((Ascii (false, false, false, false,
                                       false, true, false, false)), (String
                                       ((Ascii (false, true, false, false,
                                       true, true, true, false)), (String
                                       ((Ascii (true, false, true, false,
                                       false, true, true, false)), (String
                                       ((Ascii (true, false, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (true, false, false, false,
                                       false, true, true, false)), (String
                                       ((Ascii (false, false, false, false,
                                       true, true, true, false)), (String
                                       ((Ascii (false, false, false, false,
                                       false, true, false, false)), (String
                                       ((Ascii (true, false, true, false,
                                       false, true, true, false)), (String
                                       ((Ascii (false, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (true, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (true, false, true, false,
                                       true, true, true, false)), (String
                                       ((Ascii (true, true, true, false,
                                       false, true, true, false)), (String
                                       ((Ascii (false, false, false, true,
                                       false, true, true, false)), (String
                                       ((Ascii (false, false, false, false,
                                       false, true, false, false)), (String
                                       ((Ascii (true, true, false, false,
                                       false, true, true, false)), (String
                                       ((Ascii (true, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (false, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (true, true, false, false,
                                       true, true, true, false)), (String
                                       ((Ascii (false, false, true, false,
                                       true, true, true, false)), (String
                                       ((Ascii (false, true, false, false,
                                       true, true, true, false)), (String
                                       ((Ascii (true, false, true, false,
                                       true, true, true, false)), (String
                                       ((Ascii (true, true, false, false,
                                       false, true, true, false)), (String
                                       ((Ascii (false, false, true, false,
                                       true, true, true, false)), (String
                                       ((Ascii (true, true, true, true,
                                       false, true, true, false)), (String
                                       ((Ascii (false, true, false, false,
                                       true, true, true, false)), (String
                                       ((Ascii (true, true, false, false,
                                       true, true, true, false)),
                                       EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                   (fun s ->
                                   PrettyPrinterMonad.append
                                     (String.to_string s))
                               | None ->
                                 bind (Obj.magic coq_Monad_PrettyPrinter)
                                   (PrettyPrinterMonad.append (String ((Ascii
                                     (false, true, true, false, false, true,
                                     false, false)), EmptyString))) (fun _ ->
                                   bind (Obj.magic coq_Monad_PrettyPrinter)
                                     (print_ind _UU03a3_ remaps0 h ind)
                                     (fun _ ->
                                     bind (Obj.magic coq_Monad_PrettyPrinter)
                                       (PrettyPrinterMonad.append (String
                                         ((Ascii (false, true, false, true,
                                         true, true, false, false)), (String
                                         ((Ascii (false, true, false, true,
                                         true, true, false, false)),
                                         EmptyString))))) (fun _ ->
                                       PrettyPrinterMonad.append
                                         (clean_global_ident
                                           (String.to_string ctor_name))))))
                              (fun _ ->
                              bind (Obj.magic coq_Monad_PrettyPrinter)
                                (push_indent
                                  (add col (mul (S (S O)) indent_size)))
                                (fun _ ->
                                bind (Obj.magic coq_Monad_PrettyPrinter)
                                  (let rec print_branch bctx0 args _UU0393_0 =
                                     match bctx0 with
                                     | [] ->
                                       let nextra =
                                         match rem with
                                         | Some _ -> npars
                                         | None -> S npars
                                       in
                                       let extra =
                                         repeat (String ((Ascii (true, true,
                                           true, true, true, false, true,
                                           false)), EmptyString)) nextra
                                       in
                                       let args0 =
                                         app extra
                                           (map String.to_string
                                             (List0.rev args))
                                       in
                                       bind
                                         (Obj.magic coq_Monad_PrettyPrinter)
                                         (print_parenthesized
                                           (Nat.ltb O
                                             (Datatypes.length args0))
                                           (append_join (String ((Ascii
                                             (false, false, true, true,
                                             false, true, false, false)),
                                             (String ((Ascii (false, false,
                                             false, false, false, true,
                                             false, false)), EmptyString))))
                                             args0)) (fun _ ->
                                         bind
                                           (Obj.magic coq_Monad_PrettyPrinter)
                                           (PrettyPrinterMonad.append (String
                                             ((Ascii (false, false, false,
                                             false, false, true, false,
                                             false)), (String ((Ascii (true,
                                             false, true, true, true, true,
                                             false, false)), (String ((Ascii
                                             (false, true, true, true, true,
                                             true, false, false)), (String
                                             ((Ascii (false, false, false,
                                             false, false, true, false,
                                             false)), (String ((Ascii (true,
                                             true, false, true, true, true,
                                             true, false)),
                                             EmptyString))))))))))) (fun _ ->
                                           bind
                                             (Obj.magic
                                               coq_Monad_PrettyPrinter)
                                             append_nl (fun _ ->
                                             print_term0 _UU0393_0 t0)))
                                     | name0 :: bctx1 ->
                                       bind
                                         (Obj.magic coq_Monad_PrettyPrinter)
                                         (Obj.magic fresh_ident name0
                                           _UU0393_0) (fun name1 ->
                                         print_branch bctx1 (name1 :: args)
                                           (name1 :: _UU0393_0))
                                   in print_branch (List0.rev bctx) []
                                        _UU0393_) (fun _ ->
                                  bind (Obj.magic coq_Monad_PrettyPrinter)
                                    pop_indent (fun _ ->
                                    bind (Obj.magic coq_Monad_PrettyPrinter)
                                      append_nl (fun _ ->
                                      bind
                                        (Obj.magic coq_Monad_PrettyPrinter)
                                        (PrettyPrinterMonad.append (String
                                          ((Ascii (true, false, true, true,
                                          true, true, true, false)), (String
                                          ((Ascii (false, false, true, true,
                                          false, true, false, false)),
                                          EmptyString))))) (fun _ ->
                                        print_cases branches ctors0 (S c)))))))))
                   in print_cases brs (Ex.ind_ctors oib) O) (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent
                    (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                      (fun _ ->
                      bind (Obj.magic coq_Monad_PrettyPrinter)
                        (PrettyPrinterMonad.append (String ((Ascii (true,
                          false, true, true, true, true, true, false)),
                          EmptyString))) (fun _ -> pop_indent)))))))))))

(** val print_remapped_case :
    Ex.global_env -> (ident list -> term -> unit coq_PrettyPrinter) -> ident
    list -> inductive -> term -> (name list * term) list -> string -> unit
    coq_PrettyPrinter **)

let print_remapped_case _UU03a3_ print_term0 _UU0393_ ind discr brs eliminator =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent col) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (PrettyPrinterMonad.append
          (append eliminator (String ((Ascii (false, false, false, true,
            false, true, false, false)), EmptyString)))) (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (wrap_result (Obj.magic lookup_ind_decl _UU03a3_ ind)
            (Obj.magic id)) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (push_indent (add col indent_size)) (fun _ ->
            let map_cases =
              let rec map_cases = function
              | [] -> []
              | p :: brs1 ->
                let (bctx, t0) = p in
                (let rec print_branch bctx0 args _UU0393_0 =
                   match bctx0 with
                   | [] ->
                     let args0 = map String.to_string (List0.rev args) in
                     bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                       (fun _ ->
                       bind (Obj.magic coq_Monad_PrettyPrinter)
                         (append_concat
                           (map (fun a ->
                             append a (String ((Ascii (false, false, true,
                               true, false, true, false, false)), (String
                               ((Ascii (false, false, false, false, false,
                               true, false, false)), EmptyString))))) args0))
                         (fun _ ->
                         bind (Obj.magic coq_Monad_PrettyPrinter)
                           (PrettyPrinterMonad.append (String ((Ascii (true,
                             true, false, true, true, true, true, false)),
                             EmptyString))) (fun _ ->
                           bind (Obj.magic coq_Monad_PrettyPrinter)
                             (push_indent
                               (add col (mul (S (S O)) indent_size)))
                             (fun _ ->
                             bind (Obj.magic coq_Monad_PrettyPrinter)
                               append_nl (fun _ ->
                               bind (Obj.magic coq_Monad_PrettyPrinter)
                                 (print_term0 _UU0393_0 t0) (fun _ ->
                                 bind (Obj.magic coq_Monad_PrettyPrinter)
                                   pop_indent (fun _ ->
                                   bind (Obj.magic coq_Monad_PrettyPrinter)
                                     append_nl (fun _ ->
                                     PrettyPrinterMonad.append (String
                                       ((Ascii (true, false, true, true,
                                       true, true, true, false)), (String
                                       ((Ascii (false, false, true, true,
                                       false, true, false, false)),
                                       EmptyString))))))))))))
                   | name0 :: bctx1 ->
                     bind (Obj.magic coq_Monad_PrettyPrinter)
                       (Obj.magic fresh_ident name0 _UU0393_0) (fun name1 ->
                       print_branch bctx1 (name1 :: args) (name1 :: _UU0393_0))
                 in print_branch bctx [] _UU0393_) :: (map_cases brs1)
              in map_cases
            in
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (monad_append_concat (map_cases brs)) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (print_term0 _UU0393_ discr) (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter)
                    (PrettyPrinterMonad.append (String ((Ascii (true, false,
                      false, true, false, true, false, false)), EmptyString)))
                    (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent
                      (fun _ -> pop_indent))))))))))

(** val needs_block : term -> bool **)

let needs_block = function
| Coq_tLetIn (_, _, _) -> true
| Coq_tFix (_, _) -> true
| _ -> false

(** val print_term :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ident list -> term ->
    unit coq_PrettyPrinter **)

let rec print_term _UU03a3_ remaps0 h _UU0393_ = function
| Coq_tBox -> PrettyPrinterMonad.append h.term_box_symbol
| Coq_tRel n ->
  (match nth_error _UU0393_ n with
   | Some name0 -> PrettyPrinterMonad.append (String.to_string name0)
   | None ->
     printer_fail
       (append (String ((Ascii (true, false, true, false, true, true, true,
         false)), (String ((Ascii (false, true, true, true, false, true,
         true, false)), (String ((Ascii (false, true, false, false, false,
         true, true, false)), (String ((Ascii (true, true, true, true, false,
         true, true, false)), (String ((Ascii (true, false, true, false,
         true, true, true, false)), (String ((Ascii (false, true, true, true,
         false, true, true, false)), (String ((Ascii (false, false, true,
         false, false, true, true, false)), (String ((Ascii (false, false,
         false, false, false, true, false, false)), (String ((Ascii (false,
         false, true, false, true, true, true, false)), (String ((Ascii
         (false, true, false, false, true, false, true, false)), (String
         ((Ascii (true, false, true, false, false, true, true, false)),
         (String ((Ascii (false, false, true, true, false, true, true,
         false)), (String ((Ascii (false, false, false, false, false, true,
         false, false)), EmptyString))))))))))))))))))))))))))
         (string_of_nat n)))
| Coq_tVar ident0 ->
  printer_fail
    (append (String ((Ascii (false, false, true, false, true, true, true,
      false)), (String ((Ascii (false, true, true, false, true, false, true,
      false)), (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, true, false, false, true, true, true,
      false)), (String ((Ascii (false, false, false, false, false, true,
      false, false)), EmptyString)))))))))) (String.to_string ident0))
| Coq_tEvar (_, _) ->
  printer_fail (String ((Ascii (true, false, true, false, true, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, false, true, true, true, true,
    false)), (String ((Ascii (false, false, false, false, true, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (true, true, false, false, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, true, true, false, true, true, true,
    false)), (String ((Ascii (true, false, false, false, false, true, true,
    false)), (String ((Ascii (false, true, false, false, true, true, true,
    false)), EmptyString))))))))))))))))))))))))))))))
| Coq_tLambda (name0, t1) ->
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic fresh_ident name0 _UU0393_) (fun name1 ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (Obj.magic get_current_line_length) (fun col ->
      bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent col) (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (PrettyPrinterMonad.append
            (append (String ((Ascii (true, true, false, false, true, true,
              true, false)), (String ((Ascii (true, false, true, false,
              false, true, true, false)), (String ((Ascii (false, false,
              true, true, false, true, true, false)), (String ((Ascii (false,
              true, true, false, false, true, true, false)), (String ((Ascii
              (false, true, true, true, false, true, false, false)), (String
              ((Ascii (true, true, false, false, false, true, true, false)),
              (String ((Ascii (false, false, true, true, false, true, true,
              false)), (String ((Ascii (true, true, true, true, false, true,
              true, false)), (String ((Ascii (true, true, false, false, true,
              true, true, false)), (String ((Ascii (true, false, true, false,
              true, true, true, false)), (String ((Ascii (false, true, false,
              false, true, true, true, false)), (String ((Ascii (true, false,
              true, false, false, true, true, false)), (String ((Ascii
              (false, false, false, true, false, true, false, false)),
              (String ((Ascii (true, false, true, true, false, true, true,
              false)), (String ((Ascii (true, true, true, true, false, true,
              true, false)), (String ((Ascii (false, true, true, false, true,
              true, true, false)), (String ((Ascii (true, false, true, false,
              false, true, true, false)), (String ((Ascii (false, false,
              false, false, false, true, false, false)), (String ((Ascii
              (false, false, true, true, true, true, true, false)),
              EmptyString))))))))))))))))))))))))))))))))))))))
              (append (String.to_string name1) (String ((Ascii (false, false,
                true, true, true, true, true, false)), (String ((Ascii
                (false, false, false, false, false, true, false, false)),
                (String ((Ascii (true, true, false, true, true, true, true,
                false)), EmptyString))))))))) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (push_indent (add col indent_size)) (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
              let _UU0393_0 = name1 :: _UU0393_ in
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (print_term _UU03a3_ remaps0 h _UU0393_0 t1) (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                    (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (PrettyPrinterMonad.append (String ((Ascii (true,
                        false, true, true, true, true, true, false)), (String
                        ((Ascii (true, false, false, true, false, true,
                        false, false)), EmptyString))))) (fun _ -> pop_indent))))))))))
| Coq_tLetIn (na, val0, body) ->
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic fresh_ident na _UU0393_) (fun name0 ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (Obj.magic get_current_line_length) (fun col ->
      bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent col) (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (PrettyPrinterMonad.append
            (append (String ((Ascii (false, false, true, true, false, true,
              true, false)), (String ((Ascii (true, false, true, false,
              false, true, true, false)), (String ((Ascii (false, false,
              true, false, true, true, true, false)), (String ((Ascii (false,
              false, false, false, false, true, false, false)),
              EmptyString))))))))
              (append (String.to_string name0) (String ((Ascii (false, false,
                false, false, false, true, false, false)), (String ((Ascii
                (true, false, true, true, true, true, false, false)),
                EmptyString))))))) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (if needs_block val0
             then PrettyPrinterMonad.append (String ((Ascii (false, false,
                    false, false, false, true, false, false)), (String
                    ((Ascii (true, true, false, true, true, true, true,
                    false)), EmptyString))))
             else ret (Obj.magic coq_Monad_PrettyPrinter) ()) (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (push_indent (add col indent_size)) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (print_term _UU03a3_ remaps0 h _UU0393_ val0) (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent
                    (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (if needs_block val0
                       then bind (Obj.magic coq_Monad_PrettyPrinter)
                              append_nl (fun _ ->
                              PrettyPrinterMonad.append (String ((Ascii
                                (true, false, true, true, true, true, true,
                                false)), (String ((Ascii (true, true, false,
                                true, true, true, false, false)),
                                EmptyString)))))
                       else PrettyPrinterMonad.append (String ((Ascii (true,
                              true, false, true, true, true, false, false)),
                              EmptyString))) (fun _ ->
                      bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                        (fun _ ->
                        bind (Obj.magic coq_Monad_PrettyPrinter)
                          (print_term _UU03a3_ remaps0 h (name0 :: _UU0393_)
                            body) (fun _ -> pop_indent))))))))))))
| Coq_tApp (head, arg) ->
  let rec f head0 args_printed =
    match head0 with
    | Coq_tApp (head1, arg0) ->
      let printed_arg =
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (if needs_block arg0
           then PrettyPrinterMonad.append (String ((Ascii (true, true, false,
                  true, true, true, true, false)), (String ((Ascii (false,
                  false, false, false, false, true, false, false)),
                  EmptyString))))
           else ret (Obj.magic coq_Monad_PrettyPrinter) ()) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (print_term _UU03a3_ remaps0 h _UU0393_ arg0) (fun _ ->
            if needs_block arg0
            then PrettyPrinterMonad.append (String ((Ascii (false, false,
                   false, false, false, true, false, false)), (String ((Ascii
                   (true, false, true, true, true, true, true, false)),
                   EmptyString))))
            else ret (Obj.magic coq_Monad_PrettyPrinter) ()))
      in
      f head1 (printed_arg :: args_printed)
    | Coq_tConst kn -> print_const _UU03a3_ remaps0 h kn args_printed
    | Coq_tConstruct (ind, i, l) ->
      (match l with
       | [] -> print_constructor _UU03a3_ remaps0 h ind i args_printed
       | _ :: _ ->
         printer_fail
           (append (String ((Ascii (true, true, false, false, false, false,
             true, false)), (String ((Ascii (true, true, true, true, false,
             true, true, false)), (String ((Ascii (true, true, false, false,
             true, true, true, false)), (String ((Ascii (false, false, true,
             false, true, true, true, false)), (String ((Ascii (false, true,
             false, false, true, true, true, false)), (String ((Ascii (true,
             false, true, false, true, true, true, false)), (String ((Ascii
             (true, true, false, false, false, true, true, false)), (String
             ((Ascii (false, false, true, false, true, true, true, false)),
             (String ((Ascii (true, true, true, true, false, true, true,
             false)), (String ((Ascii (false, true, false, false, true, true,
             true, false)), (String ((Ascii (true, true, false, false, true,
             true, true, false)), (String ((Ascii (true, false, true, true,
             false, true, false, false)), (String ((Ascii (true, false,
             false, false, false, true, true, false)), (String ((Ascii (true,
             true, false, false, true, true, true, false)), (String ((Ascii
             (true, false, true, true, false, true, false, false)), (String
             ((Ascii (false, true, false, false, false, true, true, false)),
             (String ((Ascii (false, false, true, true, false, true, true,
             false)), (String ((Ascii (true, true, true, true, false, true,
             true, false)), (String ((Ascii (true, true, false, false, false,
             true, true, false)), (String ((Ascii (true, true, false, true,
             false, true, true, false)), (String ((Ascii (true, true, false,
             false, true, true, true, false)), (String ((Ascii (false, false,
             false, false, false, true, false, false)), (String ((Ascii
             (true, false, false, true, false, true, true, false)), (String
             ((Ascii (true, true, false, false, true, true, true, false)),
             (String ((Ascii (false, false, false, false, false, true, false,
             false)), (String ((Ascii (false, true, true, true, false, true,
             true, false)), (String ((Ascii (true, true, true, true, false,
             true, true, false)), (String ((Ascii (false, false, true, false,
             true, true, true, false)), (String ((Ascii (false, false, false,
             false, false, true, false, false)), (String ((Ascii (true, true,
             false, false, true, true, true, false)), (String ((Ascii (true,
             false, true, false, true, true, true, false)), (String ((Ascii
             (false, false, false, false, true, true, true, false)), (String
             ((Ascii (false, false, false, false, true, true, true, false)),
             (String ((Ascii (true, true, true, true, false, true, true,
             false)), (String ((Ascii (false, true, false, false, true, true,
             true, false)), (String ((Ascii (false, false, true, false, true,
             true, true, false)), (String ((Ascii (true, false, true, false,
             false, true, true, false)), (String ((Ascii (false, false, true,
             false, false, true, true, false)), (String ((Ascii (false, true,
             false, true, true, true, false, false)), (String ((Ascii (false,
             false, false, false, false, true, false, false)),
             EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
             (String.to_string (string_of_kername ind.inductive_mind))))
    | _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (PrettyPrinterMonad.append
          (concat EmptyString
            (repeat (String ((Ascii (false, false, false, true, false, true,
              true, false)), (String ((Ascii (true, false, false, true,
              false, true, true, false)), (String ((Ascii (false, true, true,
              true, false, true, true, false)), (String ((Ascii (false,
              false, true, false, true, true, true, false)), (String ((Ascii
              (true, true, true, true, true, false, true, false)), (String
              ((Ascii (true, false, false, false, false, true, true, false)),
              (String ((Ascii (false, false, false, false, true, true, true,
              false)), (String ((Ascii (false, false, false, false, true,
              true, true, false)), (String ((Ascii (false, false, false,
              true, false, true, false, false)),
              EmptyString)))))))))))))))))) (Datatypes.length args_printed))))
        (fun _ ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (if needs_block head0
           then PrettyPrinterMonad.append (String ((Ascii (true, true, false,
                  true, true, true, true, false)), (String ((Ascii (false,
                  false, false, false, false, true, false, false)),
                  EmptyString))))
           else ret (Obj.magic coq_Monad_PrettyPrinter) ()) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (print_term _UU03a3_ remaps0 h _UU0393_ head0) (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (if needs_block head0
               then PrettyPrinterMonad.append (String ((Ascii (false, false,
                      false, false, false, true, false, false)), (String
                      ((Ascii (true, false, true, true, true, true, true,
                      false)), EmptyString))))
               else ret (Obj.magic coq_Monad_PrettyPrinter) ()) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (PrettyPrinterMonad.append (String ((Ascii (true, false,
                  false, true, false, true, false, false)), EmptyString)))
                (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter)
                    (fun pref a ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (PrettyPrinterMonad.append pref) (fun _ ->
                      bind (Obj.magic coq_Monad_PrettyPrinter) a (fun _ ->
                        bind (Obj.magic coq_Monad_PrettyPrinter)
                          (PrettyPrinterMonad.append (String ((Ascii (true,
                            false, false, true, false, true, false, false)),
                            EmptyString))) (fun _ ->
                          ret (Obj.magic coq_Monad_PrettyPrinter) (String
                            ((Ascii (true, false, false, true, false, true,
                            false, false)), (String ((Ascii (false, false,
                            false, true, false, true, false, false)),
                            EmptyString)))))))) args_printed (String ((Ascii
                    (false, false, false, true, false, true, false, false)),
                    EmptyString))) (fun _ ->
                  ret (Obj.magic coq_Monad_PrettyPrinter) ()))))))
  in f head
       ((if needs_block arg
         then bind (Obj.magic coq_Monad_PrettyPrinter)
                (PrettyPrinterMonad.append (String ((Ascii (true, true,
                  false, true, true, true, true, false)), (String ((Ascii
                  (false, false, false, false, false, true, false, false)),
                  EmptyString))))) (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (print_term _UU03a3_ remaps0 h _UU0393_ arg) (fun _ ->
                  PrettyPrinterMonad.append (String ((Ascii (false, false,
                    false, false, false, true, false, false)), (String
                    ((Ascii (true, false, true, true, true, true, true,
                    false)), EmptyString))))))
         else print_term _UU03a3_ remaps0 h _UU0393_ arg) :: [])
| Coq_tConst kn -> print_const _UU03a3_ remaps0 h kn []
| Coq_tConstruct (ind, i, l) ->
  (match l with
   | [] -> print_constructor _UU03a3_ remaps0 h ind i []
   | _ :: _ ->
     printer_fail
       (append (String ((Ascii (true, true, false, false, false, false, true,
         false)), (String ((Ascii (true, true, true, true, false, true, true,
         false)), (String ((Ascii (true, true, false, false, true, true,
         true, false)), (String ((Ascii (false, false, true, false, true,
         true, true, false)), (String ((Ascii (false, true, false, false,
         true, true, true, false)), (String ((Ascii (true, false, true,
         false, true, true, true, false)), (String ((Ascii (true, true,
         false, false, false, true, true, false)), (String ((Ascii (false,
         false, true, false, true, true, true, false)), (String ((Ascii
         (true, true, true, true, false, true, true, false)), (String ((Ascii
         (false, true, false, false, true, true, true, false)), (String
         ((Ascii (true, true, false, false, true, true, true, false)),
         (String ((Ascii (true, false, true, true, false, true, false,
         false)), (String ((Ascii (true, false, false, false, false, true,
         true, false)), (String ((Ascii (true, true, false, false, true,
         true, true, false)), (String ((Ascii (true, false, true, true,
         false, true, false, false)), (String ((Ascii (false, true, false,
         false, false, true, true, false)), (String ((Ascii (false, false,
         true, true, false, true, true, false)), (String ((Ascii (true, true,
         true, true, false, true, true, false)), (String ((Ascii (true, true,
         false, false, false, true, true, false)), (String ((Ascii (true,
         true, false, true, false, true, true, false)), (String ((Ascii
         (true, true, false, false, true, true, true, false)), (String
         ((Ascii (false, false, false, false, false, true, false, false)),
         (String ((Ascii (true, false, false, true, false, true, true,
         false)), (String ((Ascii (true, true, false, false, true, true,
         true, false)), (String ((Ascii (false, false, false, false, false,
         true, false, false)), (String ((Ascii (false, true, true, true,
         false, true, true, false)), (String ((Ascii (true, true, true, true,
         false, true, true, false)), (String ((Ascii (false, false, true,
         false, true, true, true, false)), (String ((Ascii (false, false,
         false, false, false, true, false, false)), (String ((Ascii (true,
         true, false, false, true, true, true, false)), (String ((Ascii
         (true, false, true, false, true, true, true, false)), (String
         ((Ascii (false, false, false, false, true, true, true, false)),
         (String ((Ascii (false, false, false, false, true, true, true,
         false)), (String ((Ascii (true, true, true, true, false, true, true,
         false)), (String ((Ascii (false, true, false, false, true, true,
         true, false)), (String ((Ascii (false, false, true, false, true,
         true, true, false)), (String ((Ascii (true, false, true, false,
         false, true, true, false)), (String ((Ascii (false, false, true,
         false, false, true, true, false)), (String ((Ascii (false, true,
         false, true, true, true, false, false)), (String ((Ascii (false,
         false, false, false, false, true, false, false)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         (String.to_string (string_of_kername ind.inductive_mind))))
| Coq_tCase (p, discr, brs) ->
  let (ind, npars) = p in
  (match brs with
   | [] ->
     PrettyPrinterMonad.append (String ((Ascii (false, false, false, false,
       true, true, true, false)), (String ((Ascii (true, false, false, false,
       false, true, true, false)), (String ((Ascii (false, true, true, true,
       false, true, true, false)), (String ((Ascii (true, false, false, true,
       false, true, true, false)), (String ((Ascii (true, true, false, false,
       false, true, true, false)), (String ((Ascii (true, false, false,
       false, false, true, false, false)), (String ((Ascii (false, false,
       false, true, false, true, false, false)), (String ((Ascii (false,
       true, false, false, false, true, false, false)), (String ((Ascii
       (true, false, false, false, false, false, true, false)), (String
       ((Ascii (false, true, false, false, false, true, true, false)),
       (String ((Ascii (true, true, false, false, true, true, true, false)),
       (String ((Ascii (true, false, true, false, true, true, true, false)),
       (String ((Ascii (false, true, false, false, true, true, true, false)),
       (String ((Ascii (false, false, true, false, false, true, true,
       false)), (String ((Ascii (false, false, false, false, false, true,
       false, false)), (String ((Ascii (true, true, false, false, false,
       true, true, false)), (String ((Ascii (true, false, false, false,
       false, true, true, false)), (String ((Ascii (true, true, false, false,
       true, true, true, false)), (String ((Ascii (true, false, true, false,
       false, true, true, false)), (String ((Ascii (true, false, false,
       false, false, true, false, false)), (String ((Ascii (false, true,
       false, false, false, true, false, false)), (String ((Ascii (true,
       false, false, true, false, true, false, false)),
       EmptyString))))))))))))))))))))))))))))))))))))))))))))
   | _ :: _ ->
     (match remaps0.remap_inductive ind with
      | Some rem ->
        (match rem.re_ind_match with
         | Some s ->
           print_remapped_case _UU03a3_ (print_term _UU03a3_ remaps0 h)
             _UU0393_ ind discr brs (String.to_string s)
         | None ->
           print_case _UU03a3_ remaps0 h (print_term _UU03a3_ remaps0 h)
             _UU0393_ ind npars discr brs)
      | None ->
        print_case _UU03a3_ remaps0 h (print_term _UU03a3_ remaps0 h)
          _UU0393_ ind npars discr brs))
| Coq_tProj (p, _) ->
  let { proj_ind = ind; proj_npars = _; proj_arg = _ } = p in
  printer_fail
    (append (String ((Ascii (true, false, true, false, true, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (false, false, false, true, false, true, true,
      false)), (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (false, false, true, false, false, true, true,
      false)), (String ((Ascii (false, false, true, true, false, true, true,
      false)), (String ((Ascii (true, false, true, false, false, true, true,
      false)), (String ((Ascii (false, false, true, false, false, true, true,
      false)), (String ((Ascii (false, false, false, false, false, true,
      false, false)), (String ((Ascii (false, false, true, false, true, true,
      true, false)), (String ((Ascii (false, false, false, false, true,
      false, true, false)), (String ((Ascii (false, true, false, false, true,
      true, true, false)), (String ((Ascii (true, true, true, true, false,
      true, true, false)), (String ((Ascii (false, true, false, true, false,
      true, true, false)), (String ((Ascii (false, false, false, false,
      false, true, false, false)), (String ((Ascii (true, true, true, true,
      false, true, true, false)), (String ((Ascii (false, true, true, true,
      false, true, true, false)), (String ((Ascii (false, false, false,
      false, false, true, false, false)),
      EmptyString))))))))))))))))))))))))))))))))))))))
      (String.to_string (string_of_kername ind.inductive_mind)))
| Coq_tFix (defs, i) ->
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent col) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter) (fun pat d ->
          let (_UU0393_0, cells) = pat in
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (Obj.magic fresh_ident d.dname _UU0393_0) (fun na ->
            bind (Obj.magic coq_Monad_PrettyPrinter) (push_use na) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (PrettyPrinterMonad.append
                  (append (String ((Ascii (false, false, true, true, false,
                    true, true, false)), (String ((Ascii (true, false, true,
                    false, false, true, true, false)), (String ((Ascii
                    (false, false, true, false, true, true, true, false)),
                    (String ((Ascii (false, false, false, false, false, true,
                    false, false)), EmptyString))))))))
                    (append (String.to_string na) (String ((Ascii (false,
                      false, false, false, false, true, false, false)),
                      (String ((Ascii (true, false, true, true, true, true,
                      false, false)), (String ((Ascii (false, false, false,
                      false, false, true, false, false)), (String ((Ascii
                      (true, true, false, false, true, true, true, false)),
                      (String ((Ascii (true, false, true, false, false, true,
                      true, false)), (String ((Ascii (false, false, true,
                      true, false, true, true, false)), (String ((Ascii
                      (false, true, true, false, false, true, true, false)),
                      (String ((Ascii (false, true, true, true, false, true,
                      false, false)), (String ((Ascii (true, false, false,
                      false, false, true, true, false)), (String ((Ascii
                      (false, false, true, true, false, true, true, false)),
                      (String ((Ascii (false, false, true, true, false, true,
                      true, false)), (String ((Ascii (true, true, true, true,
                      false, true, true, false)), (String ((Ascii (true,
                      true, false, false, false, true, true, false)), (String
                      ((Ascii (false, false, false, true, false, true, false,
                      false)), (String ((Ascii (true, true, false, false,
                      true, true, true, false)), (String ((Ascii (false,
                      false, true, false, true, true, true, false)), (String
                      ((Ascii (false, false, true, false, false, true, true,
                      false)), (String ((Ascii (false, true, false, true,
                      true, true, false, false)), (String ((Ascii (false,
                      true, false, true, true, true, false, false)), (String
                      ((Ascii (true, true, false, false, false, true, true,
                      false)), (String ((Ascii (true, false, true, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, true, false, true, true, false)), (String
                      ((Ascii (false, false, true, true, false, true, true,
                      false)), (String ((Ascii (false, true, false, true,
                      true, true, false, false)), (String ((Ascii (false,
                      true, false, true, true, true, false, false)), (String
                      ((Ascii (true, true, false, false, false, false, true,
                      false)), (String ((Ascii (true, false, true, false,
                      false, true, true, false)), (String ((Ascii (false,
                      false, true, true, false, true, true, false)), (String
                      ((Ascii (false, false, true, true, false, true, true,
                      false)), (String ((Ascii (false, true, false, true,
                      true, true, false, false)), (String ((Ascii (false,
                      true, false, true, true, true, false, false)), (String
                      ((Ascii (false, true, true, true, false, true, true,
                      false)), (String ((Ascii (true, false, true, false,
                      false, true, true, false)), (String ((Ascii (true,
                      true, true, false, true, true, true, false)), (String
                      ((Ascii (false, false, false, true, false, true, false,
                      false)), (String ((Ascii (false, true, true, true,
                      false, false, true, false)), (String ((Ascii (true,
                      true, true, true, false, true, true, false)), (String
                      ((Ascii (false, true, true, true, false, true, true,
                      false)), (String ((Ascii (true, false, true, false,
                      false, true, true, false)), (String ((Ascii (true,
                      false, false, true, false, true, false, false)),
                      (String ((Ascii (true, false, false, true, false, true,
                      false, false)), (String ((Ascii (true, true, false,
                      true, true, true, false, false)),
                      EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
                  ret (Obj.magic coq_Monad_PrettyPrinter)
                    (((String.append na
                        (String.of_string (String ((Ascii (false, true, true,
                          true, false, true, false, false)), (String ((Ascii
                          (true, true, true, false, false, true, true,
                          false)), (String ((Ascii (true, false, true, false,
                          false, true, true, false)), (String ((Ascii (false,
                          false, true, false, true, true, true, false)),
                          (String ((Ascii (false, false, false, true, false,
                          true, false, false)), (String ((Ascii (true, false,
                          false, true, false, true, false, false)), (String
                          ((Ascii (false, true, true, true, false, true,
                          false, false)), (String ((Ascii (true, false, true,
                          false, true, true, true, false)), (String ((Ascii
                          (false, true, true, true, false, true, true,
                          false)), (String ((Ascii (true, true, true, false,
                          true, true, true, false)), (String ((Ascii (false,
                          true, false, false, true, true, true, false)),
                          (String ((Ascii (true, false, false, false, false,
                          true, true, false)), (String ((Ascii (false, false,
                          false, false, true, true, true, false)), (String
                          ((Ascii (false, false, false, true, false, true,
                          false, false)), (String ((Ascii (true, false,
                          false, true, false, true, false, false)),
                          EmptyString)))))))))))))))))))))))))))))))) :: _UU0393_0),
                    (na :: cells))))))) defs (_UU0393_, [])) (fun x ->
        let (_UU0393_0, cells) = x in
        let cells0 = List0.rev cells in
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter) (fun _ pat ->
            let (print_def, cell) = pat in
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (PrettyPrinterMonad.append
                (append cell (String ((Ascii (false, true, true, true, false,
                  true, false, false)), (String ((Ascii (true, true, false,
                  false, true, true, true, false)), (String ((Ascii (true,
                  false, true, false, false, true, true, false)), (String
                  ((Ascii (false, false, true, false, true, true, true,
                  false)), (String ((Ascii (false, false, false, true, false,
                  true, false, false)), (String ((Ascii (true, true, false,
                  false, true, false, true, false)), (String ((Ascii (true,
                  true, true, true, false, true, true, false)), (String
                  ((Ascii (true, false, true, true, false, true, true,
                  false)), (String ((Ascii (true, false, true, false, false,
                  true, true, false)), (String ((Ascii (false, false, false,
                  true, false, true, false, false)),
                  EmptyString)))))))))))))))))))))) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (push_indent (add col indent_size)) (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter) print_def
                    (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (PrettyPrinterMonad.append (String ((Ascii (true,
                        false, false, true, false, true, false, false)),
                        (String ((Ascii (true, false, false, true, false,
                        true, false, false)), (String ((Ascii (true, true,
                        false, true, true, true, false, false)),
                        EmptyString))))))) (fun _ ->
                      bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent
                        (fun _ -> append_nl)))))))
            (combine
              (map (fun d -> print_term _UU03a3_ remaps0 h _UU0393_0 d.dbody)
                defs) (map String.to_string cells0)) ()) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (PrettyPrinterMonad.append
              (append
                (String.to_string
                  (nth i cells0 (String.of_string EmptyString))) (String
                ((Ascii (false, true, true, true, false, true, false,
                false)), (String ((Ascii (true, true, true, false, false,
                true, true, false)), (String ((Ascii (true, false, true,
                false, false, true, true, false)), (String ((Ascii (false,
                false, true, false, true, true, true, false)), (String
                ((Ascii (false, false, false, true, false, true, false,
                false)), (String ((Ascii (true, false, false, true, false,
                true, false, false)), (String ((Ascii (false, true, true,
                true, false, true, false, false)), (String ((Ascii (true,
                false, true, false, true, true, true, false)), (String
                ((Ascii (false, true, true, true, false, true, true, false)),
                (String ((Ascii (true, true, true, false, true, true, true,
                false)), (String ((Ascii (false, true, false, false, true,
                true, true, false)), (String ((Ascii (true, false, false,
                false, false, true, true, false)), (String ((Ascii (false,
                false, false, false, true, true, true, false)), (String
                ((Ascii (false, false, false, true, false, true, false,
                false)), (String ((Ascii (true, false, false, true, false,
                true, false, false)),
                EmptyString)))))))))))))))))))))))))))))))) (fun _ ->
            pop_indent)))))
| Coq_tCoFix (_, _) ->
  printer_fail (String ((Ascii (true, true, false, false, false, false, true,
    false)), (String ((Ascii (true, false, false, false, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (true, true, true, true, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (false, false, false, true, false, true, true,
    false)), (String ((Ascii (true, false, false, false, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (false, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, true, true, false, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (true, true, false, false, false, false, true,
    false)), (String ((Ascii (true, true, true, true, false, true, true,
    false)), (String ((Ascii (false, true, true, false, false, false, true,
    false)), (String ((Ascii (true, false, false, true, false, true, true,
    false)), (String ((Ascii (false, false, false, true, true, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (true, false, false, true, true, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), EmptyString))))))))))))))))))))))))))))))))))))))))))))))))
| Coq_tPrim _ ->
  printer_fail (String ((Ascii (true, true, false, false, false, false, true,
    false)), (String ((Ascii (true, false, false, false, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (true, true, true, true, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (false, false, false, true, false, true, true,
    false)), (String ((Ascii (true, false, false, false, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (false, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, true, true, false, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (true, true, false, false, false, false, true,
    false)), (String ((Ascii (true, true, true, true, false, true, true,
    false)), (String ((Ascii (true, false, false, false, true, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (false, false, false, false, true, true, true,
    false)), (String ((Ascii (false, true, false, false, true, true, true,
    false)), (String ((Ascii (true, false, false, true, false, true, true,
    false)), (String ((Ascii (true, false, true, true, false, true, true,
    false)), (String ((Ascii (true, false, false, true, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (true, false, false, true, false, true, true,
    false)), (String ((Ascii (false, true, true, false, true, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (true, false, false, true, true, true, true,
    false)), (String ((Ascii (false, false, false, false, true, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (true, true, false, false, true, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (true, false, false, true, true, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)),
    EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val print_constant :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> kername -> (name
    list * box_type) -> E.term -> unit coq_PrettyPrinter **)

let print_constant _UU03a3_ remaps0 h kn type0 body =
  let rname = const_global_ident_of_kername h kn in
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun name_col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent name_col) (fun _ ->
      let (type_vars, ty) = type0 in
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter)
          (fun _UU0393_ty name0 ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (Obj.magic fresh_ty_arg_name name0 _UU0393_ty) (fun name1 ->
            ret (Obj.magic coq_Monad_PrettyPrinter)
              (app _UU0393_ty (name1 :: [])))) type_vars [])
        (fun _UU0393_ty ->
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (match remaps0.remap_constant kn with
           | Some s ->
             PrettyPrinterMonad.append
               (replace (String ((Ascii (true, true, false, false, false,
                 true, false, false)), (String ((Ascii (true, true, false,
                 false, false, true, false, false)), (String ((Ascii (false,
                 true, true, true, false, true, true, false)), (String
                 ((Ascii (true, false, false, false, false, true, true,
                 false)), (String ((Ascii (true, false, true, true, false,
                 true, true, false)), (String ((Ascii (true, false, true,
                 false, false, true, true, false)), (String ((Ascii (true,
                 true, false, false, false, true, false, false)), (String
                 ((Ascii (true, true, false, false, false, true, false,
                 false)), EmptyString)))))))))))))))) rname
                 (String.to_string s))
           | None ->
             (match remaps0.remap_inline_constant kn with
              | Some _ -> ret (Obj.magic coq_Monad_PrettyPrinter) ()
              | None ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (PrettyPrinterMonad.append
                    (append (String ((Ascii (false, true, true, false, false,
                      true, true, false)), (String ((Ascii (false, true,
                      true, true, false, true, true, false)), (String ((Ascii
                      (false, false, false, false, false, true, false,
                      false)), EmptyString)))))) rname)) (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter)
                    (print_parenthesized_with (String ((Ascii (false, false,
                      true, true, true, true, false, false)), EmptyString))
                      (String ((Ascii (false, true, true, true, true, true,
                      false, false)), EmptyString))
                      (Nat.ltb O (Datatypes.length _UU0393_ty))
                      (append_join (String ((Ascii (false, false, true, true,
                        false, true, false, false)), (String ((Ascii (false,
                        false, false, false, false, true, false, false)),
                        EmptyString))))
                        (map (fun na ->
                          append na (String ((Ascii (false, true, false,
                            true, true, true, false, false)), (String ((Ascii
                            (false, false, false, false, false, true, false,
                            false)), (String ((Ascii (true, true, false,
                            false, false, false, true, false)), (String
                            ((Ascii (true, true, true, true, false, true,
                            true, false)), (String ((Ascii (false, false,
                            false, false, true, true, true, false)), (String
                            ((Ascii (true, false, false, true, true, true,
                            true, false)), EmptyString)))))))))))))
                          (map String.to_string _UU0393_ty)))) (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (PrettyPrinterMonad.append (String ((Ascii (false,
                        false, false, true, false, true, false, false)),
                        (String ((Ascii (false, true, true, false, false,
                        true, false, false)), (String ((Ascii (true, true,
                        true, false, false, true, false, false)), (String
                        ((Ascii (true, false, false, false, false, true,
                        true, false)), (String ((Ascii (false, false, false,
                        false, false, true, false, false)), (String ((Ascii
                        (true, true, false, false, true, true, true, false)),
                        (String ((Ascii (true, false, true, false, false,
                        true, true, false)), (String ((Ascii (false, false,
                        true, true, false, true, true, false)), (String
                        ((Ascii (false, true, true, false, false, true, true,
                        false)), EmptyString))))))))))))))))))) (fun _ ->
                      let rec print_top _UU0393_ body0 ty0 =
                        match body0 with
                        | Coq_tLambda (na, body1) ->
                          (match ty0 with
                           | TArr (dom, cod) ->
                             bind (Obj.magic coq_Monad_PrettyPrinter)
                               (Obj.magic fresh_ident na _UU0393_)
                               (fun na0 ->
                               bind (Obj.magic coq_Monad_PrettyPrinter)
                                 (PrettyPrinterMonad.append
                                   (append (String ((Ascii (false, false,
                                     true, true, false, true, false, false)),
                                     (String ((Ascii (false, false, false,
                                     false, false, true, false, false)),
                                     EmptyString))))
                                     (append (String.to_string na0) (String
                                       ((Ascii (false, true, false, true,
                                       true, true, false, false)), (String
                                       ((Ascii (false, false, false, false,
                                       false, true, false, false)),
                                       EmptyString))))))) (fun _ ->
                                 bind (Obj.magic coq_Monad_PrettyPrinter)
                                   (print_type _UU03a3_ remaps0 h _UU0393_ty
                                     dom) (fun _ ->
                                   print_top (na0 :: _UU0393_) body1 cod)))
                           | _ ->
                             bind (Obj.magic coq_Monad_PrettyPrinter)
                               (PrettyPrinterMonad.append (String ((Ascii
                                 (true, false, false, true, false, true,
                                 false, false)), (String ((Ascii (false,
                                 false, false, false, false, true, false,
                                 false)), (String ((Ascii (true, false, true,
                                 true, false, true, false, false)), (String
                                 ((Ascii (false, true, true, true, true,
                                 true, false, false)), (String ((Ascii
                                 (false, false, false, false, false, true,
                                 false, false)), EmptyString)))))))))))
                               (fun _ ->
                               bind (Obj.magic coq_Monad_PrettyPrinter)
                                 (print_type _UU03a3_ remaps0 h _UU0393_ty
                                   ty0) (fun _ ->
                                 bind (Obj.magic coq_Monad_PrettyPrinter)
                                   (PrettyPrinterMonad.append (String ((Ascii
                                     (false, false, false, false, false,
                                     true, false, false)), (String ((Ascii
                                     (true, true, false, true, true, true,
                                     true, false)), EmptyString)))))
                                   (fun _ ->
                                   bind (Obj.magic coq_Monad_PrettyPrinter)
                                     (push_indent (add name_col indent_size))
                                     (fun _ ->
                                     bind (Obj.magic coq_Monad_PrettyPrinter)
                                       append_nl (fun _ ->
                                       bind
                                         (Obj.magic coq_Monad_PrettyPrinter)
                                         (push_use (String.of_string rname))
                                         (fun _ ->
                                         bind
                                           (Obj.magic coq_Monad_PrettyPrinter)
                                           (print_term _UU03a3_ remaps0 h
                                             _UU0393_ body0) (fun _ ->
                                           bind
                                             (Obj.magic
                                               coq_Monad_PrettyPrinter)
                                             pop_indent (fun _ ->
                                             bind
                                               (Obj.magic
                                                 coq_Monad_PrettyPrinter)
                                               append_nl (fun _ ->
                                               PrettyPrinterMonad.append
                                                 (String ((Ascii (true,
                                                 false, true, true, true,
                                                 true, true, false)),
                                                 EmptyString))))))))))))
                        | _ ->
                          bind (Obj.magic coq_Monad_PrettyPrinter)
                            (PrettyPrinterMonad.append (String ((Ascii (true,
                              false, false, true, false, true, false,
                              false)), (String ((Ascii (false, false, false,
                              false, false, true, false, false)), (String
                              ((Ascii (true, false, true, true, false, true,
                              false, false)), (String ((Ascii (false, true,
                              true, true, true, true, false, false)), (String
                              ((Ascii (false, false, false, false, false,
                              true, false, false)), EmptyString)))))))))))
                            (fun _ ->
                            bind (Obj.magic coq_Monad_PrettyPrinter)
                              (print_type _UU03a3_ remaps0 h _UU0393_ty ty0)
                              (fun _ ->
                              bind (Obj.magic coq_Monad_PrettyPrinter)
                                (PrettyPrinterMonad.append (String ((Ascii
                                  (false, false, false, false, false, true,
                                  false, false)), (String ((Ascii (true,
                                  true, false, true, true, true, true,
                                  false)), EmptyString))))) (fun _ ->
                                bind (Obj.magic coq_Monad_PrettyPrinter)
                                  (push_indent (add name_col indent_size))
                                  (fun _ ->
                                  bind (Obj.magic coq_Monad_PrettyPrinter)
                                    append_nl (fun _ ->
                                    bind (Obj.magic coq_Monad_PrettyPrinter)
                                      (push_use (String.of_string rname))
                                      (fun _ ->
                                      bind
                                        (Obj.magic coq_Monad_PrettyPrinter)
                                        (print_term _UU03a3_ remaps0 h
                                          _UU0393_ body0) (fun _ ->
                                        bind
                                          (Obj.magic coq_Monad_PrettyPrinter)
                                          pop_indent (fun _ ->
                                          bind
                                            (Obj.magic
                                              coq_Monad_PrettyPrinter)
                                            append_nl (fun _ ->
                                            PrettyPrinterMonad.append (String
                                              ((Ascii (true, false, true,
                                              true, true, true, true,
                                              false)), EmptyString)))))))))))
                      in print_top [] body ty))))) (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (Obj.magic get_num_inline_args _UU03a3_ kn)
            (fun num_inline_args ->
            bind (Obj.magic coq_Monad_PrettyPrinter)
              (if Nat.ltb O num_inline_args
               then bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                      (fun _ ->
                      bind (Obj.magic coq_Monad_PrettyPrinter)
                        (PrettyPrinterMonad.append
                          (append (String ((Ascii (false, true, true, false,
                            false, true, true, false)), (String ((Ascii
                            (false, true, true, true, false, true, true,
                            false)), (String ((Ascii (false, false, false,
                            false, false, true, false, false)),
                            EmptyString))))))
                            (append rname (String ((Ascii (true, true, true,
                              true, true, false, true, false)), (String
                              ((Ascii (true, true, true, true, true, false,
                              true, false)), (String ((Ascii (true, true,
                              false, false, false, true, true, false)),
                              (String ((Ascii (true, false, true, false,
                              true, true, true, false)), (String ((Ascii
                              (false, true, false, false, true, true, true,
                              false)), (String ((Ascii (false, true, false,
                              false, true, true, true, false)), (String
                              ((Ascii (true, false, false, true, false, true,
                              true, false)), (String ((Ascii (true, false,
                              true, false, false, true, true, false)),
                              (String ((Ascii (false, false, true, false,
                              false, true, true, false)),
                              EmptyString))))))))))))))))))))) (fun _ ->
                        bind (Obj.magic coq_Monad_PrettyPrinter)
                          (print_parenthesized_with (String ((Ascii (false,
                            false, true, true, true, true, false, false)),
                            EmptyString)) (String ((Ascii (false, true, true,
                            true, true, true, false, false)), EmptyString))
                            (Nat.ltb O (Datatypes.length _UU0393_ty))
                            (append_join (String ((Ascii (false, false, true,
                              true, false, true, false, false)), (String
                              ((Ascii (false, false, false, false, false,
                              true, false, false)), EmptyString))))
                              (map (fun na ->
                                append na (String ((Ascii (false, true,
                                  false, true, true, true, false, false)),
                                  (String ((Ascii (false, false, false,
                                  false, false, true, false, false)), (String
                                  ((Ascii (true, true, false, false, false,
                                  false, true, false)), (String ((Ascii
                                  (true, true, true, true, false, true, true,
                                  false)), (String ((Ascii (false, false,
                                  false, false, true, true, true, false)),
                                  (String ((Ascii (true, false, false, true,
                                  true, true, true, false)),
                                  EmptyString)))))))))))))
                                (map String.to_string _UU0393_ty))))
                          (fun _ ->
                          bind (Obj.magic coq_Monad_PrettyPrinter)
                            (PrettyPrinterMonad.append (String ((Ascii
                              (false, false, false, true, false, true, false,
                              false)), (String ((Ascii (false, true, true,
                              false, false, true, false, false)), (String
                              ((Ascii (true, true, true, false, false, true,
                              false, false)), (String ((Ascii (true, false,
                              false, false, false, true, true, false)),
                              (String ((Ascii (false, false, false, false,
                              false, true, false, false)), (String ((Ascii
                              (true, true, false, false, true, true, true,
                              false)), (String ((Ascii (true, false, true,
                              false, false, true, true, false)), (String
                              ((Ascii (false, false, true, true, false, true,
                              true, false)), (String ((Ascii (false, true,
                              true, false, false, true, true, false)),
                              (String ((Ascii (true, false, false, true,
                              false, true, false, false)), (String ((Ascii
                              (false, false, false, false, false, true,
                              false, false)), (String ((Ascii (true, false,
                              true, true, false, true, false, false)),
                              (String ((Ascii (false, true, true, true, true,
                              true, false, false)), (String ((Ascii (false,
                              false, false, false, false, true, false,
                              false)),
                              EmptyString)))))))))))))))))))))))))))))
                            (fun _ ->
                            bind (Obj.magic coq_Monad_PrettyPrinter)
                              (print_type _UU03a3_ remaps0 h _UU0393_ty ty)
                              (fun _ ->
                              bind (Obj.magic coq_Monad_PrettyPrinter)
                                (PrettyPrinterMonad.append (String ((Ascii
                                  (false, false, false, false, false, true,
                                  false, false)), (String ((Ascii (true,
                                  true, false, true, true, true, true,
                                  false)), EmptyString))))) (fun _ ->
                                bind (Obj.magic coq_Monad_PrettyPrinter)
                                  (push_indent (add name_col indent_size))
                                  (fun _ ->
                                  bind (Obj.magic coq_Monad_PrettyPrinter)
                                    append_nl (fun _ ->
                                    bind (Obj.magic coq_Monad_PrettyPrinter)
                                      (push_use
                                        (String.of_string
                                          (append rname (String ((Ascii
                                            (true, true, true, true, true,
                                            false, true, false)), (String
                                            ((Ascii (true, true, true, true,
                                            true, false, true, false)),
                                            (String ((Ascii (true, true,
                                            false, false, false, true, true,
                                            false)), (String ((Ascii (true,
                                            false, true, false, true, true,
                                            true, false)), (String ((Ascii
                                            (false, true, false, false, true,
                                            true, true, false)), (String
                                            ((Ascii (false, true, false,
                                            false, true, true, true, false)),
                                            (String ((Ascii (true, false,
                                            false, true, false, true, true,
                                            false)), (String ((Ascii (true,
                                            false, true, false, false, true,
                                            true, false)), (String ((Ascii
                                            (false, false, true, false,
                                            false, true, true, false)),
                                            EmptyString)))))))))))))))))))))
                                      (fun _ ->
                                      bind
                                        (Obj.magic coq_Monad_PrettyPrinter)
                                        (let rec make_eta_term n body0 ty0 =
                                           match body0 with
                                           | Coq_tLambda (na, body1) ->
                                             (match ty0 with
                                              | TArr (_, cod) ->
                                                bind
                                                  (Obj.magic
                                                    coq_Monad_PrettyPrinter)
                                                  (make_eta_term (S n) body1
                                                    cod) (fun eta_term ->
                                                  ret
                                                    (Obj.magic
                                                      coq_Monad_PrettyPrinter)
                                                    (Coq_tLambda (na,
                                                    eta_term)))
                                              | _ ->
                                                ret
                                                  (Obj.magic
                                                    coq_Monad_PrettyPrinter)
                                                  (mkApps (Coq_tConst kn)
                                                    (rev_map (fun x ->
                                                      Coq_tRel x) (seq O n))))
                                           | _ ->
                                             ret
                                               (Obj.magic
                                                 coq_Monad_PrettyPrinter)
                                               (mkApps (Coq_tConst kn)
                                                 (rev_map (fun x -> Coq_tRel
                                                   x) (seq O n)))
                                         in make_eta_term O body ty)
                                        (fun eta_term ->
                                        bind
                                          (Obj.magic coq_Monad_PrettyPrinter)
                                          (print_term _UU03a3_ remaps0 h []
                                            eta_term) (fun _ ->
                                          bind
                                            (Obj.magic
                                              coq_Monad_PrettyPrinter)
                                            pop_indent (fun _ ->
                                            bind
                                              (Obj.magic
                                                coq_Monad_PrettyPrinter)
                                              append_nl (fun _ ->
                                              PrettyPrinterMonad.append
                                                (String ((Ascii (true, false,
                                                true, true, true, true, true,
                                                false)), EmptyString)))))))))))))))
               else ret (Obj.magic coq_Monad_PrettyPrinter) ()) (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent (fun _ ->
                ret (Obj.magic coq_Monad_PrettyPrinter) ())))))))

(** val print_ind_ctor_definition :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ident list -> ident ->
    (name * box_type) list -> unit coq_PrettyPrinter **)

let print_ind_ctor_definition _UU03a3_ remaps0 h _UU0393_ ctor_name data =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (PrettyPrinterMonad.append
      (clean_global_ident (String.to_string ctor_name))) (fun _ ->
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (PrettyPrinterMonad.append (String ((Ascii (false, false, false, true,
        false, true, false, false)), EmptyString))) (fun _ ->
      let print_phantom =
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (PrettyPrinterMonad.append (String ((Ascii (false, false, false,
            false, true, false, true, false)), (String ((Ascii (false, false,
            false, true, false, true, true, false)), (String ((Ascii (true,
            false, false, false, false, true, true, false)), (String ((Ascii
            (false, true, true, true, false, true, true, false)), (String
            ((Ascii (false, false, true, false, true, true, true, false)),
            (String ((Ascii (true, true, true, true, false, true, true,
            false)), (String ((Ascii (true, false, true, true, false, true,
            true, false)), (String ((Ascii (false, false, true, false, false,
            false, true, false)), (String ((Ascii (true, false, false, false,
            false, true, true, false)), (String ((Ascii (false, false, true,
            false, true, true, true, false)), (String ((Ascii (true, false,
            false, false, false, true, true, false)), (String ((Ascii (false,
            false, true, true, true, true, false, false)), (String ((Ascii
            (false, true, true, false, false, true, false, false)), (String
            ((Ascii (true, true, true, false, false, true, false, false)),
            (String ((Ascii (true, false, false, false, false, true, true,
            false)), (String ((Ascii (false, false, false, false, false,
            true, false, false)), EmptyString)))))))))))))))))))))))))))))))))
          (fun _ ->
          bind (Obj.magic coq_Monad_PrettyPrinter)
            (if Nat.eqb (Datatypes.length _UU0393_) O
             then PrettyPrinterMonad.append (String ((Ascii (false, false,
                    false, true, false, true, false, false)), (String ((Ascii
                    (true, false, false, true, false, true, false, false)),
                    EmptyString))))
             else print_parenthesized
                    (Nat.ltb (S O) (Datatypes.length _UU0393_))
                    (append_join (String ((Ascii (false, false, true, true,
                      false, true, false, false)), (String ((Ascii (false,
                      false, false, false, false, true, false, false)),
                      EmptyString)))) (map String.to_string _UU0393_)))
            (fun _ ->
            PrettyPrinterMonad.append (String ((Ascii (false, true, true,
              true, true, true, false, false)), EmptyString))))
      in
      let print_datas =
        print_phantom :: (map
                           (compose (print_type _UU03a3_ remaps0 h _UU0393_)
                             snd) data)
      in
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (monad_append_join
          (PrettyPrinterMonad.append (String ((Ascii (false, false, true,
            true, false, true, false, false)), (String ((Ascii (false, false,
            false, false, false, true, false, false)), EmptyString)))))
          print_datas) (fun _ ->
        PrettyPrinterMonad.append (String ((Ascii (true, false, false, true,
          false, true, false, false)), EmptyString)))))

(** val print_mutual_inductive_body :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ind_attr_map -> kername
    -> Ex.mutual_inductive_body -> unit coq_PrettyPrinter **)

let print_mutual_inductive_body _UU03a3_ remaps0 h ind_attrs kn mib =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent col) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (let rec print_ind_bodies l prefix i =
           match l with
           | [] -> ret (Obj.magic coq_Monad_PrettyPrinter) ()
           | oib :: l0 ->
             bind (Obj.magic coq_Monad_PrettyPrinter) (Obj.magic prefix)
               (fun _ ->
               bind (Obj.magic coq_Monad_PrettyPrinter)
                 (PrettyPrinterMonad.append
                   (ind_attrs { inductive_mind = kn; inductive_ind = i }))
                 (fun _ ->
                 bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
                   bind (Obj.magic coq_Monad_PrettyPrinter)
                     (PrettyPrinterMonad.append (String ((Ascii (false,
                       false, false, false, true, true, true, false)),
                       (String ((Ascii (true, false, true, false, true, true,
                       true, false)), (String ((Ascii (false, true, false,
                       false, false, true, true, false)), (String ((Ascii
                       (false, false, false, false, false, true, false,
                       false)), (String ((Ascii (true, false, true, false,
                       false, true, true, false)), (String ((Ascii (false,
                       true, true, true, false, true, true, false)), (String
                       ((Ascii (true, false, true, false, true, true, true,
                       false)), (String ((Ascii (true, false, true, true,
                       false, true, true, false)), (String ((Ascii (false,
                       false, false, false, false, true, false, false)),
                       EmptyString))))))))))))))))))) (fun _ ->
                     bind (Obj.magic coq_Monad_PrettyPrinter)
                       (print_ind _UU03a3_ remaps0 h { inductive_mind = kn;
                         inductive_ind = i }) (fun _ ->
                       bind (Obj.magic coq_Monad_PrettyPrinter)
                         (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter)
                           (fun _UU0393_ name0 ->
                           bind (Obj.magic coq_Monad_PrettyPrinter)
                             (Obj.magic fresh_ty_arg_name name0.tvar_name
                               _UU0393_) (fun name1 ->
                             ret (Obj.magic coq_Monad_PrettyPrinter)
                               (app _UU0393_ (name1 :: []))))
                           oib.ind_type_vars []) (fun _UU0393_ ->
                         bind (Obj.magic coq_Monad_PrettyPrinter)
                           (PrettyPrinterMonad.append (String ((Ascii (false,
                             false, true, true, true, true, false, false)),
                             EmptyString))) (fun _ ->
                           bind (Obj.magic coq_Monad_PrettyPrinter)
                             (append_join (String ((Ascii (false, false,
                               true, true, false, true, false, false)),
                               (String ((Ascii (false, false, false, false,
                               false, true, false, false)), EmptyString))))
                               ((String ((Ascii (true, true, true, false,
                               false, true, false, false)), (String ((Ascii
                               (true, false, false, false, false, true, true,
                               false)),
                               EmptyString)))) :: (map String.to_string
                                                    _UU0393_))) (fun _ ->
                             bind (Obj.magic coq_Monad_PrettyPrinter)
                               (PrettyPrinterMonad.append (String ((Ascii
                                 (false, true, true, true, true, true, false,
                                 false)), (String ((Ascii (false, false,
                                 false, false, false, true, false, false)),
                                 (String ((Ascii (true, true, false, true,
                                 true, true, true, false)), EmptyString)))))))
                               (fun _ ->
                               bind (Obj.magic coq_Monad_PrettyPrinter)
                                 (push_indent (add col indent_size))
                                 (fun _ ->
                                 bind (Obj.magic coq_Monad_PrettyPrinter)
                                   append_nl (fun _ ->
                                   bind (Obj.magic coq_Monad_PrettyPrinter)
                                     (monad_append_join
                                       (bind
                                         (Obj.magic coq_Monad_PrettyPrinter)
                                         (PrettyPrinterMonad.append (String
                                           ((Ascii (false, false, true, true,
                                           false, true, false, false)),
                                           EmptyString))) (fun _ ->
                                         append_nl))
                                       (map (fun pat ->
                                         let (y, _) = pat in
                                         let (name0, data) = y in
                                         print_ind_ctor_definition _UU03a3_
                                           remaps0 h _UU0393_ name0 data)
                                         (Ex.ind_ctors oib))) (fun _ ->
                                     bind (Obj.magic coq_Monad_PrettyPrinter)
                                       pop_indent (fun _ ->
                                       bind
                                         (Obj.magic coq_Monad_PrettyPrinter)
                                         append_nl (fun _ ->
                                         bind
                                           (Obj.magic coq_Monad_PrettyPrinter)
                                           (PrettyPrinterMonad.append (String
                                             ((Ascii (true, false, true,
                                             true, true, true, true, false)),
                                             EmptyString))) (fun _ ->
                                           Obj.magic print_ind_bodies l0
                                             append_nl (S i))))))))))))))))
         in print_ind_bodies (Ex.ind_bodies mib)
              (ret coq_Monad_PrettyPrinter ()) O) (fun names ->
        bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent (fun _ ->
          ret (Obj.magic coq_Monad_PrettyPrinter) names))))

(** val print_type_alias :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> kername ->
    type_var_info list -> box_type -> unit coq_PrettyPrinter **)

let print_type_alias _UU03a3_ remaps0 h nm tvars bt =
  let rname = ty_const_global_ident_of_kername h nm in
  (match remaps0.remap_constant nm with
   | Some s ->
     PrettyPrinterMonad.append
       (replace (String ((Ascii (true, true, false, false, false, true,
         false, false)), (String ((Ascii (true, true, false, false, false,
         true, false, false)), (String ((Ascii (false, true, true, true,
         false, true, true, false)), (String ((Ascii (true, false, false,
         false, false, true, true, false)), (String ((Ascii (true, false,
         true, true, false, true, true, false)), (String ((Ascii (true,
         false, true, false, false, true, true, false)), (String ((Ascii
         (true, true, false, false, false, true, false, false)), (String
         ((Ascii (true, true, false, false, false, true, false, false)),
         EmptyString)))))))))))))))) (String.to_string rname)
         (String.to_string s))
   | None ->
     bind (Obj.magic coq_Monad_PrettyPrinter)
       (PrettyPrinterMonad.append
         (append (String ((Ascii (false, false, true, false, true, true,
           true, false)), (String ((Ascii (true, false, false, true, true,
           true, true, false)), (String ((Ascii (false, false, false, false,
           true, true, true, false)), (String ((Ascii (true, false, true,
           false, false, true, true, false)), (String ((Ascii (false, false,
           false, false, false, true, false, false)), EmptyString))))))))))
           (append (String.to_string rname) (String ((Ascii (false, false,
             true, true, true, true, false, false)), EmptyString)))))
       (fun _ ->
       bind (Obj.magic coq_Monad_PrettyPrinter)
         (monad_fold_left (Obj.magic coq_Monad_PrettyPrinter)
           (fun _UU0393_ tvar ->
           bind (Obj.magic coq_Monad_PrettyPrinter)
             (Obj.magic fresh_ty_arg_name tvar.tvar_name _UU0393_)
             (fun name0 ->
             ret (Obj.magic coq_Monad_PrettyPrinter) (name0 :: _UU0393_)))
           tvars []) (fun _UU0393_rev ->
         let _UU0393_ = List0.rev _UU0393_rev in
         bind (Obj.magic coq_Monad_PrettyPrinter)
           (append_join (String ((Ascii (false, false, true, true, false,
             true, false, false)), (String ((Ascii (false, false, false,
             false, false, true, false, false)), EmptyString)))) ((String
             ((Ascii (true, true, true, false, false, true, false, false)),
             (String ((Ascii (true, false, false, false, false, true, true,
             false)), EmptyString)))) :: (map String.to_string _UU0393_)))
           (fun _ ->
           bind (Obj.magic coq_Monad_PrettyPrinter)
             (PrettyPrinterMonad.append (String ((Ascii (false, true, true,
               true, true, true, false, false)), (String ((Ascii (false,
               false, false, false, false, true, false, false)), (String
               ((Ascii (true, false, true, true, true, true, false, false)),
               (String ((Ascii (false, false, false, false, false, true,
               false, false)), EmptyString))))))))) (fun _ ->
             bind (Obj.magic coq_Monad_PrettyPrinter)
               (print_type _UU03a3_ remaps0 h _UU0393_ bt) (fun _ ->
               PrettyPrinterMonad.append (String ((Ascii (true, true, false,
                 true, true, true, false, false)), EmptyString))))))))

(** val print_decls_aux :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ind_attr_map ->
    ((kername * bool) * Ex.global_decl) list -> unit coq_PrettyPrinter ->
    unit coq_PrettyPrinter **)

let rec print_decls_aux _UU03a3_ remaps0 h ind_attrs decls prefix =
  match decls with
  | [] -> ret (Obj.magic coq_Monad_PrettyPrinter) ()
  | p :: decls0 ->
    let (p0, decl) = p in
    let (kn, _) = p0 in
    bind (Obj.magic coq_Monad_PrettyPrinter)
      (match decl with
       | Ex.ConstantDecl c ->
         let { Ex.cst_type = type0; Ex.cst_body = cst_body0 } = c in
         (match cst_body0 with
          | Some body ->
            bind (Obj.magic coq_Monad_PrettyPrinter) prefix (fun _ ->
              print_constant _UU03a3_ remaps0 h kn type0 body)
          | None -> ret (Obj.magic coq_Monad_PrettyPrinter) ())
       | Ex.InductiveDecl mib ->
         (match remaps0.remap_inductive { inductive_mind = kn;
                  inductive_ind = O } with
          | Some _ -> ret (Obj.magic coq_Monad_PrettyPrinter) ()
          | None ->
            bind (Obj.magic coq_Monad_PrettyPrinter) prefix (fun _ ->
              print_mutual_inductive_body _UU03a3_ remaps0 h ind_attrs kn mib))
       | Ex.TypeAliasDecl o ->
         (match o with
          | Some p1 ->
            let (tvars, bt) = p1 in
            bind (Obj.magic coq_Monad_PrettyPrinter) prefix (fun _ ->
              print_type_alias _UU03a3_ remaps0 h kn tvars bt)
          | None -> ret (Obj.magic coq_Monad_PrettyPrinter) ())) (fun _ ->
      print_decls_aux _UU03a3_ remaps0 h ind_attrs decls0
        (bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
          append_nl)))

type coq_Preamble = { top_preamble : string list;
                      program_preamble : string list }

(** val print_program :
    Ex.global_env -> remaps -> coq_RustPrintConfig -> ind_attr_map ->
    coq_Preamble -> unit coq_PrettyPrinter **)

let print_program _UU03a3_ remaps0 h ind_attrs h0 =
  bind (Obj.magic coq_Monad_PrettyPrinter)
    (Obj.magic get_current_line_length) (fun sig_col ->
    bind (Obj.magic coq_Monad_PrettyPrinter) (push_indent sig_col) (fun _ ->
      bind (Obj.magic coq_Monad_PrettyPrinter)
        (monad_append_join append_nl
          (map PrettyPrinterMonad.append h0.top_preamble)) (fun _ ->
        let is_const = fun pat ->
          let (_, decl) = pat in
          (match decl with
           | Ex.ConstantDecl _ -> true
           | _ -> false)
        in
        let _UU03a3_0 =
          filter (fun pat -> let (_, d) = pat in negb (is_empty_type_decl d))
            _UU03a3_
        in
        bind (Obj.magic coq_Monad_PrettyPrinter)
          (print_decls_aux _UU03a3_ remaps0 h ind_attrs
            (filter (compose negb is_const) (List0.rev _UU03a3_0))
            (bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
              append_nl))) (fun _ ->
          let constants =
            flat_map (fun pat ->
              let (y, decl) = pat in
              (match decl with
               | Ex.ConstantDecl cst -> (y, cst) :: []
               | _ -> [])) (List0.rev _UU03a3_0)
          in
          bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
            bind (Obj.magic coq_Monad_PrettyPrinter) append_nl (fun _ ->
              bind (Obj.magic coq_Monad_PrettyPrinter)
                (push_indent (add sig_col indent_size)) (fun _ ->
                bind (Obj.magic coq_Monad_PrettyPrinter)
                  (PrettyPrinterMonad.append (String ((Ascii (true, true,
                    false, false, true, true, true, false)), (String ((Ascii
                    (false, false, true, false, true, true, true, false)),
                    (String ((Ascii (false, true, false, false, true, true,
                    true, false)), (String ((Ascii (true, false, true, false,
                    true, true, true, false)), (String ((Ascii (true, true,
                    false, false, false, true, true, false)), (String ((Ascii
                    (false, false, true, false, true, true, true, false)),
                    (String ((Ascii (false, false, false, false, false, true,
                    false, false)), (String ((Ascii (false, false, false,
                    false, true, false, true, false)), (String ((Ascii
                    (false, true, false, false, true, true, true, false)),
                    (String ((Ascii (true, true, true, true, false, true,
                    true, false)), (String ((Ascii (true, true, true, false,
                    false, true, true, false)), (String ((Ascii (false, true,
                    false, false, true, true, true, false)), (String ((Ascii
                    (true, false, false, false, false, true, true, false)),
                    (String ((Ascii (true, false, true, true, false, true,
                    true, false)), (String ((Ascii (false, false, false,
                    false, false, true, false, false)), (String ((Ascii
                    (true, true, false, true, true, true, true, false)),
                    EmptyString))))))))))))))))))))))))))))))))) (fun _ ->
                  bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                    (fun _ ->
                    bind (Obj.magic coq_Monad_PrettyPrinter)
                      (PrettyPrinterMonad.append (String ((Ascii (true, true,
                        true, true, true, false, true, false)), (String
                        ((Ascii (true, true, true, true, true, false, true,
                        false)), (String ((Ascii (true, false, false, false,
                        false, true, true, false)), (String ((Ascii (false,
                        false, true, true, false, true, true, false)),
                        (String ((Ascii (false, false, true, true, false,
                        true, true, false)), (String ((Ascii (true, true,
                        true, true, false, true, true, false)), (String
                        ((Ascii (true, true, false, false, false, true, true,
                        false)), (String ((Ascii (false, true, false, true,
                        true, true, false, false)), (String ((Ascii (false,
                        false, false, false, false, true, false, false)),
                        (String ((Ascii (false, true, false, false, false,
                        true, true, false)), (String ((Ascii (true, false,
                        true, false, true, true, true, false)), (String
                        ((Ascii (true, false, true, true, false, true, true,
                        false)), (String ((Ascii (false, false, false, false,
                        true, true, true, false)), (String ((Ascii (true,
                        false, false, false, false, true, true, false)),
                        (String ((Ascii (false, false, true, true, false,
                        true, true, false)), (String ((Ascii (true, true,
                        true, true, false, true, true, false)), (String
                        ((Ascii (false, true, false, true, true, true, false,
                        false)), (String ((Ascii (false, true, false, true,
                        true, true, false, false)), (String ((Ascii (false,
                        true, false, false, false, false, true, false)),
                        (String ((Ascii (true, false, true, false, true,
                        true, true, false)), (String ((Ascii (true, false,
                        true, true, false, true, true, false)), (String
                        ((Ascii (false, false, false, false, true, true,
                        true, false)), (String ((Ascii (false, false, true,
                        true, false, true, false, false)),
                        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))
                      (fun _ ->
                      bind (Obj.magic coq_Monad_PrettyPrinter) pop_indent
                        (fun _ ->
                        bind (Obj.magic coq_Monad_PrettyPrinter) append_nl
                          (fun _ ->
                          bind (Obj.magic coq_Monad_PrettyPrinter)
                            (PrettyPrinterMonad.append (String ((Ascii (true,
                              false, true, true, true, true, true, false)),
                              EmptyString))) (fun _ ->
                            bind (Obj.magic coq_Monad_PrettyPrinter)
                              append_nl (fun _ ->
                              bind (Obj.magic coq_Monad_PrettyPrinter)
                                append_nl (fun _ ->
                                bind (Obj.magic coq_Monad_PrettyPrinter)
                                  (PrettyPrinterMonad.append (String ((Ascii
                                    (true, false, false, true, false, true,
                                    true, false)), (String ((Ascii (true,
                                    false, true, true, false, true, true,
                                    false)), (String ((Ascii (false, false,
                                    false, false, true, true, true, false)),
                                    (String ((Ascii (false, false, true,
                                    true, false, true, true, false)), (String
                                    ((Ascii (false, false, true, true, true,
                                    true, false, false)), (String ((Ascii
                                    (true, true, true, false, false, true,
                                    false, false)), (String ((Ascii (true,
                                    false, false, false, false, true, true,
                                    false)), (String ((Ascii (false, true,
                                    true, true, true, true, false, false)),
                                    (String ((Ascii (false, false, false,
                                    false, false, true, false, false)),
                                    (String ((Ascii (false, false, false,
                                    false, true, false, true, false)),
                                    (String ((Ascii (false, true, false,
                                    false, true, true, true, false)), (String
                                    ((Ascii (true, true, true, true, false,
                                    true, true, false)), (String ((Ascii
                                    (true, true, true, false, false, true,
                                    true, false)), (String ((Ascii (false,
                                    true, false, false, true, true, true,
                                    false)), (String ((Ascii (true, false,
                                    false, false, false, true, true, false)),
                                    (String ((Ascii (true, false, true, true,
                                    false, true, true, false)), (String
                                    ((Ascii (false, false, false, false,
                                    false, true, false, false)), (String
                                    ((Ascii (true, true, false, true, true,
                                    true, true, false)),
                                    EmptyString)))))))))))))))))))))))))))))))))))))
                                  (fun _ ->
                                  bind (Obj.magic coq_Monad_PrettyPrinter)
                                    append_nl (fun _ ->
                                    bind (Obj.magic coq_Monad_PrettyPrinter)
                                      (PrettyPrinterMonad.append (String
                                        ((Ascii (false, true, true, false,
                                        false, true, true, false)), (String
                                        ((Ascii (false, true, true, true,
                                        false, true, true, false)), (String
                                        ((Ascii (false, false, false, false,
                                        false, true, false, false)), (String
                                        ((Ascii (false, true, true, true,
                                        false, true, true, false)), (String
                                        ((Ascii (true, false, true, false,
                                        false, true, true, false)), (String
                                        ((Ascii (true, true, true, false,
                                        true, true, true, false)), (String
                                        ((Ascii (false, false, false, true,
                                        false, true, false, false)), (String
                                        ((Ascii (true, false, false, true,
                                        false, true, false, false)), (String
                                        ((Ascii (false, false, false, false,
                                        false, true, false, false)), (String
                                        ((Ascii (true, false, true, true,
                                        false, true, false, false)), (String
                                        ((Ascii (false, true, true, true,
                                        true, true, false, false)), (String
                                        ((Ascii (false, false, false, false,
                                        false, true, false, false)), (String
                                        ((Ascii (true, true, false, false,
                                        true, false, true, false)), (String
                                        ((Ascii (true, false, true, false,
                                        false, true, true, false)), (String
                                        ((Ascii (false, false, true, true,
                                        false, true, true, false)), (String
                                        ((Ascii (false, true, true, false,
                                        false, true, true, false)), (String
                                        ((Ascii (false, false, false, false,
                                        false, true, false, false)), (String
                                        ((Ascii (true, true, false, true,
                                        true, true, true, false)),
                                        EmptyString)))))))))))))))))))))))))))))))))))))
                                      (fun _ ->
                                      bind
                                        (Obj.magic coq_Monad_PrettyPrinter)
                                        (push_indent
                                          (add sig_col indent_size))
                                        (fun _ ->
                                        bind
                                          (Obj.magic coq_Monad_PrettyPrinter)
                                          append_nl (fun _ ->
                                          bind
                                            (Obj.magic
                                              coq_Monad_PrettyPrinter)
                                            (PrettyPrinterMonad.append
                                              (String ((Ascii (false, false,
                                              false, false, true, false,
                                              true, false)), (String ((Ascii
                                              (false, true, false, false,
                                              true, true, true, false)),
                                              (String ((Ascii (true, true,
                                              true, true, false, true, true,
                                              false)), (String ((Ascii (true,
                                              true, true, false, false, true,
                                              true, false)), (String ((Ascii
                                              (false, true, false, false,
                                              true, true, true, false)),
                                              (String ((Ascii (true, false,
                                              false, false, false, true,
                                              true, false)), (String ((Ascii
                                              (true, false, true, true,
                                              false, true, true, false)),
                                              (String ((Ascii (false, false,
                                              false, false, false, true,
                                              false, false)), (String ((Ascii
                                              (true, true, false, true, true,
                                              true, true, false)),
                                              EmptyString)))))))))))))))))))
                                            (fun _ ->
                                            bind
                                              (Obj.magic
                                                coq_Monad_PrettyPrinter)
                                              (push_indent
                                                (add sig_col
                                                  (mul (S (S O)) indent_size)))
                                              (fun _ ->
                                              bind
                                                (Obj.magic
                                                  coq_Monad_PrettyPrinter)
                                                append_nl (fun _ ->
                                                bind
                                                  (Obj.magic
                                                    coq_Monad_PrettyPrinter)
                                                  (PrettyPrinterMonad.append
                                                    (String ((Ascii (true,
                                                    true, true, true, true,
                                                    false, true, false)),
                                                    (String ((Ascii (true,
                                                    true, true, true, true,
                                                    false, true, false)),
                                                    (String ((Ascii (true,
                                                    false, false, false,
                                                    false, true, true,
                                                    false)), (String ((Ascii
                                                    (false, false, true,
                                                    true, false, true, true,
                                                    false)), (String ((Ascii
                                                    (false, false, true,
                                                    true, false, true, true,
                                                    false)), (String ((Ascii
                                                    (true, true, true, true,
                                                    false, true, true,
                                                    false)), (String ((Ascii
                                                    (true, true, false,
                                                    false, false, true, true,
                                                    false)), (String ((Ascii
                                                    (false, true, false,
                                                    true, true, true, false,
                                                    false)), (String ((Ascii
                                                    (false, false, false,
                                                    false, false, true,
                                                    false, false)), (String
                                                    ((Ascii (false, true,
                                                    false, false, false,
                                                    true, true, false)),
                                                    (String ((Ascii (true,
                                                    false, true, false, true,
                                                    true, true, false)),
                                                    (String ((Ascii (true,
                                                    false, true, true, false,
                                                    true, true, false)),
                                                    (String ((Ascii (false,
                                                    false, false, false,
                                                    true, true, true,
                                                    false)), (String ((Ascii
                                                    (true, false, false,
                                                    false, false, true, true,
                                                    false)), (String ((Ascii
                                                    (false, false, true,
                                                    true, false, true, true,
                                                    false)), (String ((Ascii
                                                    (true, true, true, true,
                                                    false, true, true,
                                                    false)), (String ((Ascii
                                                    (false, true, false,
                                                    true, true, true, false,
                                                    false)), (String ((Ascii
                                                    (false, true, false,
                                                    true, true, true, false,
                                                    false)), (String ((Ascii
                                                    (false, true, false,
                                                    false, false, false,
                                                    true, false)), (String
                                                    ((Ascii (true, false,
                                                    true, false, true, true,
                                                    true, false)), (String
                                                    ((Ascii (true, false,
                                                    true, true, false, true,
                                                    true, false)), (String
                                                    ((Ascii (false, false,
                                                    false, false, true, true,
                                                    true, false)), (String
                                                    ((Ascii (false, true,
                                                    false, true, true, true,
                                                    false, false)), (String
                                                    ((Ascii (false, true,
                                                    false, true, true, true,
                                                    false, false)), (String
                                                    ((Ascii (false, true,
                                                    true, true, false, true,
                                                    true, false)), (String
                                                    ((Ascii (true, false,
                                                    true, false, false, true,
                                                    true, false)), (String
                                                    ((Ascii (true, true,
                                                    true, false, true, true,
                                                    true, false)), (String
                                                    ((Ascii (false, false,
                                                    false, true, false, true,
                                                    false, false)), (String
                                                    ((Ascii (true, false,
                                                    false, true, false, true,
                                                    false, false)), (String
                                                    ((Ascii (false, false,
                                                    true, true, false, true,
                                                    false, false)),
                                                    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                  (fun _ ->
                                                  bind
                                                    (Obj.magic
                                                      coq_Monad_PrettyPrinter)
                                                    pop_indent (fun _ ->
                                                    bind
                                                      (Obj.magic
                                                        coq_Monad_PrettyPrinter)
                                                      append_nl (fun _ ->
                                                      bind
                                                        (Obj.magic
                                                          coq_Monad_PrettyPrinter)
                                                        (PrettyPrinterMonad.append
                                                          (String ((Ascii
                                                          (true, false, true,
                                                          true, true, true,
                                                          true, false)),
                                                          EmptyString)))
                                                        (fun _ ->
                                                        bind
                                                          (Obj.magic
                                                            coq_Monad_PrettyPrinter)
                                                          pop_indent
                                                          (fun _ ->
                                                          bind
                                                            (Obj.magic
                                                              coq_Monad_PrettyPrinter)
                                                            append_nl
                                                            (fun _ ->
                                                            bind
                                                              (Obj.magic
                                                                coq_Monad_PrettyPrinter)
                                                              (PrettyPrinterMonad.append
                                                                (String
                                                                ((Ascii
                                                                (true, false,
                                                                true, true,
                                                                true, true,
                                                                true,
                                                                false)),
                                                                EmptyString)))
                                                              (fun _ ->
                                                              bind
                                                                (Obj.magic
                                                                  coq_Monad_PrettyPrinter)
                                                                append_nl
                                                                (fun _ ->
                                                                bind
                                                                  (Obj.magic
                                                                    coq_Monad_PrettyPrinter)
                                                                  append_nl
                                                                  (fun _ ->
                                                                  bind
                                                                    (Obj.magic
                                                                    coq_Monad_PrettyPrinter)
                                                                    (monad_append_join
                                                                    append_nl
                                                                    (map
                                                                    PrettyPrinterMonad.append
                                                                    h0.program_preamble))
                                                                    (fun _ ->
                                                                    bind
                                                                    (Obj.magic
                                                                    coq_Monad_PrettyPrinter)
                                                                    (print_decls_aux
                                                                    _UU03a3_
                                                                    remaps0 h
                                                                    ind_attrs
                                                                    (map
                                                                    (on_snd
                                                                    (fun x ->
                                                                    Ex.ConstantDecl
                                                                    x))
                                                                    constants)
                                                                    (bind
                                                                    (Obj.magic
                                                                    coq_Monad_PrettyPrinter)
                                                                    append_nl
                                                                    (fun _ ->
                                                                    append_nl)))
                                                                    (fun _ ->
                                                                    bind
                                                                    (Obj.magic
                                                                    coq_Monad_PrettyPrinter)
                                                                    append_nl
                                                                    (fun _ ->
                                                                    bind
                                                                    (Obj.magic
                                                                    coq_Monad_PrettyPrinter)
                                                                    (PrettyPrinterMonad.append
                                                                    (String
                                                                    ((Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false)),
                                                                    EmptyString)))
                                                                    (fun _ ->
                                                                    pop_indent))))))))))))))))))))))))))))))))))))

(** val extract_rust_within_coq :
    (kername -> bitmask option) -> (kername -> bool) ->
    extract_template_env_params **)

let extract_rust_within_coq overridden_masks should_inline =
  { template_transforms = ((template_inline should_inline) :: []);
    check_wf_env_func = extract_within_coq.check_wf_env_func; pcuic_args =
    { optimize_prop_discr = true; extract_transforms =
    ((dearg_transform overridden_masks true false false false false) :: (transform :: [])) } }
