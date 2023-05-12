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

(** val to_kername : Ast0.term -> kername option **)

let to_kername = function
| Ast0.Coq_tConst (c, _) -> Some c
| Ast0.Coq_tInd (c, _) -> Some c.inductive_mind
| _ -> None

(** val to_globref : Ast0.term -> global_reference option **)

let to_globref = function
| Ast0.Coq_tConst (kn, _) -> Some (ConstRef kn)
| Ast0.Coq_tInd (ind, _) -> Some (IndRef ind)
| Ast0.Coq_tConstruct (ind, c, _) -> Some (ConstructRef (ind, c))
| _ -> None

(** val result_of_typing_result :
    PCUICEnvironment.global_env_ext -> 'a1 typing_result -> ('a1, String.t)
    result **)

let result_of_typing_result _UU03a3_ = function
| Checked a -> Ok a
| TypeError err -> Err (string_of_type_error _UU03a3_ err)

(** val string_of_env_error :
    PCUICEnvironment.global_env_ext -> env_error -> String.t **)

let string_of_env_error _UU03a3_ = function
| IllFormedDecl (s, e0) ->
  String.append (String.String (Coq_x49, (String.String (Coq_x6c,
    (String.String (Coq_x6c, (String.String (Coq_x46, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x6d,
    (String.String (Coq_x65, (String.String (Coq_x64, (String.String
    (Coq_x44, (String.String (Coq_x65, (String.String (Coq_x63,
    (String.String (Coq_x6c, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))))))
    (String.append s
      (String.append (String.String (Coq_x5c, (String.String (Coq_x6e,
        (String.String (Coq_x54, (String.String (Coq_x79, (String.String
        (Coq_x70, (String.String (Coq_x65, (String.String (Coq_x20,
        (String.String (Coq_x65, (String.String (Coq_x72, (String.String
        (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x72,
        (String.String (Coq_x3a, (String.String (Coq_x20,
        String.EmptyString))))))))))))))))))))))))))))
        (string_of_type_error _UU03a3_ e0)))
| AlreadyDeclared s ->
  String.append (String.String (Coq_x41, (String.String (Coq_x6c,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x61, (String.String (Coq_x64, (String.String (Coq_x79,
    (String.String (Coq_x64, (String.String (Coq_x65, (String.String
    (Coq_x63, (String.String (Coq_x6c, (String.String (Coq_x61,
    (String.String (Coq_x72, (String.String (Coq_x65, (String.String
    (Coq_x64, (String.String (Coq_x20,
    String.EmptyString)))))))))))))))))))))))))))))))) s

(** val result_of_option :
    'a1 option -> String.t -> ('a1, String.t) result **)

let result_of_option o err =
  match o with
  | Some a -> Ok a
  | None -> Err err

(** val to_string_name : Ast0.term -> String.t **)

let to_string_name t0 =
  match to_kername t0 with
  | Some kn -> string_of_kername kn
  | None ->
    String.String (Coq_x4e, (String.String (Coq_x6f, (String.String (Coq_x74,
      (String.String (Coq_x20, (String.String (Coq_x61, (String.String
      (Coq_x20, (String.String (Coq_x63, (String.String (Coq_x6f,
      (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
      (Coq_x74, (String.String (Coq_x61, (String.String (Coq_x6e,
      (String.String (Coq_x74, (String.String (Coq_x20, (String.String
      (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x20,
      (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
      (Coq_x64, (String.String (Coq_x75, (String.String (Coq_x63,
      (String.String (Coq_x74, (String.String (Coq_x69, (String.String
      (Coq_x76, (String.String (Coq_x65,
      String.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val remap : kername -> string -> kername * string **)

let remap kn new_name =
  (kn, new_name)

(** val nat_syn_to_nat : EAst.term -> nat option **)

let rec nat_syn_to_nat = function
| EAst.Coq_tApp (t1, t2) ->
  (match t1 with
   | EAst.Coq_tConstruct (ind, i, l) ->
     (match l with
      | [] ->
        if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind ((MPfile
             ((String.String (Coq_x44, (String.String (Coq_x61,
             (String.String (Coq_x74, (String.String (Coq_x61, (String.String
             (Coq_x74, (String.String (Coq_x79, (String.String (Coq_x70,
             (String.String (Coq_x65, (String.String (Coq_x73,
             String.EmptyString)))))))))))))))))) :: ((String.String
             (Coq_x49, (String.String (Coq_x6e, (String.String (Coq_x69,
             (String.String (Coq_x74,
             String.EmptyString)))))))) :: ((String.String (Coq_x43,
             (String.String (Coq_x6f, (String.String (Coq_x71,
             String.EmptyString)))))) :: [])))), (String.String (Coq_x6e,
             (String.String (Coq_x61, (String.String (Coq_x74,
             String.EmptyString)))))))
        then (match i with
              | O -> None
              | S n ->
                (match n with
                 | O ->
                   (match nat_syn_to_nat t2 with
                    | Some v -> Some (S v)
                    | None -> None)
                 | S _ -> None))
        else None
      | _ :: _ -> None)
   | _ -> None)
| EAst.Coq_tConstruct (ind, n, l) ->
  (match n with
   | O ->
     (match l with
      | [] ->
        if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind ((MPfile
             ((String.String (Coq_x44, (String.String (Coq_x61,
             (String.String (Coq_x74, (String.String (Coq_x61, (String.String
             (Coq_x74, (String.String (Coq_x79, (String.String (Coq_x70,
             (String.String (Coq_x65, (String.String (Coq_x73,
             String.EmptyString)))))))))))))))))) :: ((String.String
             (Coq_x49, (String.String (Coq_x6e, (String.String (Coq_x69,
             (String.String (Coq_x74,
             String.EmptyString)))))))) :: ((String.String (Coq_x43,
             (String.String (Coq_x6f, (String.String (Coq_x71,
             String.EmptyString)))))) :: [])))), (String.String (Coq_x6e,
             (String.String (Coq_x61, (String.String (Coq_x74,
             String.EmptyString)))))))
        then Some O
        else None
      | _ :: _ -> None)
   | S _ -> None)
| _ -> None

(** val _xI : EAst.term **)

let _xI =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x70,
    (String.String (Coq_x6f, (String.String (Coq_x73, (String.String
    (Coq_x69, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x76, (String.String (Coq_x65,
    String.EmptyString))))))))))))))))); inductive_ind = O }, O, [])

(** val _xO : EAst.term **)

let _xO =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x70,
    (String.String (Coq_x6f, (String.String (Coq_x73, (String.String
    (Coq_x69, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x76, (String.String (Coq_x65,
    String.EmptyString))))))))))))))))); inductive_ind = O }, (S O), [])

(** val _xH : EAst.term **)

let _xH =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x70,
    (String.String (Coq_x6f, (String.String (Coq_x73, (String.String
    (Coq_x69, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x76, (String.String (Coq_x65,
    String.EmptyString))))))))))))))))); inductive_ind = O }, (S (S O)), [])

(** val _N0 : EAst.term **)

let _N0 =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x4e,
    String.EmptyString))); inductive_ind = O }, O, [])

(** val _Npos : EAst.term **)

let _Npos =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x4e,
    String.EmptyString))); inductive_ind = O }, (S O), [])

(** val _Z0 : EAst.term **)

let _Z0 =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x5a,
    String.EmptyString))); inductive_ind = O }, O, [])

(** val _Zpos : EAst.term **)

let _Zpos =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x5a,
    String.EmptyString))); inductive_ind = O }, (S O), [])

(** val _Zneg : EAst.term **)

let _Zneg =
  EAst.Coq_tConstruct ({ inductive_mind = ((MPfile ((String.String (Coq_x42,
    (String.String (Coq_x69, (String.String (Coq_x6e, (String.String
    (Coq_x4e, (String.String (Coq_x75, (String.String (Coq_x6d,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
    (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
    (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
    (String.String (Coq_x73,
    String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
    (String.String (Coq_x6f, (String.String (Coq_x71,
    String.EmptyString)))))) :: [])))), (String.String (Coq_x5a,
    String.EmptyString))); inductive_ind = O }, (S (S O)), [])

(** val pos_syn_to_nat_aux : nat -> EAst.term -> nat option **)

let rec pos_syn_to_nat_aux n = function
| EAst.Coq_tApp (_xO0, t1) ->
  (match _xO0 with
   | EAst.Coq_tConstruct (ind, i, l) ->
     (match l with
      | [] ->
        if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind ((MPfile
             ((String.String (Coq_x42, (String.String (Coq_x69,
             (String.String (Coq_x6e, (String.String (Coq_x4e, (String.String
             (Coq_x75, (String.String (Coq_x6d, (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
             (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
             (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
             (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
             (String.String (Coq_x6f, (String.String (Coq_x71,
             String.EmptyString)))))) :: [])))), (String.String (Coq_x70,
             (String.String (Coq_x6f, (String.String (Coq_x73, (String.String
             (Coq_x69, (String.String (Coq_x74, (String.String (Coq_x69,
             (String.String (Coq_x76, (String.String (Coq_x65,
             String.EmptyString)))))))))))))))))
        then (match i with
              | O ->
                (match pos_syn_to_nat_aux (add n n) t1 with
                 | Some v -> Some (add n v)
                 | None -> None)
              | S n0 ->
                (match n0 with
                 | O -> pos_syn_to_nat_aux (add n n) t1
                 | S _ -> None))
        else None
      | _ :: _ -> pos_syn_to_nat_aux (add n n) t1)
   | _ -> pos_syn_to_nat_aux (add n n) t1)
| EAst.Coq_tConstruct (ind, n0, l) ->
  (match n0 with
   | O -> None
   | S n1 ->
     (match n1 with
      | O -> None
      | S n2 ->
        (match n2 with
         | O ->
           (match l with
            | [] ->
              if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind
                   ((MPfile ((String.String (Coq_x42, (String.String
                   (Coq_x69, (String.String (Coq_x6e, (String.String
                   (Coq_x4e, (String.String (Coq_x75, (String.String
                   (Coq_x6d, (String.String (Coq_x73,
                   String.EmptyString)))))))))))))) :: ((String.String
                   (Coq_x4e, (String.String (Coq_x75, (String.String
                   (Coq_x6d, (String.String (Coq_x62, (String.String
                   (Coq_x65, (String.String (Coq_x72, (String.String
                   (Coq_x73,
                   String.EmptyString)))))))))))))) :: ((String.String
                   (Coq_x43, (String.String (Coq_x6f, (String.String
                   (Coq_x71, String.EmptyString)))))) :: [])))),
                   (String.String (Coq_x70, (String.String (Coq_x6f,
                   (String.String (Coq_x73, (String.String (Coq_x69,
                   (String.String (Coq_x74, (String.String (Coq_x69,
                   (String.String (Coq_x76, (String.String (Coq_x65,
                   String.EmptyString)))))))))))))))))
              then Some n
              else None
            | _ :: _ -> None)
         | S _ -> None)))
| _ -> None

(** val pos_syn_to_nat : EAst.term -> nat option **)

let pos_syn_to_nat =
  pos_syn_to_nat_aux (S O)

(** val coq_N_syn_to_nat : EAst.term -> nat option **)

let coq_N_syn_to_nat = function
| EAst.Coq_tApp (t1, t2) ->
  (match t1 with
   | EAst.Coq_tConstruct (ind, n, l) ->
     (match n with
      | O -> None
      | S n0 ->
        (match n0 with
         | O ->
           (match l with
            | [] ->
              if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind
                   ((MPfile ((String.String (Coq_x42, (String.String
                   (Coq_x69, (String.String (Coq_x6e, (String.String
                   (Coq_x4e, (String.String (Coq_x75, (String.String
                   (Coq_x6d, (String.String (Coq_x73,
                   String.EmptyString)))))))))))))) :: ((String.String
                   (Coq_x4e, (String.String (Coq_x75, (String.String
                   (Coq_x6d, (String.String (Coq_x62, (String.String
                   (Coq_x65, (String.String (Coq_x72, (String.String
                   (Coq_x73,
                   String.EmptyString)))))))))))))) :: ((String.String
                   (Coq_x43, (String.String (Coq_x6f, (String.String
                   (Coq_x71, String.EmptyString)))))) :: [])))),
                   (String.String (Coq_x4e, String.EmptyString)))
              then pos_syn_to_nat t2
              else None
            | _ :: _ -> None)
         | S _ -> None))
   | _ -> None)
| EAst.Coq_tConstruct (ind, n, l) ->
  (match n with
   | O ->
     (match l with
      | [] ->
        if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind ((MPfile
             ((String.String (Coq_x42, (String.String (Coq_x69,
             (String.String (Coq_x6e, (String.String (Coq_x4e, (String.String
             (Coq_x75, (String.String (Coq_x6d, (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
             (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
             (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
             (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
             (String.String (Coq_x6f, (String.String (Coq_x71,
             String.EmptyString)))))) :: [])))), (String.String (Coq_x4e,
             String.EmptyString)))
        then Some O
        else None
      | _ :: _ -> None)
   | S _ -> None)
| _ -> None

(** val coq_Z_syn_to_Z : EAst.term -> coq_Z option **)

let coq_Z_syn_to_Z = function
| EAst.Coq_tApp (t1, t2) ->
  (match t1 with
   | EAst.Coq_tConstruct (ind, i, l) ->
     (match l with
      | [] ->
        if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind ((MPfile
             ((String.String (Coq_x42, (String.String (Coq_x69,
             (String.String (Coq_x6e, (String.String (Coq_x4e, (String.String
             (Coq_x75, (String.String (Coq_x6d, (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
             (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
             (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
             (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
             (String.String (Coq_x6f, (String.String (Coq_x71,
             String.EmptyString)))))) :: [])))), (String.String (Coq_x5a,
             String.EmptyString)))
        then (match i with
              | O -> None
              | S n ->
                (match n with
                 | O ->
                   (match pos_syn_to_nat t2 with
                    | Some v -> Some (Z.of_nat v)
                    | None -> None)
                 | S n0 ->
                   (match n0 with
                    | O ->
                      (match pos_syn_to_nat t2 with
                       | Some v -> Some (Z.opp (Z.of_nat v))
                       | None -> None)
                    | S _ -> None)))
        else None
      | _ :: _ -> None)
   | _ -> None)
| EAst.Coq_tConstruct (ind, n, l) ->
  (match n with
   | O ->
     (match l with
      | [] ->
        if ReflectEq.eqb Kername.reflect_kername ind.inductive_mind ((MPfile
             ((String.String (Coq_x42, (String.String (Coq_x69,
             (String.String (Coq_x6e, (String.String (Coq_x4e, (String.String
             (Coq_x75, (String.String (Coq_x6d, (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x4e,
             (String.String (Coq_x75, (String.String (Coq_x6d, (String.String
             (Coq_x62, (String.String (Coq_x65, (String.String (Coq_x72,
             (String.String (Coq_x73,
             String.EmptyString)))))))))))))) :: ((String.String (Coq_x43,
             (String.String (Coq_x6f, (String.String (Coq_x71,
             String.EmptyString)))))) :: [])))), (String.String (Coq_x5a,
             String.EmptyString)))
        then Some Z0
        else None
      | _ :: _ -> None)
   | S _ -> None)
| _ -> None

(** val parens : bool -> string -> string **)

let parens top s =
  if top
  then s
  else append (String ((Ascii (false, false, false, true, false, true, false,
         false)), EmptyString))
         (append s (String ((Ascii (true, false, false, true, false, true,
           false, false)), EmptyString)))

(** val nl : string **)

let nl =
  String ((ascii_of_nat (S (S (S (S (S (S (S (S (S (S O))))))))))),
    EmptyString)

(** val string_of_list_aux :
    ('a1 -> string) -> string -> 'a1 list -> string **)

let rec string_of_list_aux f sep = function
| [] -> EmptyString
| a :: l0 ->
  (match l0 with
   | [] -> f a
   | _ :: _ -> append (f a) (append sep (string_of_list_aux f sep l0)))

(** val string_of_list : ('a1 -> string) -> 'a1 list -> string **)

let string_of_list f l =
  append (String ((Ascii (true, true, false, true, true, false, true,
    false)), EmptyString))
    (append
      (string_of_list_aux f (String ((Ascii (false, false, true, true, false,
        true, false, false)), EmptyString)) l) (String ((Ascii (true, false,
      true, true, true, false, true, false)), EmptyString)))

(** val print_list : ('a1 -> string) -> string -> 'a1 list -> string **)

let print_list =
  string_of_list_aux
