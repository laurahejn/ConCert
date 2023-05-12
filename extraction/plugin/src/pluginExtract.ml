open All_Forall
open Ascii
open Ast0
open BasicAst
open CRelationClasses
open Classes0
open Datatypes
open Extraction0
open Kernames
open List0
open MCProd
open MCString
open PrettyPrinterMonad
open Primitive
open Printing
open ResultMonad
open RustExtract
open Signature
open Specif
open String0
open Universes0
open Utils
open Bytestring
open Monad_utils

type __ = Obj.t

(** val plugin_extract_preamble : coq_Preamble **)

let plugin_extract_preamble =
  { top_preamble = ((String ((Ascii (true, true, false, false, false, true,
    false, false)), (String ((Ascii (true, false, false, false, false, true,
    false, false)), (String ((Ascii (true, true, false, true, true, false,
    true, false)), (String ((Ascii (true, false, false, false, false, true,
    true, false)), (String ((Ascii (false, false, true, true, false, true,
    true, false)), (String ((Ascii (false, false, true, true, false, true,
    true, false)), (String ((Ascii (true, true, true, true, false, true,
    true, false)), (String ((Ascii (true, true, true, false, true, true,
    true, false)), (String ((Ascii (false, false, false, true, false, true,
    false, false)), (String ((Ascii (false, false, true, false, false, true,
    true, false)), (String ((Ascii (true, false, true, false, false, true,
    true, false)), (String ((Ascii (true, false, false, false, false, true,
    true, false)), (String ((Ascii (false, false, true, false, false, true,
    true, false)), (String ((Ascii (true, true, true, true, true, false,
    true, false)), (String ((Ascii (true, true, false, false, false, true,
    true, false)), (String ((Ascii (true, true, true, true, false, true,
    true, false)), (String ((Ascii (false, false, true, false, false, true,
    true, false)), (String ((Ascii (true, false, true, false, false, true,
    true, false)), (String ((Ascii (true, false, false, true, false, true,
    false, false)), (String ((Ascii (true, false, true, true, true, false,
    true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))) :: ((String ((Ascii
    (true, true, false, false, false, true, false, false)), (String ((Ascii
    (true, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, true, true, false, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, false, true, true, true, false)), (String ((Ascii
    (false, false, false, true, false, true, false, false)), (String ((Ascii
    (false, true, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii
    (false, true, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, false, true, false, true, true, true, false)), (String ((Ascii
    (true, false, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, false, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, true, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, false, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, true, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, false, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, true, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, false, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, true, false, true, false)), (String
    ((Ascii (false, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (true, true, false,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))) :: ((String ((Ascii (true, false, true, true, true,
    true, true, false)), EmptyString)) :: (EmptyString :: ((String ((Ascii
    (true, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, true, false, true, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (false, true, true, true, false, true, true, false)), (String ((Ascii
    (false, false, true, false, false, true, true, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, true, false, true, false, false)), (String ((Ascii
    (false, false, true, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, false, true, true, false, false)), (String ((Ascii
    (false, true, false, true, true, true, false, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, false, false)), (String ((Ascii
    (false, true, false, true, true, true, false, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, false, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, false, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, true, false, false, true, false, false)), (String ((Ascii
    (false, true, true, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, false, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    true, true, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (false, true, false,
    false, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    true, true, true, true, false)), (String ((Ascii (false, true, false,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (true, true, false,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, false, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))) :: ((String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    false, true, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, false, true, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))) :: ((String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, true, false, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, true, true, false, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, false, false, true, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))) :: ((String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (true, false,
    true, true, true, true, true, false)),
    EmptyString)))))))))))))))))) :: ((String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, true, true, true, false)), EmptyString)))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, true, false,
    true, true, true, true, false)), (String ((Ascii (false, true, false,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, false, false, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (true, true, true,
    false, false, true, true, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, true, false,
    true, true, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, false,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, false, false, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (true, true, false,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, false,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))) :: ((String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    false, true, true, true, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))) :: ((String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, true, false, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, true, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, true, true, false, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, false, true, true, true, false)), (String ((Ascii
    (false, true, true, false, true, true, false, false)), (String ((Ascii
    (false, false, true, false, true, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))) :: ((String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (true, false,
    true, true, true, true, true, false)),
    EmptyString)))))))))))))))))) :: ((String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, true, true, true, false)), EmptyString)))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, true,
    true, false, false, true, false)), (String ((Ascii (true, true, true,
    true, true, false, true, false)), (String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, true, false,
    true, true, true, true, false)), (String ((Ascii (false, true, false,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    false, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)),
    EmptyString)))))) :: ((String ((Ascii (true, false, true, true, true,
    true, true, false)), EmptyString)) :: (EmptyString :: ((String ((Ascii
    (true, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, true, false, true, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, true, true, true, false, false, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, true, false)), (String ((Ascii
    (true, false, true, true, false, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, true, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))) :: ((String ((Ascii (true, false, true, true, true,
    true, true, false)), EmptyString)) :: (EmptyString :: ((String ((Ascii
    (false, false, true, false, true, true, true, false)), (String ((Ascii
    (true, false, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (false, false, true, true, true, true, false, false)), (String ((Ascii
    (true, false, false, false, false, false, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, false, true, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, true, false, true, false, false)), (String ((Ascii
    (true, false, false, false, false, false, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, false, true, false)), (String ((Ascii
    (true, false, false, true, false, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, false, false)), (String
    ((Ascii (false, true, false, false, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))) :: ((String ((Ascii (true, false, true, true, true,
    true, true, false)), EmptyString)) :: (EmptyString :: ((String ((Ascii
    (false, true, true, false, false, true, true, false)), (String ((Ascii
    (false, true, true, true, false, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, false, true, true, false, true, true, false)), (String ((Ascii
    (true, true, false, true, false, true, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (false, false, true, true, true, true, false, false)), (String ((Ascii
    (true, false, false, false, false, false, true, false)), (String ((Ascii
    (false, true, false, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, false, false, false, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, true, true, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, false, true, false)), (String ((Ascii
    (false, true, false, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, false, false, false, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, true, true, true, true, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, true, false, true, false, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (false, true, false, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, false, false, false, false, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (false, true, false, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, false, true, false)), (String ((Ascii
    (true, false, false, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, false, true, false, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (true, true, true, true, true, false, true, false)), (String ((Ascii
    (false, false, false, false, true, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, true, false)), (String ((Ascii
    (false, true, false, false, true, true, true, false)), (String ((Ascii
    (false, false, true, true, true, true, false, false)), (String ((Ascii
    (true, false, false, false, false, false, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, false, true, false)), (String ((Ascii
    (false, true, true, true, true, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, true, false, true, true, true, true, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, false, false, true, false, true, false, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii
    (false, false, true, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (false, true, false, false, false, true, true, false)), (String ((Ascii
    (true, false, false, true, false, true, false, false)), (String ((Ascii
    (false, false, false, false, false, true, false, false)), (String ((Ascii
    (true, false, true, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: (EmptyString :: ((String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (false, false, true, true, true, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, false, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, false, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, false, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, true, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, false, true, false)), (String
    ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, false, true, false)), (String
    ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, true, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, false, true, true, false, true, false, false)), (String
    ((Ascii (false, true, true, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, false, true, false)), (String
    ((Ascii (false, true, false, false, true, false, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)),
    EmptyString)))))) :: ((String ((Ascii (true, false, true, true, true,
    true, true, false)),
    EmptyString)) :: [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    program_preamble = ((String ((Ascii (false, true, true, false, false,
    true, true, false)), (String ((Ascii (false, true, true, true, false,
    true, true, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (true, false, false, false, false,
    true, true, false)), (String ((Ascii (false, false, true, true, false,
    true, true, false)), (String ((Ascii (false, false, true, true, false,
    true, true, false)), (String ((Ascii (true, true, true, true, false,
    true, true, false)), (String ((Ascii (true, true, false, false, false,
    true, true, false)), (String ((Ascii (false, false, true, true, true,
    true, false, false)), (String ((Ascii (false, false, true, false, true,
    false, true, false)), (String ((Ascii (false, true, true, true, true,
    true, false, false)), (String ((Ascii (false, false, false, true, false,
    true, false, false)), (String ((Ascii (false, true, true, false, false,
    true, false, false)), (String ((Ascii (true, true, true, false, false,
    true, false, false)), (String ((Ascii (true, false, false, false, false,
    true, true, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (true, true, false, false, true,
    true, true, false)), (String ((Ascii (true, false, true, false, false,
    true, true, false)), (String ((Ascii (false, false, true, true, false,
    true, true, false)), (String ((Ascii (false, true, true, false, false,
    true, true, false)), (String ((Ascii (false, false, true, true, false,
    true, false, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (false, false, true, false, true,
    true, true, false)), (String ((Ascii (false, true, false, true, true,
    true, false, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (false, false, true, false, true,
    false, true, false)), (String ((Ascii (true, false, false, true, false,
    true, false, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (true, false, true, true, false,
    true, false, false)), (String ((Ascii (false, true, true, true, true,
    true, false, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (false, true, true, false, false,
    true, false, false)), (String ((Ascii (true, true, true, false, false,
    true, false, false)), (String ((Ascii (true, false, false, false, false,
    true, true, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (false, false, true, false, true,
    false, true, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (true, true, false, true, true,
    true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: (EmptyString :: ((String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (true, true, true,
    true, false, true, true, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, true, true, false, false)), (String ((Ascii (false, false, true,
    false, true, false, true, false)), (String ((Ascii (true, false, false,
    false, false, false, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    false, true, false, true, false)), (String ((Ascii (false, true, false,
    false, true, false, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    false, false, true, false, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (false, true, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    false, false, false, true, false)), (String ((Ascii (false, true, false,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, false,
    true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, true, true, true, false)), (String ((Ascii (false, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    false, false, false, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, true,
    false, true, false, true, false)), (String ((Ascii (true, false, false,
    false, false, false, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    false, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    false, true, false, true, false)), (String ((Ascii (false, true, false,
    false, true, false, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    false, false, true, false, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    false, false, true, false, false)), (String ((Ascii (true, true, true,
    false, false, true, false, false)), (String ((Ascii (true, false, false,
    false, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    false, false, true, true, false)), (String ((Ascii (true, false, false,
    true, true, true, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, true, true,
    false, false, false, true, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, true,
    false, true, false, true, false)), (String ((Ascii (true, false, false,
    false, false, false, true, false)), (String ((Ascii (false, true, false,
    false, true, true, true, false)), (String ((Ascii (true, true, true,
    false, false, true, true, false)), (String ((Ascii (true, false, false,
    true, false, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, false, true,
    true, false, true, false, false)), (String ((Ascii (false, true, true,
    true, true, true, false, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (false, false, true,
    false, true, false, true, false)), (String ((Ascii (false, true, false,
    false, true, false, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, true,
    false, true, true, true, false)), (String ((Ascii (false, false, false,
    false, false, true, false, false)), (String ((Ascii (true, true, false,
    true, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, true, true, true, true, false, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, true, true, true, false, true, false, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, true, false, true, true, false)), (String
    ((Ascii (true, true, true, true, false, true, true, false)), (String
    ((Ascii (true, true, false, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)), (String
    ((Ascii (false, true, true, false, false, false, true, false)), (String
    ((Ascii (true, false, false, true, false, true, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))) :: ((String
    ((Ascii (true, false, true, true, true, true, true, false)),
    EmptyString)) :: []))))))) }

(** val coq_RustConfig : coq_RustPrintConfig **)

let coq_RustConfig =
  { term_box_symbol = (String ((Ascii (false, false, false, true, false,
    true, false, false)), (String ((Ascii (true, false, false, true, false,
    true, false, false)), EmptyString)))); type_box_symbol = (String ((Ascii
    (false, false, false, true, false, true, false, false)), (String ((Ascii
    (true, false, false, true, false, true, false, false)), EmptyString))));
    any_type_symbol = (String ((Ascii (false, false, false, true, false,
    true, false, false)), (String ((Ascii (true, false, false, true, false,
    true, false, false)), EmptyString)))); print_full_names = true }

(** val default_attrs : ind_attr_map **)

let default_attrs _ =
  String ((Ascii (true, true, false, false, false, true, false, false)),
    (String ((Ascii (true, true, false, true, true, false, true, false)),
    (String ((Ascii (false, false, true, false, false, true, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (false, true, false, false, true, true, true, false)),
    (String ((Ascii (true, false, false, true, false, true, true, false)),
    (String ((Ascii (false, true, true, false, true, true, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (false, false, false, true, false, true, false, false)),
    (String ((Ascii (false, false, true, false, false, false, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (false, true, false, false, false, true, true, false)),
    (String ((Ascii (true, false, true, false, true, true, true, false)),
    (String ((Ascii (true, true, true, false, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, false, false)),
    (String ((Ascii (false, false, false, false, false, true, false, false)),
    (String ((Ascii (true, true, false, false, false, false, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (false, true, true, true, false, true, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (true, false, false, true, false, true, false, false)),
    (String ((Ascii (true, false, true, true, true, false, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))

module T = Env

(** val extract_lines :
    T.program -> remaps -> (kername -> bool) -> (String.t list, String.t)
    result **)

let extract_lines p remaps0 should_inline =
  bind (Obj.magic coq_Monad_result)
    (match snd p with
     | Coq_tConst (kn, _) -> ret (Obj.magic coq_Monad_result) kn
     | Coq_tInd (ind, _) ->
       ret (Obj.magic coq_Monad_result) ind.inductive_mind
     | _ ->
       Err
         (String.of_string (String ((Ascii (true, false, true, false, false,
           false, true, false)), (String ((Ascii (false, false, false, true,
           true, true, true, false)), (String ((Ascii (false, false, false,
           false, true, true, true, false)), (String ((Ascii (true, false,
           true, false, false, true, true, false)), (String ((Ascii (true,
           true, false, false, false, true, true, false)), (String ((Ascii
           (false, false, true, false, true, true, true, false)), (String
           ((Ascii (true, false, true, false, false, true, true, false)),
           (String ((Ascii (false, false, true, false, false, true, true,
           false)), (String ((Ascii (false, false, false, false, false, true,
           false, false)), (String ((Ascii (false, false, false, false, true,
           true, true, false)), (String ((Ascii (false, true, false, false,
           true, true, true, false)), (String ((Ascii (true, true, true,
           true, false, true, true, false)), (String ((Ascii (true, true,
           true, false, false, true, true, false)), (String ((Ascii (false,
           true, false, false, true, true, true, false)), (String ((Ascii
           (true, false, false, false, false, true, true, false)), (String
           ((Ascii (true, false, true, true, false, true, true, false)),
           (String ((Ascii (false, false, false, false, false, true, false,
           false)), (String ((Ascii (false, false, true, false, true, true,
           true, false)), (String ((Ascii (true, true, true, true, false,
           true, true, false)), (String ((Ascii (false, false, false, false,
           false, true, false, false)), (String ((Ascii (false, true, false,
           false, false, true, true, false)), (String ((Ascii (true, false,
           true, false, false, true, true, false)), (String ((Ascii (false,
           false, false, false, false, true, false, false)), (String ((Ascii
           (true, false, false, false, false, true, true, false)), (String
           ((Ascii (false, false, false, false, false, true, false, false)),
           (String ((Ascii (false, false, true, false, true, true, true,
           false)), (String ((Ascii (true, true, false, false, false, false,
           true, false)), (String ((Ascii (true, true, true, true, false,
           true, true, false)), (String ((Ascii (false, true, true, true,
           false, true, true, false)), (String ((Ascii (true, true, false,
           false, true, true, true, false)), (String ((Ascii (false, false,
           true, false, true, true, true, false)), (String ((Ascii (false,
           false, false, false, false, true, false, false)), (String ((Ascii
           (true, true, true, true, false, true, true, false)), (String
           ((Ascii (false, true, false, false, true, true, true, false)),
           (String ((Ascii (false, false, false, false, false, true, false,
           false)), (String ((Ascii (false, false, true, false, true, true,
           true, false)), (String ((Ascii (true, false, false, true, false,
           false, true, false)), (String ((Ascii (false, true, true, true,
           false, true, true, false)), (String ((Ascii (false, false, true,
           false, false, true, true, false)),
           EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (fun entry ->
    let without_deps = fun kn ->
      match remaps0.remap_inductive { inductive_mind = kn; inductive_ind = O } with
      | Some _ -> true
      | None ->
        (match remaps0.remap_constant kn with
         | Some _ -> true
         | None ->
           (match remaps0.remap_inline_constant kn with
            | Some _ -> true
            | None -> false))
    in
    bind (Obj.magic coq_Monad_result)
      (Obj.magic extract_template_env
        (extract_rust_within_coq (fun _ -> None) should_inline) (fst p)
        (KernameSet.singleton entry) without_deps) (fun _UU03a3_ ->
      let p0 =
        print_program _UU03a3_ remaps0 coq_RustConfig default_attrs
          plugin_extract_preamble
      in
      bind (Obj.magic coq_Monad_result)
        (timed (String ((Ascii (false, false, false, false, true, false,
          true, false)), (String ((Ascii (false, true, false, false, true,
          true, true, false)), (String ((Ascii (true, false, false, true,
          false, true, true, false)), (String ((Ascii (false, true, true,
          true, false, true, true, false)), (String ((Ascii (false, false,
          true, false, true, true, true, false)), (String ((Ascii (true,
          false, false, true, false, true, true, false)), (String ((Ascii
          (false, true, true, true, false, true, true, false)), (String
          ((Ascii (true, true, true, false, false, true, true, false)),
          EmptyString)))))))))))))))) (fun _ ->
          map_error String.of_string (Obj.magic finish_print_lines p0)))
        (fun x -> let (_, s) = x in Ok (map String.of_string s))))

(** val extract :
    T.program -> remaps -> (kername -> bool) -> (String.t, String.t) result **)

let extract p remaps0 should_inline =
  bind (Obj.magic coq_Monad_result)
    (Obj.magic extract_lines p remaps0 should_inline) (fun lines ->
    ret (Obj.magic coq_Monad_result) (String.concat nl lines))
