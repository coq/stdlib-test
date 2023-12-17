(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Extraction to Ocaml : special handling of ascii and strings *)

From Stdlib Require Extraction.

From Stdlib Require Import Ascii String.
From Stdlib.Strings Require Import Byte.
From Stdlib Require Export ExtrOcamlChar.

Extract Inductive string => "char list" [ "[]" "(::)" ].
