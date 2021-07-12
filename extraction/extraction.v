(* extraction.v *)

(* Code extraction towards OCaml.

  Note: we rely on Coq.IO library to extract code. This library provides additional elements to read from files.

*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

(* Suppress warnings on accessing opaque elements*)
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Oqarina.aadl_declarative.

(* Move to "extraction" directory *)
Cd "extraction/generated-src".

Separate Extraction aadl_declarative.

(** The classic Hello World program. *)
Definition hello_world (argv : list LString.t) : C.t System.effect unit :=
  System.log (LString.s "Hello world!").

  (** Extract the Hello World program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main := Extraction.launch hello_world.
Extraction "main" main.
Cd "../..". (* move back to original directory to avoid complaints in batch mode*)


