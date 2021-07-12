(* extraction.v *)

(* Code extraction towards OCaml.

  Note: we rely on Coq.IO library to extract code. This library provides additional elements to read from files, print strings etc.

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

(* Move to "extraction/generated-src" directory *)
Cd "extraction/generated-src".

Separate Extraction aadl_declarative.

Fixpoint parse_arguments (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | h :: t => do! System.log (h) in parse_arguments (t)
  | _ => ret tt
  end.

(** The classic Hello World program. *)
Definition hello_world (argv : list LString.t) : C.t System.effect unit :=
  do! System.log (LString.s "Hello world!") in
  parse_arguments (argv).

  (** Extract the Hello World program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main := Extraction.launch hello_world.
Extraction "main" main.

Cd "../..". (* move back to original directory, to avoid errors like "cannot generate extraction.vo" *)
