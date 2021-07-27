(* extraction.v *)

(* Code extraction towards OCaml.

  Note: we rely on Coq.IO library to extract code. This library provides additional elements to read from files, print strings etc.

*)

(* Coq library *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

(* Coq.IO and Coq.ListString libraries *)
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Import C.Notations.

(* Suppress warnings on accessing opaque elements*)
Set Warnings "-extraction-opaque-accessed,-extraction".

(* Move to "extraction/generated-src" directory *)
Cd "extraction/generated-src".

(* List of modules we want to generate *)
Require Import Oqarina.AADL.atin_frontend.atin_frontend.

(** * Default tool commands *)

(** In the following, we bind tool commands to actual Coq definition. We first define a generic [tool_cmd] record that binds a command line flag to a help string and function to be executed.

Then, we provide various basic utility functions.

*)

Record tool_cmd : Type := {
  flag : string ;
  help_string : string ;
  cmd : list LString.t -> C.t System.effect unit ;
}.

(** - [show_version] display version information *)

Definition show_version (argv : list LString.t) : C.t System.effect unit :=
  System.log (LString.s "Oqarina version 0.1").

Definition version_cmd := {|
  flag := "--version" ;
  help_string := "display version" ;
  cmd := show_version ;
|}.

(** * - [parse_aadl_instance_file] : parse an AADL instance file *)

Definition parse_aadl_instance_file (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | [_; _; file_name] =>
    let! content := System.read_file file_name in
    match content with
    | None => System.log (LString.s "Cannot read file")
    | Some content => let foo := string2aadl (Conversion.to_string content) in
      match foo with
      | None => System.log (LString.s "parse error")
      | _    => System.log (LString.s "parsing success")
      end
    end
  | _ => System.log (LString.s "Expected one parameter.")
  end.

Definition parse_cmd := {|
  flag := "--parse" ;
  help_string := "parse file" ;
  cmd := parse_aadl_instance_file ;
|}.

(** - [show_help] display help information *)

Fixpoint show_help_ (cmd: list tool_cmd) :=
  match cmd with
  | h :: t => do! System.log (LString.s (h.(flag) ++ " " ++ h.(help_string))) in show_help_ (t)
  | _ => ret tt
  end.

Definition show_help (argv : list LString.t) : C.t System.effect unit :=
  do! System.log (LString.s "Usage: oqarina [switches] <files>") in
  do! show_help_ ([version_cmd; parse_cmd]) in
  System.log (LString.s "--help show help").

Definition help_cmd := {|
  flag := "--help" ;
  help_string := "display help" ;
  cmd := show_help ;
|}.

(** * Argument processing *)

Definition Oqarina_Cmd : list tool_cmd := [ version_cmd ; help_cmd ; parse_cmd ].

Fixpoint parse_argument (arg : LString.t) (cmd : list tool_cmd) : list tool_cmd :=
  match cmd with
    | h :: t =>
      if LString.eqb arg (LString.s h.(flag))
        then [ h ] else parse_argument arg t
    | nil => nil
   end.

Fixpoint parse_arguments (argv : list LString.t) : list tool_cmd :=
  match argv with
  | h :: t => (parse_argument h Oqarina_Cmd) ++ (parse_arguments t )
  | _ => nil
  end.

Fixpoint process_arguments
  (argv : list LString.t) (l : list tool_cmd) : C.t System.effect unit :=
    match l with
    | h :: t => do! (h.(cmd) argv) in process_arguments argv t
    | nil => ret tt
    end.

(** * Main entrypoint for Oqarina *)

Definition Oqarina_main (argv : list LString.t) : C.t System.effect unit :=
  let action_todo := parse_arguments (argv) in
  match action_todo with
  | nil => show_help argv
  | _ =>  process_arguments argv action_todo
  end.

(** Extract the program to `extraction/main.ml`. *)
Definition main := Extraction.launch Oqarina_main.
Extraction "main" main.

Cd "../..". (* move back to original directory, to avoid errors like "cannot generate extraction.vo" *)
