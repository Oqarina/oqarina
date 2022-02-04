(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)

(* Coq library *)

From Coq Require Import
     Strings.String
     Lists.List.
Import ListNotations.

From Coq.extraction Require Import
     ExtrOcamlIntConv.

(* begin hide *)
Set Warnings "-extraction-opaque-accessed,-extraction".
(* end hide *)

(* List of modules we want to generate *)
From Oqarina Require Import
  coq_utils.all
  AADL.Kernel.all
  AADL.json_frontend.json_frontend
  AADL.instance.all.

  From SimpleIO Require Import
  IO_Sys
  IO_RawChar
  IO_Monad
  IO_Stdlib.
Import IO.Notations.

Open Scope string_scope.

(** * Default tool commands *)

(** In the following, we bind tool commands to actual Coq definition. We first define a generic [tool_cmd] record that binds a command line flag to a help string and function to be executed.

Then, we provide various basic utility functions.

*)

Record tool_cmd : Type := {
  flag : string ;
  help_string : string ;
  cmd : list string -> IO unit ;
}.

(** - [show_version] display version information *)

Definition show_version (argv : list string) : IO unit :=
  print_endline (to_ostring "Oqarina version 0.1").

Definition version_cmd := {|
  flag := "--version" ;
  help_string := "display version" ;
  cmd := show_version ;
|}.

(** * - [parse_aadl_json_file] : parse an AADL JSON file *)

Definition validate_AADL_root (c : list component) : IO unit :=
  let AADL_Root := hd nil_component c in
  let AADL_Root_Valid := Oracle (Well_Formed_Component_Instance_dec AADL_Root) in
  if AADL_Root_Valid then print_endline (to_ostring "well-formed success")
                     else print_endline (to_ostring "well-formed failure").

Definition read_file (filename : string) :=
  ch <- open_in (to_ostring filename) ;;
  ch_len <- in_channel_length ch ;;
  s <- really_input_string ch ch_len ;;
  _ <- close_in ch ;;
  IO.ret s.

Definition process_aadl_content (m : string) :=
  let AADL_Root := Map_JSON_String_To_Component m in
  match AADL_Root with
  | inl _ => print_endline "parse error"
  | inr AADL_Root' => print_endline "parsing success"
  end.

Definition parse_aadl_json_file (argv : list string) : IO unit :=
  match argv with
  | [_; _; file_name] =>
    content <- read_file file_name ;;
    component <- process_aadl_content (from_ostring content) ;;
    IO.ret tt

  | _ => print_endline "expected filename"
  end ;;  IO.ret tt.

Definition parse_cmd := {|
  flag := "--parse" ;
  help_string := "parse JSON file" ;
  cmd := parse_aadl_json_file ;
|}.

(** - [show_help] display help information *)

Fixpoint show_help_ (cmd: list tool_cmd) : IO unit :=
  match cmd with
  | h :: t => print_endline
                 (h.(flag) ++ " " ++ h.(help_string)) ;;
    show_help_ (t)
  | _ => IO.ret tt
  end.

Definition show_help (argv : list string) : IO unit :=
  print_endline (to_ostring "Usage: oqarina [switches] <files>") ;;
  show_help_ [version_cmd ; parse_cmd] ;;
  print_endline (to_ostring "--help show help").

Definition help_cmd := {|
  flag := "--help" ;
  help_string := "display help" ;
  cmd := show_help ;
|}.

(** * Argument processing *)

Definition Oqarina_Cmd : list tool_cmd :=
  [ version_cmd ; help_cmd ; parse_cmd ].

Fixpoint parse_argument (arg : string) (cmd : list tool_cmd) : list tool_cmd :=
  match cmd with
    | h :: t =>
      if eqb arg h.(flag)
        then [ h ] else parse_argument arg t
    | nil => nil
   end.

Fixpoint parse_arguments (argv : list string) : list tool_cmd :=
  match argv with
  | h :: t => (parse_argument h Oqarina_Cmd) ++ (parse_arguments t)
  | _ => nil
  end.

Fixpoint process_arguments
  (argv : list string) (l : list tool_cmd) : IO unit :=
    match l with
    | h :: t => (h.(cmd) argv) ;; process_arguments argv t
    | nil => IO.ret tt
    end.

(** * Main entrypoint for Oqarina *)

Definition Oqarina_main (argv : list string) : IO unit :=
  let action_todo := parse_arguments (argv) in
  match action_todo with
    | nil => show_help argv
    | _   => process_arguments argv action_todo
  end.

Definition main' : IO unit :=
  args <- OSys.argv ;;
  Oqarina_main (map from_ostring args).

Definition main : io_unit := IO.unsafe_run main'.

Extraction Blacklist Char.
(* It seems coq-ext-lib hides this definition. Hence, we instruct the extraction mechanism to handle this conflict. See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/.E2.9C.94.20Unbound.20value.20Char.2Echr.20when.20compiling.20extracted.20code.3A *)

(*Extraction "main" main. *)
Separate Extraction main.
