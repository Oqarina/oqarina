(** %\chapter{AADL instance model JSON parser}\label{chap::aadl_json}% *)

(**
This module introduces a JSON-based parser for Oqarina. It maps a JSON file produced by Ocarina to an Oqarina instance model.

This implementation relies on the `coq-json` library for parsing a JSON file, producing an AST. Then the [Map_JSON] function maps this AST onto a valid AADL instance file. Because of Coq typing rules, we can only build a valid instance model, albeit incomplete.
*)

(* begin hide *)
(** Coq Library *)
From JSON Require Import
    Lexer
    Printer.
Import
    List
    ListNotations.

(** Oqarina library *)
From Oqarina Require Import
    Kernel.all
    core.identifiers.
(* end hide *)

(** * Helper functions *)

(** - [get_identifier] extracts a string object from a JSON object *)
Definition get_identifier (j : json) :=
  match get_string "identifier" j with
  | Some s => Id s
  | _ => empty_identifier
  end.

(** - [get_json_list] turns a JSON__Array object into a list *)

Definition get_json_list (j : json) :=
  match get_list (fun x => Some x) j with
  | Some l => l
  | None => []
  end.

(** * Mapping helper functions *)

(** These functions map various elements of a JSON AST to their AADL counterpart. *)

Definition Map_JSON_To_ComponentCategory (cat : json) :=
  match cat with
  | JSON__String "system" => system
  | JSON__String "abstract" => abstract
  | JSON__String "bus" => bus
  | JSON__String "data" => data
	| JSON__String "device" => device
  | JSON__String "memory" => memory
  | JSON__String "processor" => processor
  | JSON__String "process" => process
  | JSON__String "subprogram" => subprogram
  | JSON__String "subprogram group" => subprogramGroup
  | JSON__String "thread group" => threadGroup
	| JSON__String "thread" => thread
  | JSON__String "virtual bus" => virtualBus
  | JSON__String "virtual processor" => virtualProcessor
  | _ => null
  end.

Definition Map_JSON_To_Feature_Direction (j : json) :=
  match j with
    | JSON__Object [("kind", JSON__String "out")] => outF
    | JSON__Object [("kind", JSON__String "in")] => inF
    | JSON__Object [("kind", JSON__String "inout")] => inoutF
    | _ => nullDirection
  end.

Definition Map_JSON_To_Feature_Category (j : json) :=
  match j with
    | JSON__Object [("kind", JSON__String "data")] => dataPort
    | JSON__Object [("kind", JSON__String "event")] => eventPort
    | JSON__Object [("kind", JSON__String "event_data")] => eventDataPort
    | JSON__Object [("kind", JSON__String "feature")] => abstractFeature
    | _ => invalid
  end.

Definition get_subcomponents (j : json) :=
  let s := get_json "component" (get_json "subcomponents" j) in
  match s with
  | JSON__Object f => [ s ]
  | JSON__Array l => get_json_list s
  | _ => []
  end.

Definition get_features (j : json) : list json :=
  let f := get_json "feature" (get_json "features" j) in
  match f with
  | JSON__Object o => [ f ]
  | JSON__Array l => get_json_list f
  | _ => []
  end.

Fixpoint Map_JSON_To_Component' (fuel : nat) (c : list json) : list component :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match c with
    | (JSON__Object f) :: t =>
       ( Component (get_identifier (JSON__Object f))
                   (Map_JSON_To_ComponentCategory (get_json "category" (JSON__Object f)))
                   empty_fqname (* classifier *)
                   (Map_JSON_To_Feature' m (get_features (JSON__Object f))) (* features *)
                   (Map_JSON_To_Component' m (get_subcomponents (JSON__Object f))) (* subcomponents *)
                   nil (* properties *)
                   nil (* connections *)
       )
      :: (Map_JSON_To_Component' m t)
    | _ => []
    end
  end
with Map_JSON_To_Feature' (fuel : nat) (j : list json) :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match j with
      | (JSON__Object o) :: t =>
        ( Feature (get_identifier (JSON__Object o)) (* identifier *)
                (Map_JSON_To_Feature_Direction (get_json "direction" (JSON__Object o))) (* directionType *)
                (Map_JSON_To_Feature_Category (get_json "type" (JSON__Object o))) (* feature category *)
                (hd nil_component (Map_JSON_To_Component' m [get_json "component" (get_json "corresponding_instance" (JSON__Object o))]))
                nil (* properties *)
        )
        :: Map_JSON_To_Feature' m t
      | _ => [  ]
      end
  end.

Definition Map_JSON_To_Component (c : list json) : list component :=
  Map_JSON_To_Component' 10 c. (* XXX should us a better value. The fuel value is the "depth of the model" *)

Definition Map_JSON_Root_To_Component (AST : option string + json) :=
  match AST with
    | inr (JSON__Object l) =>
    let aadl_xml := get_json "aadl_xml" (JSON__Object l) in
    let comps := get_json "components" aadl_xml in
      Map_JSON_To_Component ([get_json "component" comps])
    | _ =>  []
  end.

Definition Map_JSON_String_To_Component (s : string) :=
    Map_JSON_Root_To_Component (from_string s).
