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
(** %\chapter{AADL instance model JSON parser}\label{chap::aadl_json}% *)

(**
This module introduces a JSON-based parser for Oqarina. It maps a JSON file produced by Ocarina to a Coq term denoting an AADL instance model.

This implementation relies on the `coq-json` library for parsing a JSON file, producing an AST. Then the [Map_JSON_String_To_Component ] function maps this AST onto a valid AADL instance file. Because of Coq typing rules, we can only build a valid instance model, albeit incomplete.
*)

(* begin hide *)
(** Coq Library *)
From JSON Require Import
    Lexer
    Printer.
Import
    List
    ListNotations
    Strings.String.
#[local] Open Scope Z_scope.

(** Oqarina library *)
From Oqarina Require Import
    coq_utils.all
    AADL.Kernel.all
    core.identifiers
    AADL.property_sets.all
    AADL.instance.all.
(* end hide *)

(** * Helper functions *)

Definition get_string_from_json (s : string) (j : json) :=
  match get_string s j with
  | Some s' => s'
  | _ => EmptyString
  end.

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

Definition get_properties (j : json) : list json :=
  let f := get_json "property" (get_json "properties" j) in
  match f with
  | JSON__Object o => [ f ]
  | JSON__Array l => get_json_list f
  | _ => []
  end.

Definition Map_JSON_To_Property_Value_Abstract (j2 : json) (f : json -> property_value ): property_value :=
  match j2 with
  | JSON__Object j3 => f j2
  | JSON__Array j3 => PV_List (map (fun x => f x) j3)
  | _ => PV_Bool false
  end.

Fixpoint Map_JSON_To_Property_Value (j : json) : property_value :=
  match j with
  | JSON__Object [("boolean", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_Bool (parse_bool (get_string_from_json "value" x)))

  | JSON__Object [("string", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_String (get_string_from_json "value" x))

  | JSON__Object [("integer", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_Int (parse_int (get_string_from_json "value" x)))

  | JSON__Object [("integer_unit", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_IntU (parse_int (get_string_from_json "value" x))
                (PV_Unit (Id (get_string_from_json "unit" x))))

  | JSON__Object [("enumeration", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_Enum (Id (get_string_from_json "value" x)))

  | JSON__Object [("integer_range", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_IntRange (PV_Int (parse_int (get_string_from_json "value_low" x)))
                            (PV_Int (parse_int (get_string_from_json "value_high" x))))

  | JSON__Object [("integer_range_unit", j2)] =>
    Map_JSON_To_Property_Value_Abstract j2
      (fun x => PV_IntRange (PV_IntU (parse_int (get_string_from_json "value_low" x))
                            (PV_Unit (Id (get_string_from_json "unit_low" x))))
                            (PV_IntU (parse_int (get_string_from_json "value_high" x))
                            (PV_Unit (Id (get_string_from_json "unit_high" x)))))

  | JSON__Object [("list", j2)] =>
    Map_JSON_To_Property_Value j2

(* The following are not handled yet, To be continued

  | PV_Real (r : REAL)
  | PV_RealU (r : REAL) (unit : property_value)
  | PV_RealRange (min max : property_value)
  | PV_IntRangeD (min max : property_value) (delta : property_value)
  | PV_RealRangeD (min max : property_value) (delta : property_value)
  | PV_PropertyRef (qname : ps_qname) (* ref to property or constant *)
  | PV_Classifier (* TBD *)
  | PV_ModelRef (path : list identifier)
  | PV_Record (fields : list field_value)
  | PV_Computed (function : string)
*)

    | _  => PV_Bool false (* error reporting *)
  end.

Definition Map_JSON_To_PSQName (j: json) :=
  let psqn := parse_psq_name(get_string_from_json "name" j) in
  match psqn with
  | PSQN "" s => PSQN (Get_AADL_Predeclared_Property_Set_Name s) s
  | _ => psqn
  end.

Fixpoint Map_JSON_To_Property_Association (j : list json) :=
  match j with
      | (JSON__Object o) :: t =>
        {| P := (Map_JSON_To_PSQName (JSON__Object o)) ;
          PV := (Map_JSON_To_Property_Value (get_json "property_value" (JSON__Object o))) |}
        :: Map_JSON_To_Property_Association  t
      | _ => [  ]
  end.

Fixpoint Map_JSON_To_Component' (fuel : nat) (c : list json) : list component :=
  match fuel with
  | 0%nat => nil
  | S m =>
    match c with
    | (JSON__Object f) :: t =>
       ( Component (get_identifier (JSON__Object f))
                   (Map_JSON_To_ComponentCategory (get_json "category" (JSON__Object f)))
                   (parse_fq_name (get_string_from_json "$t" (get_json "classifier" (JSON__Object f))))  (* classifier *)
                   None (* extends *)
                   (Map_JSON_To_Feature' m (get_features (JSON__Object f))) (* features *)
                   (Map_JSON_To_Component' m (get_subcomponents (JSON__Object f))) (* subcomponents *)
                   (Map_JSON_To_Property_Association (get_properties (JSON__Object f)))(* properties *)
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
        inr (Map_JSON_To_Component ([get_json "component" comps]))
    | inr _ => inl (Some "Invalid JSON Object")
    | inl x => inl x
  end.

Definition Map_JSON_String_To_Component (s : string) :=
    Map_JSON_Root_To_Component (from_string s).

Definition Get_Instance (c : option string + list component) :=
  match c with
    | inr c' =>
      match c' with
        | h :: _ => h
        | _ => nil_component
      end
    | _ => nil_component
  end.
