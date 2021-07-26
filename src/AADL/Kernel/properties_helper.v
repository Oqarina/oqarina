(* begin hide *)

(** Coq Library *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.AADL.Kernel.properties.
Require Import Oqarina.AADL.Kernel.typecheck.

(* end hide *)

(** [Is_Property_Name] returns [true] iff [pa] has name [name]. This functions allows on to filter property associations by name. *)
Definition Is_Property_Name (name : ps_qname) (pa : property_association) :=
  ps_qname_beq pa.(P) name.

(** [Map_PV_Int] maps a property value to an integer. *)

Definition Map_PV_Int (pa : property_association) :=
  match pa.(PV) with
    | PV_Int i => i
    | PV_IntU i _ => i (* XXX implement unit conversion *)
    | _ => 0 (** XXX address error case *)
  end.

(** [Map_PV_Int_List] returns the property value for property [name] or [default] is the property is not set *)

Definition Map_PV_Int_List (pa : list property_association) (default : property_value) (name : property_association -> bool) :=
  match filter name pa with
    | nil => match default with
            | PV_Int i => i
            | _ => 0
            end
    | v :: _ => Map_PV_Int v
    end.

(** [Get_Record_Member] return the member [name] from the list of field_value *)

Fixpoint Get_Record_Member (pv : list field_value) (name : identifier) :=
      match pv with
      | nil => None
      | h :: t =>
        match h with
        | FieldVal id v => if identifier_beq id name then Some h
                                                     else Get_Record_Member t name
        end
      end.