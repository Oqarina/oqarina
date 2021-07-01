(* begin hide *)

(** Coq Library *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.properties.properties.
(* end hide *)

(** [Is_Property_Name] returns [true] iff [pa] has name [name]. This functions allows on to filter property associations by name. *)
Definition Is_Property_Name (name : ps_qname) (pa : property_association) :=
  match pa.(PT) with
  | PT_TypeRef id => ps_qname_beq id name
  | _ => false
  end.

(** [Map_PV_Int] maps a property value to an integer. *)

Definition Map_PV_Int (pa : property_association) :=
  match pa.(PV) with
    | PV_Int i => i
    | PV_IntU i _ => i (* XXX implement unit conversion *)
    | _ => 0 (** XXX address error case *)
  end.

(** [Map_PV_Int_List] returns the property value for property [name] or [default] is the property is not set *)

(** XXX default should not be required, we should be able to resolve default form the property type declaration, *)

Definition Map_PV_Int_List (pa : list property_association) (default : Z) (name : property_association -> bool) :=
  match filter name pa with
    | nil => default
    | v :: _ => Map_PV_Int v
    end.
