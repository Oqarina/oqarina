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
(* begin hide *)

(** Coq Library *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.AADL.Kernel.properties.
Require Import Oqarina.AADL.Kernel.typecheck.
Require Import Oqarina.coq_utils.utils.
#[local] Open Scope Z_scope.
(* end hide *)

(** [Is_Property_Name] returns [true] iff [pa] has name [name]. This functions allows on to filter property associations by name. *)
Definition Is_Property_Name (name : ps_qname) (pa : property_association) :=
  ps_qname_beq pa.(P) name.

(** [Is_Property_Defined] returns [True] iff property [name] is defined. *)

Fixpoint Is_Property_Defined (name : ps_qname) (pa : list property_association) :=
  match pa with
  | [] => False
  | h :: t => (name = h.(P)) \/ (Is_Property_Defined name t)
  end.

Lemma Is_Property_Defined_dec :
  forall (name:ps_qname) (pa: list property_association),
    {Is_Property_Defined name pa} + {~ Is_Property_Defined name pa}.
Proof.
  intros.
  unfold Is_Property_Defined.
  induction pa.
  auto.
  apply dec_sumbool_or.
  apply ps_qname_eq_dec.
  apply IHpa.
Qed.

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

(** [Map_PV_Bool] maps a property value to an integer. *)

Definition Map_PV_Bool (pa : property_association) :=
  match pa.(PV) with
    | PV_Bool b => b
    | _ => false (** XXX address error case *)
  end.

(** [Map_PV_BoolList] returns the property value for property [name] or [default] is the property is not set *)

Definition Map_PV_Bool_List (pa : list property_association) (default : property_value) (name : property_association -> bool) :=
  match filter name pa with
    | nil => match default with
            | PV_Bool i => i
            | _ => false
            end
    | v :: _ => Map_PV_Bool v
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