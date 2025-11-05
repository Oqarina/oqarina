.. coq::


.. coq:: none

   Require Import Coq.ZArith.ZArith.
   Require Import Coq.Lists.List.
   Import ListNotations.

   (** Oqarina library *)
   Require Import Oqarina.core.all.
   Require Import Oqarina.AADL.Kernel.component.
   Require Import Oqarina.AADL.Kernel.components_helper.
   Require Import Oqarina.AADL.Kernel.properties.
   Require Import Oqarina.AADL.Kernel.typecheck.

   Require Import Oqarina.coq_utils.all.
   #[local] Open Scope Z_scope.

Properties Helper Library
=========================

[Is_Property_Name] returns [true] iff [pa] has name [name]. This functions allows on to filter property associations by name.

.. coq::

   Definition Is_Property_Name
     (name : ps_qname) (pa : property_association) :=
     ps_qname_beq pa.(P) name.

[Is_Property_Defined] returns [True] iff property [name] is defined.

.. coq::

   Definition Is_Property_Defined
     (name : ps_qname) (pa : list property_association) :=
     In name (map (fun x => x.(P)) pa).

   Lemma Is_Property_Defined_dec :
     forall (name:ps_qname) (pa: list property_association),
       {Is_Property_Defined name pa} + {~ Is_Property_Defined name pa}.
   Proof.
     generalize ps_qname_eq_dec.
     prove_dec.
   Defined.

[Map_PV_Int] maps a property value to an integer.

.. coq::

   Definition Map_PV_Int (pa : property_association) :=
     match pa.(PV) with
       | PV_Int i => i
       | PV_IntU i _ => i (* XXX implement unit conversion *)
       | _ => 0 (** XXX address error case *)
     end.

[Map_PV_Int_List] returns the property value for property [name] or [default] is the property is not set

.. coq::

   Definition Map_PV_Int_List (pa : list property_association) (default : property_value) (name : property_association -> bool) :=
     match filter name pa with
       | nil => match default with
               | PV_Int i => i
               | _ => 0
               end
       | v :: _ => Map_PV_Int v
       end.

[Map_PV_Bool] maps a property value to an integer.

.. coq::

   Definition Map_PV_Bool (pa : property_association) :=
     match pa.(PV) with
       | PV_Bool b => b
       | _ => false (** XXX address error case *)
     end.

[Map_PV_BoolList] returns the property value for property [name] or [default] is the property is not set

.. coq::

   Definition Map_PV_Bool_List (pa : list property_association) (default : property_value) (name : property_association -> bool) :=
     match filter name pa with
       | nil => match default with
               | PV_Bool i => i
               | _ => false
               end
       | v :: _ => Map_PV_Bool v
       end.

[Get_Record_Member] return the member [name] from the list of field_value

.. coq::

   Fixpoint Get_Record_Member (pv : list field_value) (name : identifier) :=
         match pv with
         | nil => None
         | h :: t =>
           match h with
           | FieldVal id v => if identifier_beq id name then Some h
                                                        else Get_Record_Member t name
           end
         end.

ModelRef_to_fqname transforms a PV_Model_Ref (i.e a reference
to some component, presented as a path) into a proper fqname

.. coq::

   Definition ModelRef_to_fqname (l : list identifier) :=
     let rev_path := rev l in
     FQN (rev (tl rev_path)) (hd empty_identifier rev_path) (None).

Resolve a PV_ModelRef in the context of component c.
 Note: c is usually the parent of the subcomponent defining this property.

 .. coq::

    Definition Resolve_PV_ModelRef
      (c: component)
      (pa : property_association)
    :=
      match pa.(PV) with
      | PV_ModelRef path => Resolve_Subcomponent c (ModelRef_to_fqname path)
      | _ => None
      end.
