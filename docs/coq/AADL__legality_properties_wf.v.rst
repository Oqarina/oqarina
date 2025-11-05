.. coq::


.. coq:: none

   (** Coq Library *)
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Coq.Lists.ListDec.
   Require Import Coq.Bool.Sumbool.

   (** Oqarina library *)
   Require Import Oqarina.AADL.Kernel.all.
   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.

Properties
----------

Properties type checking rules

.. coq::

    Definition Property_Correctly_Applies_To (c : component) (ps : property_sets) (p : property_association) :=
        let p_decl := resolve_property_decl ps p.(P) in
        match p_decl with
           | Some p_decl' => In (CompCat (c->category)) (Applicable_ComponentCategory p_decl')
           | None => False
        end.

     Lemma Property_Correctly_Applies_To_dec :
       forall (p : property_association) (ps : property_sets) (c : component),
           { Property_Correctly_Applies_To c ps p  } + { ~ Property_Correctly_Applies_To c ps p } .
     Proof.
       intros p ps c.
       unfold Property_Correctly_Applies_To.
       prove_dec.
       apply AppliesToCategory_eq_dec.
     Qed.

   Fixpoint Property_Correctly_Applies_To_list (c : component) (ps : property_sets) (p : list property_association) :=
       match p with
       | [] => True
       | h :: t => Property_Correctly_Applies_To c ps h /\
           Property_Correctly_Applies_To_list c ps t
       end.

   Lemma Property_Correctly_Applies_To_list_dec :
   forall (c : component) (ps : property_sets) (p : list property_association),
       { Property_Correctly_Applies_To_list c ps p  } + { ~ Property_Correctly_Applies_To_list c ps p } .
   Proof.
       intros c ps.
       unfold Property_Correctly_Applies_To_list.
       induction p.
       - auto.
       - apply dec_sumbool_and. apply Property_Correctly_Applies_To_dec. apply IHp.
   Qed.

   Definition Well_Formed_Property_Associations (c : component) (ps : property_sets) :=
       Property_Correctly_Applies_To_list c ps (projectionComponentProperties c).

   Lemma Well_Formed_Property_Associations_dec : forall (ps : property_sets) (c : component),
       { Well_Formed_Property_Associations c ps } +
       { ~ Well_Formed_Property_Associations c ps }.
   Proof.
       prove_dec.
       apply Property_Correctly_Applies_To_list_dec.
   Qed.

   Definition Well_Formed_Property_Value
       (c : component)
       (pa : property_association)
   :=
       match pa.(PV) with
           | PV_ModelRef _ => let c := Resolve_PV_ModelRef c pa in
               match c with | Some _ => True | _ => False end
           | _ => True
       end.

   Lemma Well_Formed_Property_Value_dec :
       forall (c : component) (pa : property_association),
           { Well_Formed_Property_Value  c pa } + { ~ Well_Formed_Property_Value  c pa  }.
   Proof.
       prove_dec.
   Qed.

   Global Hint Resolve Well_Formed_Property_Value_dec : well_know_wf_dec.

   Definition Well_Formed_Property_Values'
       (parent : component)
       (c : component)
   :=
       All (fun x => Well_Formed_Property_Value parent x)
           (projectionComponentProperties c).

   Lemma Well_Formed_Property_Values'_dec:
       forall (parent : component) (c : component),
           { Well_Formed_Property_Values'  parent c } +
           { ~ Well_Formed_Property_Values'  parent c }.
   Proof.
       prove_dec.
   Qed.

   Global Hint Resolve Well_Formed_Property_Values'_dec : well_know_wf_dec.

   Definition Well_Formed_Property_Values'' (c: component) :=
       All (fun x => Well_Formed_Property_Values' c x) (c->subcomps).

   Lemma Well_Formed_Property_Values''_dec :
       forall (c : component),
           { Well_Formed_Property_Values''  c } +
           { ~ Well_Formed_Property_Values''  c }.
   Proof.
       prove_dec.
   Qed.

   Definition Well_Formed_Property_Values (c: component) :=
       All Well_Formed_Property_Values'' (Unfold c).

   Lemma Well_Formed_Property_Values_dec :
       forall (c : component),
           { Well_Formed_Property_Values  c } +
           { ~ Well_Formed_Property_Values  c  }.
   Proof.
       prove_dec.
   Qed.
