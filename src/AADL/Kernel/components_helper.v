(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.Bool.Sumbool.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.AADL.Kernel.component.
Require Import Oqarina.AADL.Kernel.properties.
Require Import Oqarina.AADL.Kernel.typecheck.

Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.utils.
(* end hide *)

(** XXX Actually wrong, we must check for the direction of the feature as well *)

Fixpoint Valid_Features_Category
(l : list feature) (lcat : list FeatureCategory) :=
    match l with
    | nil => True
    | h :: t => In (projectionFeatureCategory  h) lcat /\
                Valid_Features_Category t lcat
    end.

Lemma Valid_Features_Category_dec :
    forall (l:list feature) (lcat :list FeatureCategory),
        { Valid_Features_Category l lcat } +
        { ~Valid_Features_Category l lcat }.
Proof.
    intros.
    unfold Valid_Features_Category.
    induction l.
    auto.
    apply dec_sumbool_and.
    - apply In_dec; apply FeatureCategory_eq_dec.
    - auto.
Qed.

Definition Well_Formed_Component_Interface
    (c: component) (l : list FeatureCategory) :=
        Valid_Features_Category (c->features) l.

Lemma Well_Formed_Component_Interface_dec :
    forall (c:component) (lcat :list FeatureCategory),
        {Well_Formed_Component_Interface c lcat} +
        { ~Well_Formed_Component_Interface c lcat}.
Proof.
    intros.
    unfold Well_Formed_Component_Interface.
    apply Valid_Features_Category_dec.
Qed.

(** XXX Actually wrong, we must check for the direction of the feature as well *)

Fixpoint Valid_Subcomponents_Category
    (l : list component) (lcat : list ComponentCategory) :=
    match l with
        | nil => True
        | h :: t => In (h->category) lcat /\
            Valid_Subcomponents_Category t lcat
    end.

Lemma Valid_Subcomponents_Category_dec :
    forall (l:list component) (lcat :list ComponentCategory),
        { Valid_Subcomponents_Category l lcat } +
        { ~Valid_Subcomponents_Category l lcat }.
Proof.
    intros.
    unfold Valid_Subcomponents_Category.
    induction l.
    auto.
    apply dec_sumbool_and.
    - apply In_dec; apply ComponentCategory_eq_dec.
    - auto.
Qed.

Definition Well_Formed_Component_Subcomponents
    (c: component) (l : list ComponentCategory) :=
        Valid_Subcomponents_Category (c->subcomps) l.

Lemma Well_Formed_Component_Subcomponents_dec :
    forall (c:component) (lcat :list ComponentCategory),
        {Well_Formed_Component_Subcomponents c lcat} +
        { ~Well_Formed_Component_Subcomponents c lcat}.
Proof.
    intros.
    unfold Well_Formed_Component_Subcomponents.
    apply Valid_Subcomponents_Category_dec.
Qed.

 (** ** Properties type checking rules *)

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
    destruct (resolve_property_decl ps (P p)).
    apply in_dec.
    apply AppliesToCategory_eq_dec.
    auto.
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
    unfold Well_Formed_Property_Associations.
    intros.
    destruct (c ->properties);
    apply Property_Correctly_Applies_To_list_dec.
Qed.
