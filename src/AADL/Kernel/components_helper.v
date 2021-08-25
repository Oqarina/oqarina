(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.Bool.Sumbool.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.categories.

Require Import Oqarina.AADL.Kernel.component.

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
