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

(*| .. coq:: none |*)
Import EqNotations. (* from Coq.Init.Logic *)
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Lists.List.
Import ListNotations. (* from Coq.Lists.List *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Oqarina.Tactics.cpdttactics.
Require Import Oqarina.Configuration.
(*| .. coq:: |*)

(*|
Family
======

A :coq:`family` consists of an index type I, together with a function from I to a type.  One says the function f defines a family of elements in X indexed by I.

Typicall examples are set of objects indexed by either integers or strings. This is useful when defining, e.g., the set of ports of a component.

|*)

Record family@{t} (T : Type@{t}) : Type@{t+1} := {
  family_index :> Type@{t} ;
  family_element :> family_index -> T ;
  (* Note: we use coercion (":>") to ease manipulation *)
}.

Arguments family_index [T].
Arguments family_element [T _].

Lemma family_eq {T : Type} {X Y : family T}
  (p : family_index X = family_index Y)
  (q : ∀ i : X, family_element i = family_element (rew [idmap] p in i))
  : X = Y.
Proof.
    destruct X, Y. simpl in *.
    subst. f_equal.
    apply functional_extensionality_dep. intros x.
    rewrite q. simpl. reflexivity.
Defined.

Definition family_mkeq {T} (X Y : family T) :=
  { p : family_index X = family_index Y |
    ∀ i : X, family_element i = family_element (rew [idmap] p in i) }.

Lemma family_eq_iff {T} (X Y : family T) :
  family_mkeq X Y <-> X = Y.
Proof.
  split; intros.
  - destruct H. eapply family_eq. apply e.
  - subst. exists Logic.eq_refl. simpl. trivial.
Qed.

(*|

The category of families
------------------------

One can consider maps between families over (or modulo) maps between the types they’re from.

Given :math:`f : A -> B` and families :math:`K` from :math:`A` and :math:`L` from :math:`B]`, a map over :math:`f` from :math:`K` to :math:`L` is a function :math:`ff` from elements of :math:`K` to elements of :math:`L`, such that for any element :math:`i \in K`, its realisation :math:`K i` as an element of :math:`A` is mapped under :math:`f` to the realisation :math:`L (ff\:  i)` in :math:`B`.

 |*)

Definition family_morphism [A B: Type]
  (f : A -> B) (K : family A) (L : family B)
:= { ff : K -> L
     & ∀ i : K, L (ff i) = f (K i) }.

Program Definition family_morphism_map
    [A B : Type] (f : A -> B) (X : family A) (Y : family B)
    : family_morphism f X Y -> (X -> Y)
:= @projT1 _ _.

Coercion family_morphism_map : family_morphism >-> Funclass.

Definition family_morphism_commutes
  {A B} {f : A -> B} {K : family A} {L : family B}
  : ∀ ff : family_morphism f K L,
    ∀ i : K, L (ff i) = f (K i)
:= @projT2 _ _.

Definition family_map {A} (K L : family A)
  := family_morphism idmap K L.

#[export] Program Instance map_Setoid {X: Type} (FA FB : family X):
  Setoid (family_map FA FB) := {|
  equiv := fun f1 f2 => (f1) = (f2)
|}.

Program Definition family_map_id {A} (K : family A)
  : family_map K K := _.
Next Obligation.
    unfold family_map, family_morphism.
    exists idmap. trivial.
Defined.

Definition family_compose_general {X Y Z} [g : Y -> Z] [f : X -> Y]
   {K} {L} {M} (gg : family_morphism g L M) (ff : family_morphism f K L)
  : family_morphism (g ∘ f) K M.
Proof.
    unfold family_morphism in *.
    destruct gg. destruct ff.
    unfold fun_compose.

    eexists.
    intros.
    specialize (e0 i). rewrite <- e0.
    specialize (e (x0 i)). rewrite <- e.
    intuition.
Defined.

Definition family_compose {X} {K L M : family X}
  (g : family_map L M) (f : family_map K L)
  : family_map K M
:= family_compose_general g f.

Lemma family_id_left {X: Type}:
  ∀ (x y : family X) (f : family_map x y),
    family_compose (family_map_id y) f = f.
Proof.
  intros.
  unfold family_map_id, family_compose.
  simpl.
  destruct f.
  apply f_equal.
  apply functional_extensionality_dep.
  intros.
  rewrite e.
  intuition.
Qed.

Lemma family_id_right {X: Type}:
  ∀ (x y : family X) (f : family_map x y),
    family_compose f (family_map_id x) = f.
Proof.
  intros.
  unfold family_map_id, family_compose.
  unfold family_map_id_obligation_1.
  unfold family_compose_general.
  simpl.
  destruct f.
  apply f_equal.
  apply functional_extensionality_dep.
  intros.
  rewrite e.
  intuition.
Qed.

Lemma family_compose_assoc {X: Type} :
  ∀ (x y z w: family X)
    (f : family_map z w) (g : family_map y z) (h : family_map x y),
    family_compose f (family_compose g h)
      = family_compose (family_compose f g) h.
Proof.
  intros.
  destruct f, g, h.
  unfold family_compose.
  unfold family_compose_general.

  f_equal.
  apply functional_extensionality_dep.

  intros.

  (* This proof is slightly upsetting, so let's use crush *)
  crush.
Qed.

(*|

From the previous definitions and lemmas, we build :coq:`FamilyCat`, the category of families.

|*)

Definition FamilyCat@{t+} (T : Type@{t}) : Category := {|
  obj      := family T;
  hom      := λ (x y: family T), family_map x y;
  homset   := @map_Setoid T;
  id       := @family_map_id T;
  compose  := @family_compose T;
  comp_assoc := @family_compose_assoc T;
  id_left  := @family_id_left T;
  id_right := @family_id_right T;
  comp_assoc_sym := λ i j k l f g h,
      symmetry (family_compose_assoc _ _ _ _ _ _ _);
|}.

(*|

Specific instances
------------------

* Empty family

An empty family is a family indexed by the empty set.
|*)

Definition void {A : Type} : Empty_set -> A :=
  λ bad, match bad with end.

Definition family_empty A : family A :=
  Build_family A Empty_set void.

(*| * Singleton family

A singleton family is indexed by a single element, :coq:`unit`,
and contains only :coq:`x`.

|*)

Definition singleton {X} (x:X) : family X :=
  Build_family X unit (λ t : unit, x).
