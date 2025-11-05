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

Require Import Oqarina.Configuration.
Require Import Oqarina.coq_utils.list_utils.

(*| .. coq:: |*)

Set Implicit Arguments.

(* refactor code

make family a category indexed by finset from stdpp, use in interface_stdpp
make Aut an explicit box from interface_stdpp
refactor interface_stdpp to have box as a SMC

As a conclusion, Aut will inherit all the features from Box automatically
do the same for DEVS btw

*)

Section aut.

(*|

automata
========

In the following, we consider the definition of an automaton as defined in "the Joy of Cats", p20

aut with objects all (deterministic, sequential, Moore) automata. Objects are sextuples (Q, Σ, Y, δ, q0, y), where Q is the set of states, Σ and Y are the sets of input symbols and output symbols, respectively, δ : Σ ×Q→Q is the transition map, q0 ∈Q is the initial state, and y : Q→Y is the output map.

|*)

Record aut := {
    Q : Type;
    Σ : Type;
    Y : Type;

    q0 : Q;
    δ : Σ -> Q -> Q;
    y : Q -> Y;
}.

Definition next_step (a : aut) (q : Q a) (σ : Σ a) : Q a :=
    (δ a) σ q.

Definition next_steps (a : aut) (q : Q a) (l : list (Σ a)) : Q a :=
    fold_left (fun x y => next_step a x y) l q.

(**)

Lemma next_steps_cons: forall a q σ l,
    next_steps a q (σ :: l) = next_steps a (next_step a q σ ) l.
Proof.
    intros.
    unfold next_steps.
    rewrite fold_left_cons.
    trivial.
Qed.

Lemma next_steps_app: forall a q l1 l2,
    next_steps a q (l1 ++ l2) = next_steps a (next_steps a q l1) l2.
Proof.
    intros.
    unfold next_steps.
    rewrite fold_left_app.
    trivial.
Qed.

(*|
    Morphisms from an automaton (Q, Σ, Y, δ, q0, y) to an automaton (Q′, Σ′, Y ′, δ′, q′0, y′) are triples (fQ, fΣ, fY ) of functions fQ : Q→Q′, fΣ : Σ →Σ′, and fY : Y →Y ′ satisfying the following conditions:

    (i) preservation of transition: δ′(fΣ(σ), fQ(q)) = fQ(δ(σ, q)),
    (ii) preservation of outputs: fY (y(q)) = y′(fQ(q)),
    (iii) preservation of initial state: fQ(q0) = q′0.

|*)

Record aut_morphism_r (Q Σ Y Q' Σ' Y': Type) := {
    fQ : Q -> Q';
    fΣ : Σ -> Σ';
    fY : Y -> Y'
}.

(*| :coq:`aut_morphism_next_steps` shows that an automaton morphism
preserves states. This technical lemma is defined in this expanded form to ease further proofs. |*)

Lemma aut_morphism_next_steps:
    ∀  (x y0 : aut)
    (x0 : aut_morphism_r (Q x) (Σ x) (Y x) (Q y0) (Σ y0) (Y y0))
    (a : ∀ (σ : Σ x) (q : Q x), δ y0 (fΣ x0 σ) (fQ x0 q) = fQ x0 (δ x σ q))
    (a1: q0 y0 = fQ x0 (q0 x))
    ( σ : list (Σ x)),

    (fQ x0 (next_steps x (q0 x) σ) =
    (next_steps y0 (q0 y0) (map (fΣ x0) σ))).

Proof.
    intros.
    rewrite a1.
    induction σ using rev_ind.
    - simpl. trivial.
    - rewrite next_steps_app.
    rewrite map_app.
    rewrite next_steps_app.
    simpl.
    unfold next_step.

    specialize (a x1 (next_steps x (q0 x) σ)).
    rewrite <- a.

    rewrite IHσ.

    intuition.
Qed.

Definition aut_morphism
    (A : aut) (B: aut) : Type
:=
    { f : aut_morphism_r (Q A) (Σ A) (Y A) (Q B) (Σ B) (Y B) &

    (* (i) *)
    (∀ (σ: (Σ A)) (q : (Q A)), (δ B) ((fΣ f) σ) ((fQ f) q) = (fQ f) ((δ A) σ q)) /\

    (* (ii) *)
    (∀ (q : (Q A)), (fY f) ((y A) q) = (y B) ((fQ f) q)) /\

    (* (iii) *)
    (q0  B) = (fQ f) (q0 A)
}.

Definition aut_morphism_map
    (A : aut) (B: aut)
    (M : aut_morphism A B)
    : aut_morphism_r (Q A) (Σ A) (Y A) (Q B) (Σ B) (Y B)
    := @projT1 _ _ M.

(*| From these considerations, it is quite trivial to derive that automata form a Category, :coq:`aut`. |*)

#[export] Program Instance aut_morphism_Setoid
    {A : aut} {B: aut} :
    Setoid (aut_morphism A B) := {|
        equiv := fun f1 f2 => (aut_morphism_map f1) = (aut_morphism_map f2)
    |}.

Definition aut_morphism_r_compose
    [Q Σ Y Q' Σ' Y' Q'' Σ'' Y'': Type]
    (g : aut_morphism_r Q' Σ' Y' Q'' Σ'' Y'')
    (f : aut_morphism_r Q Σ Y Q' Σ' Y')

    : (aut_morphism_r Q Σ Y Q'' Σ'' Y'')
:= {|
        fQ := (fQ g) ∘ (fQ f);
        fΣ := (fΣ g) ∘ (fΣ f);
        fY := (fY g) ∘ (fY f);
|}.

Program Definition aut_morphism_compose
    (A B C : aut)
    (g : aut_morphism B C)
    (f : aut_morphism A B)
    : aut_morphism A C
:= ((aut_morphism_r_compose
        (aut_morphism_map g)
        (aut_morphism_map f)); _).
Next Obligation.
    destruct f as [fa fH].
    destruct g as [ga gH].

    unfold aut_morphism_map in *.
    unfold fun_compose.
    simpl in *.

    split.
    - intros.

      destruct fH as [fH1 fH2].
      specialize (fH1 σ q).
      destruct gH as [gH1 gH2].
      specialize (gH1 (fΣ fa σ) (fQ fa q)).

      rewrite <- fH1. trivial.

    - split.
    + intros.
      destruct fH as [fH1 fH2].
      destruct gH as [gH1 gH2].
      destruct fH2 as [fH2 fH3].
      specialize (fH2 q).
      destruct gH2 as [gH2 gH3].
      specialize (gH2 (fQ fa q)).

      rewrite fH2. intuition.
    +  destruct fH as [fH1 fH2].
     destruct fH2 as [fH2 fH3].
    rewrite <- fH3. intuition.
Defined.

Definition aut_morphism_r_id (Q Σ Y : Type)
    : aut_morphism_r Q Σ Y Q Σ Y
:= {|
    fQ := idmap;
    fΣ := idmap;
    fY := idmap;
|}.

Program Definition aut_morphism_id
    (A : aut) :
    (aut_morphism A A)
    := (aut_morphism_r_id (Q A) (Σ A) (Y A);_).

#[export]
Program Instance Aut : Category := {|
    obj     := aut;
    hom     := aut_morphism;
    homset  := @aut_morphism_Setoid;
    id      := @aut_morphism_id ;

    compose := @aut_morphism_compose;

|}.

End aut.


(*

https://golem.ph.utexas.edu/category/2022/07/compositional_constructions_of.html

*)