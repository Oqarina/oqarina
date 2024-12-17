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
Require Import Category.Theory.Functor.

Require Import Oqarina.Configuration.
Require Import Oqarina.coq_utils.list_utils.
Require Import Oqarina.Categories.aut.
(*| .. coq:: |*)

Set Implicit Arguments.

(*|

Beh -- Category of Behaviors
============================

http://www.jfsowa.com/ikl/Goguen89.pdf

|*)

Section Behavior.

(* We use definition from http://www.jfsowa.com/ikl/Goguen89.pdf,
funny enough, the definition of the category is wrong., should be (X, Y, b'). Y is missing.

*)

Record beh := {
    behX : Type;
    behY : Type;

    b : list behX -> behY;
}.

Record beh_morphism_r (tX tY tX' tY': Type)
:= {
    fbeh : tX -> tX';
    gbeh : tY -> tY';
}.

(*
 This means that for the category Beh of behav-
iors (i.e., triples (Σ, Y, b), where Σ∗ b
−→Y is a function) and behavior morphisms
[i.e., (f, g) : (Σ, Y, b)→(Σ′, Y ′, b′), where Σ f
−→Σ′ and Y g
−→Y ′ are functions
with (g ◦b)(σ1σ2···σn) = b′(f (σ1)f (σ2)···f (σn))],

*)

Definition beh_morphism
    (A : beh) (B: beh) : Type
:=
    { ff : beh_morphism_r (behX A) (behY A) (behX B) (behY B)  &

(* (g ◦b)(σ1σ2···σn) = b′(f (σ1)f (σ2)···f (σn))] *)

    ∀ (σ: list (behX A)) ,
        (gbeh ff) ((b A) σ) = (b B) (map (fbeh ff) σ)

}.

Definition beh_morphism_map
    (A : beh) (B: beh)
    (M : beh_morphism A B)
    : beh_morphism_r (behX A) (behY A) (behX B) (behY B)
    := @projT1 _ _ M.

#[export] Program Instance beh_morphism_Setoid
    {A : beh} {B: beh} :
    Setoid (beh_morphism A B) := {|
        equiv := fun f1 f2 => (beh_morphism_map  f1) = (beh_morphism_map  f2)
    |}.

Definition beh_morphism_r_compose
    [X Y X' Y' X'' Y'': Type]
    (g : beh_morphism_r X' Y' X'' Y'')
    (f : beh_morphism_r X Y X' Y')

    : (beh_morphism_r X Y X'' Y'')
:= {|
        fbeh := (fbeh g) ∘ (fbeh f);
        gbeh := (gbeh g) ∘ (gbeh f);
    |}.

Definition beh_morphism_r_id (X Y : Type)
    : beh_morphism_r X Y X Y
:= {|
    fbeh := idmap;
    gbeh := idmap;
|}.

Program Definition beh_morphism_id
    (A : beh) :
    (beh_morphism A A)
    := (beh_morphism_r_id (behX A) (behY A) ;_).
Next Obligation.
    rewrite map_id. trivial.
Defined.

Program Definition beh_morphism_compose
    (A B C : beh)
    (g : beh_morphism B C)
    (f : beh_morphism A B)
    : beh_morphism A C
:= ((beh_morphism_r_compose
        (beh_morphism_map g)
        (beh_morphism_map f)); _).
Next Obligation.
    destruct f as [fa fH].
    destruct g as [ga gH].

    unfold beh_morphism_map in *.
    unfold fun_compose.
    simpl in *.

    specialize (fH σ).
    specialize (gH ((map (fbeh fa) σ))).
    now rewrite fH, gH, map_map.
Qed.

#[export]
Program Instance Beh : Category := {|
    obj     := beh;
    hom     := beh_morphism;
    homset  := @beh_morphism_Setoid;
    id      := @beh_morphism_id ;

    compose := @beh_morphism_compose;

|}.

(*| Definition of a functor Aut -> Beh |*)

Definition aut_beh_ (a : aut) (q : Q a) (l : list (Σ a)) : Y a :=
    y a (next_steps a q l).

Definition aut_beh (a : aut): beh :=
{|
    behX := (Σ a);
    behY := (Y a);

    b := aut_beh_ a (q0 a)
|}.

Definition
  fmap_aut_beh_r (x y : aut) (f : aut_morphism x y)
  : beh_morphism_r (Σ x) (Y x) (Σ y) (Y y)
    := {|
        fbeh := ((fΣ (aut_morphism_map f)) ) ;
        gbeh := ((fY (aut_morphism_map f)) ) ;
    |}.

Program Instance aut_to_beh_Functor: Aut ⟶ Beh :=  {
  fobj := aut_beh;
}.
Next Obligation.
    unfold beh_morphism.
    exists ( fmap_aut_beh_r f).

    destruct f.
    intros.
    unfold fmap_aut_beh_r.
    simpl in *.
    destruct a as [a a1].
    destruct a1 as [a1 a2].

    unfold aut_beh_ in *.

    assert (H: (fQ x0 (next_steps x (q0 x) σ) =
        (next_steps y (q0 y) (map (fΣ x0) σ)))).
    apply aut_morphism_next_steps.
    apply a.
    apply a2.
    rewrite <- H.
    apply a1.
Defined.

Next Obligation.
    proper.
    unfold fmap_aut_beh_r .
    rewrite H. trivial.
Defined.

End Behavior.
