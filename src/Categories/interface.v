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
From mathcomp Require Import finset fintype ssrbool ssreflect eqtype.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Oqarina.Configuration.
(*| .. coq:: |*)

(*|

Interface
=========

|*)

(*| .. coq:: none |*)
Section InterfaceCategory.
(*| .. coq:: |*)

(*|

In this section, we define the category of interfaces.

An interface is a finite set of some type. |*)

Variable Interface_Type : finType.

Definition Interface : Type := { set Interface_Type }.

(*|

Intuitively, interfaces are used to define the inputs and outputs of a "box". A box is a mapping from the powerset of :coq:`Interface_Type` to the powerset of :coq:`Interface_Type`. It corresponds to the fact that a component may be triggered by any subset of inputs on its interface, like in DEVS or AADL.

We also define the concept of a valid interface mapping, i.e., an interface so that inputs are mapped to a subset of outputs.

|*)

Definition Valid_Interface_Mapping
  (required provided : Interface)
  (f: Interface → Interface)
  : Prop
:=
  (∀ x : Interface,
    x \subset required -> (f x) \subset provided).

(*| From thes considerations, we define the concept of a "Box", a general component that is a valid interface mapping from the input interface, or input ports :coq:`inp`:, to an output interface, or output ports, :coq:`outp`. |*)

Record Box (required provided : Interface) : Type := mkBox {
    inp : Interface := required ;
    outp : Interface := provided ;
    f : Interface → Interface ;
    V:  Valid_Interface_Mapping required provided f }.

(*| We show that :coq:`Box` forms a category whose objects are :coq:`Interface`. |*)

Program Definition Box_id {i} : Box i i
  := {| f := fun x => x ; V := _ |}.
Next Obligation.
  unfold Valid_Interface_Mapping. intuition.
Defined.

Program Definition box_compose {i j k} :
  Box j k → Box i j → Box i k
  :=
  fun (f1: Box j k) (f2: Box i j) =>
    (mkBox i k (fun req => (f j k f1 (f i j f2 req))) ( _ )).
Next Obligation.
  destruct f1. destruct f2.
  unfold Valid_Interface_Mapping in *.
  intuition.
Defined.

#[local]
Ltac destruct_box_in_hyp :=
  repeat match goal with
    | [ H : Box _ _ |- _ ] => destruct H
  end; subst; simpl.

#[export] Program Instance Box_Setoid {X Y : Interface} :
  Setoid (Box X Y) := {|
  equiv := fun f1 f2 => (f X Y f1) = (f X Y f2)
|}.

Lemma box_compose_respects {i j k} :
  Proper (equiv ==> equiv ==> equiv) (@box_compose i j k).
Proof.
  proper; destruct_box_in_hyp.
  apply functional_extensionality.
  intros.

  assert (Hf1: f1 = f0) ; intuition.
  assert (Hf2: f2 = f3) ; intuition.

  rewrite Hf1. rewrite Hf2.
  reflexivity.
Qed.

Lemma box_id_left {i j} (f : Box i j) :
  box_compose Box_id f ≈ f.
Proof.
  now destruct_box_in_hyp.
Qed.

Lemma box_id_right {i j} (f : Box i j) :
  box_compose f Box_id ≈ f.
Proof.
  now destruct_box_in_hyp.
Qed.

Lemma box_compose_assoc {i j k l}
  (f : Box k l) (g : Box j k) (h : Box i j) :
  box_compose f (box_compose g h) ≈
    box_compose (box_compose f g) h.
Proof.
  now destruct_box_in_hyp.
Qed.

Definition InterfaceCat : Category := {|
  obj     := Interface;
  hom     := Box;
  homset  := @Box_Setoid;
  id      := @Box_id;

  compose := @box_compose;
  compose_respects := @box_compose_respects;

  id_left := @box_id_left;
  id_right := @box_id_right;
  comp_assoc := @box_compose_assoc;
  comp_assoc_sym := λ i j k l f g h,
    symmetry (@box_compose_assoc _ _ _ _ _ _ _);
|}.

(*| .. coq:: none |*)
End InterfaceCategory.
(*| .. coq:: |*)
