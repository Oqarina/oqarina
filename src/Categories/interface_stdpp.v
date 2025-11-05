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
Require Import stdpp.listset.
Require Import stdpp.gmap.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import -(notations)Category.Theory.Functor.

Declare Scope functor_scope.
Declare Scope functor_type_scope.
Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

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

In this section, we define two variants for the category of interfaces.

An interface is a finite set of some type. |*)

(* Let's InterfactType be a type. *)
Variable InterfaceType : Type.
Definition Interface : Type := listset InterfaceType.

(*|

Intuitively, interfaces are used to define the inputs and outputs of a "box". A box is a mapping from the powerset of :coq:`Interface_Type` to the powerset of :coq:`Interface_Type`. It corresponds to the fact that a component may be triggered by any subset of inputs on its interface, like in DEVS or AADL.

We also define the concept of a valid interface mapping, i.e., an interface so that inputs are mapped to a subset of outputs.

|*)

Definition Valid_Interface_Mapping
  (required provided : Interface)
  (f: Interface → Interface)
  : Prop
:=
  (∀ x : Interface, x ⊆ required -> (f x) ⊆ provided).

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

#[local]
Ltac destruct_box_in_hyp :=
  repeat match goal with
    | [ H : Box _ _ |- _ ] => destruct H
  end; subst; simpl.

Program Definition box_compose {i j k} :
  Box j k → Box i j → Box i k
  :=
  fun (f1: Box j k) (f2: Box i j) =>
    (mkBox i k (fun req => (f j k f1 (f i j f2 req))) ( _ )).
Next Obligation.
  destruct_box_in_hyp.
  unfold Valid_Interface_Mapping in *.
  intuition.
Defined.

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

(*| Alternatively, one can define the concept of :coq:`EmptyBox`, i.e. a box without
any implementation. This allows to build the category of "empty boxes" or :coq:`EmptyInterfaceCat`.
We build a forgetfult functor from :coq:`InterfaceCat` to :coq:`EmptyInterfaceCat`.|*)

Definition Empty_Box (required provided : Interface) : Type := unit.

(*| We show that :coq:`Empty_Box` forms a category whose objects
are :coq:`Interface`.

Note: Proofs are really trivial as we let Coq dependent types
mechanism do all the work.|*)

Program Definition Empty_Box_id {i} : Empty_Box i i := _.

Program Definition empty_box_compose {i j k} :
  Empty_Box j k → Empty_Box i j → Empty_Box i k := _.

#[export] Program Instance Empty_Box_Setoid {X Y : Interface} :
  Setoid (Empty_Box X Y) := {|
  equiv := fun f1 f2 => True;
|}.

Program Definition EmptyInterfaceCat : Category := {|
  obj     := Interface;
  hom     := Empty_Box;
  homset  := @Empty_Box_Setoid;
  id      := @Empty_Box_id;

  compose := @empty_box_compose;
  (* Note: we let Coq's solver infer the other elements
    of EmptyInterfaceCat. *)
|}.

(*| :coq:`Box_to_EmptyBox_Functor` is a forgetful functor, mapping
:coq:`InterfaceCat` to :coq:`EmotyInterfaceCat`. |*)

Program Instance Box_to_EmptyBox_Functor: InterfaceCat ⟶ EmptyInterfaceCat :=  {
  fobj := Id;
}.

(* Alternate definition, using a record *)

Record Empty_Box': Type := mkEmpty_Box' {
    inp' : Interface ;
    outp' : Interface ;
}.

Definition Empty_Box_to_Empty_Box' {i j} (b: Empty_Box i j)
  : Empty_Box' := mkEmpty_Box' i j.

(*| Unfortunately, one cannot demonstrate that :coq:`Empty_Box'` is actually a category. We miss the type enforcements brought by Coq dependent type.  |*)

(*| .. coq:: none |*)
End InterfaceCategory.
(*| .. coq:: |*)

(*|

Examples
========

Example #1: basic interface
---------------------------

A first naive example considers interfaces as intergers, and a basic
mapping from inputs to outputs.

|*)

Module Test_Interface.

Definition interface_nat := @Interface nat.

Open Scope nat_scope.

Definition i1 : interface_nat := {[ 1 ; 2]}.
Definition i2 : interface_nat := {[ 3 ; 4]}.

Definition b1 : Empty_Box _ i1 i2 := tt.
Definition b2 : Empty_Box _ i2 i2 := tt.

Definition b3 : Empty_Box _ i1 i2 := empty_box_compose _ b1 b2.

Definition basic_f1 (x : nat) : nat :=
    match x with
        | 1 => 3 | 2 => 4 | _ => 0
    end.

Definition f1 (x : interface_nat) : interface_nat :=
    set_map basic_f1 x.

Lemma test_f1: f1 i1 = i2.
Proof. set_solver. Qed.

Lemma v_i1_i2_f1: Valid_Interface_Mapping _ i1 i2 f1.
Proof.
    unfold Valid_Interface_Mapping.
    set_solver.
Qed.

Program Definition Box1 : Box _ i1 i2 :=
  {| f := f1; V := v_i1_i2_f1 |}.

End Test_Interface.
(*| .. coq:: |*)

Require Import Oqarina.Categories.family_listset.
Require Import Oqarina.Categories.family.
Require Import stdpp.listset.

Module Test_Interface_2.

Definition Interface_Type := nat.
Definition Port_Type := unit.

Definition Ports : listset Interface_Type -> Port_Type :=
  (λ x,  tt).

Definition PortFamily := finiteFamily Interface_Type Port_Type Ports.

Definition Port_Interface : Type := family_index PortFamily.

Definition i1 : Port_Interface := {[ 1 ; 2 ]}.
Definition i2 : Port_Interface := {[ 3 ; 4 ]}.

Definition b1 : Empty_Box _ i1 i2 := tt.
Definition b2 : Empty_Box _ i2 i2 := tt.

Definition b3 : Empty_Box _ i1 i2 := empty_box_compose _ b1 b2.

Definition basic_f1 (x : nat) : nat :=
    match x with
        | 1 => 3 | 2 => 4 | _ => 0
    end.

Definition f1 (x : Port_Interface) : Port_Interface :=
    set_map basic_f1 x.

Lemma test_f1: f1 i1 = i2.
Proof. set_solver. Qed.

Lemma v_i1_i2_f1: Valid_Interface_Mapping _ i1 i2 f1.
Proof.
    unfold Valid_Interface_Mapping.
    set_solver.
Qed.

Program Definition Box1 : Box _ i1 i2 :=
  {| f := f1; V := v_i1_i2_f1 |}.

End Test_Interface_2.
