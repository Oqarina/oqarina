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
(* Packages from the Coq toolset: lists, booleans, and relations *)
Require Import Coq.Lists.List.
Import ListNotations. (* Part of Coq.Lists.List *)
Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.PropExtensionality.

(* Packages from mathcomp, most specifically for finite sets (finset), finite types (fintype), and associated boolean operators (ssrbool). *)

From mathcomp Require Import finset fintype ssrbool eqtype ssreflect.

(* Definition from the coq-category package *)

Require Import Category.Lib.
Require Import Category.Construction.Product.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.

(* In the following, we control how goals in proof scripts are handled. We opted for a strict mode to ease proof readabiltiy. *)
Set Default Goal Selector "1".
Set Bullet Behavior "Strict Subproofs". (* This is disabled by ssreflect *)

Require Import Oqarina.CoqExt.finset_Ext.
Require Import Oqarina.Categories.interface.
Require Import Oqarina.Tactics.oq_tactics.
(*| .. coq:: |*)

(*|

Wiring Diagram
==============

|*)

(*| .. coq:: none |*)
Section Wiring_Rel.
(*| .. coq:: |*)

(*|

Introduction
------------

Wiring diagrams are a generic way of connecting "boxes" using wires. Wiring diagrams extends the Box category.

Let :coq:`Wire_Type` denote a general finite type, and :coq:`Interface` be a finite set of wires. We can define a box by its input and output interace. |*)

Variable Wire_Type : finType.

Definition Interface : Type := { set Wire_Type }.

Record Box: Type := {
    inp : Interface ;
    outp : Interface ;
}.

(*| We define a connection map as a binary relation between two wires. We opted for a relation as it is more general than a function. |*)
Definition connection_map := relation Wire_Type.

(*| We can now define a :coq:`Wiring`, a way to connect two boxes. In this definition,

* :coq:`X` is the inner Box, :coq:`Y` the outer Box
* :coq:`phi_int` is the set of internal wires
* :coq:`phi_in` is connecting :coq:`inp (x)` to  one of :coq:`phi_int` or :coq:`inp (y)`
* :coq:`phi_out` is connecting :coq:`outp X` to  one of :coq:`phi_int` or :coq:`outp (y)`

and :coq:`Valid_Wiring` ensures those constraints are respected. We also expect the sets of input and output ports and internal connections to be all disjoint. |*)

Record Wiring (X Y : Box) : Type := {
    phi_int : Interface;
    phi_in : connection_map;
    phi_out : connection_map;
}.

Definition Valid_Wiring_Mapping (X Y : Box) (W : Wiring X Y) :=
    ∀ (x y : Wire_Type),
    ((phi_in  _ _ W) x y -> (x \in inp X) /\ (y \in (inp Y :|: (phi_int _ _ W)))) /\
    ((phi_out _ _ W) x y -> (y \in (outp Y :|: (phi_int _ _ W)) /\ (x \in outp X))).

Definition Valid_Wiring (X Y : Box) (W : Wiring X Y) :=
    [disjoint inp  X & phi_int _ _ W] /\
    [disjoint outp X & phi_int _ _ W] /\
    [disjoint inp  Y & phi_int _ _ W] /\
    [disjoint outp Y & phi_int _ _ W] /\
    Valid_Wiring_Mapping X Y W.

Axiom prout2: ∀ {i j k l} (f : Wiring k l) (g : Wiring j k)  (h : Wiring i j),
    Valid_Wiring i j h -> Valid_Wiring j k g -> Valid_Wiring k l f ->
        [disjoint inp k &  phi_int _ _ h ] /\
        [disjoint outp k & phi_int _ _ h ].

Axiom prout4: ∀ {j k l} (f : Wiring k l) (g : Wiring j k),
    Valid_Wiring j k g -> Valid_Wiring k l f ->
    [disjoint inp j & phi_int _ _ f :|: phi_int _ _ g] /\
        [disjoint outp j & phi_int _ _ f :|: phi_int _ _ g] /\
        [disjoint inp l & phi_int _ _ f :|: phi_int _ _ g] /\
        [disjoint outp l & phi_int _ _ f :|: phi_int _ _ g].

Axiom prout5: ∀ {i j k l} (f : Wiring i k) (g: Wiring j l) ,
    Valid_Wiring i k f -> Valid_Wiring j l g ->
    [disjoint phi_int _ _ f & inp j] /\ [disjoint phi_int _ _ g & inp i] /\
    [disjoint phi_int _ _ f & outp j] /\ [disjoint phi_int _ _ g & outp i] /\
    [disjoint phi_int _ _ f & inp l] /\ [disjoint phi_int _ _ g & inp k] /\
    [disjoint phi_int _ _ f & outp l] /\ [disjoint phi_int _ _ g & outp k].

(*| We define a setoid relation for wirings, |*)

#[export] Program Instance Wiring_Setoid {X Y : Box} :
    Setoid (Wiring X Y) := {|
        equiv := fun W1 W2 =>
        ( phi_int _ _ W1 = phi_int _ _ W2 ) /\
            (∀ x y, (phi_in _ _ W1) x y <-> (phi_in _ _ W2) x y) /\
            (∀ x y, (phi_out _ _ W1) x y <-> (phi_out _ _ W2) x y)
    |}.
Next Obligation.
    equivalence.
    1-2:specialize (H0 x0 y0); intuition.

    1-2:specialize (H1 x0 y0); intuition.

    rewrite H; intuition.

    1-2: specialize (H1 x0 y0) ;
        specialize (H3 x0 y0); intuition.

    1-2: specialize (H2 x0 y0) ;
        specialize (H4 x0 y0); intuition.
Defined.

(*|
Wiring diagrams as a category
-----------------------------

We proceed in two steps for defining a category over valid wiring diagrams. First, we prove general results on wiring diagrams, assuming that these diagrams are valid in the hypotheses. Them, we define the actual category :coq:`WiringD`.

Compose operator
^^^^^^^^^^^^^^^^
|*)

Definition compose_connection_map (c1 c2: connection_map) :=
    fun x z => exists2 y, c1 x y & c2 y z.

(* /!\ We write Wiring_compose g f to mean g o f X -> Z *)

Definition Wiring_compose {X Y Z}
    (WYZ : Wiring Y Z ) (WXY : Wiring X Y)
    : Wiring X Z
:=
{|
    phi_int := (phi_int _ _ WYZ) :|: (phi_int _ _ WXY);
    phi_in :=
        (fun x z =>
            if (x \in (inp X)) then
                (exists2 y, (phi_in _ _ WXY) x y & (phi_in _ _ WYZ) y z)
                \/ ((phi_in _ _ WXY) x z /\ z \in (phi_int _ _ WXY))
            else False);

    phi_out :=
        (fun x z =>
            if (z \in (outp Z)) || (z \in (phi_int _ _ WYZ)) then
                (compose_connection_map (phi_out _ _ WXY)
                                        (phi_out _ _ WYZ)) x z
            else if (z \in (phi_int _ _ WXY)) then (phi_out _ _ WXY) x z
            else False)
|}.

(*|
Id
^^

The id of a Wiring connects all inputs of the inner box to the input of the outer box, all outputs of the inner box to the outer box and has no internal wires.

|*)

Definition Wiring_id {X} : Wiring X X := {|
    phi_int := set0;

    (* phi_in: inp (X) -> set0 + inp (X) *)
    phi_in := (fun x y => x \in (inp X) /\ x = y);

    (* phi_out: inp (Y) + set0 -> inp (Y) *)
    phi_out := (fun x y => x \in (outp X) /\ x = y);
|}.

(*| :coq:`Wiring_Id` is actually a valid Wiring. |*)

Lemma Valid_Wiring_Wiring_id: ∀ X,
    Valid_Wiring X X (Wiring_id).
Proof.
    unfold Wiring_id, Valid_Wiring.
    intuition ; simpl.

    1-4: simplify_finset.

    unfold Valid_Wiring_Mapping. simpl.
    simplify_finset.
Qed.

Lemma Wiring_id_right {i j} (f : Wiring i j) :
    Valid_Wiring _ _ f -> (Wiring_compose f (Wiring_id)) ≈ f.
Proof.
    unfold Wiring_compose, Wiring_id, Valid_Wiring, Valid_Wiring_Mapping.
    intro_proof ; my_tauto ;
        simplify_finset ;
        split_goals.

    - intros. destruct (x \in inp i) eqn:x_inpi.
        + my_tauto.
            * smart_destruct H4.
            * by simplify_finset.
        + my_tauto.
    - destruct_if.
        + left. exists x ; my_tauto.
        + specialize (H3 x y). my_tauto.
            by rewrite H3 in if0.
    - unfold compose_connection_map in *.
        smart_destruct H4.

    - specialize (H3 x y). destruct_if.
        + unfold compose_connection_map. exists x ; my_tauto.
        + rewrite_in_setU. my_tauto.
            by rewrite H5 in if0.
Qed.

Lemma Wiring_id_left {i j} (f : Wiring i j) :
    Valid_Wiring _ _ f -> (Wiring_compose (Wiring_id) f) ≈ f.
Proof.
    unfold Wiring_compose, Wiring_id, Valid_Wiring, Valid_Wiring_Mapping,
        compose_connection_map.
    intro_proof ; my_tauto ;
        simplify_finset ;
        split_goals.

    - smart_destruct H4.

    - destruct_if ;
        specialize (H3 x y); my_tauto ; rewrite_in_setU.
        + rewrite orb_True2 in H6 ; destruct H6.
            * left. exists y ; my_tauto.
            * right. my_tauto.

        + rewrite H3 in if0. intuition.

    - smart_destruct H4.

    - rewrite orb_false_r.
        specialize (H3 x y); destruct_if.
        + exists y ; my_tauto.
        + rewrite_in_setU. my_tauto.
            rewrite if0 in H5. rewrite orb_false_l in H5.
            my_tauto.
Qed.

(*|
respects lemma
^^^^^^^^^^^^^^
|*)

Lemma Wiring_compose_respects {X Y Z} :
    Proper (equiv ==> equiv ==> equiv) (@Wiring_compose X Y Z).
Proof.
    proper.

    -
    (* phi_int _ _ x :|: phi_int _ _ x0 = phi_int _ _ y :|: phi_int _ _ y0 *)
    destruct X0 ; destruct X1.
    rewrite H. rewrite H1. trivial.

    -
    (*

    if x1 \in inp X then
        (exists2 y2 : Wire_Type, phi_in _ _ y0 x1 y2 & phi_in _ _ y y2 y1) \/
        phi_in _ _ y0 x1 y1 /\ y1 \in phi_int _ _ y0
    else False

    *)

    destruct X0 ; destruct X1.
    my_tauto.

    destruct_if.
    + smart_destruct H.
        * left. exists L.
            -- specialize (H3 x1 L). intuition.
            -- specialize (H1 L y1). intuition.
        * right. specialize (H3 x1 y1).
            split. intuition.
            rewrite <- H2. trivial.

    + intuition.

    -
    (*
    if x1 \in inp X then
        (exists2 y2 : Wire_Type, phi_in _ _ x0 x1 y2 & phi_in _ _ x y2 y1) \/
        phi_in _ _ x0 x1 y1 /\ y1 \in phi_int _ _ x0
    else False

    *)

    destruct X0 ; destruct X1.
    smart_destruct H.
    + left.
    exists L.
    * specialize (H3 x1 L). intuition.
    * specialize (H1 L y1). intuition.

    + right. split.
    * specialize (H x1 y1). intuition.
    * rewrite H2. trivial.

    -
    destruct X0 ; destruct X1.
    rewrite <- H2.
    rewrite <- H0.
    unfold compose_connection_map in *.

    destruct_if.
    + smart_destruct H.
        exists L.
        * specialize (H4 x1 L). intuition.
        * specialize (H5 L y1). intuition.

    + destruct_if.
        * my_tauto. specialize (H4 x1 y1). intuition.
        * intuition.

    -
    destruct X0 ; destruct X1.
    rewrite H2. rewrite H0.
    unfold compose_connection_map in *.

    destruct_if.
        + smart_destruct H. exists L.
            * specialize (H4 x1 L). intuition.
            * specialize (H5 L y1). intuition.

        + destruct_if.
            * my_tauto. specialize (H4 x1 y1). intuition.
            * intuition.
Qed.

(*|
composition lemmas
^^^^^^^^^^^^^^^^^^

We show that the composition of two valid wirings is also valid.

|*)
Lemma Wiring_compose_Valid_Wiring_Mapping {j k l}
        (f : Wiring k l) (g : Wiring j k) :
            Valid_Wiring_Mapping j k g ->
            Valid_Wiring_Mapping k l f ->

            Valid_Wiring_Mapping j l (Wiring_compose f g).
Proof.
    unfold Wiring_compose.
    unfold Valid_Wiring_Mapping in *.
    intro_proof.

    - destruct (x \in inp j) eqn:x_inpj.
      + trivial.
      + simpl in H1. rewrite x_inpj in H1. intuition.

    - simpl in H1. destruct (x \in inp j) eqn:x_inpj.
      + smart_destruct H1.
        * specialize (H x L). specialize (H0 L y). my_tauto.
          simplify_finset. rewrite_in_setU. auto with *.
        * specialize (H x y). rewrite_in_setU. rewrite R. auto with *.

      + intuition.

    - simpl in H1. rewrite_in_setU.
      unfold compose_connection_map in *.
      destruct ((y  \in outp l) || (y  \in phi_int _ _ f)).
      + smart_destruct H1.
        specialize (H x L). specialize (H0 L y). my_tauto.
        simplify_finset. rewrite_in_setU.
        rewrite orb_True2  in H2.
        destruct H2 ; rewrite H2 ; auto with *.
      + smart_destruct H1 ; auto with *.

    - simpl in H1.
       unfold compose_connection_map in *.
       destruct ((y  \in outp l) || (y  \in phi_int _ _ f) ).
       + smart_destruct H1.
         specialize (H x L). specialize (H0 L y). my_tauto.
       + smart_destruct H1.
         specialize (H x y). specialize (H0 x y). my_tauto.
    Defined.

Lemma Wiring_compose_Valid_Wiring {j k l}
        (f : Wiring k l) (g : Wiring j k) :
            Valid_Wiring j k g ->
            Valid_Wiring k l f ->

            Valid_Wiring j l (Wiring_compose f g).
Proof.
    intros Hg Hf.

    assert ([disjoint inp j & phi_int _ _ f :|: phi_int _ _ g] /\
        [disjoint outp j & phi_int _ _ f :|: phi_int _ _ g] /\
        [disjoint inp l & phi_int _ _ f :|: phi_int _ _ g] /\
        [disjoint outp l & phi_int _ _ f :|: phi_int _ _ g]).
    eapply prout4 ; trivial.

    unfold Valid_Wiring in *.
    my_tauto.
    apply Wiring_compose_Valid_Wiring_Mapping ; intuition.
Defined.

(*| The composition of wirings is associative. |*)

Lemma Wiring_compose_assoc {i j k l}
    (f : Wiring k l) (g : Wiring j k)
    (h : Wiring i j):
    Valid_Wiring i j h ->
    Valid_Wiring j k g ->
    Valid_Wiring k l f ->
        Wiring_compose f (Wiring_compose g h) ≈
        Wiring_compose (Wiring_compose f g) h.
Proof.
    intros Hh Hg Hf.
    unfold Valid_Wiring in *.

    assert (Hd: [disjoint inp k &  phi_int _ _ h ] /\
        [disjoint outp k & phi_int _ _ h ]).
    eapply prout2.
    apply Hh. apply Hg. apply Hf.

    unfold Wiring_compose. simpl. my_tauto.

    - rewrite setUA. reflexivity.
    - split_goals.
      + destruct_if.
      * smart_destruct H16. destruct H17.
        -- left. exists x0.
        ++ trivial.
        ++ destruct_if.
        ** left. exists L ; trivial.
        ** specialize (H10 x0 L). intuition.
           contradiction_in_H H19 if1.
        -- left. exists L.
        ++ trivial.
        ++ assert (HL: L \in inp j = false).
           eapply disjointFl. apply H13. intuition.
           rewrite HL.

           unfold Valid_Wiring_Mapping in *.
           specialize (H15 x L). specialize (H5 L y). my_tauto.

           assert (L \in inp k = false).
           eapply disjointFl. apply H. trivial.
           contradiction_in_H H23 H5.

        -- smart_destruct H16.
           left. exists L.
        ++ trivial.
        ++ specialize (H15 x L). specialize (H10 L y). my_tauto.

           rewrite in_setU in H19.
           rewrite in_setU in R.
           rewrite orb_True2 in H19.
           rewrite orb_True2 in R.
           right. my_tauto.

           assert (y \in inp k = false).
           eapply disjointFl. apply H. intuition.
           contradiction_in_H H22 H19.

        -- right. my_tauto.

      * intuition.

      + destruct_if.
      * smart_destruct H16.
        destruct (L \in inp j) eqn:L_in_inpj.
        -- smart_destruct H16.
        ++ left. exists L0.
        ** left. exists L; trivial.
        ** trivial.

        ++ right. my_tauto. left. exists L; trivial.
        rewrite in_setU. auto with *.

        -- specialize (H15 x L). my_tauto.

        -- right. my_tauto. right. my_tauto. rewrite in_setU. auto with *.

        * intuition.

    - unfold compose_connection_map. repeat rewrite in_setU.
    split_goals.
    + destruct ((y \in outp l) || (y \in phi_int _ _ f)) eqn:H_y_outp_l_phi_int_f.

    * assert ([|| y  \in outp l,  y  \in phi_int _ _ f  | y  \in phi_int _ _ g]).
    rewrite orb_true_iff in H_y_outp_l_phi_int_f.
    destruct H_y_outp_l_phi_int_f ; rewrite H17 ; auto with *.
    rewrite H17.

    smart_destruct H16.
    -- exists L0 ; my_tauto.
       exists L ; my_tauto.
    -- rewrite orb_false_iff in if0.
    specialize (H15 x L). specialize (H5 L y). my_tauto.
    contradiction_in_H H22 H18.

    * rewrite orb_false_iff in H_y_outp_l_phi_int_f.
    my_tauto. rewrite H17. rewrite H18. repeat rewrite orb_false_l.

    -- destruct (y \in phi_int _ _ g) eqn:y_phi_int_g.
    ++ rewrite orb_true_l in H16. rewrite orb_true_r in H16.
    smart_destruct H16. exists L ; trivial.
    ++ rewrite orb_false_l in H16. rewrite orb_false_r in H16.

    destruct (y \in phi_int _ _ h) eqn:y_phi_int_h.

    ** assert (y \in outp k = false).
    eapply disjointFl. apply H0. trivial.
    rewrite H19 in H16 ; trivial.
    ** intuition.

    + destruct ((y \in outp l) || (y \in phi_int _ _ f)) eqn:H_y_outp_l_phi_int_f.

    * assert ([|| y  \in outp l,  y  \in phi_int _ _ f  | y  \in phi_int _ _ g]).
    rewrite orb_true_iff in H_y_outp_l_phi_int_f.
    destruct H_y_outp_l_phi_int_f ; rewrite H17 ; auto with *.
    rewrite H17 in H16.

    smart_destruct H16.
    smart_destruct H16.

    specialize (H15 x L). specialize (H10 L L0). specialize (H5 L0 y).
    my_tauto.
    exists L0. rewrite H21. rewrite orb_true_l. exists L ; trivial. trivial.

    * rewrite orb_false_iff in H_y_outp_l_phi_int_f.
    my_tauto. rewrite H17 in H16. rewrite H18 in H16.
    repeat rewrite orb_false_l in H16.

    destruct (y  \in phi_int _ _ g) eqn:y_phi_int_g.
    -- rewrite orb_true_l. rewrite orb_true_r.
    intuition.

    -- rewrite orb_false_l. rewrite orb_false_r.
    destruct (y  \in phi_int _ _ h) eqn:y_phi_int_h.

    ** assert (y \in outp k = false).
    eapply disjointFl. apply H0. trivial.
    rewrite H19 ; trivial.
    ** intuition.
Qed.

(*|

The :coq:`WiringD` catregory
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Ww combine the previous results to build the category of valid wirings, :coq:`WiringD`.

|*)

Definition WiringD (X Y : Box) : Type :=
    { W : Wiring X Y & Valid_Wiring  X Y W }.

Program Definition WiringD_id {i} : WiringD i i := (Wiring_id; _).
Next Obligation.
    apply Valid_Wiring_Wiring_id.
Defined.

#[export] Program Instance WiringD_Setoid {X Y} :
    Setoid (WiringD X Y) := {|
        equiv := fun '(f;_) '(g;_) => f ≈ g
    |}.
Next Obligation.
    equivalence.
    - destruct x. intuition.
    - destruct x, y. intuition.

    1-2: specialize (H1 x1 y); intuition.
    1-2: specialize (H2 x1 y); intuition.

    - destruct x, y, z. intuition.
    + rewrite <- H1. intuition.
    + specialize (H3 x2 y). specialize (H0 x2 y). apply H0. apply H3. intuition.
    + specialize (H3 x2 y). specialize (H0 x2 y). apply H3. apply H0. intuition.
    + specialize (H4 x2 y). specialize (H5 x2 y). apply H5. apply H4. intuition.
    + specialize (H4 x2 y). specialize (H5 x2 y). apply H4. apply H5. intuition.
Defined.

Program Definition WiringD_compose {X Y Z} :
    WiringD Y Z → WiringD X Y → WiringD X Z
:=
λ '(g; Hg) '(f; Hf),
    (Wiring_compose g f; _).
Next Obligation.
    apply Wiring_compose_Valid_Wiring ; intuition.
Defined.

Lemma WiringD_compose_respects {X Y Z} :
    Proper (equiv ==> equiv ==> equiv) (@WiringD_compose X Y Z).
Proof.
    proper.

    unfold WiringD_compose ;
        destruct x, y, x0, y0.

        destruct X0 ; destruct X1.
        destruct x. destruct x0.
        simpl in *.

        split.
        2: split.

        - subst ; intuition.

        - intros. destruct (x \in inp X) eqn:x_inp_X.
        + split.
            * intros Hphi1. destruct Hphi1. destruct H3.
                -- left. exists x0.
                    destruct H2 as [H2a H2b]. specialize (H2a x x0).
                    apply H2a ; intuition.
                    destruct H0 as [H0a H0b]. specialize (H0a x0 y).
                    apply H0a ; intuition.
                -- right. split.
                    ++ destruct H2 as [H2a H2b].
                        specialize (H2a x y). apply H2a ; intuition.
                    ++ subst. intuition.
            * intros.
                -- destruct H3.
                    left. destruct H3. exists x0.
                    destruct H2 as [H2a H2b]. specialize (H2a x x0).
                    apply H2a ; intuition.
                    destruct H0 as [H0a H0b]. specialize (H0a x0 y).
                    apply H0a ; intuition.
                    right. split.
                    destruct H2 as [H2a H2b]. specialize (H2a x y).
                    apply H2a ; intuition.
                    subst ; intuition.
            + intuition.

        - unfold compose_connection_map. intros.
        destruct ((y \in outp Z) || (y \in phi_int0)) eqn:y_outp_z_phi_int0.
        split.
        + intros. subst. rewrite y_outp_z_phi_int0. destruct H3.
            exists x0.

            * destruct H2 as [H2a H2b]. specialize (H2b x x0).
                apply H2b ; intuition.

            * destruct H0 as [H0a H0b]. specialize (H0b x0 y).
                apply H0b ; intuition.

        + intros. subst. rewrite y_outp_z_phi_int0 in H3. destruct H3. exists x0.
            * destruct H2 as [H2a H2b]. specialize (H2b x x0). apply H2b ; intuition.
            * destruct H0 as [H0a H0b]. specialize (H0b x0 y). apply H0b ; intuition.

        + rewrite orb_false_iff in y_outp_z_phi_int0. destruct y_outp_z_phi_int0 as [y_outp_z y_phi_int0]. subst. rewrite y_outp_z. rewrite y_phi_int0. simpl.
        destruct H2 as [H2a H2b]. specialize (H2b x y).
        split.
        * destruct (y \in phi_int _ _ x2). apply H2b. intuition.
        * destruct (y \in phi_int _ _ x2). apply H2b. intuition.
Defined.

Lemma WiringD_id_right {i j} (f : WiringD i j) :
    WiringD_compose f (WiringD_id) ≈ f.
Proof.
    destruct f as [f Hf].
    unfold WiringD_compose.
    unfold WiringD_id.
    simpl.
    apply Wiring_id_right.
    trivial.
Defined.

Lemma WiringD_id_left {i j} (f : WiringD i j) :
    WiringD_compose (WiringD_id) f ≈ f.
Proof.
    destruct f as [f Hf].
    unfold WiringD_compose.
    unfold WiringD_id.
    simpl.
    apply Wiring_id_left.
    trivial.
Defined.

Lemma WiringD_compose_assoc {i j k l}
    (f : WiringD k l) (g : WiringD j k)
    (h : WiringD i j):

        WiringD_compose f (WiringD_compose g h) ≈
        WiringD_compose (WiringD_compose f g) h.
Proof.
    destruct f as [f Hf].
    destruct g as [g Hg].
    destruct h as [h Hh].
    unfold WiringD_compose.
    apply Wiring_compose_assoc ; trivial.
Defined.

(*| From the previous results, we can now define :coq:`WiringDCat`, the category of Wiring diagrams. |*)

#[export]
Program Instance WiringDCat : Category := {|
    obj     := Box;
    hom     := WiringD;
    homset  := @WiringD_Setoid;
    id      := @WiringD_id;

    compose := @WiringD_compose;
    compose_respects := @WiringD_compose_respects;

    id_left := @WiringD_id_left;
    id_right := @WiringD_id_right;

    comp_assoc := @WiringD_compose_assoc;
    comp_assoc_sym := λ i j k l f g h,
        symmetry (@WiringD_compose_assoc _ _ _ _ _ _ _);
|}.

(*|

Wiring diagram as a monoidal category
=====================================

In this section, we extend :coq:`WiringD` to form a monoidal category. We define a :math:`+` operator to combine two boxes, and then show relevant lemmas to conclude.

We start by defining a plus operator on :coq:`Box`, and then extend it to :coq:`Wiring`. We then prove all lemmas for :coq:`WiringD` and conclude.
|*)

Definition Box0 := {| inp := set0; outp := set0 |}.

Definition box_plus (b1 : Box) (b2 : Box): Box :=
    {| inp := (inp b1) :|: (inp b2) ; outp := (outp b1) :|: (outp b2) |} .

Lemma box_plus_zeror: forall b, box_plus b Box0 = b.
Proof.
    intros. unfold box_plus, Box0.
    simplify_finset. trivial.
Qed.

Lemma box_plus_zerol: forall b, box_plus Box0 b = b.
Proof.
    intros. unfold box_plus, Box0.
    simplify_finset. trivial.
Qed.

Lemma box_plus_associative: forall (b1 b2 b3: Box),
    box_plus (box_plus b1 b2) b3 = box_plus b1 (box_plus b2 b3).
Proof.
    intros. unfold box_plus. simpl.
    rewrite setUA. rewrite setUA. reflexivity.
Defined.

Lemma box_plus_commutative: forall (b1 b2: Box),
    box_plus b1 b2 = box_plus b2 b1.
Proof.
    intros. unfold box_plus.
    f_equal ;
      rewrite setUC; reflexivity.
Qed.

Definition connection_map0 : connection_map := (fun a b => False).

Definition connection_map_plus (x y: connection_map) : connection_map :=
    (fun a b => x a b \/ y a b).

Definition Wiring_plus {i j k l} (w1 : Wiring i k) (w2: Wiring j l)
    : Wiring (box_plus i j) (box_plus k l)
:= {|
    phi_int := (phi_int _ _ w1) :|: (phi_int _ _ w2);
    phi_in := connection_map_plus (phi_in _ _ w1) (phi_in _ _ w2);
    phi_out := connection_map_plus (phi_out _ _ w1) (phi_out _ _ w2);
|}.

Lemma Valid_Wiring_plus {i j k l}: forall (f : Wiring i k) (g: Wiring j l),
    Valid_Wiring i k f -> Valid_Wiring j l g ->
        Valid_Wiring _ _ (Wiring_plus f g).
Proof.
    intros f g Hf Hg.
    assert ([disjoint phi_int _ _ f & inp j]
            /\ [disjoint phi_int _ _ g & inp i]
            /\ [disjoint phi_int _ _ f & outp j]
            /\ [disjoint phi_int _ _ g & outp i]
            /\ [disjoint phi_int _ _ f & inp l]
            /\ [disjoint phi_int _ _ g & inp k]
            /\ [disjoint phi_int _ _ f & outp l]
            /\ [disjoint phi_int _ _ g & outp k]).
    apply prout5 ; trivial.
    unfold Valid_Wiring, Wiring_plus, Valid_Wiring_Mapping, connection_map_plus.
    destruct Hf, Hg.
    intuition ;
    simpl.

    1-4: apply disjointU2 ; trivial.

    - simpl in H16. destruct H16.
        + specialize (H11 x y). assert (x \in inp i). now apply H11.
            rewrite in_setU. auto with *.
        + specialize (H12 x y). assert (x \in inp j). now apply H12.
            rewrite in_setU. auto with *.

    - simpl in H16. destruct H16.
        + specialize (H11 x y).
            assert (y \in inp k :|: phi_int _ _ f = true). now apply H11.
            rewrite in_setU in H18. repeat rewrite in_setU.

            rewrite orb_true_iff in H18.
            destruct H18.
            * rewrite H18; intuition.
            * rewrite H18; auto with *.

        + specialize (H12 x y).
            assert (y \in inp l :|: phi_int _ _ g = true). intuition.

            rewrite in_setU in H18. repeat rewrite in_setU.

            rewrite orb_true_iff in H18.
            destruct H18.
            * rewrite H18; auto with *.
            * rewrite H18; auto with *.

    - simpl in H16. destruct H16.
        + specialize (H11 x y).
            assert (y \in outp k :|: phi_int _ _ f  = true). now apply H11.
            rewrite in_setU in H18. repeat rewrite in_setU.
            rewrite orb_true_iff in H18.
            destruct H18.
            * rewrite H18; intuition.
            * rewrite H18; auto with *.

        + specialize (H12 x y).
            assert (y \in outp l :|: phi_int _ _ g = true). intuition.

            rewrite in_setU in H18. repeat rewrite in_setU.

            rewrite orb_true_iff in H18.
            destruct H18.
            * rewrite H18; auto with *.
            * rewrite H18; auto with *.

    - simpl in H16. destruct H16.
        + specialize (H11 x y).
            assert (x \in outp i = true). now apply H11.
            repeat rewrite in_setU.
            rewrite H18; intuition.

        + specialize (H12 x y).
            assert (x \in outp j = true). intuition.

            rewrite in_setU.
            rewrite H18; auto with *.
Qed.

Definition Wiring_0 : Wiring Box0 Box0  := {|
    phi_int := set0;
    phi_in := connection_map0;
    phi_out := connection_map0;
|}.

Lemma Valid_Wiring_Mapping_Wiring_0: Valid_Wiring _ _ Wiring_0.
Proof.
    unfold Valid_Wiring, Wiring_0, Valid_Wiring_Mapping,
        connection_map0.
    simpl.
    split_goals ;
        apply disjoint_set0.
Qed.

Lemma Wiring_plus_compose_assoc { b3 b4 b1 b2 b b0 }: forall
    (x : Wiring b1 b)
    (x0 : Wiring b2 b0)
    (x1 : Wiring b3 b1)
    (x2 : Wiring b4 b2),
        Valid_Wiring b1 b x -> Valid_Wiring b2 b0 x0 ->
         Valid_Wiring b3 b1 x1 -> Valid_Wiring b4 b2 x2 ->
    Wiring_plus (Wiring_compose x x1) (Wiring_compose x0 x2)
        ≈ Wiring_compose (Wiring_plus x x0) (Wiring_plus x1 x2).
Proof.
    intros x x0 x1 x2 v v0 v1 v2.
    unfold Wiring_plus, Wiring_compose, connection_map_plus, compose_connection_map.
    simpl.

    split.

    + rewrite setUACA; reflexivity.
    + repeat rewrite in_setU. split.
    * intros.
    repeat rewrite in_setU.

    destruct ((x3  \in inp b3) || (x3  \in inp b4)) eqn:Hx3.
    -- rewrite orb_true_iff in Hx3.

    destruct Hx3.
    assert (x3  \in inp b4 = false). admit.
    rewrite H. rewrite H0.
    split.
    ++ intros. destruct H1 ; intuition.
    destruct H2.
    left. exists x4. left. trivial. left. trivial.

    ++ intros. destruct H1.
    ** destruct H1.
    unfold Valid_Wiring in *.
    unfold Valid_Wiring_Mapping in *.

    repeat_destruct v.
    repeat_destruct v0.
    repeat_destruct v1.
    repeat_destruct v2.

    specialize (v x4 y).
    specialize (v0 x4 y).
    specialize (v1 x3 x4).
    specialize (v2 x3 x4).

    destruct H1; destruct H2.

    --- left. left. exists x4; trivial.
    --- left. left. exists x4; trivial.

    assert (x4 \in inp b1 :|: phi_int _ _ x1). apply v1 ; trivial.
    assert (x4 \in inp b2). apply v0 ; trivial.
    admit.

    --- assert (x3 \in inp b4). apply v2 ; trivial.
        contradiction_in_H H3 H0.

    --- assert (x3 \in inp b4). apply v2 ; trivial.
        contradiction_in_H H3 H0.

    ** destruct H1.
       destruct H1. rewrite orb_True2 in H2. destruct H2.

    --- left. right. intuition.

    --- repeat_destruct v1.
        specialize (v1 x3 y).
        assert (y \in inp b1 :|: phi_int _ _ x1). apply v1 ; trivial.
        admit.

    --- repeat_destruct v2.
        specialize (v2 x3 y).
        assert (x3 \in inp b4). apply v2 ; trivial.
        contradiction_in_H H3 H0.

    ++ assert (x3  \in inp b3 = false). admit.
       rewrite H. rewrite H0.

      split.
      ** intros. destruct H1 ; intuition.
      destruct H2.
      left. exists x4 ; intuition.

      ** intros. destruct H1. destruct H1.
      --- right. left.
          destruct H1.

      +++ repeat_destruct v1.
      specialize (v1 x3 x4).
      assert (x3 \in inp b3). apply v1 ; trivial.
      contradiction_in_H H3 H0.

      +++ destruct H2.
      *** repeat_destruct v2. specialize (v2 x3 x4).
          repeat_destruct v. specialize (v x4 y).

          assert (x4  \in inp b2 :|: phi_int _ _ x2). apply v2 ; trivial.
          assert (x4 \in inp b1). apply v ; trivial.
          admit.

      *** exists x4 ; trivial.

      --- destruct H1. rewrite orb_True2 in H2.
      destruct H1.
      +++ repeat_destruct v1.
      specialize (v1 x3 y).
      assert (x3 \in inp b3). apply v1 ; trivial.
      contradiction_in_H H3 H0.

      +++ destruct H2.
      *** repeat_destruct v2.
      specialize (v2 x3 y).
      assert (y  \in inp b2 :|: phi_int _ _ x2). apply v2 ; trivial.
      admit.

      *** right. right ; intuition.

      -- rewrite orb_false_iff in Hx3.
      destruct Hx3. rewrite H. rewrite H0. intuition.

      * intros. split.
      -- intros.
        destruct ((y  \in outp b) || (y  \in phi_int _ _ x)) eqn:Hy1.
        ++ assert ((y  \in outp b :|: outp b0) || (y  \in phi_int _ _ x :|: phi_int _ _ x0) = true).
        repeat rewrite in_setU. rewrite orb_true_iff in Hy1.
        destruct Hy1 ; intuition.

        rewrite H0.
        destruct H.
        ** destruct H. exists x4 ; left ; intuition.
        ** assert ((y  \in outp b0) || (y  \in phi_int _ _ x0) = false).
        admit.
        assert (y  \in phi_int _ _ x2 = false). admit.
        rewrite H1 in H. rewrite H2 in H. intuition.

        ++ rewrite orb_false_iff in Hy1. destruct Hy1.
        repeat rewrite in_setU.
        rewrite H0. rewrite H1.
        simpl.
        destruct H.

        ** destruct (y \in phi_int _ _ x1) eqn:Hy.
        assert (y \in outp b0 = false). admit.
        assert (y  \in phi_int _ _ x0 = false). admit.
        rewrite H2. rewrite H3. simpl. left; trivial.
        intuition.

        ** destruct ((y  \in outp b0) || (y  \in phi_int _ _ x0)) eqn:Hy.
        destruct H. exists x4; right ; trivial.

        destruct (y  \in phi_int _ _ x2) eqn:Hy2.
        rewrite orb_true_r. right ; trivial.
        intuition.

      -- intros.

        destruct ((y  \in outp b) || (y  \in phi_int _ _ x)) eqn:Hy1.

        ++ assert ((y  \in outp b :|: outp b0) || (y  \in phi_int _ _ x :|: phi_int _ _ x0)).
           repeat rewrite in_setU. rewrite orb_true_iff in Hy1. destruct Hy1 ; rewrite H0 ; intuition.
           rewrite H0 in H.
           destruct H.

           destruct H.
            ** destruct H1.
            --- left. exists x4 ; intuition.
            --- right.
                repeat_destruct v1. specialize (v1 x3 x4).
                repeat_destruct v0. specialize (v0 x4 y).

                assert (Hx41: x4  \in outp b2). apply v0. trivial.
                assert (Hx42: x4  \in outp b1 :|: phi_int _ _ x1). apply v1. trivial.
                admit.

            ** destruct H1.
            --- repeat_destruct v. specialize (v x4 y).
                repeat_destruct v2. specialize (v2 x3 x4).

                assert (Hx41: x4  \in outp b1). apply v. trivial.
                assert (Hx42: x4  \in outp b2 :|: phi_int _ _ x2). apply v2. trivial.
                admit.

            --- repeat_destruct v0. specialize (v0 x4 y).
                repeat_destruct v2. specialize (v2 x3 x4).

                assert (Hx41: x4  \in outp b2). apply v0. trivial.
                assert (Hx42: x4  \in outp b2 :|: phi_int _ _ x2). apply v2. trivial.
                admit.

        ++ repeat rewrite in_setU in H.
           rewrite orb_false_iff in Hy1. destruct Hy1. rewrite H0 in H. rewrite H1 in H.
           simpl in H.

           destruct ((y  \in outp b0) || (y  \in phi_int _ _ x0)).
           ** destruct H.
           destruct H.

           --- destruct H2.
           +++ repeat_destruct v. specialize (v x4 y).
                assert (y  \in outp b :|: phi_int _ _ x ). apply v. trivial.
                rewrite in_setU in H3.
                rewrite orb_True2 in H3.
                rewrite H0 in H3. rewrite H1 in H3.
                intuition.

            +++ repeat_destruct v0. specialize (v0 x4 y).
                repeat_destruct v1. specialize (v1 x3 x4).

                assert (Hx41: x4 \in outp b2). apply v0. trivial.
                assert (Hx42: x4  \in outp b1 :|: phi_int _ _ x1). apply v1. trivial.
                admit.

            --- destruct H2.
            +++ repeat_destruct v. specialize (v x4 y).
                repeat_destruct v2. specialize (v2 x3 x4).

                assert (Hx41: x4  \in outp b1). apply v. trivial.
                assert (Hx42: x4  \in outp b2 :|: phi_int _ _ x2). apply v2. trivial.
                admit.

            +++ right. exists x4 ; intuition.

            ** destruct ((y  \in phi_int _ _ x1) || (y  \in phi_int _ _ x2)) eqn:Hy1.
            --- rewrite orb_true_iff in Hy1.
            destruct Hy1, H.
            +++ rewrite H2. left. trivial.
            +++ repeat_destruct v2. specialize (v2 x3 y).
                assert (Hy1: y  \in outp b2 :|: phi_int _ _ x2 ). apply v2. trivial.
                admit.

            +++ repeat_destruct v1. specialize (v1 x3 y).
                assert (Hy1: y \in outp b1 :|: phi_int _ _ x1). apply v1. trivial.
                admit.

            +++ repeat_destruct v2. specialize (v2 x3 y).
                assert (Hy1: y  \in outp b2 :|: phi_int _ _ x2 ). apply v2. trivial.
                admit.

            --- intuition.

Admitted.

Definition WiringD_0: WiringD Box0 Box0 :=
    (Wiring_0; Valid_Wiring_Mapping_Wiring_0).

Program Definition WiringD_plus {i j k l}
    : WiringD i k -> WiringD j l -> WiringD (box_plus i j) (box_plus k l)
:=
    λ '(w1; Hw1) '(w2; Hw2), (Wiring_plus w1 w2; _).
 Next Obligation.
    apply Valid_Wiring_plus ; intuition.
Defined.

Program Definition WiringD_Tensor: WiringDCat ∏ WiringDCat ⟶ WiringDCat :=
{|
    fobj := λ '(x, y), box_plus x y;
    fmap := λ (x y : Box ∧ Box)
              (f : WiringD (fst x) (fst y) ∧ WiringD (snd x) (snd y)), _;
|}.

Next Obligation.
    unfold WiringD in *.
    destruct w. destruct w0.

    exists (Wiring_plus x x0).
    apply (Valid_Wiring_plus x x0 v v0).
Defined.

Next Obligation.
    proper.
    destruct x. destruct H0.
    destruct y. destruct H1.

    simpl in *.
    unfold connection_map_plus in *.
    destruct X as [H_phi_int_x [H_phi_in_x H_phi_out_x]].
    destruct H as [H_phi_int_x2 [H_phi_in_x2 H_phi_out_x2]].

    split.
    rewrite H_phi_int_x. rewrite H_phi_int_x2. reflexivity.

    split.
    - intros.
    specialize (H_phi_in_x x3 y) ;
    specialize (H_phi_in_x2 x3 y) ; intuition.

    - intros.
    specialize (H_phi_out_x x3 y) ;
    specialize (H_phi_out_x2 x3 y) ; intuition.
Defined.

Next Obligation. (* 3 *)
    unfold connection_map_plus.
    simplify_finset.

    + split.
    * intros. rewrite in_setU. intuition.
    * rewrite in_setU. intros. destruct H.
        rewrite orb_True2 in H. destruct H.
        left.  intuition.
        right. intuition.

    + split.
    * intros. rewrite in_setU. intuition.
    * rewrite in_setU. intros. destruct H.
        rewrite orb_True2 in H. destruct H.
        left.  intuition.
        right. intuition.
Defined.

Next Obligation. (* 4 *)
    destruct w1, w2, w, w0.
    unfold WiringD_compose.

    assert (
        Wiring_plus (Wiring_compose x x1) (Wiring_compose x0 x2) ≈
        Wiring_compose (Wiring_plus x x0) (Wiring_plus x1 x2)
    ).

    apply Wiring_plus_compose_assoc ; intuition.
    simpl in * ; intuition.
Defined.

Program Definition to_unit_left_box_plus {x}
    : (box_plus Box0 x) ~> x
:=
    (Wiring_id ; _).
Next Obligation.
    now rewrite box_plus_zerol.
Defined.
Next Obligation.
    simpl_eqs.
    rewrite box_plus_zerol.
    apply Valid_Wiring_Wiring_id.
Defined.

Program Definition from_unit_left_box_plus {x}
    : x ~> (box_plus Box0 x)
:=
    (Wiring_id ; _).
Next Obligation.
    now rewrite box_plus_zerol.
Defined.
Next Obligation.
    simpl_eqs.
    apply Valid_Wiring_Wiring_id.
Defined.

Program Instance unit_left_box_plus {x : Box}
    : @Isomorphism WiringDCat (box_plus Box0 x) x
:= {|
    to := to_unit_left_box_plus ;
    from := from_unit_left_box_plus ;
  |}.
Next Obligation.
    simpl_eqs.
    simplify_finset.

    - split_goals.
    + destruct (x0  \in inp x).
    * trivial.
    * intuition.

    + destruct (x0  \in inp x).
    * destruct H.
    -- destruct H. my_tauto.
    -- my_tauto.

    * intuition.

    + rewrite H.
    left. exists y; my_tauto.

    - simplify_finset. rewrite orb_false_r.
        split_goals.
    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
    destruct H. intuition.

    * intuition.

    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
    destruct H. my_tauto.

    * intuition.

    + rewrite H. unfold compose_connection_map.
    exists y ; my_tauto.
Defined.

Next Obligation.
    simpl_eqs.
    simplify_finset.

    - split_goals.
    + destruct (x0  \in inp x) ; intuition.
    + destruct (x0  \in inp x).
    * intuition.
      destruct H0. my_tauto.

    * intuition.

    + rewrite H. left. exists y ; intuition.

    - simplify_finset. rewrite orb_false_r.
    split_goals.
    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
        destruct H. my_tauto.
    * intuition.

    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
        destruct H. my_tauto.
    * intuition.

    + rewrite H. unfold compose_connection_map.
    exists y ; my_tauto.
Defined.

Program Definition to_unit_right_box_plus {x}
    : (box_plus x Box0) ~> x
:=
    (Wiring_id ; _).
Next Obligation.
    now rewrite box_plus_zeror.
Defined.
Next Obligation.
    simpl_eqs.
    rewrite box_plus_zeror.
    apply Valid_Wiring_Wiring_id.
Defined.

Program Definition from_unit_right_box_plus {x}
    : x ~> (box_plus x Box0)
:=
    (Wiring_id ; _).
Next Obligation.
    now rewrite box_plus_zeror.
Defined.
Next Obligation.
    simpl_eqs.
    apply Valid_Wiring_Wiring_id.
Defined.

Program Instance unit_right_box_plus {x : Box}
    : @Isomorphism WiringDCat (box_plus x Box0) x
:= {|
    to := to_unit_right_box_plus ;
    from := from_unit_right_box_plus ;
|}.
Next Obligation.
    simpl_eqs.
    simplify_finset.

    - split_goals.
    + destruct (x0  \in inp x) ; intuition.

    + destruct (x0  \in inp x) ; intuition.
    destruct H0 ; my_tauto.

    + rewrite H. left. exists y ; my_tauto.

    - simplify_finset. rewrite orb_false_r.
    split_goals.

    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
        destruct H. my_tauto.
    * intuition.

    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
        destruct H. my_tauto.
    * intuition.

    + rewrite H. unfold compose_connection_map.
    exists y ; my_tauto.
Defined.

Next Obligation.
    simpl_eqs.
    simplify_finset.

    - split_goals.
    + destruct (x0  \in inp x) ; intuition.

    + destruct (x0  \in inp x) ; intuition.
    destruct H0 ; my_tauto.

    + rewrite H. left. exists y ; my_tauto.

    - simplify_finset. rewrite orb_false_r.
    split_goals.

    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
        destruct H. my_tauto.
    * intuition.

    + destruct (y  \in outp x).
    * unfold_destruct compose_connection_map H.
        destruct H. my_tauto.
    * intuition.

    + rewrite H. unfold compose_connection_map.
    exists y ; my_tauto.
Defined.

Program Definition to_box_plus_assoc_natural {x y z}
    : box_plus (box_plus x y) z ~> box_plus x (box_plus y z)
:=
    (Wiring_id ; _).
Next Obligation.
    now rewrite box_plus_associative.
Defined.
Next Obligation.
    simpl_eqs.
    rewrite box_plus_associative.
    apply Valid_Wiring_Wiring_id.
Defined.

Program Definition from_box_plus_assoc_natural {x y z}
    : box_plus x (box_plus y z) ~> box_plus (box_plus x y) z
:=
    (Wiring_id ; _).
Next Obligation.
    now rewrite box_plus_associative.
Defined.

Next Obligation.
    simpl_eqs.
    apply Valid_Wiring_Wiring_id.
Defined.

Program Instance box_plus_assoc_natural {x y z: Box}
    : @Isomorphism WiringDCat (box_plus (box_plus x y) z) (box_plus x (box_plus y z))
:= {|
    to := to_box_plus_assoc_natural ;
    from := from_box_plus_assoc_natural ;
|}.

Next Obligation.
    simpl_eqs.
    simplify_finset.

    - destruct (x0 \in inp x :|: inp y :|: inp z) eqn:Hx0.
    + split_goals.
    * inversion H ; my_tauto.
    * left. exists y0 ; my_tauto.

    + intuition.

    - simplify_finset. rewrite orb_false_r.
    destruct ( y0 \in outp x :|: outp y :|: outp z) eqn:Hy0.
    + unfold compose_connection_map. split_goals.
    * inversion H ; intuition.
    * inversion H ; my_tauto.

    * exists y0 ; intuition.

    + intuition. subst. contradiction_in_H Hy0 H0.
Defined.

Next Obligation.
    simpl_eqs.
    simplify_finset.

    - destruct (x0 \in inp x :|: inp y :|: inp z) eqn:Hx0.
    + split_goals.
    * inversion H ; my_tauto.
    * left. exists y0 ; my_tauto.

    + intuition.

    - simplify_finset. rewrite orb_false_r.
    destruct (y0 \in outp x :|: outp y :|: outp z) eqn:Hy0.
    + unfold compose_connection_map. split_goals.
    * inversion H ; intuition.
    * inversion H ; my_tauto.

    * exists y0 ; intuition.

    + intuition. subst. contradiction_in_H Hy0 H0.
Defined.

Program Instance Wiring_is_Monoidal : @Monoidal WiringDCat :=
{|
    I := Box0;
    tensor := WiringD_Tensor;
|}.

Next Obligation. (* to_unit_left_natural {x y} (g : x ~> y) *)
    (* Clean-up definitions from Program etc *)
    unfold to_unit_left_box_plus.
    unfold to_unit_left_box_plus_obligation_1 ;
    unfold to_unit_left_box_plus_obligation_2.
    unfold WiringD_compose.
    destruct g.
    simpl.

    (* Clean up definition from Wiring etc *)
    repeat rewrite set0U.
    unfold connection_map_plus.
    unfold compose_connection_map.

    simpl_eqs.
    repeat rewrite setU0 ;
    repeat rewrite set0U ;
    repeat rewrite in_set0.

    split.
    - reflexivity.
    - split.
    + intros.
    repeat rewrite in_set0 .
    destruct (x1 \in inp x) eqn:Hx1.

    split.

    * intros.
        destruct H.
        destruct H.
        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        specialize (v' x2 y0).
        assert (y0 \in inp y :|: phi_int _ _ x0). now apply v'.

        rewrite in_setU in H1.
        assert ((y0 \in inp y) || (y0 \in phi_int _ _ x0) = true). trivial.
        rewrite orb_true_iff in H2.
        destruct H2.

        left. exists y0. right. my_tauto.
        my_tauto.
        right. split. right. my_tauto. intuition.
        intuition.

    * intros.
    destruct H.
    -- destruct H. destruct H.
    ++ intuition.
    ++ left. exists x1 ; my_tauto.
    -- destruct H. destruct H.
    ++ intuition.
    ++ left. exists x1 ; my_tauto.

    * intuition.

    + intros. repeat rewrite in_set0. rewrite orb_false_r.
    split.

    * intros.
    destruct ((y0 \in outp y) || (y0 \in phi_int _ _ x0)) eqn:y0_outp_y_phi_int_x0.
    rewrite orb_true_iff in y0_outp_y_phi_int_x0.

    destruct y0_outp_y_phi_int_x0.
    rewrite H0. destruct H. destruct H. subst.
    exists y0. right. intuition. intuition.

    destruct H.

    unfold Valid_Wiring in v.
    destruct v as [h1 [h2[ h3[ h4 v']]]].

    assert (y0 \in outp y = false).
    eapply disjointFl. apply h4. intuition.
    rewrite H2. rewrite H0. right. destruct H. subst. intuition.

    inversion H.

    * intros.
        destruct (y0 \in outp y) eqn:y0_outp_y.
        rewrite orb_true_l.
        destruct H.
        destruct H. destruct H. inversion H.

        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        unfold Valid_Wiring_Mapping in v'.
        specialize (v' x1 x2).
        assert (x1 \in outp x). intuition.
        exists x1. intuition. destruct H0. subst. intuition.

        rewrite orb_false_l.

        destruct (y0 \in phi_int _ _ x0).
        destruct H. destruct H. inversion H.
        exists x1.
        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        unfold Valid_Wiring_Mapping in v'.
        specialize (v' x1 y0).
        assert (x1 \in outp x). intuition.
        intuition. intuition.

        inversion H.
Defined.

Next Obligation. (* from_unit_left_natural {x y} (g : x ~> y) *)
    (* Clean-up definitions from Program etc *)
    unfold from_unit_left_box_plus.
    unfold from_unit_left_box_plus_obligation_1 ;
    unfold from_unit_left_box_plus_obligation_2.
    unfold WiringD_compose.
    destruct g.
    simpl.
    repeat rewrite box_plus_zerol.
    simpl.

    (* Clean up definition from Wiring etc *)
    repeat rewrite set0U. repeat rewrite setU0.
    unfold connection_map_plus.
    unfold compose_connection_map.

    simpl_eqs.

    split.
    - simplify_finset.

    - split.

    * intros. split.

    -- intros. destruct_if.
    ++ destruct H. destruct H.
       rewrite in_set0 in H0.
        destruct H0.

    ** destruct H0. intuition.

    ** my_tauto.

    unfold Valid_Wiring in v.
    destruct v as [h1 [h2[ h3[ h4 v']]]].
    unfold Valid_Wiring_Mapping in v'.
    specialize (v' x2 y0).

    assert (y0 \in inp y :|: phi_int _ _ x0). now apply v'.
    rewrite in_setU in H1.
    assert ((y0 \in inp y) || (y0 \in phi_int _ _ x0) = true). trivial.
    rewrite orb_true_iff in H2.
    destruct H2 ; trivial.

    --- left.  exists y0; my_tauto.
    --- right ; my_tauto.

    ** destruct H. rewrite in_set0 in H0. intuition.

    ++ intuition.

    -- intros. destruct_if.
    ++ destruct H. destruct H. my_tauto.

    ** left. exists x1. my_tauto. right. trivial.

    ** left. exists x1; my_tauto. right. trivial.

    ++ intuition.

    * intros. repeat rewrite in_set0. rewrite orb_false_r. split.

    -- intros.
        destruct ((y0 \in outp y) || (y0 \in phi_int _ _ x0)) eqn:y0_outp_y_phi_int_x0.
        rewrite orb_true_iff in y0_outp_y_phi_int_x0.

        destruct y0_outp_y_phi_int_x0.
        rewrite H0. smart_destruct H.

    ++ rewrite in_set0 in H. inversion H.
    ++ exists y0; intuition.
    ++ unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].

        assert (y0 \in outp y = false).
        eapply disjointFl. apply h4. intuition.

        rewrite H1. rewrite H0.

        destruct H. destruct H2.
    ** destruct H2. rewrite in_set0 in H2. inversion H2.
    ** my_tauto.

    ++ intuition.

    -- intros.
    destruct (y0 \in outp y) eqn:y0_outp_y.
    rewrite orb_true_l.

    destruct H.
    my_tauto.
    exists x1.

    unfold Valid_Wiring in v.
    destruct v as [h1 [h2[ h3[ h4 v']]]].
    unfold Valid_Wiring_Mapping in v'.
    specialize (v' x1 y0).
    assert (x1 \in outp x). intuition.


    ++ my_tauto.
    ++ right. intuition.
    ++ rewrite orb_false_l.
    destruct (y0 \in phi_int _ _ x0).
    exists x1.

    unfold Valid_Wiring in v.
    destruct v as [h1 [h2[ h3[ h4 v']]]].
    unfold Valid_Wiring_Mapping in v'.
    specialize (v' x1 y0).
    assert (x1 \in outp x). intuition.

    ** my_tauto.
    ** right. my_tauto.
    ** inversion H.

Defined.

Next Obligation. (* to_unit_right_natural {x y} (g : x ~> y) *)
    (* Clean-up definitions from Program etc *)
    unfold to_unit_right_box_plus.
    unfold to_unit_right_box_plus_obligation_1 ;
    unfold to_unit_right_box_plus_obligation_2.
    unfold WiringD_compose.
    destruct g.
    simpl.
    repeat rewrite box_plus_zeror.
    simpl.
    simpl_eqs.

    (* Clean up definition from Wiring etc *)
    repeat rewrite set0U. repeat rewrite setU0.
    unfold connection_map_plus.
    unfold compose_connection_map.

    split.
    reflexivity.

    split.
    - intros. repeat rewrite in_set0.

        split. intros.
        destruct (x1 \in inp x) eqn:x1_inp_x.
        destruct H. destruct H.
        + destruct H. subst.
            unfold Valid_Wiring in v.
            destruct v as [h1 [h2[ h3[ h4 v']]]].
            unfold Valid_Wiring_Mapping in v'.
            specialize (v' x2 y0).
            assert (y0 \in inp y :|: phi_int _ _ x0). now apply v'.

            rewrite in_setU in H1.
            assert ((y0 \in inp y) || (y0 \in phi_int _ _ x0) = true). trivial.
            rewrite orb_true_iff in H2.
            destruct H2.

            left. exists y0. left. trivial. intuition.

            right. intuition.

        + destruct H. inversion H0.

        + inversion H.

        + destruct (x1 \in inp x) eqn:x1_inp_x.
            intros. destruct H. destruct H.

            destruct H0. subst. left. exists x1. intuition. intuition.

            left. exists x1. intuition. intuition.

            intuition.

    - intros. repeat rewrite in_set0. rewrite orb_false_r.
        split. intros.

        + destruct ((y0 \in outp y) || (y0 \in phi_int _ _ x0)) eqn:y0_outp_y_phi_int_x0.
        * rewrite orb_true_iff in y0_outp_y_phi_int_x0.

            destruct y0_outp_y_phi_int_x0.
            -- rewrite H0. destruct H. destruct H. subst.
                exists y0. intuition. intuition.

            -- assert (y0 \in outp y = false).
                eapply disjointFl. unfold Valid_Wiring in v. apply v. intuition.
                rewrite H1. rewrite H0.
                destruct H. destruct H. subst. left. intuition.
        * inversion H.

        + intros.
            destruct (y0 \in outp y) eqn:y0_outp_y.
        rewrite orb_true_l.
        destruct H.
        destruct H0.
        subst. exists x1.
        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        unfold Valid_Wiring_Mapping in v'.
        specialize (v' x1 y0).
        assert (x1 \in outp x). intuition. intuition.
        intuition.

        rewrite orb_false_l.
        destruct (y0 \in phi_int _ _ x0).
        exists x1. intuition.

        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        unfold Valid_Wiring_Mapping in v'.
        specialize (v' x1 y0).
        assert (x1 \in outp x). intuition.
        intuition.
        destruct H. intuition.
        destruct H. inversion H.

        inversion H.
Defined.

Next Obligation. (* from_unit_right_natural {x y} (g : x ~> y) *)
    (* Clean-up definitions from Program etc *)
    unfold from_unit_right_box_plus.
    unfold from_unit_right_box_plus_obligation_1 ;
    unfold from_unit_right_box_plus_obligation_2.
    unfold WiringD_compose.
    destruct g.
    simpl.
    repeat rewrite box_plus_zeror.
    simpl.
    simpl_eqs.

    (* Clean up definition from Wiring etc *)
    repeat rewrite set0U. repeat rewrite setU0.
    unfold connection_map_plus.
    unfold compose_connection_map.

    split.
    reflexivity.

    split.
    - intros. repeat rewrite in_set0.

        split. intros.
        destruct (x1 \in inp x) eqn:x1_inp_x.
        destruct H. destruct H.
        + destruct H0.
            * unfold Valid_Wiring in v.
                destruct v as [h1 [h2[ h3[ h4 v']]]].
                unfold Valid_Wiring_Mapping in v'.
                specialize (v' x2 y0).
                assert (y0 \in inp y :|: phi_int _ _ x0). now apply v'.

                rewrite in_setU in H1.
                assert ((y0 \in inp y) || (y0 \in phi_int _ _ x0) = true). trivial.
                rewrite orb_true_iff in H2.
                destruct H2.

                left. exists y0. destruct H. subst. intuition. intuition.
                destruct H. subst. right. intuition.

            * destruct H0. rewrite in_set0 in H0. inversion H0.

        + destruct H. inversion H0.

        + inversion H.

        + destruct (x1 \in inp x) eqn:x1_inp_x.
            intros. destruct H. destruct H.

            destruct H0. subst. left. exists x1. intuition. left. intuition.

            left.
            exists x1. intuition. left. intuition.

            intuition.

    - intros. repeat rewrite in_set0. rewrite orb_false_r.
        split. intros.

        destruct ((y0 \in outp y) || (y0 \in phi_int _ _ x0)) eqn:y0_outp_y_phi_int_x0.
        rewrite orb_true_iff in y0_outp_y_phi_int_x0.

        destruct y0_outp_y_phi_int_x0.
        rewrite H0. destruct H. destruct H. subst.
        destruct H1.
        exists y0. intuition. intuition.
        destruct H1. rewrite in_set0 in H1. inversion H1.

        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].

        assert (y0 \in outp y = false).
        eapply disjointFl. apply h4. intuition.
        rewrite H1. rewrite H0.

        destruct H. destruct H2.
        intuition. subst. intuition.
        destruct H2. rewrite in_set0 in H2. inversion H2.

        inversion H.

        intros.
        destruct (y0 \in outp y) eqn:y0_outp_y.
        rewrite orb_true_l.
        destruct H.
        destruct H0.
        subst. exists x1.
        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        unfold Valid_Wiring_Mapping in v'.
        specialize (v' x1 y0).
        assert (x1 \in outp x). intuition. intuition.
        left. intuition.

        rewrite orb_false_l.
        destruct (y0 \in phi_int _ _ x0).
        exists x1.

        unfold Valid_Wiring in v.
        destruct v as [h1 [h2[ h3[ h4 v']]]].
        unfold Valid_Wiring_Mapping in v'.
        specialize (v' x1 y0).
        assert (x1 \in outp x). intuition.
        intuition.

        left. intuition.

        inversion H.
Defined.

Next Obligation. (* to_tensor_assoc_natural {x y z w v u}
                    (g : x ~> y) (h : z ~> w) (i : v ~> u) *)
    (* Clean-up definitions from Program etc *)
    unfold to_box_plus_assoc_natural.
    unfold to_box_plus_assoc_natural_obligation_1, to_box_plus_assoc_natural_obligation_2 .

    unfold WiringD_compose.
    unfold WiringD_compose_obligation_1.
    unfold Wiring_compose.
    destruct g, h, i.
    simpl.
    simpl_eqs.
    repeat rewrite box_plus_associative.

    simpl.

    (* Clean up definition from Wiring etc *)
    repeat rewrite set0U. repeat rewrite setU0.
    repeat rewrite setUA.
    unfold connection_map_plus.
    unfold compose_connection_map.

    split.
    reflexivity.

    split.
    - intros. repeat rewrite in_set0.
     destruct (x3 \in inp x :|: inp z :|: inp v) eqn:x3'.
     split.

     intros. destruct H. destruct H. destruct H. subst.

     destruct H0.
     + unfold Valid_Wiring in v0.
        unfold Valid_Wiring_Mapping in v0.

        destruct v0 as [h1 [h2 [h3 [h4 v0']]]].
        specialize (v0' x4 y0).
        assert (y0 \in inp y :|: phi_int _ _ x0) ; intuition.
        rewrite in_setU in H5.
        assert ((y0 \in inp y) || (y0 \in phi_int _ _ x0) = true) ; trivial.
        rewrite orb_true_iff in H4.
        destruct H4.
        left. exists y0. intuition. repeat rewrite in_setU. rewrite H4. intuition.
        right. repeat rewrite in_setU. rewrite H4. intuition.

     + destruct H0.
        unfold Valid_Wiring in v1.
        unfold Valid_Wiring_Mapping in v1.

        destruct v1 as [h1 [h2 [h3 [h4 v1']]]].
        specialize (v1' x4 y0).
        assert (y0 \in inp w :|: phi_int _ _ x1) ;intuition.
        rewrite in_setU in H5.
        assert ((y0 \in inp w) || (y0 \in phi_int _ _ x1) = true) ; trivial.
        rewrite orb_true_iff in H4.
        destruct H4.
        left. exists y0. intuition. repeat rewrite in_setU. rewrite H4. intuition.
        right. repeat rewrite in_setU. rewrite H4. intuition.

        unfold Valid_Wiring in v2.
        unfold Valid_Wiring_Mapping in v2.

        destruct v2 as [h1 [h2 [h3 [h4 v2']]]].
        specialize (v2' x4 y0).
        assert (y0 \in inp u :|: phi_int _ _ x2) ;intuition.
        rewrite in_setU in H5.
        assert ((y0 \in inp u) || (y0 \in phi_int _ _ x2) = true) ; trivial.
        rewrite orb_true_iff in H4.
        destruct H4.
        left. exists y0. intuition. repeat rewrite in_setU. rewrite H4. intuition.
        right. repeat rewrite in_setU. rewrite H4. intuition.

    + destruct H. inversion H0.

    + intros.
        destruct H. destruct H.
        repeat rewrite setUA in H.
        repeat rewrite in_setU in H0.
        destruct H0. subst.

        left. exists x3 ; intuition.
        left. exists x3 ; intuition.
    + intuition.

    - intros.
        rewrite in_set0. rewrite orb_false_r.
        split.

        destruct ( y0 \in outp y :|: outp w :|: outp u) eqn:y0'.
        rewrite orb_true_l.
        intros. destruct H.
        exists y0. destruct H. subst. intuition.

        intuition.

        rewrite orb_false_l.
        destruct (y0 \in phi_int _ _ x0 :|: phi_int _ _ x1 :|: phi_int _ _ x2) eqn:y0''.
        intros. destruct H. destruct H. subst. intuition.
        intuition.

        destruct ( y0 \in outp y :|: outp w :|: outp u) eqn:y0'.
        intros.
        rewrite orb_true_l.

        destruct H. destruct H0. subst.

        destruct H. destruct H.

        unfold Valid_Wiring in v0.
        unfold Valid_Wiring_Mapping in v0.
        destruct v0 as [h1 [h2 [h3 [h4 v0']]]].
        specialize (v0' x3 y0).
        assert (x3 \in outp x) ; intuition.
        exists x3. intuition. repeat rewrite in_setU. rewrite H5. intuition.
        intuition.

        unfold Valid_Wiring in v1.
        unfold Valid_Wiring_Mapping in v1.
        destruct v1 as [h1 [h2 [h3 [h4 v1']]]].
        specialize (v1' x3 y0).
        assert (x3 \in outp z) ; intuition.
        exists x3. intuition. repeat rewrite in_setU. rewrite H5. intuition.
        intuition.

        unfold Valid_Wiring in v2.
        unfold Valid_Wiring_Mapping in v2.
        destruct v2 as [h1 [h2 [h3 [h4 v2']]]].
        specialize (v2' x3 y0).
        assert (x3 \in outp v) ; intuition.
        exists x3. repeat rewrite in_setU. rewrite H5. intuition.
        intuition.

        rewrite orb_false_l.
        destruct (y0 \in phi_int _ _ x0 :|: phi_int _ _ x1 :|: phi_int _ _ x2).
        intros.
        destruct H. destruct H.

        unfold Valid_Wiring in v0.
        unfold Valid_Wiring_Mapping in v0.
        destruct v0 as [h1 [h2 [h3 [h4 v0']]]].
        specialize (v0' x3 y0).
        assert (x3 \in outp x) ; intuition.
        exists x3. intuition. repeat rewrite in_setU. rewrite H4. intuition.
        intuition.

        unfold Valid_Wiring in v1.
        unfold Valid_Wiring_Mapping in v1.
        destruct v1 as [h1 [h2 [h3 [h4 v1']]]].
        specialize (v1' x3 y0).
        assert (x3 \in outp z) ; intuition.
        exists x3. intuition. repeat rewrite in_setU. rewrite H4. intuition.
        intuition.

        unfold Valid_Wiring in v2.
        unfold Valid_Wiring_Mapping in v2.
        destruct v2 as [h1 [h2 [h3 [h4 v2']]]].
        specialize (v2' x3 y0).
        assert (x3 \in outp v) ; intuition.
        exists x3. repeat rewrite in_setU. rewrite H4. intuition.
        intuition.

        intuition.
Defined.

Next Obligation. (* from_tensor_assoc_natural {x y z w v u}
        (g : x ~> y) (h : z ~> w) (i : v ~> u) *)

    (* Clean-up definitions from Program etc *)
        unfold from_box_plus_assoc_natural.
        unfold from_box_plus_assoc_natural_obligation_1, from_box_plus_assoc_natural_obligation_2 .

        unfold WiringD_compose.
        unfold WiringD_compose_obligation_1.
        unfold Wiring_compose.
        destruct g, h, i.
        simpl.
        simpl_eqs.

        (* Clean up definition from Wiring etc *)
        repeat rewrite box_plus_associative.
        repeat rewrite set0U. repeat rewrite setU0.
        repeat rewrite setUA.
        unfold connection_map_plus.
        unfold compose_connection_map.
        simpl.

        split_goals.
        - intro_proof.
            simplify_finset.
            destruct_if.
            smart_destruct H.

            + smart_unfold v0.
            repeat_destruct v0.
            smart_unfold v0.

            specialize (v0 L y0).
            smart_destruct v0.
            rewrite_in_setU.
            apply orb_true_iff in H1.
            destruct H1.

            left. exists y0. intuition. rewrite_in_setU. rewrite H1. intuition.
            right. intuition. rewrite H1. intuition.

            + smart_unfold v1.
                repeat_destruct v1.
                smart_unfold v1.

                specialize (v1 L y0).
                smart_destruct v1.
                rewrite_in_setU.
                apply orb_true_iff in H1 ; destruct H1.

                left. exists y0. intuition. rewrite_in_setU. rewrite H1. intuition.
                right. intuition. rewrite H1. intuition.

         + smart_unfold v2.
            repeat_destruct v2.
            smart_unfold v2.

            specialize (v2 L y0).
            smart_destruct v2.
            my_tauto.
            rewrite_in_setU.
            apply orb_true_iff in H1 ; destruct H1.

            left. exists y0. intuition. rewrite_in_setU. rewrite H1. intuition.
            right. intuition.

        + inversion R.
        + my_tauto.

    - destruct_if.
        simplify_finset.
        rewrite_in_setU.
        smart_destruct H.

        * left. exists x3 ; intuition.
        * left. exists x3 ; intuition.
        * left. exists x3 ; intuition.
        * left. exists x3 ; intuition.
        * left. exists x3 ; intuition.
        * left. exists x3 ; intuition.
        * inversion H.

    - rewrite_in_setU.
        simplify_finset.
        rewrite orb_false_r.
        destruct_if.

        + simpl in H.

        smart_destruct H.
        exists y0. intuition. rewrite_in_setU. my_tauto.
        exists y0. intuition. rewrite_in_setU. my_tauto.
        exists y0. intuition. rewrite_in_setU. my_tauto.

        + simpl in *.
            destruct_if.
            smart_destruct H; intuition.
            intuition.

    - rewrite_in_setU. simplify_finset.
        rewrite orb_false_r in H.

        destruct ((y0 \in outp y) || (y0 \in outp w) || (y0 \in outp u)) eqn:y0'.
        simpl.

        smart_destruct H.

        smart_unfold v0.
        repeat_destruct v0.
        smart_unfold v0.

        specialize (v0 x3 y0).
        my_tauto.

        rewrite_in_setU.
        apply orb_true_iff in H ; destruct H.

        exists x3. rewrite H3. intuition. intuition.
        exists x3. rewrite H3. intuition. intuition.

        smart_unfold v1.
        repeat_destruct v1.
        smart_unfold v1.

        specialize (v1 x3 y0).
        smart_destruct v1.
        my_tauto.
        try_subst.

        rewrite_in_setU.
        apply orb_true_iff in H ; destruct H.

        exists x3. rewrite H2. intuition. intuition.
        exists x3. rewrite H2. intuition. intuition.

        smart_unfold v2.
        repeat_destruct v2.
        smart_unfold v2.

        specialize (v2 x3 y0).
        smart_destruct v2.
        my_tauto.
        try_subst.

        rewrite_in_setU.
        apply orb_true_iff in H ; destruct H.

        exists x3. rewrite H2. intuition. intuition.
        exists x3. rewrite H2. intuition. intuition.

        simpl.
        destruct_if.

        destruct H.

        smart_unfold v0.
        repeat_destruct v0.
        smart_unfold v0.

        specialize (v0 x3 y0).
        smart_destruct v0.
        my_tauto.
        rewrite_in_setU.
        apply orb_true_iff in H0 ; destruct H0.

        exists x3. rewrite H1. intuition. intuition.
        exists x3. rewrite H1. intuition. intuition.

        destruct H.

        smart_unfold v1.
        repeat_destruct v1.
        smart_unfold v1.

        specialize (v1 x3 y0).
        smart_destruct v1.
        my_tauto.
        rewrite_in_setU.
        apply orb_true_iff in H0 ; destruct H0.

        exists x3. rewrite H1. intuition. intuition.
        exists x3. rewrite H1. intuition. intuition.

        smart_unfold v2.
        repeat_destruct v2.
        smart_unfold v2.

        specialize (v2 x3 y0).
        smart_destruct v2.
        my_tauto.
        rewrite_in_setU.
        apply orb_true_iff in H0 ; destruct H0.

        exists x3. rewrite H1. intuition. intuition.
        exists x3. rewrite H1. intuition. intuition.

        inversion H.
Defined.

Next Obligation. (* triangle_identity {x y} *)
    (* Clean-up definitions from Program etc *)
        simpl_eqs.

        (* Clean up definition from Wiring etc *)
        repeat rewrite set0U. repeat rewrite setU0.
        repeat rewrite setUA.
        unfold connection_map_plus.
        unfold compose_connection_map.

        simpl.

        split_goals.

        intro_step.
        rewrite_in_setU.

        smart_destruct H.
        rewrite H. simpl.
        left. exists y0 ; intuition.

        rewrite_in_setU.

        rewrite H. rewrite orb_true_r.
        left. exists y0 ; intuition.

        rewrite_in_setU.

        destruct ((x0 \in inp x) || (x0 \in inp y)) eqn:x0'.
        apply orb_true_iff in x0'.  destruct x0'.
        destruct H. destruct H. destruct H. try_subst.
        intuition.

        destruct H. rewrite in_set0 in H1. inversion H1.

        destruct H. destruct H. destruct H. try_subst. intuition.

        destruct H. destruct H. try_subst.
        right. intuition.
        inversion H.

        + rewrite_in_setU. rewrite in_set0. rewrite orb_false_r.
        rewrite H. simpl. exists y0 ; intuition.

        + rewrite_in_setU. rewrite in_set0. rewrite orb_false_r.
        rewrite H. rewrite orb_true_r.

        exists y0 ; my_tauto.
        right. my_tauto.

        +  rewrite_in_setU. rewrite in_set0 in H.
        rewrite orb_false_r in H.
        destruct ((y0 \in outp x) || (y0 \in outp y)) eqn:y0'.
        apply orb_true_iff in y0'.  destruct y0'.
        * destruct H. destruct H. try_subst. intuition.
        * destruct H. destruct H. try_subst. intuition.
        * inversion H.
Defined.

Next Obligation (* pentagon_identity {x y z w} *).
    simpl_eqs.

    split_goals.

    - simplify_finset.

    - intros.
        unfold connection_map_plus.
        simplify_finset.

        split_goals.
        + intro_step. destruct_if.
            smart_destruct H.
            destruct R.
            * destruct H0. try_subst. rewrite if0 in H.
                smart_destruct H.
                destruct H. left. exists L0 ; intuition.
                left. exists L0. intuition.  intuition.
                inversion R.

            * destruct H0. try_subst. rewrite if0 in H.
                smart_destruct H.
                destruct H. left. exists L0 ; intuition.
                left. exists L0. intuition. intuition.
                inversion R.

            * inversion R.

            * inversion H.

    - intros.
        unfold connection_map_plus.
        unfold compose_connection_map.
        repeat rewrite in_setU.
        repeat rewrite in_setU in H.
        simplify_finset.

        destruct_if.

        + destruct H.

        * destruct H.
        left. exists x1.
        apply orb_true_iff in if0. destruct if0.
        apply orb_true_iff in H1. destruct H1.
        apply orb_true_iff in H1. destruct H1.

        rewrite H1 ; intuition.
        rewrite H1 ; intuition.
        rewrite H1 ; intuition.
        rewrite H1 ; intuition.

        my_tauto.
        left.
        exists y0 ; my_tauto.
        rewrite in_setU.

        apply orb_true_iff in if0. destruct if0.
        apply orb_true_iff in H1. destruct H1.
        apply orb_true_iff in H1. destruct H1.

        left. my_tauto.
        right. rewrite in_setU. rewrite H1. my_tauto.
        right. rewrite in_setU. rewrite H1. my_tauto. intuition.
        right. rewrite H1. my_tauto. intuition.

        * intuition.

        + intuition.

    -
    unfold compose_connection_map in *.
    unfold connection_map_plus in *.
    simplify_finset.
    repeat rewrite orb_false_r in H.
    repeat rewrite orb_false_r.

    destruct_if.
    + repeat_destruct H.
    repeat_destruct H1.

    exists y0.
    * destruct H, H3; rewrite setUA in H4; my_tauto.

    * rewrite setUA in if0. rewrite setUA. my_tauto.

    + intuition.

    - unfold compose_connection_map in *.
    unfold connection_map_plus in *.
    simplify_finset.
    repeat rewrite orb_false_r in H.
    repeat rewrite orb_false_r.

    destruct_if.
    + destruct H. exists x0.
    * my_tauto.
        rewrite setUA in if0.
        rewrite in_setU in if0.
        rewrite orb_true_iff in if0.
        destruct if0.

    -- left. my_tauto.
    -- right. my_tauto.

    * exists x1.
    -- rewrite setUA. my_tauto.
    --
    assert ((x1 \in outp x) = true \/ x1  \in outp y :|: outp z :|: outp w = true).
    rewrite <- orb_true_iff. rewrite <- in_setU. rewrite setUA in if0. intuition. repeat rewrite setUA. my_tauto.
    intuition.

    + intuition.
Defined.

(*
Program Instance Wiring_is_Braided : @BraidedMonoidal WiringDCat :=
{
braided_is_monoidal := Wiring_is_Monoidal ;

}.
Next Obligation.
*)

End Wiring_Rel.
