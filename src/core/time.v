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
(** Coq Library *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
Require Import Coq.NArith.Ndist.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.EquivDec. (* To export some notations defined there *)
Require Import Coq.ZArith.ZArith.

Require Import Oqarina.core.tactics.
Require Import Coq.ZArith.ZArith_dec.
Require Import Oqarina.CoqExt.all.

(*| .. coq:: |*)

(*|

****
Time
****

In this section, we propose an axiomatisation of the notion of time. It follows definition from :cite:`nutaroTheorySuperdenseTime2020`.

|*)


(*| .. coq:: none |*)
Section TimeClass.
(*| .. coq:: |*)

(*|

TimeClass
=========

:coq:`TimeClass` is an axiomatization of the notion of time, with elements
$0$ and $1$, the plus operation and preoder and strict order relations.
We ask for the order relations to be compatible (see lemma
:coq:`time_lt_not_le_iff`).

|*)

Class TimeClass (T : Type) := {
    Zero : T;
    One : T;

    time_eq : relation T;
    time_equiv :: Equivalence time_eq ;
    time_eq_dec :: EqDec T time_eq ;

    time_le : relation T ;
    time_le_preorder :: PreOrder time_le ;
    time_le_preorderdec :: PreOrderDec ;

    time_lt : relation T;
    time_lt_strictorder :: StrictOrder time_lt;

    time_lt_not_le_iff:
      forall (t1 t2: T), time_le t1 t2 <-> ~ time_lt t2 t1;
}.

Definition time_min (Time : Type) {ti : TimeClass Time} (t1 t2 : Time) :=
    if preorder_decb t1 t2 then t1 else t2.

Definition time_list_min (Time : Type) {ti : TimeClass Time} (l : list Time) :=
    match l with
    | [] => Zero
    | h :: t => fold_left (fun acc x: Time => time_min _ acc x) l h
    end.

(*| .. coq:: none |*)
End TimeClass.

Section TimeOperations.

Context { T: Type }
        { Time_t : TimeClass T }.

Class TimeOperations := {
    time_plus : T -> T -> T ;
    time_minus : T -> T -> T ;
}.

End TimeOperations.

Section TimeInf.
(*| .. coq::  |*)


(*|

TimeInf
=======

:coq:`TimeInf` extends a :coq:`TimeClass` instance and add the time infinity
value. :coq:`TimeInf` is a valid instance of :coq:`TimeClass`/

|*)

Context { T: Type }
        `( eq_t : EqDec _ (@eq T) )
        { Time_t : TimeClass T }.

Inductive TimeInf :=
    | t_infinity | ti : T -> TimeInf.

Definition TimeInf_eq : relation TimeInf :=
    fun (t1 t2: TimeInf) =>
    match t1 with
    | t_infinity => match t2 with
                    | t_infinity => True
                    | ti _ => False
                    end
    | ti n1 => match t2 with
                | t_infinity => False
                | ti n2 => n1 === n2
                end
end.

Lemma TimeInf_eq_reflexive : reflexive TimeInf TimeInf_eq.
Proof.
    unfold reflexive, TimeInf_eq.
    induction x ; auto with *.
Qed.

Lemma TimeInf_eq_symmetric : symmetric TimeInf TimeInf_eq.
Proof.
    unfold symmetric, TimeInf_eq.
    induction x ; induction y ; auto with *.
Qed.

Lemma TimeInf_eq_transitive : transitive TimeInf TimeInf_eq.
Proof.
    unfold transitive, TimeInf_eq.
    induction x ; induction y ; induction z ; intuition.
    eapply Equivalence_Transitive. apply H. apply H0.
Qed.

#[global] Instance TimeInf_eq_equivalence : Equivalence TimeInf_eq := {|
    Equivalence_Reflexive := TimeInf_eq_reflexive ;
    Equivalence_Symmetric := TimeInf_eq_symmetric ;
    Equivalence_Transitive := TimeInf_eq_transitive ;
|}.

Lemma TimeInf_eq_dec : forall x y : TimeInf, { x === y } + { x =/= y }.
Proof.
    intros.
    destruct x, y.
    - auto with *.
    - right. unfold "=/=". intuition.
    - right. unfold "=/=". intuition.
    - unfold "=/=". unfold "===". simpl.
        eapply equiv_dec.
Qed.

#[global] Instance TimeInf_eq_eqdec : EqDec _ TimeInf_eq := {
    equiv_dec := TimeInf_eq_dec ;
}.

Definition iZero := ti Zero.
Definition iOne  := ti One.

Definition ile :=
    fun (t1 t2: TimeInf) =>
        match t1 with
        | t_infinity => match t2 with
                        | t_infinity => True
                        | ti _ => False
                        end
        | ti n1 => match t2 with
                    | t_infinity => True
                    | ti n2 => time_le n1 n2
                    end
    end.

Lemma ile_reflexive : reflexive TimeInf ile.
Proof.
    unfold reflexive, ile.
    induction x.
    - intuition.
    - eapply PreOrder_Reflexive.
Qed.

Lemma ile_trans : transitive TimeInf ile.
Proof.
    unfold transitive. intros.
    destruct x eqn:Hx ;
    destruct y eqn:Hy ;
    destruct z eqn:Hz ; trivial.
    - inversion H0.
    - unfold ile in *.
      eapply PreOrder_Transitive. apply H. apply H0.
Qed.

#[global] Instance ile_PreOrder : PreOrder (ile) := {|
    PreOrder_Reflexive := ile_reflexive ;
    PreOrder_Transitive := ile_trans;
|}.

Lemma ile_dec : forall t1 t2,
    { ile t1 t2 } + { ~ ile t1 t2 }.
Proof.
    prove_dec.
    apply preorder_dec.
Qed.

#[global] Instance ile_PreOrderDec : PreOrderDec := {|
    preorder_dec := ile_dec ;
|}.

Definition ilt :=
    fun (t1 t2: TimeInf) =>
        match t1 with
        | t_infinity => match t2 with
                        | t_infinity => False
                        | ti _ => False
                        end
        | ti n1 => match t2 with
                    | t_infinity => True
                    | ti n2 => time_lt n1 n2
                    end
    end.

Lemma ilt_irreflexive : reflexive TimeInf (complement ilt).
Proof.
    unfold reflexive, complement, ilt.
    induction x.
    - intuition.
    - eapply StrictOrder_Irreflexive.
Qed.

Lemma ilt_trans : transitive TimeInf ilt.
Proof.
    unfold transitive. intros.
    destruct x eqn:Hx ;
    destruct y eqn:Hy ;
    destruct z eqn:Hz ; trivial.
    - inversion H0.
    - unfold ilt in *.
      eapply StrictOrder_Transitive. apply H. apply H0.
Qed.

#[global] Instance ilt_StrictOrder : StrictOrder (ilt) := {|
    StrictOrder_Irreflexive := ilt_irreflexive ;
    StrictOrder_Transitive := ilt_trans ;
|}.

Lemma ile_not_ilt_iff: forall t1 t2, ile t1 t2  <-> ~ ilt t2 t1.
Proof.
    intros. unfold ile, ilt.
    destruct t1 eqn:Ht1 ;
    destruct t2 eqn:Ht2 ; intuition.
    eapply time_lt_not_le_iff. apply H. apply H0.
    eapply time_lt_not_le_iff. intuition.
Qed.

#[global] Instance TimeInf_i : TimeClass TimeInf := {|
    Zero := iZero;
    One := iOne;
    time_lt_not_le_iff := ile_not_ilt_iff;
|}.

(*| .. coq:: none |*)
End TimeInf.

(*| .. coq:: |*)

(*| .. coq:: none |*)
Section NaturalTime.
(*| .. coq:: |*)

(*|

Integer-based Time
==================

|*)

Lemma nat_lt_not_le_iff: forall (n m:nat), n <= m <-> ~ m < n.
Proof. lia. Qed.

#[global] Instance nat_Preorder : PreOrder Nat.le := _.

#[global] Instance nat_PreorderDEc : PreOrderDec := {|
    preorder_dec := le_dec ;
|}.

#[global] Instance NaturalTime_i : TimeClass nat := {|
    Zero := 0;
    One := 1;
    time_le_preorder := nat_Preorder ;
    time_lt_not_le_iff := nat_lt_not_le_iff ;
|}.

#[global] Instance NaturalTime_ops : TimeOperations := {|
    time_plus := Nat.add ;
    time_minus := Nat.sub ;
|}.

(*| .. coq:: none |*)
End NaturalTime.
(*| .. coq:: |*)

(*| .. coq:: none |*)
Section SuperDenseTime.
(*| .. coq:: |*)

(*|

SuperDense Time
===============

|*)

Open Scope Z_scope.

Record sdTime := {
    c : Z;
    t : Z;
}.

Scheme Equality for sdTime.

Definition sdZero := {| c := 0 ; t := 0 |}.
Definition sdOne  := {| c := 0 ; t := 1 |}.

Definition sd_le (t1 t2: sdTime) :=
    (t1.(c)) < t2.(c) \/
    (t1.(c) = t2.(c) /\ t1.(t) <= t2.(t)).


Definition sd_le_dec: forall (t1 t2: sdTime),
    { sd_le t1 t2 } + { ~ sd_le t1 t2 }.
Proof.
    intros. unfold sd_le. destruct t1, t2. simpl.
    apply dec_sumbool_or.
    - apply Z_lt_dec.
    - apply dec_sumbool_and. apply Z.eq_dec. apply Z_le_dec.
Qed.

Open Scope bool_scope.
Definition sd_leb (t1 t2: sdTime) :=
    (t1.(c) <? t2.(c)) ||
    ((t1.(c) =? t2.(c)) && (t1.(t) <=? t2.(t))).

Lemma sd_le_leb: forall t1 t2,
    sd_le t1 t2 <-> sd_leb t1 t2 = true.
Proof.
    unfold sd_le, sd_leb ; lia.
Qed.

Lemma sd_le_refl : reflexive sdTime sd_le.
Proof. unfold reflexive, sd_le. auto with *. Qed.

Lemma sd_le_trans : transitive sdTime sd_le.
Proof. unfold transitive, sd_le. lia. Qed.

#[global] Instance sd_le_PreOrder : PreOrder sd_le := {|
    PreOrder_Reflexive := sd_le_refl ;
    PreOrder_Transitive := sd_le_trans ;
|}.

#[global] Instance sd_le_decidable : PreOrderDec := {|
    preorder_dec := sd_le_dec ;
|}.

Definition sd_lt (t1 t2: sdTime) :=
    (t1.(c)) < t2.(c) \/
    (t1.(c) = t2.(c) /\ t1.(t) < t2.(t)).

Lemma sd_lt_irreflexive : reflexive sdTime (complement sd_lt).
Proof.
    unfold reflexive, sd_lt, complement. auto with *.
Qed.

Lemma sd_lt_trans : transitive sdTime sd_lt.
Proof.
    unfold transitive, sd_lt. lia. Qed.

#[global] Instance sd_lt_StrictOrder : StrictOrder (sd_lt) := {|
    StrictOrder_Irreflexive := sd_lt_irreflexive ;
    StrictOrder_Transitive := sd_lt_trans ;
|}.

Lemma sd_le_not_lt: forall t1 t2,
    sd_le t1 t2 <-> ~ sd_lt t2 t1.
Proof.
    unfold sd_le, sd_lt.
    intros.
    split.
    - auto with *.
    - firstorder.
      assert (H1: c t1 <= c t2). lia.
      assert (H2: c t1 < c t2 \/ c t1 = c t2). lia.
      destruct H2.
      + left. trivial.
      + right. auto with *.
Qed.

#[global] Instance SuperDenseTime_equiv : Equivalence (@eq sdTime) := _.

Lemma sdTime_equiv_dec : forall x y: sdTime, {x === y} + { x =/= y}.
Proof.
    unfold "===", "=/=".  apply sdTime_eq_dec.
Qed.

#[global] Instance SuperDenseTime_eq : EqDec _ (@eq sdTime) := {
    equiv_dec := sdTime_eq_dec ;
}.

#[global] Instance SuperDenseTime_i : TimeClass sdTime := {|
    Zero := sdZero;
    One := sdOne;
    time_lt_strictorder := sd_lt_StrictOrder;
    time_lt_not_le_iff := sd_le_not_lt;
|}.

Definition tplus (t1 t2: sdTime) :=
    if (t2.(c) =? 0) then
        {| c := t1.(c) ;
           t := t1.(t) + t2.(t) |}
    else
        {| c := t1.(c) + t2.(c) ;
           t := t2.(t) |}.

Definition tminus (t1 t2: sdTime) :=
    if (t1.(c) =? t2.(c)) then
        {| c := 0 ;
           t := t1.(t) - t2.(t) |}
    else
        {| c := t1.(c) - t2.(c) ;
           t := t1.(t)  |}.

#[global] Instance SuperDenseTime_ops : TimeOperations := {|
    time_plus := tplus ;
    time_minus := tminus ;
|}.

Lemma P1: forall t: sdTime, tplus t sdZero = t.
Proof.
    intros. unfold tplus, Zero. simpl.
    destruct t0. simpl.

    assert (t0 + 0 = t0). lia. rewrite H.

    reflexivity.
Qed.

Lemma P2: forall (t h1 h2: sdTime),
    sd_le h1 h2 (*-> sd_le Zero h1 *) -> sd_le (tplus h1 t) (tplus h2 t).
Proof.
    unfold sd_le, tplus.
    intros.
    destruct h1, h2, t0. simpl in *.
    destruct (c2 =? 0) ; simpl.
    - destruct H. left. intuition. right. lia.
    - destruct H. left. lia. right. lia.
Qed.

Lemma P3: forall (t h1 h2: sdTime),
    sd_le sdZero h1 -> sd_le sdZero h2 -> (* positivity primoridal in this proof *)
        tplus (tplus t h1) h2 = tplus t (tplus h1 h2).
Proof.
    intros.
    unfold tplus.
    destruct (c h1 =? 0) eqn:H1 ; simpl.
    - destruct (c h2 =? 0) eqn:H2 ; simpl.
      + rewrite H1.
        assert (Ht: t t0 + t h1 + t h2  = t t0 + (t h1 + t h2)). lia.
        rewrite Ht. reflexivity.
      + assert (Hc: c h1 + c h2 =? 0 = false). lia.
        rewrite Hc.

        assert (Hc2: c t0 + (c h1 + c h2) = c t0 + c h2). lia.
        rewrite Hc2. reflexivity.

    - destruct (c h2 =? 0) eqn:H2 ; simpl.
      + rewrite H1. reflexivity.
      + unfold sd_le, Zero in *. simpl in *.
        assert (0 < c h1). lia.
        assert (0 < c h2). lia.
        assert (c h1 + c h2 =? 0 = false). lia.
        rewrite H5.
        assert (c t0 + c h1 + c h2 = c t0 + (c h1 + c h2)). lia.
        rewrite H6. reflexivity.
Qed.

Lemma P4: forall (t1 t2 : sdTime),
    sd_le sdZero t1 ->
        sd_le t1 t2 -> exists h, t2 = tplus t1 h.
Proof.
    unfold sd_le, tplus, sdZero.
    intros.
    destruct t1, t2.
    simpl in *.
    destruct H0.
    - exists ({| c := c1 - c0 ; t := t1 |}).

     assert (c1 - c0 =? 0 = false). lia.
     simpl. rewrite H1.
     assert (c0 + (c1 -c0) = c1). lia.
     rewrite H2. trivial.

    - destruct H0. rewrite H0.

      exists ({| c := 0 ;  t := t1 - t0|}).
      simpl.
      assert (t0 + (t1 - t0) = t1). lia.
      rewrite H2. trivial.
Qed.

Definition S_time (t0 : sdTime) :=
    tplus t0 sdOne.

Lemma P5 : forall t0 t1,
    sd_le t0 t1 /\ sd_lt t1 (S_time t0) -> t0 = t1.
Proof.
    unfold sd_le, sd_lt, S_time, tplus, One.
    intros.
    destruct t0, t1.
    simpl in *.
    destruct H.

    assert (Ht: t0 = t1). lia.
    assert (Hc: c0 = c1). lia.

    rewrite Ht, Hc. reflexivity.
Qed.

(*| .. coq:: none |*)
End SuperDenseTime.
(*| .. coq::|*)

(*|

Time Notations
==============

|*)


Module Time_Notations.

Declare Scope time_scope.
Delimit Scope time_scope with time.

Notation "t1 <= t2" := (time_le t1 t2) (at level 70, no associativity) : time_scope.

Notation "t1 < t2" := (time_lt t1 t2) (at level 70, no associativity) : time_scope.

Infix "+" := (time_plus) : time_scope.
Infix "-" := (time_minus) : time_scope.

End Time_Notations.

(*| .. coq:: none |*)
Section Examples.

Import Time_Notations.

Example nat_time_1 := 3.
Example nat_time_2 := 4.

Fact nat_time_test_1: (nat_time_1 <= nat_time_2)%time.
Proof. compute. lia. Qed.

Fact nat_time_test_2: ((ti nat_time_1) < t_infinity)%time.
Proof. compute. trivial. Qed.

Fact sd_time_test_1: ((ti {| c := 32; t := 4|}) < (t_infinity))%time.
Proof. compute. lia. Qed.

Fact sd_time_test_2: ((ti {| c := 32; t := 4|}) <= (t_infinity))%time.
Proof. compute. lia. Qed.

Fact sd_time_test_3: ((ti {| c := 32; t := 4|}) === (ti {| c := 32; t := 4|}))%time.
Proof. compute. auto. Qed.

End Examples.
(*| .. coq::|*)
