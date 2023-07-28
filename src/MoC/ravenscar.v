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

(*|
******************************
Ravenscar Model of Computation
******************************

In this module, we provide a formalization of the Ravenscar Ada profile.

|*)

(*| .. coq:: none |*)
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
Require Import List.
Import ListNotations. (* from List *)

Require Import Oqarina.core.all.
Require Import Oqarina.CoqExt.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.formalisms.Expressions.all.

Set Implicit Arguments.

Section Ravenscar.
(*| .. coq:: |*)

(*|
Definitions
===========

|*)

(*| Notion of time: we consider time based on natural values. This is consistent with the idea of using time ticks to measure instruction CET. *)

Definition Time : Type := nat.
Import Time_Notations.

(** priority concept. *)

Definition priority := nat.

(*|

Sequential programs
-------------------

A Ravenscar sequential program is reduced to a set of basic statements mimicking the imperative nature of an Ada program: XXX

|*)

Inductive statements : Type :=
  (* A sequential execution step *)
  | COMP (WCET : Time)

  (* Operations on protected objects *)
  | PO_FUNCTION (po : identifier) (op : identifier)
  | PO_ENTRY (po : identifier) (op : identifier)

  (* Delay until some time *)
  | DELAY_UNTIL_NEXT_PERIOD

  (* Sequence of statements *)
  | SEQ (s1: statements) (s2: statements)

  (* Condition: if b then s1 else s2 *)
  | IFTHENELSE (b: bexp) (s1: statements) (c2: statements)

  (* While b is true, execute s1 *)
  | WHILE (b: bexp) (s: statements)

  | SKIP.

Infix ";;" := SEQ (at level 80, right associativity).

(*| * Example of Ravenscar programs |*)

Example A_Program := COMP One ;; SKIP.

Example Ravenscar_Cyclic_Program := WHILE TRUE (COMP One ;;
                                                DELAY_UNTIL_NEXT_PERIOD).

(*|

Ravenscar tasks
---------------

An Ada task under the Ravenscar profile is uniquely defined by the tuple
%(priority, period, WCET)%

|*)

Inductive task_kind :=
  | PERIODIC | SPORADIC | BACKGROUND.

Inductive task_state :=
  | READY | RUNNING | IDLE | BLOCKED.

Scheme Equality for task_state.

Inductive task :=
  | Task : task_kind ->
          identifier ->
          priority ->
          Time -> (* period / MIAT *)
          statements -> task.

Record thread_state := {
  th_period : Time ;      (* period of the thread*)
  th_state : task_state ; (* current state *)
  th_cet : Time ;         (* compute execution time clock*)
  th_next_dispatch : Time (* time of the next dispatch *)
}.

Definition Dummy_thread_state := {|
  th_period := 0 ;
  th_state := RUNNING;
  th_cet := 0 ;
  th_next_dispatch := 0;
|}.

Definition set_thread_state (ts : thread_state) (state : task_state) := {|
  th_state := state ;
  th_period := ts.(th_period) ;
  th_cet := ts.(th_cet) ;
  th_next_dispatch := ts.(th_next_dispatch) |}.

Definition reset_thread_cet (ts : thread_state) := {|
  th_state := ts.(th_state) ;
  th_period := ts.(th_period) ;
  th_cet := 0 ;
  th_next_dispatch := ts.(th_next_dispatch) |}.

Definition ICET (s: statements) : nat :=
  match s with
  | COMP t => t
  | PO_FUNCTION _ _ | PO_ENTRY _ _ => 0
  | DELAY_UNTIL_NEXT_PERIOD => 0
  | SKIP => 0
  | SEQ _ _ => 0
  | IFTHENELSE _ _ _ => 0
  | WHILE _ _ => 0
  end.

Definition Update_CET (st: thread_state) (s : statements) :=
  {|
    th_state := th_state st ;
    th_period := th_period st ;
    th_cet := th_cet st + (ICET s) ;
    th_next_dispatch := st.(th_next_dispatch)
  |}.

Definition Set_Next_Dispatch_Time (st : thread_state) :=
  {|
    th_state := IDLE ;
    th_period := th_period st ;
    th_cet := th_cet st ;
    th_next_dispatch :=
      (th_next_dispatch st) + (th_period st)
  |}.

(*| We define an idle task as a background task with the lowest priority. It does nothin but waste CPU. |*)

Definition IDLE_TASK :=
  Task BACKGROUND (Id "Idle") 0 0 SKIP.

(** XXX trivial checks on well-formedness possible here also ..*)

(*|
Ravenscar Protected Object
--------------------------

An Ada protected object is similar to a Hoare monitor or a Java Synchronized inteface:
it is a collection of protected operations. There are four categories:

– PO_Set: sets a value to a protected object PO,
i.e. calling a protected operation in write mode through a procedure
– PO_Get: gets a value to a protecte object PO, i.e. calling a protected operation in write mode through
a procedure (write lock) or a function (read lock)
– PO_Send: call a procedure of a PO that ultimately impacts guards on entries for this PO.
– PO_Wait: block on an entry of this PO. Event(D): A Get Event call to synchroniser D

*)

Definition po_state : Type := identifier -> Time.

Inductive protected_operation :=
| PO_Function : identifier -> statements -> protected_operation
| PO_Entry : identifier -> statements-> protected_operation.

Inductive protected_object :=
| Protected_Object : identifier ->
                     priority ->
                     list protected_operation -> protected_object.

Definition A_PO :=
  Protected_Object (Id "A_PO") 42
    [ (PO_Function (Id "set") A_Program ) ;
      (PO_Entry (Id "get") A_Program)].

(*|
Legal Ravenscar programs
------------------------

We distinguish three cases of legal Ravenacar programs:

* periodic body
* sporadic body
* protected operation

For each situation, we define a correspoding legality rule and shows it is decidable.
|*)

(*|  A legal periodic body (PB) has the form
    PB := comp; PB | Set( _ ); PB | Get( _ ); PB | Send Event( _ ); PB | delay until
|*)

Fixpoint Legal_Periodic_Body (p : statements) :=
  match p with
  (* Atomic statements are always valid *)
  | COMP _ | PO_FUNCTION _ _  => True (* XXX *)

  | SKIP | DELAY_UNTIL_NEXT_PERIOD | WHILE _ _
  | IFTHENELSE _ _ _ => True

  (* Sequences of statements:
    - COMP, PO_GET, PO_SET, and PO_SENT are accepted *)

  (* PO_ENTRY and RET are rejected *)
  | PO_ENTRY _ _ => False

  (* DELAY_UNTIL_NEXT_PERIOD cannot be in a sequence, it can only be the last element *)
  | DELAY_UNTIL_NEXT_PERIOD  ;; _ => False

  (* Iteration *)
  | SEQ s1 s2 =>  Legal_Periodic_Body s1 /\ Legal_Periodic_Body s2
end.

Lemma Legal_Periodic_Body_dec: forall p,
  { Legal_Periodic_Body p } + { ~ Legal_Periodic_Body p }.
Proof.
  induction p ; simpl ; auto.
  destruct p1 ; auto ;
  apply dec_sumbool_and ; auto.
Qed.

Ltac prove_Legal_body := compute ; trivial ; auto.

Fact Legal_Periodic_Body_A_Program : Legal_Periodic_Body A_Program.
Proof.
  prove_Legal_body.
Qed.

Fact Legal_Periodic_Body_Ravenscar_Cyclic_Program :
  Legal_Periodic_Body Ravenscar_Cyclic_Program.
Proof.
  prove_Legal_body.
Qed.

(*| XXX |*)

Definition Legal_Sporadic_Body (p : statements)  :=
  match p with
  (* PO_WAIT is the first statement *)
  | PO_ENTRY _ _ ;; s2 => Legal_Periodic_Body s2

  (* because the precedent rule exits to execute Legal_Periodic_Body, the other
     combination should be false *)
  | _ => False
end.

Lemma Legal_Sporadic_Body_dec: forall p,
  { Legal_Sporadic_Body p } + { ~ Legal_Sporadic_Body p }.
Proof.
  induction p ; simpl ; auto.
  destruct p1 ; auto.
  apply Legal_Periodic_Body_dec.
Qed.

(*||*)
Fixpoint Legal_PO_Body (p : statements) :=
  match p with
  (* Atomic statements are always valid *)
  | COMP _  | SKIP   | WHILE _ _  | IFTHENELSE _ _ _ => True

  (* Sequences of statements:
    - COMP, PO_GET, PO_SET, and PO_SENT are accepted *)

  (* PO_ENTRY and RET are rejected *)
  | PO_FUNCTION _ _  => False (* XXX *)
  | PO_ENTRY _ _ => False

  (* DELAY_UNTIL_NEXT_PERIOD cannot be in a sequence, it can only be the last element *)
  | DELAY_UNTIL_NEXT_PERIOD  => False

  (* Iteration *)
  | SEQ s1 s2 =>  Legal_PO_Body s1 /\ Legal_PO_Body s2
end.

Lemma Legal_PO_Body_dec: forall p,
  { Legal_PO_Body p } + { ~ Legal_PO_Body p }.
Proof.
  induction p ; simpl ; auto.
  apply dec_sumbool_and ; auto.
Qed.

Definition Legal_protected_operation (p : protected_operation) :=
  match p with
    | PO_Function _ s => Legal_PO_Body s
    | PO_Entry _ s => Legal_PO_Body s
  end.

  Lemma Legal_protected_operation_dec: forall p,
  { Legal_protected_operation p } + { ~ Legal_protected_operation p }.
Proof.

  induction p ; unfold Legal_protected_operation ;
  apply Legal_PO_Body_dec.
Qed.

(*|

Semantics of Ravenscar Programs
===============================

Reduction semantics of Ravenscar programs
-----------------------------------------

( https://www.cs.princeton.edu/courses/archive/spr96/cs441/notes/l9.html )

A reduction semantics (or rewriting semantics) defines an an evaluation function eval for expressions based on a notion of reduction. We say that an expression e evaluates to an answer a if and only if e reduces to a.

The reduction relation ->* is the reflexive and transitive closure of the simpler reduction relation ->. That is, ->* consists of zero or more -> steps.
|*)

Inductive red : statements * thread_state
                -> statements * thread_state -> Prop :=
  | red_seq_done: forall c s,
    red (SEQ SKIP c, s) (c, s)

  | red_seq_step: forall c1 c s1 c2 s2,
    red (c1, s1) (c2, s2) ->
    red (SEQ c1 c, s1) (SEQ c2 c, s2)

  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval b then c1 else c2), s)

  | red_comp: forall s t,
    red (COMP t, s)
        (SKIP, Update_CET s (COMP t))

  | red_delay_until: forall s,
      red (DELAY_UNTIL_NEXT_PERIOD, s)
          (SKIP, Set_Next_Dispatch_Time s)

  | red_po_function: forall s i1 i2,
    red (PO_FUNCTION i1 i2, s)
        (SKIP, Update_CET s (PO_FUNCTION i1 i2))

  | red_po_entry: forall s i1 i2,
    red (PO_ENTRY i1 i2, s)
      (SKIP, Update_CET s (PO_ENTRY i1 i2))

  | red_while_false: forall b c s,
      beval b = false ->
      red (WHILE b c, s) (SKIP, s)

  | red_while_true: forall b c s,
      beval b = true ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s).

(*| A configuration [(c,s)] reduces to at most one configuration, in other words all Ravenscar programs are deterministic. |*)

Lemma red_determ:
    forall cs cs1, red cs cs1 -> forall cs2, red cs cs2 -> cs1 = cs2.
Proof.
    induction 1; intros cs2 R2; inversion R2; subst; eauto.
    - inversion H3.
    - inversion H.
    - assert (EQ: (c2, s2) = (c4, s3)) by auto. congruence.
    - congruence.
    - congruence.
Qed.

Lemma red_seq_steps: forall c2 s c s' c',
  clos_refl_trans_1n _ red (c, s) (c', s') ->
    clos_refl_trans_1n _ red ((c;;c2), s) ((c';;c2), s').
Proof.
  intros. dependent induction H.
  - apply rt1n_refl.
  - destruct y as [c1 st1]. apply rt1n_trans with (c1;;c2, st1).
    apply red_seq_step. apply H. apply  IHclos_refl_trans_1n ; auto.
Qed.

(*|

Natural semantics of Ravenscar programs
---------------------------------------

|*)

Inductive rexec: thread_state -> statements -> thread_state
-> Prop :=
  | rexec_skip: forall s,
    rexec s SKIP s

  | rexec_po_function: forall s i1 i2,
    rexec s (PO_FUNCTION i1 i2) (Update_CET s (PO_FUNCTION i1 i2))

  | rexec_po_entry: forall s i1 i2,
    rexec s (PO_ENTRY i1 i2) (Update_CET s (PO_ENTRY i1 i2))

  | rexec_seq: forall c1 c2 s s' s'',
    rexec s c1 s' -> rexec s' c2 s'' ->
      rexec s (SEQ c1 c2) s''

  | rexec_ifthenelse: forall b c1 c2 s s',
      rexec s (if beval b then c1 else c2) s' ->
      rexec s (IFTHENELSE b c1 c2) s'

  | rexec_comp: forall s t,
      rexec s (COMP t) (Update_CET s (COMP t))

  | rexec_delay_until: forall s,
      rexec s (DELAY_UNTIL_NEXT_PERIOD)
            (Set_Next_Dispatch_Time s)

  | rexec_while_false: forall b c s,
            beval b = false ->
            rexec s (WHILE b c) s

  | rexec_while_true: forall b c s s' s'',
            beval b = true -> rexec s c s' -> rexec s' (WHILE b c) s'' ->
            rexec s (WHILE b c) s''.

Theorem rexec_to_reds: forall s c s',
  rexec s c s' ->
    clos_refl_trans_1n _ red (c, s) (SKIP, s').
Proof.
  induction 1.

  - (* SKIP *)
    apply rt1n_refl.

  - (* PO_FUNCTION *)
    eapply rt1n_trans. apply red_po_function. apply rt1n_refl.

  - (* PO_ENTRY *)
    eapply rt1n_trans. apply red_po_entry. apply rt1n_refl.

  - (* SEQ *)
    eapply rt1n_trans'. apply red_seq_steps. apply IHrexec1.
    eapply rt1n_trans.  apply red_seq_done.  apply IHrexec2.

  - (* IFTHENELSE *)
    eapply rt1n_trans. apply red_ifthenelse. auto.

  - (* COMP *)
    eapply rt1n_trans. apply red_comp. apply rt1n_refl.

  - (* DELAY_UNTIL_NEXT_PERIOD *)
    eapply rt1n_trans. apply red_delay_until. apply rt1n_refl.

  - (* WHILE / false *)
  eapply rt1n_trans. apply red_while_false. apply H. apply rt1n_refl.

  - (* WHILE / true *)
  eapply rt1n_trans. apply red_while_true. apply H.
  eapply rt1n_trans'. apply red_seq_steps. apply IHrexec1.
  eapply rt1n_trans. apply red_seq_done. apply IHrexec2.

Qed.

(*|
Equivalence between reduction and natural semantics
---------------------------------------------------
|*)

Lemma red_append_rexec:
  forall c1 s1 c2 s2, red (c1, s1) (c2, s2) ->
  forall s', rexec s2 c2 s' -> rexec s1 c1 s'.
Proof.
  intros until s2; intros STEP. dependent induction STEP; intros.

  - (* SKIP *)
    apply rexec_seq with s2. apply rexec_skip. auto.

  - (* SEQ *)
    inversion H; subst. apply rexec_seq with s'0.
    eapply IHSTEP; eauto.
    auto.

  - (* red_ifthenelse *)
    apply rexec_ifthenelse. auto.

  - (* COMP *)
    inversion H. subst. apply rexec_comp.

  - (* DELAY_UNTIL_NEXT_PERIOD *)
    inversion H. subst. apply rexec_delay_until.

  - (* PO_FUNCTION*)
    inversion H. subst. apply rexec_po_function.

  - (* PO_ENTRY *)
    inversion H. subst. apply rexec_po_entry.

  - (* WHILE / false *)
    inversion H0. subst. eapply rexec_while_false. trivial.

  - (* WHILE / true *)
    inversion H0. subst. apply rexec_while_true with (s' := s'0) ; auto.

Qed.

(** By induction on the reduction sequence, it follows that a command
    that reduces to [SKIP] executes according to the natural semantics,
    with the same final state. *)

Theorem reds_to_rexec: forall s c s',
  clos_refl_trans_1n _ red (c, s) (SKIP, s') -> rexec s c s'.
Proof.
  intros. dependent induction H.
  - apply rexec_skip.
  - destruct y as [c1 s1]. apply red_append_rexec with c1 s1; auto.
Qed.

(*|
Simulation of Ravenscar programs
--------------------------------

|*)

Fixpoint Eval (fuel : nat) (st :thread_state) (s : statements)
  : thread_state * bool
:=

  match fuel with
  | 0 => (st, false)
  | S fuel' =>

  match s with
    (* A sequential execution step *)
    | COMP t => (Update_CET st s, true)

    (* Operations on protected objects *)
    | PO_FUNCTION _ _ | PO_ENTRY _ _ => (Update_CET st s, true)

    (* Delay until some time *)
    | DELAY_UNTIL_NEXT_PERIOD => (Set_Next_Dispatch_Time st, true)

    | SKIP => (st, true)

    | WHILE b s1 =>
      if beval b then
        match Eval fuel' st s1 with
        | (st', false) => (st', false)
        | (st', true) => Eval fuel' st' (WHILE b s1)
        end
      else (st, true)

    | IFTHENELSE b s1 s2 =>
      Eval fuel' st (if beval b then s1 else s2)

    | SEQ s1 s2 =>
      match Eval fuel' st s1 with
      | (st', false) => (st', false)
      | (st', true) => Eval fuel' st' s2
      end
  end
end.

Compute Eval 10 Dummy_thread_state Ravenscar_Cyclic_Program.

Lemma Eval_sound: forall fuel s c s' ,
  Eval fuel s c = (s', true) -> rexec s c s'.
Proof.
  induction fuel.
  - discriminate.
  - induction c;  simpl.
    + (* COMP *)
      intros. inversion H. apply rexec_comp.

    + (* PO_FUNCTION *)
      intros. inversion H.
      apply rexec_po_function.

    + (* PO_ENTRY *)
      intros. inversion H. apply rexec_po_entry.

    + (* DELAY_UNTIL_NEXT_PERIOD *)
      intros. inversion H. apply rexec_delay_until.

    + (* SEQ *)
      intros. destruct (Eval fuel s c1) eqn:H2.
      apply rexec_seq with (s' := t).

      apply IHfuel.
      destruct b eqn:H0. apply H2. inversion H.

      apply IHfuel.
      destruct b eqn:H0. apply H. inversion H.

    + (* IFTHENELSE *)
      intros. destruct (beval b) eqn:H2.
      -- eapply rexec_ifthenelse. rewrite H2. apply IHfuel. apply H.
      -- eapply rexec_ifthenelse. rewrite H2. apply IHfuel. apply H.

    + (* WHILE *)
      intros. destruct (beval b) eqn:H2.
      -- destruct (Eval fuel s c) eqn:H3.

        apply rexec_while_true with (s' := t).
        apply H2.
        apply IHfuel.
        destruct b0. apply H3. inversion H.

        apply IHfuel. destruct b0. apply H. inversion H.

      -- inversion H. eapply rexec_while_false. apply H2.

    + (* SKIP *)
      intros. inversion H. apply rexec_skip.
Qed.

(*| :coq:`Eval_cont'_end` shows that if :coq:`Eval_cont'` converges to some value, then :coq:`fuel > 0`. |*)
Lemma Eval_end: forall fuel st s st',
  Eval fuel st s = (st', true) -> fuel > 0.
Proof.
  induction fuel as [ | fuel ].
  - discriminate.
  - auto with *.
Qed.

Lemma Eval_split_seq: forall fuel st s1 s2 st',
  Eval (S fuel) st (s1;; s2) = (st', true) ->
    exists st'', Eval fuel st s1 = (st'', true) /\ Eval fuel st'' s2 = (st', true).
Proof.
  intros.
  simpl in H.
  destruct (Eval fuel st s1).
  exists t.
  destruct b.
  - auto.
  - inversion H.
Qed.

Lemma Eval_split_while: forall fuel st b s1 st',
  Eval (S fuel) st (WHILE b s1) = (st', true) ->
    ((beval b = true) /\
      (exists st'', (Eval fuel st s1 = (st'', true)) /\
                    (Eval fuel st'' (WHILE b s1)) = (st', true)))
    \/ ((beval b = false) /\ st = st').
Proof.
  intros.
  simpl in H.
  destruct (beval b).
  - destruct (Eval fuel st s1).
    left. split. trivial. exists t.
    destruct b0. auto. inversion H.
  - right. split. trivial. inversion H. trivial.
Qed.

Lemma Eval_end_fix: forall fuel st s st' ,
  Eval fuel st s = (st', true) -> Eval (S fuel) st s = (st', true).
Proof.
  intro fuel.
  induction fuel.
  - intros. discriminate.
  - destruct s ; try intuition. (* Simplify all trivial cases *)
    + (* SEQ *)
      apply Eval_split_seq in H.
      destruct H as (st'' ,H).
      destruct H.

      assert (H1 : Eval (S (S fuel)) st (s1;; s2) =
                match Eval (S fuel) st s1 with
                | (st'', false) => (st'', false)
                | (st'', true) => Eval (S fuel) st'' s2
                end).
      intuition.

      assert (Eval (S fuel) st s1 = (st'', true)).
      apply IHfuel ; trivial.
      rewrite H2 in H1.

      assert (Eval (S fuel) st'' s2 = (st', true)).
      apply IHfuel ; trivial.

      rewrite H3 in H1.
      trivial.

    + (* IFTHENELSE *)
      assert (H1:
        Eval (S fuel) st (IFTHENELSE b s1 s2) =
        Eval fuel st (if beval b then s1 else s2)).
      intuition.

      assert (H1b:
        Eval (S (S fuel)) st (IFTHENELSE b s1 s2) =
        Eval (S fuel) st (if beval b then s1 else s2)).
      intuition.

      destruct (beval b) eqn:beval.

      * assert (H2: Eval fuel st s1 = (st', true)).
        rewrite <- H1. trivial.
        rewrite H1b. apply IHfuel ; trivial.

      * assert (H2: Eval fuel st s2 = (st', true)).
        rewrite <- H1. trivial.
        rewrite H1b. apply IHfuel ; trivial.

    + (* WHILE *)
      assert (H1 : Eval (S (S fuel)) st (WHILE b s) =
            if (beval b) then
            match Eval (S fuel) st s with
            | (st'', false) => (st'', false)
            | (st'', true) => Eval (S fuel) st'' (WHILE b s)
            end
            else (st, true)).
      intuition.
      apply Eval_split_while in H.

      destruct (beval b).

    * destruct H. destruct H.
      destruct H0 as (st'', H0).
      destruct H0.

      assert (Eval (S fuel) st s = (st'', true)).
      apply IHfuel; trivial.

      rewrite H3 in H1.

      assert (Eval (S fuel) st'' (WHILE b s) = (st', true)).
      apply IHfuel; trivial.

      rewrite H4 in H1. trivial.

      destruct H.
      discriminate.

    * destruct H. destruct H.

      discriminate.

      destruct H. subst. trivial.
Qed.

Lemma Eval_complete: forall s c s',
  rexec s c s' -> exists fuel1,
    forall fuel, (fuel >= fuel1)%nat -> Eval fuel s c = (s', true).
Proof.
  induction 1 ; intuition.

  - (* SKIP *)
    exists 1. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* PO_FUNCTION *)
    exists 1. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* PO_ENTRY *)
    exists 1. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* SEQ *)
    intros.
    destruct IHrexec1 as (fuel1, IHrexec1').
    destruct IHrexec2 as (fuel2, IHrexec2').

    exists (fuel1 + fuel2 + 2).
    intros.
    assert (fuel > 0). lia.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H2.
    destruct H3 as (n, H3).
    subst. simpl.

    assert (n > fuel1). lia.
    assert (Eval n s c1 = (s', true)). apply IHrexec1'. lia.
    rewrite H4.
    apply IHrexec2'. lia.

  - (* IFTHENELSE *)
    destruct IHrexec as (fuel, IHrexec').
    exists (fuel + 1).
    intros.
    assert (exists n, fuel0 = S n).
    apply zero_or_succ_positive. lia.
    destruct H1 as (n, H1).
    subst. simpl.

    apply IHrexec'. lia.

  - (* COMP *)
    exists 1. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* DELAY_UNTIL_NEXT_PERIOD *)
    exists 1. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* WHILE / false *)
    exists 1. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H0.
    destruct H1 as (n, H1).
    subst. simpl. rewrite H. trivial.

  - (* WHILE / true *)

    destruct IHrexec1 as (fuel1, IHrexec1').
    destruct IHrexec2 as (fuel2, IHrexec2').

    exists (fuel1 + fuel2 + 2).
    intros.
    assert (fuel > 0). lia.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H3.
    destruct H4 as (n, H4).
    subst. simpl.
    rewrite H.

    assert (n > fuel1). lia.
    assert (Eval n s c = (s', true)). apply IHrexec1'. lia.
    rewrite H5. apply IHrexec2'. lia.
Qed.

Fixpoint Eval2 (fuel : nat) (st :thread_state) (s : statements)
  : thread_state * bool * nat
:=
  match fuel with
  | 0 => (st, false, 0)
  | S fuel' =>

  match s with
    (* A sequential execution step *)
    | COMP t => (Update_CET st s, true, ICET s)

    (* Operations on protected objects *)
    | PO_FUNCTION _ _ | PO_ENTRY _ _ => (Update_CET st s, true, ICET s)

    (* Delay until some time *)
    | DELAY_UNTIL_NEXT_PERIOD => (Set_Next_Dispatch_Time st, true, ICET s)

    | SKIP => (st, true, ICET s)

    | IFTHENELSE b s1 s2 =>
      if beval b then
         Eval2 fuel' st s1 else
         Eval2 fuel' st s2

    | WHILE b s1 =>
      if beval b then
        match Eval2 fuel' st s1 with
        | (st', false, _) => (st', false, 0)
        | (st', true, cet) => Eval2 (fuel' - cet) st' (WHILE b s1)
        end

      (*  Eval2 fuel' st (s1 ;; (WHILE b s1)) *)
      else (st, true, 0)

    | SEQ s1 s2 =>
      match Eval2 fuel' st s1 with
      | (st', false, _) => (st', false, 0)
      | (st', true, cet) => Eval2 (fuel' - cet) st' s2
      end
  end
end.

(*| :coq:`Eval_cont'_end` shows that if :coq:`Eval_cont'` converges to some value, then :coq:`fuel > 0`. |*)
Lemma Eval2_end: forall fuel st s st' cet,
  Eval2 fuel st s = (st', true, cet) -> fuel > 0.
Proof.
  induction fuel as [ | fuel ].
  - discriminate.
  - auto with *.
Qed.

Lemma Eval2_split_seq: forall fuel st s1 s2 st' cet,
  Eval2 (S fuel) st (s1;; s2) = (st', true, cet) ->
    exists st'' cet'',
      Eval2 fuel st s1 = (st'', true, cet'') /\
      Eval2 (fuel - cet'') st'' s2 = (st', true, cet).
Proof.
  intros.
  simpl in H.
  destruct (Eval2 fuel st s1).
  destruct p.
  exists t. exists (n).
  destruct b.
  - auto.
  - inversion H.
Qed.

Lemma Eval2_split_while: forall fuel st b s1 st' cet,
  Eval2 (S fuel) st (WHILE b s1) = (st', true, cet) ->
    ((beval b = true) /\
      (exists st'' cet', (Eval2 fuel st s1 = (st'', true, cet')) /\
                    (Eval2 (fuel - cet') st'' (WHILE b s1)) = (st', true, cet)))
    \/ ((beval b = false) /\ st = st' /\ cet = 0).
Proof.
  intros.
  simpl in H.
  destruct (beval b).
  - destruct (Eval2 fuel st s1) eqn:Eval2.
    destruct p.
    left. split.

    + trivial.
    + assert (fuel > 0). eapply Eval2_end.
      destruct b0.
      apply Eval2. inversion H.

      assert (exists n, fuel = S n).
      apply zero_or_succ_positive. lia.
      destruct H1 as (p, H1).
      subst.

      exists t. exists n.
      destruct b0. auto. inversion H.
  - right. split. trivial. inversion H. split; trivial.
Qed.

Lemma Eval2_split_ifthenelse: forall fuel st st' cet b s1 s2,
Eval2 (S fuel) st (IFTHENELSE b s1 s2) = (st', true, cet) ->
  ((beval b = true) /\ Eval2 fuel st s1 = (st', true, cet)) \/
  ((beval b = false) /\ Eval2 fuel st s2 = (st', true, cet)).
Proof.
  intros.
  simpl in H.
  destruct (beval b) ; intuition.
Qed.

Lemma Eval2_complete: forall s c s',
  rexec s c s' -> exists fuel1 cet,
    forall fuel, (fuel >= fuel1)%nat -> Eval2 fuel s c = (s', true, cet).
Proof.
  induction 1 ; intuition.

  - (* SKIP *)
    exists 1. exists 0. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* PO_FUNCTION *)
    exists 1. exists 0. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* PO_ENTRY *)
    exists 1. exists 0. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* SEQ *)
    intros.
    destruct IHrexec1 as (fuel1, IHrexec1).
    destruct IHrexec1 as (cet1, IHrexec1).

    destruct IHrexec2 as (fuel2, IHrexec2).
    destruct IHrexec2 as (cet2, IHrexec2).

    exists (fuel1 + fuel2 + 2 + cet1).
    exists cet2.
    intros.
    assert (fuel > 0). lia.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H2.
    destruct H3 as (n, H3).
    subst. simpl.

    assert (n > fuel1). lia.
    assert (Eval2 n s c1 = (s', true, cet1)). apply IHrexec1. lia.
    rewrite H4.
    apply IHrexec2. lia.

  - (* IFTHENELSE *)
    destruct IHrexec as (fuel, IHrexec).
    destruct IHrexec as (t, IHrexec).

    exists (fuel + 1). exists t.
    intros.
    assert (exists n, fuel0 = S n).
    apply zero_or_succ_positive. lia.
    destruct H1 as (n, H1).
    subst. simpl.

    destruct (beval b) ;
      apply IHrexec ; lia.

  - (* COMP *)
    exists 1. exists t. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* DELAY_UNTIL_NEXT_PERIOD *)
    exists 1. exists 0. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H.
    destruct H0 as (n, H0).
    subst. simpl ; trivial.

  - (* WHILE / false *)
    exists 1. exists 0. intros.
    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H0.
    destruct H1 as (n, H1).
    subst. simpl. rewrite H. trivial.

  - (* WHILE / true *)

    destruct IHrexec1 as (fuel1, IHrexec1).
    destruct IHrexec1 as (cet1, IHrexec1).

    destruct IHrexec2 as (fuel2, IHrexec2).
    destruct IHrexec2 as (cet2, IHrexec2).

    exists (fuel1 + fuel2 + 2 + cet1).
    exists cet2.
    intros.
    assert (fuel > 0). lia.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive , H3.
    destruct H4 as (n, H4).
    subst. simpl.
    rewrite H.

    assert (n > fuel1). lia.
    assert (Eval2 n s c = (s', true, cet1)). apply IHrexec1. lia.

    rewrite H5.

    assert (Hm: exists m, n = S m).
    apply zero_or_succ_positive. lia.
    destruct Hm as (m, Hm).
    subst. simpl.

    assert (Eval2 m s c = (s', true, cet1)). apply IHrexec1. lia.
    apply IHrexec2.
    destruct cet1 ; lia.
Qed.

Lemma Eval2_end_fix: forall s fuel st st' cet,
  Eval2 fuel st s = (st', true, cet) -> Eval2 (S fuel) st s = (st', true, cet).
Proof.
  induction s.
  - (* COMP *)
    intros.
    assert (Hfuel: fuel > 0). eapply Eval2_end. apply H.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct Hn as (n, Hn).
    subst.
    simpl in H. simpl. apply H.

  - (* PO_FUNCTION *)
    intros.
    assert (Hfuel: fuel > 0). eapply Eval2_end. apply H.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct Hn as (n, Hn).
    subst.
    simpl in H. simpl. apply H.

  - (* PO_ENTRY *)
    intros.
    assert (Hfuel: fuel > 0). eapply Eval2_end. apply H.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct Hn as (n, Hn).
    subst.
    simpl in H. simpl. apply H.

  - (* DELAY_UNTIL_NEXT_PERIOD *)
    intros.
    assert (Hfuel: fuel > 0). eapply Eval2_end. apply H.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct Hn as (n, Hn).
    subst.
    simpl in H. simpl. apply H.

  - (* SEQ *)
    intros.

    assert (Hfuel: fuel > 0).
    eapply Eval2_end. apply H.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct H0 as (n, H0).
    subst.

    apply Eval2_split_seq in H.
    destruct H as (st'' ,H).
    destruct H as (cet'', H).

    assert (H1 : Eval2 (S (S n)) st (s1;; s2) =
                match Eval2 (S n) st s1 with
                | (st'', false, _) => (st'', false, 0)
                | (st'', true, cet) => Eval2 (S n - cet) st'' s2
                end).
      intuition.

      assert (H2: Eval2 (S n) st s1 = (st'', true, cet'')).
      apply IHs1 ; apply H.
      rewrite H2 in H1.

      assert (H3: Eval2 (S (n - cet'')) st'' s2 = (st', true, cet)).
      apply IHs2 ; apply H.

      assert (n - cet'' > 0).
      eapply Eval2_end. apply H.

      assert (S (n - cet'') = S n - cet'').
      lia.

      rewrite H4 in H3.
      rewrite H3 in H1.
      trivial.

  - (* IFTHENELSE *)
    strong induction fuel.
    intros.

    assert (Hfuel: fuel > 0).
    eapply Eval2_end. apply H0.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct H1 as (n, H1).
    subst.

    assert (HSSn: Eval2 (S (S n)) st (IFTHENELSE b s1 s2) =
      if beval b then Eval2 (S n) st s1 else Eval2 (S n) st s2).
    intuition.

    assert (HSn: Eval2 (S n) st (IFTHENELSE b s1 s2) =
      if beval b then Eval2 n st s1 else Eval2 n st s2).
    intuition.

    apply Eval2_split_ifthenelse in H0.

    destruct (beval b).
    + rewrite HSSn.
      assert (Eval2 n st s1 = (st', true, cet)).
      destruct H0.
      * intuition.
      * destruct H0. auto with *.
      * auto.
    + rewrite HSSn.
        assert (Eval2 n st s2 = (st', true, cet)).
        destruct H0.
        * destruct H0. auto with *.
        * intuition.
        * auto.

  -  (* WHILE *)
    strong induction fuel.

    intros.
    assert (Hfuel: fuel > 0).
    eapply Eval2_end. apply H0.

    assert (exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct H1 as (n, H1).
    subst.

    assert (H1 : Eval2 (S (S n)) st (WHILE b s) =
          if (beval b) then

          match Eval2 (S n) st s with
          | (st'', false, _) => (st'', false, 0)
          | (st'', true, cet') => Eval2 (S n - cet') st'' (WHILE b s)
          end
           (* Eval2 (S n) st (s ;; WHILE b s) *)
          else (st, true, 0)).
    intuition.
    apply Eval2_split_while in H0.

    destruct (beval b).

    * destruct H0.

      -- destruct H0.
         destruct H2 as (st'', H2).
         destruct H2 as (cet', H2).
         destruct H2.

         assert (H4: Eval2 (S n) st s = (st'', true, cet')).
         apply IHs; trivial.
         rewrite H4 in H1.

         destruct (cet').
         ++ rewrite H1.
            assert (S n - 0 = S n). lia. rewrite H5.
            eapply H. lia. rewrite <- H3.
            assert (n - 0 = n). lia. rewrite H6. reflexivity.

         ++ rewrite H1.
            assert (n - S n0 > 0). eapply Eval2_end. apply H3.
            assert (S n - S n0 = S (n - S n0)). lia.
            rewrite H6.
            eapply H. lia. apply H3.

      -- inversion H0. inversion H2.

    * destruct H0.
      -- destruct H0. inversion H0.
      -- destruct H0. destruct H2. subst. apply H1.

  - (* SKIP *)
    intros.
    assert (Hfuel: fuel > 0). eapply Eval2_end. apply H.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.
    destruct Hn as (n, Hn).
    subst.
    simpl in H. simpl. apply H.
Qed.

(* XXX Make this more generic *)
Lemma Eval2_end_fix': forall fuel s st st' cet,
Eval2 fuel st s = (st', true, cet) -> (forall n, Eval2 (fuel + n) st s = (st', true, cet)).
Proof.
intros.
induction n.
- assert (fuel + 0 = fuel). auto. rewrite H0. apply H.
- assert (fuel + S n = S (fuel + n)). lia. rewrite H0.
  apply Eval2_end_fix. apply IHn.
Qed.

Lemma Eval2_end_fix'': forall fuel s st st' cet,
Eval2 fuel st s = (st', true, cet) -> (forall fuel', fuel' > fuel -> Eval2 fuel' st s = (st', true, cet)).
Proof.
intros.
assert (exists n, fuel' = fuel + n).
apply nat_split. apply H0.
destruct H1 as (n, H1). rewrite H1. apply Eval2_end_fix'.
apply H.
Qed.

Lemma Eval2_sound: forall c fuel s s' cet,
  Eval2 fuel s c = (s', true, cet) -> rexec s c s'.
Proof.
  intros c fuel.
  generalize dependent fuel.

  induction c.
  - induction fuel. discriminate. intros. inversion H. apply rexec_comp.
  - induction fuel. discriminate. intros. inversion H. apply rexec_po_function.
  - induction fuel. discriminate. intros. inversion H. apply rexec_po_entry.
  - induction fuel. discriminate. intros. inversion H. apply rexec_delay_until.

  - (* SEQ *)
    intros.

    assert (Hfuel: fuel > 0).
    eapply Eval2_end. apply H.

    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive. apply Hfuel.
    destruct Hn as (n, Hn).
    subst. simpl in H.

    destruct (Eval2 n s c1) eqn:H2. destruct p.
    apply rexec_seq with (s' := t).

    eapply IHc1.
    destruct b eqn:H0. apply H2. inversion H.

    eapply IHc2.
    destruct b eqn:H0. apply H. inversion H.

  - (* IFTHENELSE *)
    strong induction fuel.
    intros.

    assert (Hfuel: fuel > 0).
    eapply Eval2_end. apply H0.

    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive. apply Hfuel.
    destruct Hn as (n, Hn).
    subst.

    apply Eval2_split_ifthenelse in H0.

    destruct H0.
    + destruct H0. eapply rexec_ifthenelse.
      rewrite H0. eapply IHc1. apply H1.
    + destruct H0. eapply rexec_ifthenelse.
      rewrite H0. eapply IHc2. apply H1.

  - (* WHILE *)

    strong induction fuel.
    intros.

    assert (Hfuel: fuel > 0).
    eapply Eval2_end. apply H0.

    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive. apply Hfuel.
    destruct Hn as (n, Hn).
    subst.
    apply Eval2_split_while in H0.

    destruct H0.
    + destruct H0.
      destruct H1 as (st'', H1).
      destruct H1 as (cet', H1).
      destruct H1.

      apply rexec_while_true with (s' := st'').
      * apply H0.
      * eapply IHc. apply H1.
      * eapply H with (s := st'') (n := n - cet'). lia. apply H2.

    + destruct H0. destruct H1. subst.
      eapply rexec_while_false. apply H0.

  - (* SKIP *)
  induction fuel. discriminate. intros. inversion H. apply rexec_skip.
Qed.

(*|
These proofs are highly repetitive. We define a couple of handy tactices to expedite the process

* :coq:`prove_fuel_positive_in_Eval2_Hyp` shows that if one hypothesis contains a valuation of Eval2 that returns true, then the fuel parameter is positive.

|*)

Ltac prove_fuel_positive_in_Eval2_Hyp x :=
  match goal with
    | [ H: Eval2 x _ _ = (_, true, _ ) |- _ ] =>
      let H2 := fresh "H" in
      assert (x > 0) as H2 by solve [
        eapply Eval2_end ; apply H | idtac ]

    | [ H: _ |- _ ]=> idtac
  end.

(*|

* :coq:`destruct_positive` looks for a positive number and destruct it.

|*)

Ltac destruct_positive x :=
  match goal with
    | [ H: x > 0 |- _ ] =>
      let H2 := fresh "H" in

      assert (exists n, x = S n) as H2 by solve [
      apply zero_or_succ_positive ; apply H ] ;
      destruct H2 as (n, H2); subst

    | [ H: _ |- _ ]=> idtac
  end.

Ltac Eval2_Eval_Equivalent_base_cases H :=
  simpl in * ; inversion H ;reflexivity.

Lemma Eval2_Eval_Equivalent: forall fuel c s s' cet,
  Eval2 fuel s c = (s', true, cet) -> Eval fuel s c = (s', true).
Proof.
  strong induction fuel.

  induction c.

  + (* COMP *)
    intros s s' cet H0.

    prove_fuel_positive_in_Eval2_Hyp fuel.
    destruct_positive fuel.
    Eval2_Eval_Equivalent_base_cases H0.

  + (* PO_FUNCTION *)
    intros s s' cet H0.

    prove_fuel_positive_in_Eval2_Hyp fuel.
    destruct_positive fuel.
    Eval2_Eval_Equivalent_base_cases H0.

  + (* PO_ENTRY *)
    intros s s' cet H0.

    prove_fuel_positive_in_Eval2_Hyp fuel.
    destruct_positive fuel.
    Eval2_Eval_Equivalent_base_cases H0.

  + (* DELAY_UNTIL_NEXT_PERIOD *)
    intros s s' cet H0.

    prove_fuel_positive_in_Eval2_Hyp fuel.
    destruct_positive fuel.
    Eval2_Eval_Equivalent_base_cases H0.

  + (* c1 ;; c2 *)
    intros.
    assert (Hfuel: fuel > 0). apply Eval2_end in H0. apply H0.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive. apply Hfuel.
    destruct Hn as (n, Hn). subst.

    assert (H2 : Eval2 (S n) s (c1;; c2) =
                match Eval2 n s c1 with
                | (st'', false, _) => (st'', false, 0)
                | (st'', true, cet) => Eval2 (n - cet) st'' c2
                end).
    intuition.
    destruct (Eval2 n s c1) eqn:HEval2.
    destruct p.
    pose proof H0.
    rewrite H0 in H2.
    assert (b = true). destruct b. reflexivity. inversion H2.
    subst.

    assert (H3 : Eval (S n) s (c1;; c2) =
      match Eval n s c1 with
      | (st'', false) => (st'', false)
      | (st'', true) => Eval n st'' c2
      end).
    intuition.

    assert (Eval n s c1 = (t, true)).
    eapply H. lia. apply HEval2.
    rewrite H4 in H3.

    assert (Eval n t c2 = (s', true)).
    eapply H. lia. apply eq_sym in H2.

    destruct n0.
    assert (n - 0 = n). lia. rewrite H5 in H2. apply H2.

    eapply Eval2_end_fix''.
    apply H2.

    assert (n > 0). eapply Eval_end. apply H4.
    lia.

    rewrite H5 in H3. apply H3.

  + (* IFTHENELSE *)
    intros.

    assert (Hfuel: fuel > 0). apply Eval2_end in H0. apply H0.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive. apply Hfuel.
    destruct Hn as (n, Hn). subst.
    simpl in H0. simpl.

    destruct (beval b).
    * eapply H. lia. apply H0.
    * eapply H. lia. apply H0.

  + (* WHILE b c *)
    intros.
    assert (Hfuel: fuel > 0). apply Eval2_end in H0. apply H0.
    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive. apply Hfuel.
    destruct Hn as (n, Hn). subst.

    apply Eval2_split_while in H0.

    destruct H0.
    * destruct H0.
      destruct H1 as (st'', H1).
      destruct H1 as (cet', H1).
      destruct H1.

      simpl.
      rewrite H0.

      assert (Eval n s c = (st'', true)).
      eapply H. lia. apply H1.
      rewrite H3.

      destruct cet'.
      assert (n - 0 = n). lia. rewrite H4 in H2.
      eapply H. lia. apply H2.

      apply H with (cet := cet). lia.
      eapply Eval2_end_fix'' with ( fuel:= n - S cet').
      apply H2.
      assert (n > 0). eapply Eval2_end. apply H1.

      lia.

    * simpl. destruct H0. rewrite H0. destruct H1. subst. reflexivity.

  + (* SKIP *)
    intros s s' cet H0.

    prove_fuel_positive_in_Eval2_Hyp fuel.
    destruct_positive fuel.
    Eval2_Eval_Equivalent_base_cases H0.

Qed.

(*|
Continuation semantics
======================

we now introduce another form of "small-step" semantics as an alternative to the reduction semantics.  In the new semantics, the command to be executed is explicitly decomposed into

  * a sub-command under focus, where computation takes place;
  * a context that describes the position of the sub-command in the
      whole command; or, equivalently, a continuation that describes
      the parts of the whole command that remain to execute once
      the sub-command terminates.

Consequently, the semantics is presented as a transition relation between triples (sub-command under focus, continuation, state).

|*)

Inductive cont : Type :=
  | Kstop
  | Kseq (c: statements) (k: cont)
  | Kwhile (b: bexp) (c: statements) (k: cont).

Fixpoint statement_to_cont (c : statements) :=
  match c with
  | SEQ c1 c2 => Kseq c1 (statement_to_cont c2)
  | WHILE b c1 => Kwhile b c1 Kstop
  | c => Kseq c Kstop
  end.

Fixpoint cont_to_statement (k: cont) (c: statements) :=
  match k with
    | Kstop => c
    | Kseq c1 k1 => cont_to_statement k1 (SEQ c c1)
    | Kwhile b1 c1 k1 => cont_to_statement k1 (SEQ c (WHILE b1 c1))
  end.

Inductive step: statements * cont * thread_state ->
                statements * cont * thread_state -> Prop :=

  | step_seq: forall c1 c2 s k,               (**r focusing *)
      step (SEQ c1 c2, k, s) (c1, Kseq c2 k, s)

  | step_skip_seq: forall c k s,              (**r resumption *)
      step (SKIP, Kseq c k, s) (c, k, s)

  | step_comp: forall t k s,
      step (COMP t, k, s)
            (SKIP, k,
              (Update_CET s (COMP t)))

  | step_delay_until: forall k s ,
    step (DELAY_UNTIL_NEXT_PERIOD, k, s)
          (SKIP, k,
            (Set_Next_Dispatch_Time s))

  | step_po_function: forall c1 c2 k s ,
    step (PO_FUNCTION c1 c2, k, s)
        (SKIP, k, (Update_CET s (PO_FUNCTION c1 c2)))

  | step_po_entry: forall c1 c2 k s ,
    step (PO_ENTRY c1 c2, k, s)
          (SKIP, k, (Update_CET s (PO_ENTRY c1 c2)))

  | step_ifthenelse: forall b c1 c2 k s,
      step (IFTHENELSE b c1 c2, k, s) ((if beval b then c1 else c2), k, s)

  | step_while_done: forall b c k s,
    beval b = false ->
      step (WHILE b c, k, s) (SKIP, k, s)

  | step_while_loop: forall b c k s,
    beval b = true ->
      step (WHILE b c, k, s) (c, Kwhile b c k, s).

(*|
Equivalence between the continuation semantics and the reduction semantics
--------------------------------------------------------------------------
|*)

Inductive match_conf : statements * cont * thread_state -> statements * thread_state -> Prop :=
  | match_conf_intro: forall c k s c',
      c' = cont_to_statement k c ->
      match_conf (c, k, s) (c', s).

(*| We show that every transition of the continuation semantics
    is simulated by zero, one or several reduction steps.
    The anti-stuttering measure counts the nesting of [SEQ] constructs
    in the command. |*)

Fixpoint num_seq (c: statements) : nat :=
  match c with
  | SEQ c1 c2 => S (num_seq c1)
  | _ => O
  end.

Definition kmeasure (C: statements * cont * thread_state ) : nat :=
  let '(c, k, s) := C in num_seq c.

Remark red_cont_to_statement:
  forall k c1 s1 c2 s2,
  red (c1, s1) (c2, s2) ->
  red (cont_to_statement k c1, s1) (cont_to_statement k c2, s2).
Proof.
  induction k; intros; simpl; eauto using red_seq_step.
Qed.

Lemma simulation_cont_red:
  forall C1 C1', step C1 C1' ->
  forall C2, match_conf C1 C2 ->
  exists C2',
     (clos_refl_trans_1n_plus _ red C2 C2' \/
     (clos_refl_trans_1n _ red C2 C2' /\ kmeasure C1' < kmeasure C1))%nat
  /\ match_conf C1' C2'.
  Proof.
    destruct 1; intros C2 MC; inversion MC; subst; cbn.
    1: econstructor; split; [right; split; [apply rt1n_refl | lia] | constructor; auto ].

    all: econstructor; split; [left; apply clos_refl_trans_1n_plus_one; apply red_cont_to_statement; auto using red | constructor; auto].
Qed.

Inductive red_cont_to_statement_cases:
  cont -> statements -> thread_state -> statements -> thread_state -> Prop :=
  | racc_base: forall c1 s1 c2 s2 k,
    red (c1, s1) (c2, s2) ->
    red_cont_to_statement_cases k c1 s1 (cont_to_statement k c2) s2
  | racc_skip_seq: forall c k s,
    red_cont_to_statement_cases (Kseq c k) SKIP s (cont_to_statement k c) s
  | racc_skip_while: forall b c k s,
  red_cont_to_statement_cases (Kwhile b c k) SKIP s (cont_to_statement k (WHILE b c)) s.

Lemma invert_red_cont_to_statement:
  forall k c s c' s',
    red (cont_to_statement k c, s) (c', s') ->
    red_cont_to_statement_cases k c s c' s'.
Proof.
  induction k; simpl; intros.
  - (* Kstop *)
    change c' with (cont_to_statement Kstop c'). apply racc_base ; auto.
  - (* Kseq *)
    specialize (IHk _ _ _ _ H). inversion IHk; subst.
    + (* base *)
    inversion H0; clear H0; subst.
      * (* seq finish *)
        apply racc_skip_seq.
      * (* seq step *)
        change (cont_to_statement k (c4;;c)) with (cont_to_statement (Kseq c k) c4).
        apply racc_base; auto.

  - (* KWhile *)
  specialize (IHk _ _ _ _ H). inversion IHk; subst.
  inversion H0; clear H0; subst.
    * (* seq finish *)
      apply racc_skip_while.
    * (* seq step *)
      change (cont_to_statement k (c4;;WHILE b c)) with (cont_to_statement(Kwhile b c k) c4).
      apply racc_base; auto.
Qed.

(*|
Simulation in the continuation style
------------------------------------
|*)

Definition Initial_thread_state (p : Time):=
  {| th_state := READY ;
     th_period := p ;
     th_cet := 0 ;
     th_next_dispatch := 0 |}.

Example Test_Program_1 := COMP 1 ;; SKIP ;; COMP 2 ;; SKIP ;; COMP 3.

Fixpoint Eval_cont' (fuel : nat) (st :thread_state) (k : cont)
  : thread_state * cont
:=
  match fuel with
  | 0 => (st, k)
  | S n =>
    match k with
    | Kstop => (st, Kstop)

    | Kseq s' k' =>
      match Eval n st s' with
      | (st', false) => (st, k)
      | (st', true) => Eval_cont' n st' k'
      end

    | Kwhile b s' k' =>
      if beval b then
          match Eval n st s' with
          | (st', false) => (st, (Kseq s' (Kwhile b s' k')))
          | (st', true) => Eval_cont' n st' (Kwhile b s' k')
          end
      else (st, Kstop)
    end
end.

Compute Eval_cont' 10 Dummy_thread_state
  (statement_to_cont Ravenscar_Cyclic_Program).

(*| :coq:`Eval_cont'_end` shows that if :coq:`Eval_cont'` converges to some value, then :coq:`fuel > 0`. |*)

Lemma Eval_cont'_end: forall k st x fuel, k <> Kstop ->
  Eval_cont' fuel st k = (x, Kstop) -> fuel > 0.
Proof.
  induction fuel as [ | fuel ].
  - simpl. intros H H0. inversion H0. contradiction.
  - auto with *.
Qed.

Lemma Eval_cont'_end': forall fuel k st x ,
  Eval_cont' fuel st k = (x, Kstop) ->
    Eval_cont' (S fuel) st k = (x, Kstop).
Proof.
  intro fuel.
  induction fuel.
  - intros. simpl in *. inversion H. trivial.
  - destruct k.
    + (* Kstop *)
      intuition.

    + (* Kseq *)
      intros. simpl in H.

      assert (H0: exists st', Eval fuel st c = (st', true)).
      destruct (Eval fuel st c).
      exists t ; trivial.
      destruct b. trivial. inversion H.

      destruct H0 as (st', H0).
      rewrite H0 in H.

      assert (H1: Eval_cont' (S (S fuel)) st (Kseq c k) =
        match Eval (S fuel) st c with
          | (st', false) => (st, (Kseq c k))
          | (st', true) => Eval_cont' (S fuel) st' k
        end).
      reflexivity.

      assert (H2: Eval (S fuel) st c = (st', true)).
      apply Eval_end_fix. apply H0.

      rewrite H2 in H1.

      assert (H3: Eval_cont' (S fuel) st' k = (x, Kstop)).
      apply IHfuel. apply H.

      rewrite H3 in H1. trivial.

    + (* Kwhile *)
      intros. simpl in H.

      assert (H0: Eval_cont' (S (S fuel)) st (Kwhile b c k) =
        if beval b
        then
        match Eval (S fuel) st c with
        | (st', false) => (st, (Kseq c (Kwhile b c k)))
        | (st', true) => Eval_cont' (S fuel) st' (Kwhile b c k)
  end
        else (st, Kstop)
      ). reflexivity.

      destruct (beval b) eqn:Hbeval.

      * assert (H1: exists st', Eval fuel st c = (st', true)).
        destruct (Eval fuel st c).
        exists t ; trivial.
        inversion H.
        destruct b0. trivial. inversion H2.


        destruct H1 as (st', H1).
        rewrite H1 in H.

        assert (H2: Eval (S fuel) st c = (st', true)).
        apply Eval_end_fix. apply H1.
        rewrite H2 in H0.

        assert (Eval_cont' (S fuel) st' (Kwhile b c k) = (x, Kstop)).
        apply IHfuel. apply H.
        rewrite H3 in H0. trivial.

      * rewrite H in H0. trivial.
Qed.

Lemma Eval_cont'_Kstop: forall fuel st ,
  fuel > 0 -> Eval_cont' fuel st Kstop = (st, Kstop).
Proof.
  intros.
  assert (exists n, fuel = S n).
  apply zero_or_succ_positive, H.
  destruct H0 as (n, H0).
  subst.
  simpl.
  reflexivity.
Qed.

Lemma statement_to_cont_no_Kstop:
  forall s, (exists s' k', statement_to_cont s = Kseq s' k') \/
    (exists b s' k', statement_to_cont s = Kwhile b s' k').
Proof.
  intros.
  induction s ; simpl.
  1-6,8: left ; eexists ; eexists ; trivial.
  right. exists b; exists s; exists Kstop ; trivial.
Qed.

Lemma statement_to_cont_no_Kstop':
  forall s, statement_to_cont s <> Kstop.
Proof.
  intros.
  induction s ; discriminate.
Qed.

Lemma Eval_cont'_Eval_OK: forall fuel s st x,
  Eval_cont' fuel st (statement_to_cont s) = (x, Kstop)
  -> Eval fuel st s = (x, true).
Proof.
  (* This proof is technical but not that complex.
      We perform a double induction on fuel and s (statements). *)

  intro fuel.
  induction fuel.

- (* fuel = 0 *)
  intros. simpl.

  (* We have an apparent contradiction in H, that we leverage to
    complete the proof. *)
  inversion H. subst.
  assert (statement_to_cont s <> Kstop).
  apply statement_to_cont_no_Kstop'. contradiction.

- (* S fuel *)
  intro s.
  induction s.

  + (* s = COMP *)
    intros.

    (* Intermediate result #1 *)
    assert (H1: exists st', Eval fuel st (COMP WCET) = (st', true)).
    destruct (Eval fuel st (COMP WCET)) eqn:H2.
    simpl in H. rewrite H2 in H. exists t.
    destruct b. trivial. inversion H.

    destruct H1 as (st', H1).

    (* Intermediate result #2 *)
    assert (H2: Eval_cont' fuel st' Kstop  = (st', Kstop)).
    destruct fuel; simpl ; trivial.

    (* We now show that st' = x *)
    assert (H3: st' = x).
    simpl in H. rewrite H1 in H.
    rewrite H2 in H. inversion H. trivial.

    subst.
    apply Eval_end_fix. trivial.

  + (* s = PO_FUNCTION po op *)
    intros.

    (* Intermediate result #1 *)
    assert (H1: exists st',
      Eval fuel st (PO_FUNCTION po op) = (st', true)).
    destruct (Eval fuel st (PO_FUNCTION po op)) eqn:H2.
    simpl in H. rewrite H2 in H. exists t.
    destruct b. trivial. inversion H.

    destruct H1 as (st', H1).

    (* Intermediate result #2 *)
    assert (H2: Eval_cont' fuel st' Kstop  = (st', Kstop)).
    destruct fuel; simpl ; trivial.

    (* We now show that st' = x *)
    assert (H3: st' = x).
    simpl in H. rewrite H1 in H.
    rewrite H2 in H. inversion H. trivial.

    subst.
    apply Eval_end_fix. trivial.

  + (* s = PO_ENTRY po op *)
    intros.

    (* Intermediate result #1 *)
    assert (H1: exists st',
      Eval fuel st (PO_ENTRY po op) = (st', true)).
    destruct (Eval fuel st (PO_ENTRY po op)) eqn:H2.
    simpl in H. rewrite H2 in H. exists t.
    destruct b. trivial. inversion H.

    destruct H1 as (st', H1).

    (* Intermediate result #2 *)
    assert (H2: Eval_cont' fuel st' Kstop  = (st', Kstop)).
    destruct fuel; simpl ; trivial.

    (* We now show that st' = x *)
    assert (H3: st' = x).
    simpl in H. rewrite H1 in H.
    rewrite H2 in H. inversion H. trivial.

    subst.
    apply Eval_end_fix. trivial.

  + (* s = DELAY_UNTIL_NEXT_PERIOD *)
    intros.

    (* Intermediate result #1 *)
    assert (H1: exists st',
      Eval fuel st DELAY_UNTIL_NEXT_PERIOD = (st', true)).
    destruct (Eval fuel st DELAY_UNTIL_NEXT_PERIOD) eqn:H2.
    simpl in H. rewrite H2 in H. exists t.
    destruct b. trivial. inversion H.

    destruct H1 as (st', H1).

    (* Intermediate result #2 *)
    assert (H2: Eval_cont' fuel st' Kstop  = (st', Kstop)).
    destruct fuel; simpl ; trivial.

    (* We now show that st' = x *)
    assert (H3: st' = x).
    simpl in H. rewrite H1 in H.
    rewrite H2 in H. inversion H. trivial.

    subst.
    apply Eval_end_fix. trivial.

  + (* s = s1 ;; s2 *)
    intros. simpl in H. simpl.

    assert (H1: exists st',  Eval fuel st s1 = (st', true)).
    destruct (Eval fuel st s1) eqn:H2.
    exists t. destruct b. trivial. inversion H.

    destruct H1 as (st', H1).
    rewrite H1 in H.
    rewrite H1.

    eapply IHfuel. apply H.

  + (* s = IFTHENELSE b s1 s2 *)
    intros. simpl in H. simpl.

    assert (H1: exists st',  Eval fuel st (IFTHENELSE b s1 s2) = (st', true)).
    destruct (Eval fuel st (IFTHENELSE b s1 s2)).
    destruct b0. exists t. trivial. inversion H.

    destruct H1 as (st', H1).
    rewrite H1 in H.

    assert (Hfuel: fuel > 0).
    eapply Eval_end. apply H1.

    assert (Hn: exists n, fuel = S n).
    apply zero_or_succ_positive, Hfuel.

    destruct Hn as (n, Hn).
    subst. simpl in H1.

    assert (st' = x).
    simpl in H. inversion H. trivial.
    subst.
    apply Eval_end_fix. trivial.

  + (* s = WHILE b s *)
    intros.
    simpl in H. simpl.
    destruct (beval b) eqn:beval.

    * (* beval b = true *)

      assert (H1: exists st',  Eval fuel st s = (st', true)).
      destruct (Eval fuel st s) eqn:H2.
      exists t. destruct b0. trivial. inversion H.

      destruct H1 as (st', H1).
      rewrite H1 in H.
      rewrite H1.

      apply IHfuel.

      assert (H2: statement_to_cont (WHILE b s) = Kwhile b s Kstop).
      trivial.
      rewrite H2.
      apply H.

    * (* beval b = false *)
      inversion H. trivial.

  +(* s = SKIP *)
    intros.

    (* Intermediate result #1 *)
    assert (H1: exists st', Eval fuel st (SKIP) = (st', true)).
    destruct (Eval fuel st (SKIP)) eqn:H2.
    simpl in H. rewrite H2 in H. exists t.
    destruct b. trivial. inversion H.

    destruct H1 as (st', H1).

    (* Intermediate result #2 *)
    assert (H2: Eval_cont' fuel st' Kstop  = (st', Kstop)).
    destruct fuel; simpl ; trivial.

    (* We now show that st' = x *)
    assert (H3: st' = x).
    simpl in H. rewrite H1 in H.
    rewrite H2 in H. inversion H. trivial.

    subst.
    apply Eval_end_fix. trivial.

Qed.

Lemma Eval_Eval_cont'_OK: forall fuel s st x,
  (Eval fuel st s = (x, true) ->
    Eval_cont' fuel st (statement_to_cont s) = (x, Kstop))
\/
  (Eval fuel st s = (x, false) ->
    Eval_cont' fuel st (statement_to_cont s) <> (x, Kstop)).
Proof.
  intro fuel.
  induction fuel.
  - (* fuel = 0 *)
    intros. simpl. right. intros. inversion H.

    assert (H0: statement_to_cont s <> Kstop).
    apply statement_to_cont_no_Kstop'.

    rewrite pair_equal_spec. firstorder.

  - (* S fuel *)
    intro s. induction s.

    + (* s = COMP WCET *)
      pose (s':= COMP WCET).

      intros. simpl.
      destruct (Eval fuel st s') eqn:Hs.
      destruct b.

      * (* b = true *)
        left.

        assert (Hfuel: fuel > 0).
        apply Eval_end with (st := st) (s := s') (st' := t).
        apply Hs.

        assert (Hn: exists n, fuel = S n).
        apply zero_or_succ_positive, Hfuel.
        destruct Hn as (n, Hn).

        subst.
        simpl.
        repeat rewrite pair_equal_spec. firstorder.

      * (* b = false *)
        right. intros. inversion H.


    + (* s = PO_FUNCTION po op*)
      pose (s':= PO_FUNCTION po op).

      intros. simpl.
      destruct (Eval fuel st s') eqn:Hs.
      destruct b.

      * (* b = true *)
        left.

        assert (Hfuel: fuel > 0).
        apply Eval_end with (st := st) (s := s') (st' := t).
        apply Hs.

        assert (Hn: exists n, fuel = S n).
        apply zero_or_succ_positive, Hfuel.
        destruct Hn as (n, Hn).

        subst.
        simpl.
        repeat rewrite pair_equal_spec. firstorder.

      * (* b = false *)
        right. intros. inversion H.

    + (* s = PO_ENTRY po op*)
      pose (s':= PO_ENTRY po op).

      intros. simpl.
      destruct (Eval fuel st s') eqn:Hs.
      destruct b.

      * (* b = true *)
        left.

        assert (Hfuel: fuel > 0).
        apply Eval_end with (st := st) (s := s') (st' := t).
        apply Hs.

        assert (Hn: exists n, fuel = S n).
        apply zero_or_succ_positive, Hfuel.
        destruct Hn as (n, Hn).

        subst.
        simpl.
        repeat rewrite pair_equal_spec. firstorder.

      * (* b = false *)
        right. intros. inversion H.

    + (* s = DELAY_UNTIL_NEXT_PERIOD*)
      pose (s':= DELAY_UNTIL_NEXT_PERIOD).

      intros. simpl.
      destruct (Eval fuel st s') eqn:Hs.
      destruct b.

      * (* b = true *)
        left.

        assert (Hfuel: fuel > 0).
        apply Eval_end with (st := st) (s := s') (st' := t).
        apply Hs.

        assert (Hn: exists n, fuel = S n).
        apply zero_or_succ_positive, Hfuel.
        destruct Hn as (n, Hn).

        subst.
        simpl.
        repeat rewrite pair_equal_spec. firstorder.

      * (* b = false *)
        right. intros. inversion H.

    + (* s = s1 ;; s2 *)
      intros. simpl.
      destruct (Eval fuel st s1) eqn:Hs1.
      destruct b.

      * apply IHfuel.
      * right. intros. rewrite pair_equal_spec. intuition. inversion H2.

    + (* s = IFTHENELSE b s1 s2 *)
      intros. simpl.
      destruct (Eval fuel st (IFTHENELSE b s1 s2)) eqn:hh.
      destruct b0.

      * (* b = true *)
        left.
        intros.
        assert (Hfuel: fuel > 0).
        eapply Eval_end. apply H.

        assert (Hn: exists n, fuel = S n).
        apply zero_or_succ_positive, Hfuel.
        destruct Hn as (n, Hn).

        subst.
        simpl.
        simpl in hh.
        apply Eval_end_fix in hh.
        rewrite H in hh.
        inversion hh.
        intuition.

      * (* b = false *)
        right.
        intros.
        intuition. inversion H0.

    + (* s = WHILE b s *)
      intros. simpl.
      destruct (beval b) eqn:beval.
      destruct (Eval fuel st s) eqn:Hs.
      destruct b0.
      * apply IHfuel.
      * right. intros. rewrite pair_equal_spec. intuition. inversion H2.
      * left. intros. inversion H. trivial.

    + (* S = SKIP *)

    pose (s':= SKIP).

    intros. simpl.
    destruct (Eval fuel st s') eqn:Hs.
    destruct b.

    * (* b = true *)
      left.

      assert (Hfuel: fuel > 0).
      apply Eval_end with (st := st) (s := s') (st' := t).
      apply Hs.

      assert (Hn: exists n, fuel = S n).
      apply zero_or_succ_positive, Hfuel.
      destruct Hn as (n, Hn).

      subst.
      simpl.
      repeat rewrite pair_equal_spec. firstorder.

    * (* b = false *)
      right. intros. inversion H.
Qed.

Fixpoint Trace_Eval_Cont''
  (n : nat)
  (st_k : (thread_state * cont))
  (l : list (thread_state * cont))
  : list (thread_state * cont)
:=
  match n with
  | 0 => l
  | S n' =>
  let (st, k) := st_k in
    let x := Eval_cont' 1 st k in
      match x with
        | (st', Kstop) => l ++ [(st', Kstop)]
        | (st', k') =>
          Trace_Eval_Cont'' n' (st', k') (l ++ [(st', k')])
      end
  end.

Fact Run_Test_Program_0_OK' :
  Eval_cont' 10 (Initial_thread_state 0) (statement_to_cont Test_Program_1) =
  ({| th_state := READY; th_period := 0 ; th_cet := 6 ; th_next_dispatch := 0 |}, Kstop).
Proof. trivial. Qed.

Compute Eval_cont' 3 (Initial_thread_state 0) (statement_to_cont Test_Program_1).

Compute Trace_Eval_Cont'' 10
  ((Initial_thread_state 0), (statement_to_cont Test_Program_1)) [].


(*|
Simulation of Ravenscar tasksets
================================

|*)

Inductive task_instance :=
| task_i: identifier -> priority -> thread_state -> cont -> task_instance.
Scheme Equality for task_instance.

Definition Map_Task_to_Task_Instance (t : task) :=
  match t with
  | Task kind ident priority period statements =>
    task_i ident priority (Initial_thread_state period) (statement_to_cont statements)
  end.

Definition Idle_task_Instance := Map_Task_to_Task_Instance IDLE_TASK.
Compute Idle_task_Instance.

Definition get_id (i : task_instance) :=
  match i with
  | task_i id _ _ _ => id
  end.

Definition get_priority (i : task_instance) : nat :=
  match i with
  | task_i _ priority _ _ => priority
  end.
Definition get_task_state (i : task_instance) :=
  match i with
  | task_i _ _ st _ => st.(th_state)
  end.

Definition get_thread_state_and_cont (i : task_instance) :=
  match i with
  | task_i _ _ st k => (st, k)
  end.

Definition get_thread_state (i : task_instance) :=
  match i with
  | task_i _ _ st _ => st
  end.

Definition get_continuation (i : task_instance) :=
  match i with
  | task_i _ _ _ k => k
  end.

Definition reset_cet (i : task_instance) :=
  match i with
  | task_i id p st k => task_i id p (reset_thread_cet st) k
  end.

Definition Simulate_Task (i : task_instance) (fuel : nat) : task_instance :=
  let (st, k) := Eval_cont' fuel (get_thread_state i) (get_continuation i) in
  match (st, k) with
  | (st, Kstop) =>
      task_i (get_id i) (get_priority i) (set_thread_state st IDLE) k
  | (st, k) => task_i (get_id i) (get_priority i) st k

  end.

Definition max_prio_thread (i1 i2: task_instance) :=
  if (negb (task_state_beq (get_task_state i1) READY)) &&
     (negb (task_state_beq (get_task_state i2) READY))
  then Idle_task_Instance

  else if (task_state_beq (get_task_state i1) READY) &&
          (negb (task_state_beq (get_task_state i2) READY))
  then i1

  else if (negb (task_state_beq (get_task_state i1) READY)) &&
          (task_state_beq (get_task_state i2) READY)
  then i2

  else if Nat.leb (get_priority i2) (get_priority i1)
  then i1

  else i2.

Definition get_thread_by_priority (l : list task_instance) :=
  match l with
  | [] => Idle_task_Instance
  | h :: t => fold_left (fun acc x => max_prio_thread acc x) l h
  end.

Definition get_next_dispatch_time_i (i : task_instance) :=
  th_next_dispatch (get_thread_state i).

Definition get_next_dispatch_time_l (l : list task_instance) :=
  list_min (map (fun x => get_next_dispatch_time_i x) l).

Definition update_thread_state_at_time (i : task_instance) (t : Time) :=
  match i with
  | task_i id p st k =>
    if (PeanoNat.Nat.eqb (th_next_dispatch st) t) then
      task_i id p (set_thread_state st READY) k
    else
      i
  end.

Definition update_all_thread_state_at_time
  (l : list task_instance)
  (t : Time)
:=
  map (fun x => update_thread_state_at_time x t) l.

Fixpoint replace_task_instance (i : task_instance) (l : list task_instance) :=
  match l with
  | [] => []
  | h :: t => if (identifier_beq (get_id i) (get_id h))
              then i :: t
              else h :: (replace_task_instance i t)
  end.

(*|
System
-------
|*)

Record ravenscar_system := {
  clock : Time ;
  taskset : list task_instance ;
}.

(*|

:coq:`Simulate_Ravenscar_Monocore` simulate a Ravenscar system, for the mono core case. It proceeds in a basic sequence of actions to

* elect the next thread to be executed
* run this thread
* from the state of the thread, increase the global clock by the thread cet
* reset the cet of the thread
* update the task set.

|*)

Definition Simulate_Ravenscar_Monocore (s : ravenscar_system) (fuel : nat) :=
  let l := taskset s in
  let elected_thread := get_thread_by_priority l in

  if (negb (task_instance_beq Idle_task_Instance elected_thread)) then
    let executed_thread := Simulate_Task elected_thread fuel in
    let time_advance := th_cet (get_thread_state executed_thread) in
    let executed_thread' := reset_cet executed_thread in {|
      clock := (clock s) + time_advance;
      taskset := replace_task_instance executed_thread' l;
    |}
  else
    let next_dispatch := get_next_dispatch_time_l l in {|
      clock := next_dispatch ;
      taskset := update_all_thread_state_at_time l next_dispatch;
    |}.

(*|
Examples
========

|*)

Unset Printing Records. (* condensed printing for records *)

Example A_PERIODIC_TASK_1 :=
  Task PERIODIC (Id "task_1") 1 10 Ravenscar_Cyclic_Program.

Example A_PERIODIC_TASK_2 :=
  Task PERIODIC (Id "task_2") 2 10 Ravenscar_Cyclic_Program.

Example TASK_1 := Map_Task_to_Task_Instance A_PERIODIC_TASK_1.
Example TASK_2 := Map_Task_to_Task_Instance A_PERIODIC_TASK_2.

Print Simulate_Task.

Compute Simulate_Task TASK_1 10.

Example system_1 := {|
  clock := 0;
  taskset := [TASK_1 ; TASK_2 ];
|}.

Example system_1_10 := Simulate_Ravenscar_Monocore system_1 10.
Compute system_1_10.

Example system_1_20 := Simulate_Ravenscar_Monocore system_1_10 20.
Compute system_1_20.

Example system_1_30 := Simulate_Ravenscar_Monocore system_1_20 30.
Compute system_1_30.

Example system_1_40 := Simulate_Ravenscar_Monocore system_1_30 30.
Compute system_1_40.

End Ravenscar.
