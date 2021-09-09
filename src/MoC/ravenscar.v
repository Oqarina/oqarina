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
(**
In this module, we provide a formalization of the Ravenscar Ada profile.
It follows the formalization proposed in

Irfan Hamid, Elie Najm:
Operational Semantics of Ada Ravenscar. Ada-Europe 2008: 44-58
https://doi.org/10.1007/978-3-540-68624-8_4

Nice readings

Yves Bertot. Theorem proving support in programming language semantics.
[Research Report] RR- 6242, INRIA. 2007, pp.23. inria-00160309v2

Yves Bertot. Semantics for programming languages with Coq encodings:
First part: natural semantics. Master. France. 2015. cel-01130272

*)

Set Implicit Arguments.
Require Import Coq.Init.Datatypes.
Require Import Oqarina.core.identifiers.
Require Import List.
Import ListNotations. (* from List *)

(** A %\coqdocvar{seq_program}% denotes a sequence of code
statements. By definition, it should not hold any calls to concurrent
API. *)

Definition seq_program := Set.

Definition Simple_Program : seq_program := Empty_set.

(** priority concept. *)

Definition priority := nat.

(** time concept. *)

Definition time := nat.

(**

An Ada protected object is similar to a Hoard monitor or a Java Synchronized inteface:
it is a collection of protected operations. There are four categories:

– PO_Set: sets a value to a protected object PO,
i.e. calling a protected operation in write mode through a procedure
– PO_Get: gets a value to a protecte object PO, i.e. calling a protected operation in write mode through
a procedure (write lock) or a function (read lock)
– PO_Send: call a procedure of a PO that ultimately impacts guards on entries for this PO.
– PO_Wait: block on an entry of this PO. Event(D): A Get Event call to synchroniser D

*)

Inductive protected_operation :=
| PO_Get : identifier -> seq_program -> protected_operation
| PO_Set : identifier -> seq_program -> protected_operation
| PO_Send : identifier -> seq_program -> protected_operation
| PO_Wait : identifier -> seq_program -> protected_operation.

Inductive protected_object :=
| Protected_Object : identifier -> priority -> list protected_operation -> protected_object.

Definition A_PO :=
  Protected_Object (Id "A_PO") 42
    [ (PO_Get (Id "get") Simple_Program ) ;
      (PO_Set (Id "set") Simple_Program)].

(**
    A Ravenscar profile is reduced to a set of basic statements: XXX

    *)

Inductive statements : Type :=
| COMP                                        (* A sequential execution step *)
| PO_GET (po : identifier) (op : identifier)  (* Operations on protected objects *)
| PO_SET (po : identifier) (op : identifier)
| PO_SEND (po : identifier) (op : identifier)
| PO_WAIT (po : identifier) (op : identifier)
| DELAY_UNTIL (t : nat)                       (* delay until some time *)
| SEQ (s1: statements) (s2: statements)       (* Sequence of statements *)
| RET.

Infix ";;" := SEQ (at level 80, right associativity).

Definition A_Program := COMP ;; RET.
Definition Ravenscar_Cyclic_Program := COMP ;;
                                       PO_GET (Id "A_PO") (Id "get") ;;
                                       DELAY_UNTIL 10.

(** A legal periodic body (PB) has the form
    PB := comp; PB | Set( _ ); PB | Get( _ ); PB | Send Event( _ ); PB | delay until *)

Fixpoint Legal_Periodic_Body (p : statements)  :=
  match p with
  (* DELAY_UNTIL is the last statement *)
  | COMP => False | PO_GET _ _ => False | PO_SET _ _ => False
  | PO_SEND _ _ => False | PO_WAIT _ _ => False | RET => False
  | DELAY_UNTIL _ => True

  (* COMP, PO_GET, PO_SET, and PO_SENT are accepted *)
  | COMP ;; s2 => Legal_Periodic_Body s2
  | PO_GET _ _ ;; s2 => Legal_Periodic_Body s2
  | PO_SET _ _ ;; s2 => Legal_Periodic_Body s2
  | PO_SEND _ _ ;; s2 => Legal_Periodic_Body s2
  (* PO_WAIT and RET are rejected *)
  | PO_WAIT _ _ ;; _ => False
  | RET ;; _ => False
  (* DELAY_UNTIL cannot be in a sequence *)
  | DELAY_UNTIL  _ ;; _ => False

  (* Iteration *)
  | (s1 ;; s2) ;; s3 => Legal_Periodic_Body s1 /\ Legal_Periodic_Body s2
                        /\ Legal_Periodic_Body s3
  end.

(**

A legal Sporadic Body has the form
    SB := Get Event ; PB

*)

Fixpoint Legal_Sporadic_Body (p : statements)  :=
  match p with
  (* PO_WAIT is the first statement *)
  | PO_WAIT _ _ ;; s2 => Legal_Periodic_Body s2

  (* because the precedent rule exits to execute Legal_Periodic_Bodym the other
     combination should be false *)
  | COMP ;; _ => False | PO_GET _ _ ;; _ => False | PO_SET _ _ ;; _ => False
  | PO_SEND _ _ ;; _ => False | RET ;; _ => False
  | DELAY_UNTIL _ ;; _ => False

  | COMP => False | PO_GET _ _ => False | PO_SET _ _ => False
  | PO_SEND _ _ => False | PO_WAIT _ _ => True | RET => False
  | DELAY_UNTIL _ => False

  (* Iteration *)
  | (s1 ;; s2) ;; s3 => Legal_Sporadic_Body s1 /\ Legal_Periodic_Body s2
                        /\ Legal_Periodic_Body s3
  end.

(**

An Ada task under the Ravenscar profile is uniquely defined by the tuple
%(priority, period, WCET)%

*)

Inductive task_kind :=
| PERIODIC | SPORADIC | ISR.

Inductive task :=
| Task : task_kind ->
         identifier ->
         priority ->
         time -> (* period *)
         time -> (* WCET *)
         statements -> task.

Definition A_PERIODIC_TASK :=
  Task PERIODIC (Id "a_task") 42 10 1 Ravenscar_Cyclic_Program.

  (** XXX trivial checks on well-formedness possible here also ..*)

(**


*)

Inductive ravenscar_system :=
| Ravenscar : list task -> list protected_object -> ravenscar_system.

Definition A_RAVENSCAR_SYSTEM :=
    Ravenscar [ A_PERIODIC_TASK ]
              [ A_PO ].

Definition po_state : Type := identifier -> nat.

Inductive red : statements * nat -> statements * nat -> Prop :=
| red_seq_comp: forall c s,
    red (SEQ COMP c, s) (c, S s)
| red_seq_step: forall c1 c s1 c2 s2,
    red (c1, s1) (c2, s2) ->
    red (SEQ c1 c, s1) (SEQ c2 c, s2)
| red_seq_done: forall c s,
    red (SEQ RET c, s) (c, s)
    .

Lemma red_determ:
    forall cs cs1, red cs cs1 -> forall cs2, red cs cs2 -> cs1 = cs2.
Proof.
    induction 1; intros cs2 R2; inversion R2; subst; eauto.
    - inversion H3.
    - inversion H.
    - assert (EQ: (c2, s2) = (c4, s3)) by auto. congruence.
    - inversion H.
    - inversion H3.
Qed.



