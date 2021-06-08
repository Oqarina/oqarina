(** %\chapter{Labelled Transitionsition System (LTS)}\label{chap::lts}%

In this chapter, we define Labelled Transition Systems (or LTS). This definition follows the canonical definition of a _deterministic_ LTS, see %\cite00{gorrieriLabeledTransitionSystems2017a}%. *)

(* begin hide *)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)

Section LTS_Definition.
(* end hide *)

(** * Definition of LTS

_Notes_:
- we opted for [bool] rather than [Prop] to allow for on-the-fly evaluation of the LTS.
- we define both a [LTS_Transition] predicate and a [LTS_Step] function. The step function allows building a simulator, whereas the transition function allows performing proof. We keep the definition of [LTS_Transition] but are likely to remove it ultimately.

*)

  Definition LTS_Transitions (S : Type) (A : Type) := S -> A -> S -> bool.

  Definition LTS_Step (S : Type) (A : Type) := S -> A -> S.

  Record LTS_struct : Type := mkLTS_struct  {
    States : Type;
    Init : States;
    Actions : Type;
    Steps : LTS_Step States Actions;
  }.

(** [step_lts] performs one step of the LTS. *)

  Definition step_lts
    (A_LTS : LTS_struct) (state: States A_LTS) (action : Actions A_LTS) :=
      (Steps A_LTS) state action.

(** See implementation in [lts.v] for example of use. *)

(* begin hide *)
End LTS_Definition.

(* The following could be added to the definition of a LTS *)
 (* Transitions : LTS_Transitions States Actions;

 XXX But this seems like an unnecessary definition
 *)

(*
Definition Transitions_Steps_Equivalent (A_LTS : LTS_struct) :=
  forall (state: States A_LTS) (action: Actions A_LTS),
  exists x: (States A_LTS), In x ((Steps A_LTS) state action) ->
    (Transitions A_LTS state action x) = true.

Definition step_lts_predicate
  (A_LTS : LTS_struct) (current_state : States A_LTS)
  (action : Actions A_LTS) (destination : States A_LTS) :=
    (Transitions A_LTS) current_state action destination.
*)

(** Example *)

Section Example.

Inductive ab : Set := A | B.
Inductive ab_actions : Set := ReadA | ReadB | Fail.

Definition AB_Transitions (s1 : ab) (a: ab_actions) (s2 : ab) : bool :=
    match s1, a, s2 with
    | A, _, B => true
    | B, _, A => true
    | _, _, _ => false
    end.

Definition AB_Steps (s1 : ab) (a: ab_actions) :=
  match s1, a  with
  | A, _ => B
  | B, _ => A
  end.

Definition LTS_Test : LTS_struct := {|
  States := ab;
  Init := A;
  Actions := ab_actions;
  (*Transitions := AB_Transitions; *)
  Steps := AB_Steps;
|}.

(*
Lemma e: Transitions_Steps_Equivalent LTS_Test.
Proof.
    unfold Transitions_Steps_Equivalent.
    intros.
    induction state.
    - now exists B.
    - now exists A.
Qed.
*)
Example f' := step_lts LTS_Test (Init LTS_Test) ReadA.
Lemma test : f' = B.
Proof.
  auto.
Qed.

End Example.
(* end hide *)
