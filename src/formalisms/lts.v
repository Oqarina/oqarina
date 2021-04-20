(** %\chapter{Labelled Transitionsition System (LTS)}\label{chap::lts}%

  This definition follows the canonical definition of a LTS, see %\cite{gorrieriLabeledTransitionSystems2017a}%

*)

(* begin hide *)
Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

(** * Definition of LTS *)

Definition LTS_Transitions (S : Type) (A : Set) := S -> A -> S -> Prop.

(** We use Coq module to increase the modularity of this formalization.
  Ultimately, a LTS will be parameterized by States and Actions.

  Probably use a record instead XXXX

  *)

Module Type LTS_struct.
  Parameter State : Type.
  Parameter Init : State.
  Parameter Action : Set.
  Parameter Transitions : LTS_Transitions State Action.
End LTS_struct.

(** * Example *)

Inductive ab := A | B.

Inductive ab_state : Set := ReadA | ReadB | Fail.

Definition Some_Transitions
  (s1 : ab) (a: ab_state) (s2 : ab) : Prop
  :=
  match s1, a, s2 with
  | _, _, _ => True
  end.

Module LTS_Test <: LTS_struct.
  Definition State := ab.
  Definition Init := A.
  Definition Action := ab_state.
  Definition Transitions := Some_Transitions.
End LTS_Test.

Compute LTS_Test.Transitions A ReadA B.
