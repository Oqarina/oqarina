(* From https://www.cs.cornell.edu/courses/cs4160/2020sp/sf/vfa/full/ADT.html

*)

Require Import List.
Import ListNotations. (* from List *)

Module Type Queue.
  Parameter V : Type.
  Parameter queue : Type.
  Parameter empty: queue.
  Parameter is_empty : queue -> bool.
  Parameter enq : queue -> V -> queue.
  Parameter deq : queue -> queue.
  Parameter peek : V -> queue -> V.
  Axiom is_empty_empty : is_empty empty = true.
  Axiom is_empty_nonempty : forall q v, is_empty (enq q v) = false.
  Axiom peek_empty : forall d, peek d empty = d.
  Axiom peek_nonempty : forall d q v, peek d (enq q v) = v.
  Axiom deq_empty : deq empty = empty.
  Axiom deq_nonempty : forall q v, deq (enq q v) = q.
End Queue.

Module ListQueue <: Queue.
  Definition V := nat. (* for simplicity *)
  Definition queue := list V.
  Definition empty : queue := nil.

  Definition is_empty (q : queue) : bool :=
    match q with
    | nil => true
    | _ :: _ => false
    end.

  Definition enq (q : queue) (v : V) : queue :=  v :: q.

  Definition deq (q : queue) : queue :=
    match q with
    | x :: q' => q'
    | [] => []
    end.

  Definition peek (default : V) (q : queue) : V :=
      match q with
      | x :: q' => x
      | [ ] => default
      end.

  Theorem is_empty_empty : is_empty empty = true.
  Proof.
    unfold is_empty.
    unfold empty.
    auto.
  Qed.

  Theorem is_empty_nonempty : forall q v,
      is_empty (enq q v) = false.
  Proof.
    unfold enq.
    intros.
    unfold is_empty.
    auto.
  Qed.

  Theorem peek_empty : forall d,
      peek d empty = d.
  Proof.
    auto.
  Qed.

  Theorem peek_nonempty : forall d q v,
      peek d (enq q v) = v.
  Proof.
      intros. simpl. auto.
  Qed.

 Theorem deq_empty :
    deq empty = empty.
  Proof.
      auto.
  Qed.

  Theorem deq_nonempty : forall q v,
      deq (enq q v) = q.
  Proof.
    intros. simpl. auto.
  Qed.

End ListQueue.
