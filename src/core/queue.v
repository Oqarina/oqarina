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
(* From https://www.cs.cornell.edu/courses/cs4160/2020sp/sf/vfa/full/ADT.html

*)

Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListDec.
Require Import Oqarina.coq_utils.utils.

Module Type Queue.
  Parameter V : Type.
  Parameter Invalid_Value : V.
  Parameter queue : Type.
  Parameter empty: queue.
  Parameter is_empty : queue -> bool.
  Parameter enq : queue -> V -> queue.
  Parameter deq : queue -> queue.
  Parameter peek : queue -> V.
  Parameter count: queue -> nat.
  Axiom is_empty_empty : is_empty empty = true.
  Axiom is_empty_nonempty : forall q v, is_empty (enq q v) = false.
  Axiom peek_empty : peek empty = Invalid_Value.
  Axiom deq_empty : deq empty = empty.
End Queue.

Module Type ValType.
  Parameter V : Type.
  Parameter Invalid_Value : V.
End ValType.

Module ListQueue (VT : ValType) <: Queue.

  Definition V := VT.V.
  Definition Invalid_Value := VT.Invalid_Value.
  Definition key := nat.

  Definition queue := list V.
  Definition empty : queue := nil.

  Definition is_empty (q : queue) : bool :=
    match q with
    | nil => true
    | _ :: _ => false
    end.

  Definition Is_Empty (q : queue) : Prop :=
    match q with
    | nil => True
    | _ => False
    end.

  (** It is tempting to define [Is_Empty] as
    [[
      Definition Is_Empty (q : queue) : Prop := q = empty.
    ]]

    but this obfuscates the evaluation procedure. This style seems preferable. *)

  Lemma Is_Empty_dec : forall q, { Is_Empty q } + { ~ Is_Empty q }.
  Proof.
    unfold Is_Empty.
    induction q; auto.
  Defined.

  Definition enq (q : queue) (v : V) : queue :=  q ++ [v].

  Definition deq (q : queue) : queue :=
    match q with
    | x :: q' => q'
    | [] => []
    end.

  Definition peek (q : queue) : V :=
      match q with
      | x :: q' => x
      | [ ] => Invalid_Value
      end.

  Definition count (q: queue) : nat :=
    length q.

  Theorem is_empty_empty : is_empty empty = true.
  Proof.
    unfold is_empty.
    unfold empty.
    auto.
  Qed.

  Theorem is_empty_nonempty : forall q v,
      is_empty (enq q v) = false.
  Proof.
    intros.
    unfold enq.
    unfold is_empty.
    induction q ; auto.
  Qed.

  Theorem peek_empty : peek empty = Invalid_Value.
  Proof.
    auto.
  Qed.

 Theorem deq_empty :
    deq empty = empty.
  Proof.
      auto.
  Qed.

End ListQueue.
