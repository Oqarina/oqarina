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


(*
https://en.wikipedia.org/wiki/Monad_(functional_programming)

https://www.toptal.com/javascript/option-maybe-either-future-monads-js

https://github.com/vzaliva/helix/blob/master/coq/Util/ErrorSetoid.v

https://github.com/coq-community/coq-ext-lib/issues/79

https://github.com/mukeshtiwari/Dlog-zkp/blob/main/src/Distr.v#L148-L251

https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Monads.html

http://adam.chlipala.net/poplmark/compile/soln.html

https://en.wikipedia.org/wiki/Monad_transformer

https://hackmd.io/@alexhkurz/H1OxumxRP#A-Short-Introduction-to-Monads

https://gitlab.inria.fr/kmaillar/dijkstra-monads-for-all/-/blob/master/theories/sprop/DijkstraMonadExamples.v



*)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Oqarina.Configuration.

Set Implicit Arguments.
Set Strict Implicit.

Section Monads.

Class Monad (M : Type -> Type) := {
  ret  : forall {A : Type}, A -> M A ;
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B
}.

End Monads.

Module Monad_Notations.

Notation "x <- c1 ;; c2" :=
  (bind c1 (fun x => c2))
  (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" :=
  (bind c1 (fun _ => c2))
  (at level 100, right associativity).

End Monad_Notations.

Section Monad_Laws.

  Class MonadLaws m {M : Monad m} :=
  { bind_of_return : forall {A B} (a : A) (f : A -> m B),
      bind (ret a) f = f a
  ; return_of_bind : forall {A} (aM : m A),
      bind aM ret = aM
  ; bind_associativity :
      forall {A B C} (aM:m A) (f :A -> m B) (g:B -> m C),
        bind (bind aM f) g = bind aM (fun a => bind (f a) g)
  }.

End Monad_Laws.

Section Identity_Monad.

(*|
Identiy Monad
=============

The :coq:`IdentitynMonad` is the most basic monad, having no impact. It is used in those sit
|*)

#[global] Instance IdentitynMonad : Monad idmap := {
  ret  := fun {A:Type} (x: A) => x ;
  bind := fun {A B:Type} (x: A) (f: A -> B) => f x
}.

#[global] Instance IdentiyynMonadLaws: @MonadLaws idmap _.
Proof.
  split ; intuition.
Qed.

End Identity_Monad.

Section Option_Monad.

(*|
Option Monad
============

The :coq:`OptionMonad` wraps functions that may return an option
type, allowing to chain calls in a natural way without the boilerplate
code to check for :coq:`None`.

The :coq:`ret` function returns an option type, :coq:`bind` chains calls
if the parameter :coq:`x` is different from :coq:`None`, otherwise it
returns :coq:`None`.

|*)

#[global] Instance OptionMonad : Monad option := {
  ret  := fun {A:Type} (x:A) => Some x ;
  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with
              | None => None
              | Some y => f y
            end
}.

#[global] Instance OptionMonadLaws: @MonadLaws option _.
Proof.
  split.
  - intuition.
  - intros. destruct aM ; intuition.
  - intros. destruct aM ; intuition.
Qed.

End Option_Monad.

Section Option_Monad_Test.

Import Monad_Notations.

(*| In the following, we show how to use the
:coq:`OptionMonad`. We first define the context to use this
monad. Here, the :coq:`OptionMonad` is being brought in as a
consequence of the :coq:`s_add_option` function returning an option
type. |*)

Variable m : Type -> Type.
Context {Monad_m: Monad m}.

Definition s_add_option (n m: nat) : option nat :=
  match m with
  | 0 => None
  | _ => Some (n + m)
  end.

(*| A first basic test that shows how to use the monad. This
test is probably useless in that there is no chaining of
calls. It only illustrates the "syntax" of the notation. |*)

Lemma Option_Monad_Test_0 :
  (x <- (s_add_option 1 2) ;; ret x) = Some 3.
Proof. intuition. Qed.

(*| Without much surprise, this second example is equally
naive. Here :coq:`(s_add 1 2) is hidden by the second call
to :coq:`s_add` as it would be the case in a typical
imperative language. |*)

Lemma Option_Monad_Test_1 :
  (x <- (s_add_option 1 2) ;; (s_add_option 1 3)) = Some 4.
Proof. intuition. Qed.

(*| The next two examples show how to do some useful stuff with this monad: chaining computation in a simple way. |*)

Lemma Option_Monad_Test_2 :
  (n1 <- (s_add_option 1 2) ;; n2 <- (s_add_option 1 0) ;; (s_add_option n1 n2))
  = None.
Proof. intuition. Qed.

(*| Note that the last statement may either be :coq:`ret` or a function returning a :coq:`option nat`. |*)

Lemma Option_Monad_Test_3 :
  (n1 <- (s_add_option 1 2) ;; n2 <- (s_add_option 1 3) ;; (s_add_option n1 n2))
  = Some 7.
Proof. intuition. Qed.

Lemma Option_Monad_Test_4 :
  (n1 <- (s_add_option 1 2) ;; n2 <- (s_add_option 1 3) ;; ret (n1 + n2))
  = Some 7.
Proof. intuition. Qed.

(*| Let us review in more details the last example. It is equivalent to the following if we unset "Printing Notations"). |*)

Example Option_Monad_Test_4' :=
  bind
    (s_add_option 1 2)
    (fun n1 : nat => bind (s_add_option 1 3)
                          (fun n2 : nat => ret (Nat.add n1 n2))).
Compute Option_Monad_Test_4'.

Example step1 :=
bind
(Some 3)
(fun n1 : nat => bind (Some 4)
                      (fun n2 : nat => ret (Nat.add n1 n2))).
Compute step1.

(*| Remember that for the option monad, bind is defined as

  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with
              | None => None
              | Some y => f y
            end

The following simplifies to

|*)

Example step2 :=
  bind (Some 3) (fun n1 : nat => ret (Nat.add n1 4)).
Compute step2.

(*| and then to the following. You will note that at this stage, Coq is unable to know which variant of :coq:`ret` it should uses, there is not enough context. In the previous iterations, the :coq:`OptionMonad` variant has been inferred from the second parameter of :coq:`bind`. |*)

Example step3 := ret (Nat.add 3 4).
Compute step3.

(*| Ultimately, this simplifies to the following expression. We force a
"dispatch" to the right instance of :coq:`ret`. |*)

Example step4 := @ret _ OptionMonad _ 7.
Compute step4.

(*| We confirm this expression dispatches to the right instance as follows: |*)
Eval simpl in @ret _ OptionMonad _.

End Option_Monad_Test.

Section Either_Monad.

(*|
Either Monad
============

The :coq:`EitherMonad` uses a sum type to denote functions that may return a default value. It follows a pattern similar to the :coq:`OptionMonad`.

The :coq:`ret` function returns the right part of a sum type, i.e.
:coq:`inr` , :coq:`bind` chains calls if the parameter :coq:`x` is
different from :coq:`inl`, otherwise it returns :coq:`inl`.

|*)

Variable T : Type.

#[global] Instance EitherMonad : Monad (sum T) :=
{ ret  := fun _ v => inr v
; bind := fun _ _ c1 c2 => match c1 with
                             | inl v => inl v
                             | inr v => c2 v
                           end
}.

Instance EitherMonadLaws: @MonadLaws (sum T) _.
Proof.
  split ; intuition.
Qed.

End Either_Monad.

Section Either_Monad_Test.

Import Monad_Notations.

Variable m : Type -> Type.
Context {Monad_m: Monad m}.

(*| This test is similar to the tests for the :coq:`OptionMonad`. If the second parameter is 0, we return 0 immediatly. |*)

Definition s_add_sum (n m: nat) : nat + nat :=
  match m with
  | 0 => inl 0
  | _ => inr (n + m)
  end.

Lemma Either_Monad_Test_1 :
  (n1 <- (s_add_sum 1 2) ;; n2 <- (s_add_sum 1 3) ;; ret (n1 + n2))
  = inr 7.
Proof. intuition. Qed.

Lemma Either_Monad_Test_2 :
  (n1 <- (s_add_sum 1 2) ;; n2 <- (s_add_sum 3 0 ) ;; ret (n1 + n2))
  = inl 0.
Proof. intuition. Qed.

End Either_Monad_Test.

Section State_Monad.

(* https://brandon.si/code/the-state-monad-a-tutorial-for-the-confused/
*)

Variable S : Type.

Record state (t : Type) : Type := mkState
  { runState : S -> t * S }.

Definition evalState {t} (c : state t) (s : S) : t :=
  fst (runState c s).

Definition execState {t} (c : state t) (s : S) : S :=
  snd (runState c s).

#[global] Instance StateMonad : Monad state :=
{ ret  := fun _ v => mkState (fun s => (v, s))
; bind := fun _ _ c1 c2 =>
    mkState (fun s =>
      let (v,s) := runState c1 s in
      runState (c2 v) s)
}.

#[global] Instance StateMonadLaws: @MonadLaws state _.
Proof.
  split ; intros ; simpl.
  - destruct (f a). simpl. reflexivity.

  - destruct (aM).
    simpl. f_equal.
    apply functional_extensionality.
    intros. destruct (runState0 x). reflexivity.

  - f_equal. apply functional_extensionality.
    intros. destruct (runState aM x). reflexivity.
Qed.

End State_Monad.


(*
Free monad
https://serokell.io/blog/introduction-to-free-monads

https://github.com/tchajed/coq-io/tree/master


https://www.haskellforall.com/2012/06/you-could-have-invented-free-monads.html

https://www.haskellforall.com/2013/06/from-zero-to-cooperative-threads-in-33.html

https://www.cis.upenn.edu/~stevez/papers/LZ06b.pdf

https://www.reddit.com/r/scala/comments/18njy4v/seriously_what_is_the_best_explanation_of_monads/
=> adhit blog post

*)
