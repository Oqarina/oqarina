.. coq::


.. coq:: none

   Require Import Coq.Bool.Bool.
   Require Import Coq.Lists.List.

   Export ListNotations.
   Require Import Coq.Lists.ListDec.
   Require Import Coq.Unicode.Utf8.
   Require Import Coq.ssr.ssrbool.
   Require Import Coq.Relations.Relation_Definitions.
   Require Import Coq.Relations.Relation_Operators.
   Require Import Coq.Sorting.Permutation.

   Require Import Oqarina.coq_utils.all.

   Set Implicit Arguments.

   Fixpoint map_fold_right (A B:Type) (f : B -> A) (g : A -> A -> A) a l := match l with
    | nil => a
    | b::l2 => g (f b) (map_fold_right f g a l2)
   end.

   Declare Scope PropF_scope.

   Section List_reflect.

   Scheme Equality for list.

   Variable A : Type.
   Variable A_beq : A -> A -> bool.
   Variable A_reflect : forall x y, reflect ( x = y) (A_beq x y).

   Lemma list_eq_1 (l v:list A) :
       list_beq A_beq l v = true -> l = v.
   Proof.
       destruct(list_eq_dec A_beq) with l v as [H|H];
       intros.
       - eapply (elimT (A_reflect x y)) in H ; trivial.
       - eapply (introT (A_reflect x y)) in H ; trivial.
       - apply H.
       - contradict H. apply internal_list_dec_bl with A_beq.
           + intros.
             eapply (elimT (A_reflect x y)) in H ; trivial.
           + apply H0.
   Qed.

   Lemma list_eq_2 (l v:list A) :
       l = v -> list_beq A_beq l v = true.
   Proof.
     apply internal_list_dec_lb.
     intros.
     eapply (introT (A_reflect x y)). apply H.
   Qed.

   Lemma list_eq_reflect: forall l1 l2,
     reflect (l1 = l2) (list_beq A_beq l1 l2).
   Proof.
     intros.
     apply iff_reflect.
     split.
     apply list_eq_2.
     apply list_eq_1.
   Qed.

   End List_reflect.

Propositional Formulas
======================

We define classical propositional formulas (:coq:`PropF`) and associated reduction results.

Then, we define translation functions from a propositional formula to disjunctive or conjunctive normal form. We define an intermediate notations for negation normal form to ease the translations and proofs of correctness.

.. coq:: none

   Section Propositions.

Definitions
-----------

A propositional formula follows typical notation for conjunctives, disjunctives, negation, etc. Bot (⊥) corresponds to the False statement.
We use PropVars as a general type for variables.

.. coq::

   Open Scope PropF_scope.

   Variable PropVars : Set.

   Hypothesis PropVars_eqdec : forall x y : PropVars, {x = y} + {x ≠ y}.
   Variable PropVars_beq: PropVars → PropVars → bool.
   Hypothesis PropVars_reflect: forall x y,
     reflect (x = y) (PropVars_beq x y).

   Inductive PropF : Set :=
    | Var : PropVars -> PropF        (* Variable *)
    | Bot : PropF                    (* Bottom -- False *)
    | Conj : PropF -> PropF -> PropF (* Conjunction -- AND *)
    | Disj : PropF -> PropF -> PropF (* Disjuntion -- OR *)
    | Impl : PropF -> PropF -> PropF (* Implication *)
    | Neg : PropF -> PropF.          (* Negation *)

   Lemma PropFeq_dec : forall (x y : PropF), {x = y} + {x <> y}.
   Proof.
     decide equality.
   Qed.

   Notation "# P" := (Var P) (at level 1) : PropF_scope.
   Notation "A ∨ B" := (Disj A B) (at level 85, right associativity) : PropF_scope.
   Notation "A ∧ B" := (Conj A B) (at level 80, right associativity) : PropF_scope.
   Notation "⊥" := Bot (at level 0)  : PropF_scope.
   Definition Top := Neg ⊥.
   Notation "⊤" := (Neg ⊥) (at level 0) : PropF_scope.

:coq:`Eval_PropF` maps a :coq:`PropF` to a bool value with ⊥ being false

.. coq::

   Fixpoint Eval_PropF v A : bool :=
     match A with
     | # P   => v P
     | ⊥     => false
     | Neg B => negb (Eval_PropF v B)
     | B ∨ C => (Eval_PropF v B) || (Eval_PropF v C)
     | B ∧ C => (Eval_PropF v B) && (Eval_PropF v C)
     | Impl B C => (negb (Eval_PropF v B)) || (Eval_PropF v C)
   end.

:coq:`sat_PropF` maps a :coq:`PropF` to a Prop value. We show that :coq:`sat_PropF` is decidable, more speficially we show that one can either build a proof that a :coq:`PropF` is sat or unsat.

.. coq::

   Inductive sat_PropF: (PropVars -> Prop) -> PropF -> Prop :=
   | sat_Var (v: PropVars -> Prop) A : sat_PropF v (# A)
   | sat_Bot v : sat_PropF v ⊥
   | sat_Neg v p: unsat_PropF v p -> sat_PropF v (Neg p)
   | sat_And v p1 p2: sat_PropF v p1 -> sat_PropF v p2
       -> sat_PropF v (p1 ∧ p2)
   | sat_Or_1 v p1 p2: sat_PropF v p1 -> sat_PropF v (p1 ∨ p2)
   | sat_Or_2 v p1 p2: sat_PropF v p2 -> sat_PropF v (p1 ∨ p2)
   | sat_Impl v p1 p2: sat_PropF v (Neg p1) \/ sat_PropF v p2
       -> sat_PropF v (Impl p1 p2)

   with unsat_PropF: (PropVars -> Prop) -> PropF -> Prop :=
   | unsat_Var (v: PropVars -> Prop) A : unsat_PropF v (# A)
   | unsat_Neg v p: sat_PropF v p -> unsat_PropF v (Neg p)
   | unsat_And_1 v p1 p2: unsat_PropF v p1 -> unsat_PropF v (p1 ∧ p2)
   | unsat_And_2 v p1 p2: unsat_PropF v p2 -> unsat_PropF v (p1 ∧ p2)
   | unsat_Or v p1 p2: unsat_PropF v p1 -> unsat_PropF v p2
       -> unsat_PropF v (p1 ∨ p2)
   | unsat_Impl v p1 p2: sat_PropF v p1 -> unsat_PropF v p2
       -> unsat_PropF v (Impl p1 p2).

   Lemma sat_PropF_and_rewrite: forall v A1 A2,
       sat_PropF v (A1 ∧ A2) <-> sat_PropF v A1 /\ sat_PropF v A2.
   Proof.
     split; intro H.
     - inversion H. intuition.
     - apply sat_And ; intuition.
   Qed.

   Lemma sat_PropF_or_rewrite : forall v A1 A2,
       sat_PropF v (A1 ∨ A2) <-> sat_PropF v A1 \/ sat_PropF v A2.
   Proof.
     split; intro H.
     - inversion H ; intuition.
     - destruct H.
       + apply sat_Or_1 ; intuition.
       + apply sat_Or_2 ; intuition.
   Qed.

   Lemma sat_PropF_impl_rewrite: forall v A1 A2,
       sat_PropF v (Impl A1 A2) <-> sat_PropF v (Neg A1) \/ sat_PropF v A2.
   Proof.
     split; intro H.
     - inversion H ; intuition.
     - destruct H ; apply sat_Impl ; intuition.
   Qed.

   Lemma sat_PropF_neg_rewrite: forall v A1,
       sat_PropF v (Neg A1) <-> unsat_PropF v A1.
   Proof.
     split; intro H.
     - inversion H ; intuition.
     - apply sat_Neg ; intuition.
   Qed.

   Lemma sat_PropF_dec: forall v A,
     { sat_PropF v A } + { unsat_PropF v A }.
   Proof.
     induction A.

     - (* Var *)
       left. apply sat_Var.

     - (* Bot *)
       left. apply sat_Bot.

     - (* And *)
       destruct IHA1 as [IHA1a |IHA1b] ;
       destruct IHA2 as [IHA2a |IHA2b] ; simpl.

       + left. apply sat_PropF_and_rewrite ; intuition.
       + right. apply unsat_And_2 ; auto.

       + right. apply unsat_And_1 ; auto.
       + right. apply unsat_And_1 ; auto.

     - (* Or *)
       destruct IHA1 as [IHA1a |IHA1b] ;
       destruct IHA2 as [IHA2a |IHA2b] ; simpl.

       + left. apply sat_Or_1 ; intuition.
       + left. apply sat_Or_1 ; intuition.
       + left. apply sat_Or_2 ; intuition.
       + right. apply unsat_Or ; intuition.

     - (* Impl *)
       destruct IHA1 as [IHA1a |IHA1b] ;
       destruct IHA2 as [IHA2a |IHA2b] ; simpl.

       + left. apply sat_Impl ; intuition.
       + right. apply unsat_Impl ; intuition.
       + left. apply sat_Impl ; intuition.
       + left. apply sat_Impl. left. apply sat_Neg. intuition.

     - (* Neg *)
       destruct IHA as [IHAa |IHAb] ; simpl.
       + right. apply unsat_Neg ; intuition.
       + left. apply sat_Neg ; intuition.
   Qed.

Boolean Expressions
-------------------

.. coq::

   Fixpoint is_Boolean_Expr A : Prop :=
     match A with
     | # P   => True
     | ⊥     => True
     | Neg B => is_Boolean_Expr B
     | B ∨ C => is_Boolean_Expr B /\ is_Boolean_Expr C
     | B ∧ C => is_Boolean_Expr B /\ is_Boolean_Expr C
     | Impl B C => False
   end.

   Lemma is_Boolean_Expr_dec: forall A,
     { is_Boolean_Expr A } + { ~ is_Boolean_Expr A} .
   Proof.
     induction A ; unfold is_Boolean_Expr ; intuition.
   Qed.

Reduction lemmas
----------------

We define two sets of reduction lemmas:

* :coq:`red` and :coq:`Rewrite_PropF` reduces the head of a :coq:`PropF` only. We show that they are equivalent.

* :coq:`Rewrite_PropF_r` reduces a :coq:`PropF` recursively. We show that the result compute the same boolean value in :coq:`Rewrite_PropF_r_Sound`.

.. coq::

   Inductive red : relation (PropF) :=
     | red_Disj_comm: forall (p1 p2: PropF),
       red (Disj p1 p2) (Disj p2 p1)

     | red_Disj_Top: forall (p : PropF),
       red (Disj p Top) Top

     | red_Disj_Bot: forall (p : PropF),
       red (Disj p Bot) p

     | red_Conj_comm: forall (p1 p2: PropF),
       red (Conj p1 p2) (Conj p2 p1)

     | red_Conj_Top: forall (p : PropF),
       red (Conj p Top) p

     | red_Conj_Bot: forall (p : PropF),
       red (Conj p Bot) Bot

     | red_Impl: forall (p1 p2: PropF),
       red (Impl p1 p2) (Disj (Neg p1) p2).

   Definition Rewrite_PropF (p : PropF) : PropF :=
     match p with
       | p1 ∨ ⊤ => ⊤
       | p1 ∨ ⊥ => p1
       | p1 ∨ p2 => p2 ∨ p1

       | p1 ∧ ⊤ => p1
       | p1 ∧ ⊥ => ⊥
       | p1 ∧ p2 => p2 ∧ p1

       | Impl p1 p2 => (Neg p1) ∨ p2

       (* default *)
       | _ => p
   end.

   Lemma Rewrite_PropF_Sound : forall v (p p' : PropF),
       red p p' -> Eval_PropF v (Rewrite_PropF p) = Eval_PropF v p'.
   Proof.
       intros.
       inversion H ; simpl ; try reflexivity ;
       destruct p2 ; simpl ; try reflexivity ;
       destruct p2 ; simpl ; try reflexivity.
   Qed.

Proving that :coq:`Rewrite_PropF` is complete relies on a proof by induction over the proposition and the mechanical application of the basic reduction rules. The :coq:`prove_Rewrite_PropF_Complete` tactics expedites these steps.

.. coq::

   Ltac prove_Rewrite_PropF_Complete :=
       repeat match goal with
       | [ |- forall _ : ?T, _ ] => intros
       | [ |- clos_refl_trans PropF red (_) (_)  ] => apply rt_step ; simpl

       | [ |- red (_) (_)  ] => apply rt_step ; simpl
       | [ |- red (?p1 ∧ ?p2) (?p2 ∧ ?p1)  ] => apply red_Conj_comm
       | [ |- red (?p1 ∧ ⊥) ⊥  ] => apply red_Conj_Bot
       | [ |- red (?p1 ∧ (Neg ?p2)) _  ] =>
         destruct p2 ; simpl ; try apply red_Conj_comm ; apply red_Conj_Top
       | [ |- red (?p1 ∨ ?p2) (?p2 ∨ ?p1)  ] => apply red_Disj_comm
       | [ |- red (?p1 ∨ ⊥) ?p1  ] => apply red_Disj_Bot
       | [ |- red (?p1 ∨ (Neg ?p2)) _  ] =>
         destruct p2 ; simpl ; try apply red_Disj_comm ; apply red_Disj_Top
       | [ |- red (Impl ?p1 ?p2) _  ] => apply red_Impl
   end.

   Lemma Rewrite_PropF_Complete: forall (p : PropF),
     clos_refl_trans _ red p (Rewrite_PropF p).
   Proof.
     intros ; induction p ; auto with *.
     - case p2 ; prove_Rewrite_PropF_Complete.
     - case p2 ; prove_Rewrite_PropF_Complete.
     - case p2 ; prove_Rewrite_PropF_Complete.
   Qed.

We extentd :coq:`Rewrite_PropF` to a fully recursive variant, and prove it is sound (:coq:`Rewrite_PropF_r_Sound`).

.. coq::

   Fixpoint Rewrite_PropF_r (p : PropF) : PropF :=
     match p with
       | _ ∨ ⊤ => ⊤
       | p1 ∨ ⊥ => Rewrite_PropF_r p1
       | ⊥ ∨  p1 => Rewrite_PropF_r p1
       | p1 ∧ ⊤ => Rewrite_PropF_r p1
       | p1 ∧ ⊥ => ⊥

       | p1 ∧ p2 => (Rewrite_PropF_r p1) ∧ (Rewrite_PropF_r p2)
       | p1 ∨ p2 => (Rewrite_PropF_r p1) ∨ (Rewrite_PropF_r p2)

       | Neg p1 => Neg (Rewrite_PropF_r p1)

       | _ => p
   end.

To prove that :coq:`Rewrite_PropF_r` is sound, we first prove a couple of trivial reduction lemmas.

.. coq::

   Fact Rewrite_PropF_r_red_1: forall v (p1 p2 : PropF),
     Eval_PropF v (Rewrite_PropF_r (p1 ∧ p2)) =
         (Eval_PropF v (Rewrite_PropF_r p1)) && Eval_PropF v (Rewrite_PropF_r p2).
   Proof.
     intros.
     case p2 ; intros ; simpl ; try reflexivity.
     - rewrite andb_false_r ; reflexivity.
     - case p ; simpl ; try reflexivity. rewrite andb_true_r ; reflexivity.
   Qed.

   Fact Rewrite_PropF_r_red_2: forall v (p1 p2 : PropF),
     Eval_PropF v (p1 ∧ p2) = Eval_PropF v p1 && Eval_PropF v p2.
   Proof. auto. Qed.

   Fact Rewrite_PropF_r_red_or_1: forall v (p1 p2 : PropF),
     Eval_PropF v (p1 ∨ p2) = Eval_PropF v p1 || Eval_PropF v p2.
   Proof. auto. Qed.

   Fact Eval_PropF_Neg : forall v (p: PropF),
     Eval_PropF v (Neg p) = negb (Eval_PropF v p).
   Proof. auto. Qed.

   Lemma Rewrite_PropF_r_Sound : forall v (p : PropF),
       Eval_PropF v (Rewrite_PropF_r p) = Eval_PropF v p.
   Proof.
       intros.
       induction p ; simpl ; try reflexivity.
       - destruct p2 eqn:Hp2.
         * simpl. rewrite IHp1 ; reflexivity.
         * simpl. rewrite andb_false_r ; reflexivity.
         * rewrite Rewrite_PropF_r_red_2, IHp1, IHp2. reflexivity.
         * rewrite Rewrite_PropF_r_red_2, IHp1, IHp2. reflexivity.
         * rewrite Rewrite_PropF_r_red_2, IHp1, IHp2. reflexivity.
         * subst. destruct p ; rewrite <- IHp1.
           + rewrite Rewrite_PropF_r_red_2 ; reflexivity.
           + simpl. rewrite andb_true_r ; reflexivity.
           + rewrite Rewrite_PropF_r_red_2, IHp2 ; reflexivity.
           + rewrite Rewrite_PropF_r_red_2, IHp2 ; reflexivity.
           + rewrite Rewrite_PropF_r_red_2, IHp2 ; reflexivity.
           + rewrite Rewrite_PropF_r_red_2, IHp2 ; reflexivity.

       - destruct p2 eqn:Hp2.
         * subst. destruct p1 ;
           try rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2 ; reflexivity.

         * subst. destruct p1 ; rewrite <- IHp1 ; simpl ; auto with *.

         * subst. destruct p1 ; rewrite <- IHp1.
           + rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2. reflexivity.
           + rewrite Rewrite_PropF_r_red_2, IHp1, IHp2. reflexivity.
           + rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2. reflexivity.
           + rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2. reflexivity.
           + rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2. reflexivity.
           + rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2. reflexivity.

         * subst. destruct p1 ; rewrite <- IHp1 ;
            rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2 ; reflexivity.

         * subst. destruct p1 ; rewrite <- IHp1 ;
           try rewrite Rewrite_PropF_r_red_or_1, IHp1, IHp2 ; reflexivity.

         * subst. destruct p1 ; rewrite <- IHp1 ;
           destruct p ; try rewrite Rewrite_PropF_r_red_or_1, IHp2 ; auto with *.

       - rewrite IHp ; reflexivity.
   Qed.

   Lemma is_Boolean_Expr_Rewrite_PropF_r : forall bexpr ,
       is_Boolean_Expr bexpr -> is_Boolean_Expr (Rewrite_PropF_r bexpr).
   Proof.
       intros.
       induction bexpr ; intuition.
       - simpl in H. simpl. destruct H.
         destruct bexpr2 ; simpl ; intuition.
         simpl in H2. destruct bexpr2 ; simpl ; intuition.

       - simpl in H. simpl. destruct H.
         destruct bexpr2 ; simpl ; intuition.
         + destruct bexpr1 ; simpl ; intuition.
         + destruct bexpr1 ; simpl ; intuition.
         + destruct bexpr1 ; simpl ; intuition.
         + destruct bexpr1 ; simpl ; intuition.
         + destruct bexpr1 ; simpl ; intuition.
         + destruct bexpr1, bexpr2 ; simpl ; intuition.
   Qed.

Negation Normal Form
--------------------

We introduce an alternate form of Boolean Expressions: Negation Normal Form. A formula is in negation normal form (NNF) if the negation operator is only applied to variables, and only conjunctives and disjunctives are used.

We introduce an AST for NNF, translation functions from (:coq:`PropFtoNNF`) and to (:coq:`NNFtoPropF`). The lemma :coq:`NNF_equiv_valid` shows that an :coq:`NNF`  built from a :coq:`PropF` has the same boolean valuation than the original :coq:`PropF`.

.. coq:: none

   Section NNF.

.. coq::

   Inductive NNF : Set :=
    | NPos : PropVars -> NNF
    | NNeg : PropVars -> NNF
    | NBot : NNF
    | NTop : NNF
    | NConj : NNF -> NNF -> NNF
    | NDisj : NNF -> NNF -> NNF.

:coq:`PropFtoNNF` rewrites a :coq:`PropF` by moving all negations to the literals, and rewrites implications. :coq:`PropFtoNNNF` performs the same actions for the case of a negation.

*Note: this work-arounds limits set by Coq for fixpoint functions*.

.. coq::

   Fixpoint PropFtoNNF (A:PropF) : NNF :=
     match A with
       | # P      => NPos P
       | ⊥        => NBot
       | B ∨ C    => NDisj (PropFtoNNF B) (PropFtoNNF C)
       | B ∧ C    => NConj (PropFtoNNF B) (PropFtoNNF C)
       | Impl B C => NDisj (PropFtoNNFN B) (PropFtoNNF C)
       | Neg B    => PropFtoNNFN B
    end
   with PropFtoNNFN (A:PropF) : NNF :=
     match A with
       | # P   => NNeg P
       | ⊥     => NTop
       | B ∨ C => NConj (PropFtoNNFN B) (PropFtoNNFN C)
       | B ∧ C => NDisj (PropFtoNNFN B) (PropFtoNNFN C)
       | Neg B => PropFtoNNF B
       | Impl B C => NConj (PropFtoNNF B) (PropFtoNNFN C)
     end.

   Fixpoint NNFtoPropF (A:NNF) : PropF :=
     match A with
     | NPos P    => #P
     | NNeg P    => Neg #P
     | NBot      => ⊥
     | NTop      => ⊤
     | NConj B C => NNFtoPropF B ∧ NNFtoPropF C
     | NDisj B C => NNFtoPropF B ∨ NNFtoPropF C
   end.

   Definition To_NNF (p : PropF) := NNFtoPropF (PropFtoNNF p).

Proof that A and NNF A have the same value.

* Note: we prove the two lemmas at once since they are mutually dependent.*

.. coq::

   Lemma NNF_equiv_valid : forall v A,
       Eval_PropF v (NNFtoPropF (PropFtoNNF  A)) = Eval_PropF v A /\
       Eval_PropF v (NNFtoPropF (PropFtoNNFN A)) = Eval_PropF v (Neg A).
   Proof.
       intros v A.
       induction A ; split ; simpl in *; trivial.
       - destruct IHA1, IHA2. rewrite H, H1. reflexivity.
       - destruct IHA1, IHA2. rewrite H0, H2, negb_andb. reflexivity.
       - destruct IHA1, IHA2. rewrite H, H1. reflexivity.
       - destruct IHA1, IHA2. rewrite H0, H2, negb_orb. reflexivity.
       - destruct IHA1, IHA2. rewrite H0, H1. reflexivity.
       - destruct IHA1, IHA2. rewrite H, H2, negb_orb, negb_involutive.
         reflexivity.
       - destruct IHA. rewrite H0. reflexivity.
       - destruct IHA. rewrite H, negb_involutive. reflexivity.
   Qed.

.. coq:: none

   End NNF.

Litterals
---------

Disjunctive and conjunctive normal forms are lists of basic clauses combined. We introduce an intermediate common representation for literals and clauses.

Thus, we define a :coq:`Clause` as a list of literals, and :coq:`Clauses` as a list of :coq:`Clause`. From there, we can build CNF and DNF from clauses. They will only vary in the operator used to combine literals in a clause, and the operator use to combine clauses.

*Note: We use reflection to booleans to derive functions that can compute, in addition to formal ones.*

.. coq:: none

   Section Literals.

.. coq::

   Inductive Literal :=
     | LPos : PropVars -> Literal (* A variable *)
     | LNeg : PropVars -> Literal (* Negation of a variable *)
     | LBot : Literal             (* Bottom *)
     | LTop : Literal.            (* Top *)

   Lemma Literal_eq_dec: forall x y : Literal, {x = y} + {x ≠ y}.
   Proof.
     decide equality.
   Qed.

   Definition Literal_beq (X Y : Literal) : bool :=
       match X with
   | LPos x => match Y with
   	        | LPos x0 => PropVars_beq x x0
               | _ => false
               end
   | LNeg x => match Y with
               | LNeg x0 => PropVars_beq x x0
               | _ => false
               end
   | LBot => match Y with
             | LBot => true
             | _ => false
             end
   | LTop => match Y with
             | LTop => true
             | _ => false
             end
   end.

   Lemma Literal_eq_reflect: forall t1 t2,
     reflect (t1 = t2) (Literal_beq t1 t2).
   Proof.
     intros.
     induction t1 ; induction t2 ; simpl ; auto with * ;
     destruct (PropVars_beq p p0) eqn:pp0.
     - apply ReflectT. apply f_equal.
       eapply (elimT (PropVars_reflect p p0)). auto.
     - apply ReflectF.
       eapply (elimF (PropVars_reflect p p0)) in pp0.
       congruence.
     - apply ReflectT. apply f_equal.
       eapply (elimT (PropVars_reflect p p0)). auto.
     - apply ReflectF.
       eapply (elimF (PropVars_reflect p p0)) in pp0.
       congruence.
   Qed.

   Lemma Literal_eq_idem: forall l, Literal_beq l l = true.
   Proof.
     intros.
     eapply (introT (Literal_eq_reflect l l)).
     reflexivity.
   Qed.

   Definition LiteraltoPropF (L : Literal) : PropF :=
     match L with
     | LPos Q => #Q
     | LNeg Q => Neg #Q
     | LBot   => ⊥
     | LTop   => ⊤
     end.

   Definition Eval_Literal v (L : Literal) : bool :=
     match L with
     | LPos Q => v Q
     | LNeg Q => negb (v Q)
     | LBot   => false
     | LTop   => true
     end.

   Definition Clause : Type := list Literal.

   Lemma Clause_eq_dec: forall x y : Clause, {x = y} + {x ≠ y}.
   Proof.
     decide equality.
     apply Literal_eq_dec.
   Qed.

   Definition Clause_beq := list_beq Literal_beq.

   Lemma Clause_beq_idem: forall c, Clause_beq c c = true.
   Proof.
     induction c.
     - trivial.
     - simpl. rewrite IHc.
       rewrite Literal_eq_idem. intuition.
   Qed.

   Lemma Clause_eq_reflect: forall t1 t2,
     reflect (t1 = t2) (Clause_beq t1 t2).
   Proof.
     apply list_eq_reflect.
     apply Literal_eq_reflect.
   Qed.

   Definition Eval_Clause v (c : Clause) : list bool :=
     map (fun x => Eval_Literal v x) c.

   Lemma Eval_Clause_cons v c l:
     Eval_Clause v (c :: l) = Eval_Literal v c :: Eval_Clause v l.
   Proof.
     intuition.
   Qed.

   Lemma Eval_Clause_In: forall v a c,
     In a c -> In (Eval_Literal v a) (Eval_Clause v c).
   Proof.
     intros.
     unfold Eval_Clause.
     generalize H. apply in_map'.
   Qed.

   Definition Clauses := list (list Literal).

   Definition Clauses_beq := list_beq Clause_beq.

   Lemma Clauses_eq_dec: forall x y : Clauses, {x = y} + {x ≠ y}.
   Proof.
     repeat decide equality.
   Qed.

:coq:`AddClause` adds clause :coq:`l` to each clause of :coq:`ll`.

.. coq::

   Definition AddClause (l:Clause) (ll:Clauses) : Clauses :=
    map (fun l2 => l ++ l2) ll.

   Lemma AddClause_nil_l: forall c, AddClause [] c = c.
   Proof.
     intros. unfold AddClause. simpl. apply map_id.
   Qed.

   Lemma AddClause_nil_r: forall c, AddClause c [] = [].
   Proof.
     intros. unfold AddClause. intuition.
   Qed.

   Lemma AddClause_distrib_r: forall a a0 c,
     AddClause a (a0 :: c) = (a ++ a0) :: AddClause a c.
   Proof. intuition. Qed.

:coq:`AddClauses` adds clauses of :coq:`ll` to each clause of :coq:`ll2`.

.. coq::

   Definition AddClauses (ll ll2:Clauses) : Clauses :=
     flat_map (fun l => AddClause l ll2) ll.

   Lemma AddClauses_distrib_l: forall a c1 c2,
     AddClauses (a::c1) c2 = AddClause a c2 ++ AddClauses c1 c2.
   Proof. intuition. Qed.

   Lemma AddClauses_not_nil: forall l1 l2,
     l1 <> [] -> l2 <> [] -> AddClauses l1 l2 <> [].
   Proof.
     induction l1, l2.
     - intuition.
     - intuition.
     - intuition.
     - intros. rewrite AddClauses_distrib_l.
       rewrite AddClause_distrib_r. simpl.
       intuition. inversion H1.
   Qed.

.. coq:: none

   End Literals.

Disjunctive Normal Form
-----------------------

In the following, we define :coq:`NNFtoDNF` transformation from a NNF to a DNF form. :coq:`To_DNF` transforms a :coq:`PropF` to its equivalent DNF form. We then show in :coq:`To_DNF_equiv_valid` that the evaluates to the same value.

.. coq:: none

   Section DNF.

.. coq::

   Fixpoint NNFtoDNF (A:NNF) : Clauses := match A with
   | NPos P    => [[LPos P]]
   | NNeg P    => [[LNeg P]]
   | NBot      => [[LBot]]
   | NTop      => [[LTop]]
   | NConj B C => AddClauses (NNFtoDNF B) (NNFtoDNF C)
   | NDisj B C => NNFtoDNF B ++ NNFtoDNF C
   end.

   Lemma NNFtoDNF_not_nil: forall a,
     NNFtoDNF a <> [].
   Proof.
     intros.
     unfold NNFtoDNF.
     induction a.
     intuition ; inversion H.
     intuition ; inversion H.
     intuition ; inversion H.
     intuition ; inversion H.
     apply AddClauses_not_nil. apply IHa1. apply IHa2.
     apply app_not_nil. apply IHa1. apply IHa2.
   Qed.

   Definition DNFClausetoPropF := map_fold_right LiteraltoPropF Conj ⊤.

   Definition DNFtoPropF :=
     map_fold_right DNFClausetoPropF Disj Bot.

   Lemma is_Boolean_Expr_DNFtoPropF: forall dnf ,
     is_Boolean_Expr (DNFtoPropF dnf).
   Proof.
     intros.
     induction dnf.
     - simpl ; intuition.
     - simpl ; intuition. induction a.
         + simpl ; intuition.
         + simpl ; intuition. induction a ; simpl ; intuition.
   Qed.

   Definition To_DNF (p : PropF) := Rewrite_PropF_r (DNFtoPropF (NNFtoDNF (PropFtoNNF p))).

   Lemma DNF_or_valid : forall v ll1 ll2,
     Eval_PropF v (DNFtoPropF (ll1 ++ ll2)) =
     Eval_PropF v (DNFtoPropF ll1) || Eval_PropF v (DNFtoPropF ll2).
   Proof.
     intros.
     induction ll1 ; simpl.
     - reflexivity.
     - unfold DNFtoPropF in IHll1 at 1. rewrite IHll1. unfold DNFtoPropF at 1.
       apply orb_assoc.
   Qed.

   Lemma DNF_or_valid_2 : forall v a ll,
     Eval_PropF v (DNFtoPropF (a :: ll)) =
     Eval_PropF v (DNFtoPropF [a]) || Eval_PropF v (DNFtoPropF ll).
   Proof.
     intros.
     assert (a :: ll = [a] ++ ll).
     intuition.
     rewrite H.
     apply DNF_or_valid.
   Qed.

   Lemma DNF_or_clause_valid : forall v l1 l2,
     Eval_PropF v (DNFClausetoPropF (l1++l2)) =
     Eval_PropF v (DNFClausetoPropF l1) && Eval_PropF v (DNFClausetoPropF l2).
   Proof.
     intros.
     induction l1;simpl.
     - reflexivity.
     - unfold DNFClausetoPropF in IHl1 at 1;rewrite IHl1.
       unfold DNFClausetoPropF at 1. apply andb_assoc.
   Qed.

   Lemma DNF_and_clause_valid : forall v l ll,
     Eval_PropF v (DNFtoPropF (AddClause l ll)) =
     Eval_PropF v (DNFClausetoPropF l) && Eval_PropF v (DNFtoPropF ll).
   Proof.
     intros;induction ll;simpl.
     - rewrite andb_false_r;reflexivity.
     - unfold DNFtoPropF in IHll at 1; rewrite IHll.
       rewrite DNF_or_clause_valid.
       rewrite andb_orb_distrib_r.
       reflexivity.
   Qed.

   Lemma DNF_and_valid : forall v ll1 ll2,
     Eval_PropF v (DNFtoPropF (AddClauses ll1 ll2)) =
     Eval_PropF v (DNFtoPropF ll1) && Eval_PropF v (DNFtoPropF ll2).
   Proof.
     intros;induction ll1;simpl.
     - reflexivity.
     - rewrite DNF_or_valid, IHll1, DNF_and_clause_valid.
       rewrite andb_orb_distrib_l. reflexivity.
   Qed.

   Theorem DNF_equiv_valid' : forall v A,
     Eval_PropF v (DNFtoPropF (NNFtoDNF A)) = Eval_PropF v (NNFtoPropF A).
   Proof.
     intros; induction A; simpl ; try reflexivity.
     - destruct (v p); simpl ; reflexivity.
     - destruct (v p); simpl ; reflexivity.
     - rewrite DNF_and_valid, IHA1, IHA2 ; reflexivity.
     - rewrite DNF_or_valid, IHA1, IHA2 ; reflexivity.
   Qed.

We show that for all PropF, its DNF form evaluates to the same original value.

.. coq::

   Theorem To_DNF_equiv_valid : forall v (A : PropF),
     Eval_PropF v (To_DNF A) = Eval_PropF v A.
   Proof.
     intros.
     unfold To_DNF.
     rewrite Rewrite_PropF_r_Sound.
     rewrite DNF_equiv_valid'.
     apply NNF_equiv_valid.
   Qed.

Evaluation of Disjunctive Normal Forms
--------------------------------------

A DNF is a simpler form of a boolean expression. We proose evaluation functions for a clause (:coq:`Eval_DNF_Clause`) and for clauses (:coq:`Eval_DNF_Clauses`). We then show that for all :coq:`PropF`, its tranformation to a DNF and its evaluation yiels the same value in :coq:`Eval_DNF_sound`. We provide a collection of intermediate reduction lemmas to prove this final result.

.. coq::

   Definition Eval_DNF_Clause v (c : Clause) : bool :=
     andbl (Eval_Clause v c).

   Definition Eval_DNF v (d : Clauses) : bool :=
     orbl (map (fun x => Eval_DNF_Clause v x) d).

:Coq:`DNF_Clause` Reduction lemmas
``````````````````````````````````

.. coq::

   Lemma Eval_DNF_Clause_cons: forall v a l,
     Eval_DNF_Clause v (a :: l) = Eval_Literal v a && Eval_DNF_Clause v l.
   Proof.
     intros.
     unfold Eval_DNF_Clause. rewrite Eval_Clause_cons, andbl_cons; intuition.
   Qed.

   Lemma Eval_DNF_Clause_red: forall v c a,
     Eval_DNF_Clause v (c ++ a) = Eval_DNF v [c ++ a].
   Proof. intuition. Qed.

   Lemma Eval_DNF_Clause_nil: forall v, Eval_DNF_Clause v [] = true.
   Proof. intuition. Qed.

   Lemma Eval_DNF_singleton: forall v c,
     Eval_DNF v [c] = Eval_DNF_Clause v c.
   Proof. intuition. Qed.

   Lemma Eval_DNF_nil: forall v, Eval_DNF v [] = false.
   Proof. intuition. Qed.

   Lemma Eval_DNF_cons: forall v a l,
     Eval_DNF v (a :: l) = Eval_DNF_Clause v a || Eval_DNF v l.
   Proof.
     intros.
     unfold Eval_DNF.
     rewrite map_cons, orbl_cons. reflexivity.
   Qed.

   Lemma Eval_DNF_Clause_app: forall v a a0,
     Eval_DNF_Clause v (a ++ a0) =
       Eval_DNF_Clause v a && Eval_DNF_Clause v a0.
   Proof.
     intros.
     unfold Eval_DNF_Clause. unfold Eval_Clause. rewrite map_app.
     rewrite andbl_app, andbl_cons.
     intuition.
   Qed.

   Lemma Eval_DNF_Clause_permut: forall (c1 c2: Clause) v,
     Permutation c1 c2 -> Eval_DNF_Clause v c1 = Eval_DNF_Clause v c2.
   Proof.
     intros.
     unfold Eval_DNF_Clause.
     unfold Eval_Clause.
     assert (Permutation
       (map (λ x : Literal, Eval_Literal v x) c1)
       (map (λ x : Literal, Eval_Literal v x) c2)).
     apply Permutation_map ; auto.
     apply andbl_permut ; auto.
   Qed.

   Lemma Eval_PropF_DNF_Clause: forall v a,
     Eval_PropF v (DNFClausetoPropF a)  = Eval_DNF_Clause v a.
   Proof.
     intros.
     induction a.
     - intuition.
     - rewrite Eval_DNF_Clause_cons.
       unfold DNFClausetoPropF. simpl. fold DNFClausetoPropF.
       rewrite IHa.
       unfold LiteraltoPropF. destruct a ; intuition.
   Qed.

:Coq:`DNF` Reduction lemmas
```````````````````````````

.. coq::

   Lemma Eval_DNF_app: forall v c1 c2,
     Eval_DNF v (c1 ++ c2) = Eval_DNF v c1 || Eval_DNF v c2.
   Proof.
     intros.
     unfold Eval_DNF.
     rewrite map_app, orbl_split.
     reflexivity.
   Qed.

   Lemma Eval_DNF_AddClause: forall v a c,
     Eval_DNF v (AddClause a c) = Eval_DNF_Clause v a && Eval_DNF v c.
   Proof.
     intros. induction c.
     - rewrite AddClause_nil_r. repeat rewrite Eval_DNF_nil.
       rewrite andb_false_r ; reflexivity.
     - rewrite AddClause_distrib_r.
     repeat rewrite Eval_DNF_cons. rewrite andb_orb_distrib_r. rewrite Eval_DNF_Clause_app, IHc. auto.
   Qed.

   Lemma Eval_DNF_AddClauses: forall v c1 c2,
     Eval_DNF v (AddClauses c1 c2) = Eval_DNF v c1 && Eval_DNF v c2.
   Proof.
     intros.
     induction c1.
     - simpl. apply Eval_DNF_nil.
     - simpl. rewrite Eval_DNF_app,Eval_DNF_cons, IHc1.
       rewrite andb_orb_distrib_l. rewrite Eval_DNF_AddClause ; reflexivity.
   Qed.

   Lemma Eval_DNF_middle: forall a b c v,
     Eval_DNF v (a :: b :: c) = Eval_DNF v (b :: a :: c).
   Proof.
     intros.
     repeat rewrite  Eval_DNF_cons. repeat rewrite orb_assoc.
     rewrite orb_middle ; reflexivity.
   Qed.

   Lemma Eval_DNF_distrib_app: forall (a: Clause) (b c: Clauses) v,
     Eval_DNF v (a :: b ++ c) =
       Eval_DNF v (a :: b) || Eval_DNF v (a :: c).
   Proof.
     intros.
     rewrite <- Eval_DNF_app.

     repeat rewrite Eval_DNF_cons.
     repeat rewrite Eval_DNF_app.
     repeat rewrite Eval_DNF_cons.

     destruct (Eval_DNF_Clause v a) ;
     destruct (Eval_DNF v b) ;
     destruct (Eval_DNF v c) ;
       simpl ; tauto.
   Qed.

   Lemma Eval_DNF_distrib_cons: forall (a b c: Clause) v,
     Eval_DNF v [ a ; b ; c ] =
       Eval_DNF v [a ; b] || Eval_DNF v [ a ; c ].
   Proof.
     intros.
     repeat rewrite Eval_DNF_cons.

     destruct (Eval_DNF_Clause v a) ;
     destruct (Eval_DNF_Clause v b) ;
     destruct (Eval_DNF_Clause v c) ;
       simpl ; tauto.
   Qed.

   Lemma Eval_DNF_distrib_cons2: forall (a b : Clause) (c: Clauses) v,
     Eval_DNF v ( a :: b :: c ) =
       Eval_DNF v [a ; b] || Eval_DNF v ( a :: c ).
   Proof.
     intros.
     repeat rewrite Eval_DNF_cons.

     destruct (Eval_DNF_Clause v a) ;
     destruct (Eval_DNF_Clause v b) ;
     destruct (Eval_DNF v c) ;
       simpl ; tauto.
   Qed.

   Lemma Eval_DNF_permut: forall (c1 c2: Clauses) v,
     Permutation c1 c2 -> Eval_DNF v c1 = Eval_DNF v c2.
   Proof.
     intros.
     unfold Eval_DNF.
     assert (Permutation
       (map (λ x : Clause, Eval_DNF_Clause v x) c1)
       (map (λ x : Clause, Eval_DNF_Clause v x) c2)).
     apply Permutation_map ; auto.
     apply orbl_permut ; auto.
   Qed.

   Lemma Eval_DNF_red: forall (c1 c2: Clause) v,
      Eval_DNF v [c1 ; c2] = Eval_DNF v [c1] || Eval_DNF v [c2].
   Proof.
     intros. unfold Eval_DNF. intuition.
   Qed.

   Lemma Eval_DNF_red_incl_1: forall (c1 c2: Clause) v,
     NoDup c1 -> incl c1 c2 ->
       Eval_DNF v [ c1 ; c2 ] = Eval_DNF v [c1].
   Proof.
     intros.
     destruct (incl_split H H0).
     rewrite Eval_DNF_red.
     assert (Permutation c2 (c1 ++ x)).
     apply Permutation_sym ; auto.

     repeat rewrite Eval_DNF_singleton.

     assert (Eval_DNF_Clause v c2 = Eval_DNF_Clause v (c1 ++ x)).
     apply Eval_DNF_Clause_permut, H2.

     rewrite H3. rewrite Eval_DNF_Clause_app. rewrite absorption_orb.
     reflexivity.
   Qed.

   Lemma Eval_DNF_red_incl_l: forall (c1 : Clause) (l : Clauses) v,
     NoDup c1 -> (forall x, In x l -> incl c1 x)
              -> Eval_DNF v (c1 :: l) = Eval_DNF v [c1].
   Proof.
     intros c1 l v n p.
     induction l.
     - tauto.
     - assert (incl c1 a). auto with *.

       assert (Eval_DNF v [ c1 ; a ] = Eval_DNF v [c1]).
       apply Eval_DNF_red_incl_1. apply n. apply H.

       simpl.
       rewrite Eval_DNF_distrib_cons2.
       rewrite H0 at 1.
       rewrite orb_comm.
       rewrite Eval_DNF_cons.
       rewrite orb_comm.
       rewrite orb_assoc. rewrite Eval_DNF_singleton.
       rewrite orb_diag.
       rewrite <- Eval_DNF_cons.
       apply IHl. auto with *.
   Qed.

   Lemma Eval_PropF_DNF: forall v p,
     Eval_PropF v (DNFtoPropF p) = Eval_DNF v p.
   Proof.
     intros.
     induction p.
     - intuition.
     - rewrite Eval_DNF_cons.
       rewrite DNF_or_valid_2. rewrite IHp.
       simpl. rewrite Eval_PropF_DNF_Clause.
       rewrite orb_comm, orb_assoc, orb_false_r.
       auto with *.
   Qed.

Soundness lemmas
````````````````

.. coq::

   Lemma Eval_DNF_sound: forall v A,
     Eval_DNF v (NNFtoDNF (PropFtoNNF A)) = Eval_PropF v A /\
     Eval_DNF v (NNFtoDNF (PropFtoNNFN A)) = Eval_PropF v (Neg A).
   Proof.
     intros.
     induction A ; intuition.
     - simpl. rewrite Eval_DNF_AddClauses. rewrite H, H1 ; reflexivity.
     - simpl. rewrite Eval_DNF_app. rewrite H0, H2, negb_andb. reflexivity.
     - simpl. rewrite Eval_DNF_app. rewrite H, H1. reflexivity.
     - simpl. rewrite Eval_DNF_AddClauses. rewrite H0, H2, negb_orb.
       repeat rewrite Eval_PropF_Neg ; reflexivity.
     - simpl. rewrite Eval_DNF_app. rewrite H0, H1. rewrite Eval_PropF_Neg ; reflexivity.
     - simpl. rewrite Eval_DNF_AddClauses. rewrite H, H2. rewrite negb_orb, negb_involutive. rewrite Eval_PropF_Neg ; reflexivity.
     - simpl. rewrite H. rewrite negb_involutive ; reflexivity.
   Qed.

Rewriting of Disjunctive Normal Forms
-------------------------------------

DNF can be quite large, with redundant elements. In the following, we propose rewriting schemes and proof of equivalence for DNF clauses.

:coq:`Eval_DNF_Clause` evaluates a clause as the logical and of all literals.

Rule #1 [nodup]
```````````````

  A clause is a list of disjunctions, A ∧ A ∧ (...) evaluates to A ∧ ( .. ). In other words, one first simplification is to remove duplicates. This is captures in :coq:`DNF_Clause_Rewrite`. It is sound per lemma :coq:`DNF_Clause_Rewrite_Sound`.

  .. coq::

     Inductive DNF_red : relation (Clause) :=
     | red_nodup: forall (c: Clause),
       DNF_red c (nodup Literal_eq_dec c).

     Definition DNF_Clause_rewrite (c : Clause) :=
       nodup Literal_eq_dec c.

     Lemma Rewrite_DNF_red_Sound : forall v (c c': Clause),
       DNF_red c c'-> Eval_DNF_Clause v (DNF_Clause_rewrite c) = Eval_DNF_Clause v c'.
     Proof.
       intros.
       inversion H ; simpl ; try reflexivity.
     Qed.

     Lemma DNF_Clause_rewrite_sound: forall v c,
       Eval_DNF_Clause v c = Eval_DNF_Clause v (DNF_Clause_rewrite c).
     Proof.
       intros.
       unfold DNF_Clause_rewrite, Eval_DNF_Clause, nodup.
       induction c.
       - trivial.
       - destruct (in_dec Literal_eq_dec a c).
         * rewrite Eval_Clause_cons. rewrite <- IHc.
           assert (In (Eval_Literal v a) (Eval_Clause v c)).
           apply Eval_Clause_In ; apply i.
           rewrite In_andbl ; auto.
         * repeat rewrite Eval_Clause_cons.
           repeat rewrite andbl_cons. rewrite IHc ; reflexivity.
     Qed.

     Definition DNF_Rewrite_rule_1 (l : Clauses) :=
       (map (fun x => DNF_Clause_rewrite x) l).

     Lemma DNF_Rewrite_rule_1_cons: forall a l,
       DNF_Rewrite_rule_1 (a :: l) = DNF_Clause_rewrite a :: DNF_Rewrite_rule_1 l.
     Proof.
       intros.
       unfold DNF_Rewrite_rule_1. rewrite map_cons. reflexivity.
     Qed.

     Lemma DNF_Rewrite_rule_1_Sound: forall v l,
       Eval_DNF v l = Eval_DNF v (DNF_Rewrite_rule_1 l).
     Proof.
       intros.
       induction l.
       - simpl ; reflexivity.
       - rewrite DNF_Rewrite_rule_1_cons. repeat rewrite Eval_DNF_cons.
         rewrite IHl. rewrite DNF_Clause_rewrite_sound. reflexivity.
     Qed.

     Lemma DNF_Clause_rewrite_postcondition: forall c,
       NoDup (DNF_Clause_rewrite c).
     Proof.
       unfold DNF_Clause_rewrite.
       apply NoDup_nodup.
     Qed.

Unfortunately, this definition is purely axiomatic (because of :coq:`nodup`).

We introduce  :coq:`DNF_Clause_Rewrite'` as a variant of :coq:`DNF_Clause_Rewrite` that computes in Coq and is equivalent to the previous ones.

.. coq::

   Definition DNF_Clause_rewrite' c :=
     nodupb Literal_beq c.

   Lemma DNF_Clause_rewrite'_equiv: forall c,
     DNF_Clause_rewrite c = DNF_Clause_rewrite' c.
   Proof.
     intros.
     unfold DNF_Clause_rewrite, DNF_Clause_rewrite'.
     induction c ; auto.
     simpl.
     destruct (in_dec Literal_eq_dec a c) eqn:in_dec;
     destruct ( In_b Literal_beq a c) eqn:Inb.
     - apply IHc.
     - eapply (elimF (In_reflect  _ Literal_eq_reflect a c)) in Inb. contradiction.
     - eapply (elimT (In_reflect  _ Literal_eq_reflect a c)) in Inb. contradiction.
     - rewrite IHc ; auto.
   Qed.

   Lemma DNF_Clause_rewrite'_sound: forall v c,
     Eval_DNF_Clause v c = Eval_DNF_Clause v (DNF_Clause_rewrite' c).
   Proof.
     intros.
     rewrite DNF_Clause_rewrite_sound.
     rewrite DNF_Clause_rewrite'_equiv.
     auto.
   Qed.

   Lemma DNF_Clause_rewrite'_postcondition: forall c,
     NoDup (DNF_Clause_rewrite' c).
   Proof.
     intros.
     rewrite <- DNF_Clause_rewrite'_equiv.
     apply DNF_Clause_rewrite_postcondition.
   Qed.

   Definition DNF_Rewrite_rule_1' l :=
     (map (fun x => DNF_Clause_rewrite' x) l).

   Lemma DNF_Rewrite_rule_1_DNF_Rewrite_rule_1'_eq: forall l,
     DNF_Rewrite_rule_1 l = DNF_Rewrite_rule_1' l.
   Proof.
     intros.
     unfold DNF_Rewrite_rule_1, DNF_Rewrite_rule_1'.
     apply map_ext.
     apply DNF_Clause_rewrite'_equiv.
   Qed.

   Lemma DNF_Rewrite_rule_1'_Sound: forall v l,
     Eval_DNF v l = Eval_DNF v (DNF_Rewrite_rule_1' l).
   Proof.
     intros.
     unfold Eval_DNF.
     rewrite <- DNF_Rewrite_rule_1_DNF_Rewrite_rule_1'_eq.
     apply DNF_Rewrite_rule_1_Sound.
   Qed.

Rule #2 [absorption]
````````````````````

By the absorption laws, one can filter out some elements in a list of literals. A ∨ (A ∧ B ) evaluates to A.

Since we manipule clauses, this is equivalent to simplifying C1 ∨ C2 to C1 if C1 is included in C2.

.. coq::

   Definition filter_incl (c1 c2 : Clause) :=
       negb (inclb (Literal_beq) c1 c2
          && negb (Clause_beq c1 c2)).

   Definition filter_incl_p (c1 c2 : Clause) :=
     ~ ( incl c1 c2 /\ c1 <> c2 ).

   Lemma filter_incl_reflect : forall c1 c2,
     reflect (filter_incl_p c1 c2) (filter_incl c1 c2).
   Proof.
     intros.
     unfold filter_incl, filter_incl_p.
     apply (iffP idP) ;
       destruct (inclb Literal_beq c1 c2) eqn:Lbeq;
       destruct (Clause_beq c1 c2) eqn:Cbeq ; intros.

     - eapply (elimT (Clause_eq_reflect c1 c2)) in Cbeq.
       eapply (elimT (incl_reflect _ Literal_eq_reflect c1 c2)) in Lbeq.
       intuition.
     - eapply (elimF (Clause_eq_reflect c1 c2)) in Cbeq.
       eapply (elimT (incl_reflect _ Literal_eq_reflect c1 c2)) in Lbeq.
       intuition.
     - eapply (elimT (Clause_eq_reflect c1 c2)) in Cbeq.
       eapply (elimF (incl_reflect _ Literal_eq_reflect c1 c2)) in Lbeq.
       intuition.
     - eapply (elimF (Clause_eq_reflect c1 c2)) in Cbeq.
       eapply (elimF (incl_reflect _ Literal_eq_reflect c1 c2)) in Lbeq.
       intuition.
     - intuition.

     - contradiction H. eapply (elimF (Clause_eq_reflect c1 c2)) in Cbeq.
       eapply (elimT (incl_reflect _ Literal_eq_reflect c1 c2)) in Lbeq.
       intuition.
     - intuition.
     - intuition.
   Qed.

   Lemma filter_incl_dec: forall c1 c2,
     {filter_incl c1 c2} + {~filter_incl c1 c2}.
   Proof.
     intros.
     unfold filter_incl.
     destruct (inclb Literal_beq c1 c2 && ~~ Clause_beq c1 c2); intuition.
   Qed.

   Lemma filter_incl_false: forall (c1 c2 : Clause),
     filter_incl c1 c2 = false -> incl c1 c2.
   Proof.
     intros.
     unfold filter_incl in H.
     rewrite negb_andb in H.
     rewrite negb_involutive in H.

     assert (~~ inclb Literal_beq c1 c2 = false /\ Clause_beq c1 c2 = false).
     apply orb_false_elim, H.

     destruct H0.
     apply negb_false_iff in H0.
     eapply (elimT (incl_reflect _ Literal_eq_reflect c1 c2)) in H0.
     apply H0.
   Qed.

   Lemma filter_incl_true: forall (c1 c2 : Clause),
     filter_incl c1 c2 = true <-> ~ incl c1 c2 \/ c1 = c2.
   Proof.
     split ; intros.
     - unfold filter_incl in H.
       rewrite negb_andb in H.
       rewrite negb_involutive in H.

       assert (~~ inclb Literal_beq c1 c2 = true \/ Clause_beq c1 c2 = true).
       apply orb_prop, H.

       destruct H0.
       * apply negb_false_iff in H0.
         rewrite negb_involutive in H0.
         eapply (elimF (incl_reflect _ Literal_eq_reflect c1 c2)) in H0.
         left. apply H0.
       * right. eapply (elimT (Clause_eq_reflect c1 c2)) in H0. auto.
     - unfold filter_incl.
       rewrite negb_andb.
       rewrite negb_involutive.
       destruct H.
       * eapply (introF (incl_reflect _ Literal_eq_reflect c1 c2)) in H.
         rewrite H. intuition.
       * eapply (introT (Clause_eq_reflect c1 c2)) in H.
         rewrite H. auto with *.
   Qed.

   Lemma filter_not_incl_true: forall (c1 c2 : Clause),
      ~ incl c1 c2 -> filter_incl c1 c2 = true.
   Proof.
     intros.
     unfold filter_incl.
     rewrite negb_andb.
     rewrite negb_involutive.
     eapply (introF (incl_reflect _ Literal_eq_reflect c1 c2)) in H.
     rewrite H. intuition.
   Qed.

   Lemma filter_incl_false': forall (c1 c2 : Clause),
      incl c1 c2 /\ c1 <> c2 -> filter_incl c1 c2 = false.
   Proof.
     intros.
     unfold filter_incl.
     rewrite negb_andb.
     rewrite negb_involutive.
     destruct H.
     eapply (introT (incl_reflect _ Literal_eq_reflect c1 c2)) in H.
     rewrite H.
     eapply (introF (Clause_eq_reflect c1 c2)) in H0.
     rewrite H0.
     intuition.
   Qed.

   Lemma filter_incl_x: forall (c : Clause), filter_incl c c = true.
   Proof.
     intros.
     unfold filter_incl.
     rewrite negb_andb.
     rewrite negb_involutive.
     rewrite Clause_beq_idem.
     auto with *.
   Qed.

   Lemma filter_incl_l: forall x y l,
     In y (filter (λ y : Clause, ~~ filter_incl x y) l)
      -> incl x y.
   Proof.
     intros.
     assert (In y (filter (λ y : Clause, ~~ filter_incl x y) l)
             -> In y l ∧ ~~ filter_incl x y = true).
     apply filter_In.
     rewrite negb_true_iff in H0.
     apply H0 in H.
     destruct H.
     apply filter_incl_false ; auto.
   Qed.

   Definition rewrite_filtering'
     (x : Clause)
     (l : Clauses) :=
     if In_b Clause_beq x l then
       filter (fun y => filter_incl x y) l
     else l.

   Lemma filter_incl_x_in: forall x l,
     In x l ->
       In x (filter (λ y : Clause, filter_incl x y) l).
   Proof.
       intros.
       apply filter_In.
       split.
       - apply H.
       - apply filter_incl_x.
   Qed.

   Lemma rewrite_filtering'_sound1: forall v l x, NoDup x -> In x l ->
     Eval_DNF v l = Eval_DNF v (rewrite_filtering' x l).
   Proof.
     intros.
     unfold rewrite_filtering'.

     assert (Permutation l
       (filter (fun y => (filter_incl x y)) l ++
        filter (fun y => negb (filter_incl x y)) l)).
     apply filter_split.

     assert (Eval_DNF v l =
         Eval_DNF v  (filter (fun y => (filter_incl x y)) l ++
                      filter (fun y => negb (filter_incl x y)) l)).
     apply Eval_DNF_permut, H1.

     rewrite H2.
     rewrite Eval_DNF_app.

     assert (In x (filter (λ y : Clause, filter_incl x y) l)).
     apply filter_incl_x_in. apply H0.

     assert (exists l1 l2,
             (filter (λ y : Clause, filter_incl x y) l) = l1++x::l2).
     apply in_split. apply H3.

     destruct H4 as [l1 H4].
     destruct H4 as [l2 H4].

     rewrite H4 at 1.

     assert (Permutation (l1 ++ x :: l2) (x :: l1 ++ l2)).
     rewrite Permutation_middle. apply Permutation_refl.

     assert (Eval_DNF v (l1 ++ x :: l2) = Eval_DNF v ( x :: l1 ++ l2)).
     apply Eval_DNF_permut, H5.

     rewrite H6.
     rewrite Eval_DNF_cons.
     rewrite orb_middle.

     assert (
       Eval_DNF v (l1 ++ l2)
           || Eval_DNF_Clause v x
           || Eval_DNF v (filter (λ y : Clause, ~~ filter_incl x y) l)
     = Eval_DNF v (l1 ++ l2)
     || Eval_DNF v ( x :: (filter (λ y : Clause, ~~ filter_incl x y) l))
     ).
     rewrite Eval_DNF_cons. auto with *.

     rewrite H7.

     rewrite Eval_DNF_red_incl_l.

     rewrite orb_comm.
     rewrite Eval_DNF_singleton.
     rewrite <- Eval_DNF_cons.
     rewrite <- H6.
     rewrite <- H4.

     assert (In_b Clause_beq x l = true).
     eapply (introT (In_reflect _ Clause_eq_reflect x l)). apply H0.
     rewrite H8.
     reflexivity.

     apply H.

     intros.
     apply (filter_incl_l x x0 l).
     apply H8.
   Qed.

   Lemma rewrite_filtering'_sound2: forall v l x, NoDup x -> ~In x l ->
     Eval_DNF v l = Eval_DNF v (rewrite_filtering' x l).
   Proof.
     intros.
     unfold rewrite_filtering'.

     assert (In_b Clause_beq x l = false).
     eapply (introF (In_reflect _ Clause_eq_reflect x l)). apply H0.
     rewrite H1.
     reflexivity.
   Qed.

   Lemma rewrite_filtering'_sound: forall v l x, NoDup x ->
     Eval_DNF v l = Eval_DNF v (rewrite_filtering' x l).
   Proof.
     intros.
     destruct (in_dec Clause_eq_dec x l).
     - apply rewrite_filtering'_sound1. apply H. apply i.
     - apply rewrite_filtering'_sound2. apply H. apply n.
   Qed.

   Fixpoint min_cut_set_fix (l1 l2 : list (list Literal)) :=
       match l1 with
       | [] => l2
       | h :: t => rewrite_filtering' h (min_cut_set_fix t l2)
       end.

   Lemma min_cut_set_fix_sound: forall v l1 l2, l2 <> [] ->
     (forall x, In x l1 -> NoDup x) ->
       Eval_DNF v l2 = Eval_DNF v (min_cut_set_fix l1 l2).
   Proof.
     intros.
     induction l1.
     - intuition.
     - simpl.

       assert (NoDup a).
       specialize (H0 a). apply H0. auto with *.

       assert(Eval_DNF v (min_cut_set_fix l1 l2) =
               Eval_DNF v (rewrite_filtering' a (min_cut_set_fix l1 l2))).
       apply rewrite_filtering'_sound. apply H1.

       rewrite <- H2.
       apply IHl1.
       auto with *.
   Qed.

   Definition min_cut_set l := min_cut_set_fix l l.

   Lemma min_cut_set_sound: forall v l, l <> [] ->
     (forall x, In x l -> NoDup x) ->
       Eval_DNF v l = Eval_DNF v (min_cut_set l).
   Proof.
     intros.
     unfold min_cut_set.
     apply min_cut_set_fix_sound.
     apply H.
     apply H0.
   Qed.

Rule #3
```````

.. coq::

   Definition DNF_Rewrite_rule_3 (l : list Clause) :=
     nodup Clause_eq_dec l.

   Lemma DNF_Rewrite_rule_3_sound: forall v l,
     Eval_DNF v l = Eval_DNF v (DNF_Rewrite_rule_3 l).
   Proof.
     intros.
     unfold DNF_Rewrite_rule_3.
     unfold Eval_DNF.
     induction l.
     - simpl. reflexivity.
     - generalize (in_dec Clause_eq_dec a l).
       intros.
       destruct H.
       * rewrite In_nodup.
         rewrite map_cons.
         assert (In (Eval_DNF_Clause v a)
                   ( map (λ x : Clause, Eval_DNF_Clause v x) l)).
         apply in_map. apply i.
         rewrite In_orbl. apply IHl. apply H. apply i.
       * rewrite nodup_not_in.
         repeat rewrite map_cons. repeat rewrite orbl_cons.
         rewrite IHl at 1. reflexivity. apply n.
   Qed.

   Definition DNF_Rewrite_rule_3' (l : list Clause) :=
     nodupb Clause_beq l.

   Lemma DNF_Rewrite_rule_3_DNF_Rewrite_rule_3'_eq: forall l,
     DNF_Rewrite_rule_3' l = DNF_Rewrite_rule_3 l.
   Proof.
     intros.
     unfold DNF_Rewrite_rule_3, DNF_Rewrite_rule_3'.
     apply nodupb_sound.
     apply Clause_eq_reflect.
   Qed.

   Lemma DNF_Rewrite_rule_3'_Sound: forall v l,
     Eval_DNF v l = Eval_DNF v (DNF_Rewrite_rule_3' l).
   Proof.
     intros.

     rewrite DNF_Rewrite_rule_3_DNF_Rewrite_rule_3'_eq.
     apply DNF_Rewrite_rule_3_sound.
   Qed.

Minimal cutset of a DNF
```````````````````````

The combination of the three previous rules computes a minimum cutset from a :coq:`DNF`, and thus from a :coq:`PropF`. We define the supporting function and proofs of soundness.

.. coq::

   Definition DNF_cutset (l : list Clause) :=
     DNF_Rewrite_rule_3'
       (min_cut_set (DNF_Rewrite_rule_1' l)).

   Lemma DNF_cutset_sound: forall l v,
     l <> [] ->
       Eval_DNF v l = Eval_DNF v (DNF_cutset l).
   Proof.
     intros.
     unfold DNF_cutset.
     rewrite <- DNF_Rewrite_rule_3'_Sound.
     rewrite <- min_cut_set_sound.
     rewrite <- DNF_Rewrite_rule_1'_Sound.
     - reflexivity.
     - unfold DNF_Rewrite_rule_1'.
       contradict H. apply (map_eq_nil DNF_Clause_rewrite' l). apply H.
     - intros. unfold DNF_Rewrite_rule_1' in H0.
       apply in_map_iff in H0.
       destruct H0.
       destruct H0.
       subst.
       apply DNF_Clause_rewrite'_postcondition.
   Qed.

   Definition PropF_to_cutset p :=
      Rewrite_PropF_r (DNFtoPropF
       (DNF_cutset (NNFtoDNF (PropFtoNNF p)))).

   Lemma PropF_to_cutset_sound: forall v p,
     Eval_PropF v p = Eval_PropF v (PropF_to_cutset p).
   Proof.
     intros.
     unfold PropF_to_cutset.
     rewrite <- To_DNF_equiv_valid.
     unfold To_DNF.
     repeat rewrite Rewrite_PropF_r_Sound.
     repeat rewrite Eval_PropF_DNF.
     rewrite DNF_cutset_sound. reflexivity.
     apply NNFtoDNF_not_nil.
   Qed.

   Lemma is_Boolean_Expr_PropF_to_cutset: forall (bexpr : PropF),
       is_Boolean_Expr bexpr ->
           is_Boolean_Expr (PropF_to_cutset  bexpr).
   Proof.
       intros.
       unfold PropF_to_cutset.
       apply is_Boolean_Expr_Rewrite_PropF_r.
       apply is_Boolean_Expr_DNFtoPropF.
   Qed.

.. coq:: none

   End DNF.

   End Propositions.

Notations for :coq:`PropF`
--------------------------

The module :coq:`PropF_Notationa` exports notations used to represent Proposition formulas.

.. coq::

   Module PropF_Notations.
     Open Scope PropF_scope.

     Notation "A \/ B" := (Disj A B) (at level 85, right associativity) : PropF_scope.
     Notation "A ∨ B" := (Disj A B) (at level 85, right associativity) : PropF_scope.

     Notation "A /\ B" := (Conj A B) (at level 80, right associativity) : PropF_scope.
     Notation "A ∧ B" := (Conj A B) (at level 80, right associativity) : PropF_scope.

     Notation "~ A" := (Neg A) (at level 75, right associativity) : PropF_scope.
     Notation "¬ x" := (~x) (at level 75, right associativity) : PropF_scope.

     Notation "⊥" := Bot (at level 0)  : PropF_scope.
     Notation "⊤" := (¬ ⊥) (at level 0) : PropF_scope.

   End PropF_Notations.
