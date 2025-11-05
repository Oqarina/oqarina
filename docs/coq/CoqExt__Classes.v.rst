.. coq::


.. coq:: none

   Require Import Coq.Classes.SetoidClass.
   Require Import Coq.Relations.Relation_Definitions.
   Require Import Coq.Bool.Bool.

   Set Implicit Arguments.
   Set Strict Implicit.

   Section Classes.

Classes
=======

We define utility classes: setoid-based semigroup and commutative operator, and decision procedure.

.. coq::

   Class Setoid_SemiGroup (A : Type) (f : A -> A -> A) `{s: Setoid A} := {
       assoc_f : forall a b c : A, f a (f b c) == f (f a b) c
   }.

   Class Setoid_Commutative (A : Type) (f : A -> A -> A) `{s: Setoid A} := {
       commute_proof : forall a b : A, f a b == f b a
   }.

   Class Decision (P : Prop) := decide : {P} + {~P}. (* XXX use stdpp ? *)

:coq:`PreOrderDec` extends a preorder with a decidable relation and a helpful notation. It is built after :coq:`EqDec` from Coq's standard library.

.. coq::

   Class PreOrderDec (A: Type) (R: relation A) {preorder : PreOrder R} := {
       preorder_dec : forall x y: A, { R x y } + {~ R x y} }.

   Definition preorder_decb  (A: Type) `{PreOrderDec A} (x y : A) : bool :=
       if preorder_dec x y then true else false.

   Class EqDec2 (T: Type) :=
       { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }.

   Definition beq_dec {A} {EQ: EqDec2 A} a1 a2 : bool :=
       if eq_dec a1 a2 then true else false.

   Lemma beq_dec_iff {A} (EQ: EqDec2 A) a1 a2 :
       beq_dec a1 a2 = true <-> a1 = a2.
   Proof.
       unfold beq_dec; destruct eq_dec.
       - split ; trivial.
       - split; intros.
           + inversion H.
           + contradiction.
     Qed.

   Lemma beq_dec_false_iff {A} (EQ: EqDec2 A) a1 a2 :
       beq_dec a1 a2 = false <-> a1 <> a2.
   Proof.
       unfold beq_dec ; destruct eq_dec ; auto with *.
   Qed.

   Lemma beq_reflect {A} (EQ: EqDec2 A) x y: reflect (x=y) (beq_dec x y).
   Proof.
       intros.
       apply iff_reflect.
       split ; eapply beq_dec_iff.
   Qed.

.. coq:: none

   End Classes.

.. coq::

   Infix "b<=" := preorder_decb (no associativity, at level 70).
   (* XXX improve notation ?*)
