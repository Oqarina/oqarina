.. coq::


.. coq:: none

   Require Import Category.Lib.
   Require Import Category.Construction.Product.
   Require Import Category.Theory.Category.
   Require Import Category.Theory.Isomorphism.
   Require Import Category.Theory.Functor.
   Require Import Category.Structure.Monoidal.

   Generalizable All Variables.

   Section SymmetricMonoidal.

Symmetric Monoidal Activities
=============================

We introduce a variant of the Symmetric Monoidal Category to use an Isomorphism instead of using a Braided category first.

.. coq::

   Context {C : Category}.

   Class SymmetricMonoidal := {

     symmetric_is_monoidal : @Monoidal C;

     braid {x y} : x ⨂ y ~> y ⨂ x;
     braid_isomorphism {x y} : @Isomorphism C (x ⨂ y) (y ⨂ x);

     hexagon_identity {x y z} :
       tensor_assoc ∘ braid ∘ tensor_assoc
         << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
       id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

   }.

   (*

   (* Proving that the other hexagon identify derives from the definition
   of SymmetricMoinoidal is left as an exercise for now. *)

   Context `{SymmetricMonoidal}.

   Lemma hexagon_identity_sym { x y z } :
       tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
         << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
       braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid.
   Proof.
   Admitted.

   *)

   End SymmetricMonoidal.
