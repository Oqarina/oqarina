.. coq::


.. coq:: none

   (** Coq Library *)
   Require Import Coq.Logic.Decidable.
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Coq.Lists.ListDec.
   Require Import Coq.Bool.Sumbool.

   (** Oqarina library *)
   Require Import Oqarina.AADL.Kernel.component.

   Require Import Oqarina.core.all.
   Require Import Oqarina.coq_utils.all.

AADL package
------------

An AADL package is a named-list of AADL components.

.. coq:: none

   Section AADL_Package.

.. coq::

   Inductive package :=
       | Package : identifier -> list component -> package.

   (* From this definition; we also define a decidable equality principle, projection functions, etc. |*)

   Lemma package_eq_dec : eq_dec package.
   Proof.
       unfold eq_dec.
       repeat decide equality.
   Qed.

   Definition projectionPackageId (p : package) : identifier :=
       match p with
       | Package id _ => id
       end.

   Definition projectionPackageComponents (p : package) : list component :=
       match p with
       | Package  _ lp => lp
       end.

   #[global] Instance package_id : Element_id package := {|
       get_id := projectionPackageId;
   |}.

.. coq:: none

   End AADL_Package.

.. coq::

   Notation "p '->components' " := (projectionPackageComponents p)
       (at level 80, right associativity).
