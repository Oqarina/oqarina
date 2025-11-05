.. coq::


.. coq:: none

   (* Coq Library *)
   Require Import List.
   Import ListNotations. (* from List *)
   Require Import Floats. Open Scope float_scope.

   (* Oqarina Library *)
   Require Import Oqarina.formalisms.FaultTrees.all.
   Require Import Oqarina.formalisms.Expressions.Propositions.

Static Fault Tree Analysis
==========================

In this section, we illustrate some aspects of the Fault Tree Analsis capabilities. We present mapping of boolean expressions to cutset (:ref:`NUREG Example VII-10`), mapping of fault trees to cutset and proof of correctness (:ref:`Sample IMA Architecture` and :ref:`NUREG Example VIII-14`).

Note: in the following, we use Coq primitive floats (see :cite:t:`DBLP:conf/itp/BertholonMR19` for details) to represent the probability of occurence of some basic events. The rounding algorithms used to parse float values like 0.1 introduces some numerical discrepencies. We instruct Coq to silence those warnings and report differences from the original examples we used as a comparison.

.. coq::

   Set Warnings "-inexact-float".

NUREG Example VII-10
--------------------

In this module, we analyze the example from
:cite:`w.e.FaultTreeHandbook1981`, figure VII-10, pVII-16.

We model it as a boolean propositions and compute its minimal cutset.

.. coq:: none

   Module NUREG_Example_VII_10.

The definition os a fault tree requires a few steps

First, we define the basic events formally, as a collection of labels. We use Coq's notations to provide a nicer display.

.. coq::

   Inductive NUREG_Vars : Set := VarA | VarB | VarC.
   Scheme Equality for NUREG_Vars.

   Notation A := (Var VarA).
   Notation B := (Var VarB).
   Notation C := (Var VarC).

   Import PropF_Notations. (* Notations for boolean propositions *)

We define the gates for the fault tree from figure VII-10. Gate :coq:`T` is the top event.

.. coq::

   Definition E4 := A ∧ B.
   Definition E2 := C ∨ E4.
   Definition E3 := B ∨ C.
   Definition E1 := A ∨ E3.
   Definition T := E1 ∧ E2.

   Compute T. (* = (A ∨ B ∨ C) ∧ (C ∨ A ∧ B) *)

:coq:`T` is neither in DNF form nor in cutset. We compute these forms as intermediate steps.

.. coq::

   Compute To_DNF T.
   (* = A ∧ C ∨ A ∧ A ∧ B ∨ B ∧ C ∨ B ∧ A ∧ B ∨ C ∧ C ∨ C ∧ A ∧ B *)

   Compute PropF_to_cutset NUREG_Vars_beq T.
   (* A ∧ B ∨ C *)

We check this is consistent with the result provided p VIi-17.

.. coq::

   Lemma T_cutset_OK:
       (PropF_to_cutset NUREG_Vars_beq T) = (A ∧ B ∨ C).
   Proof. trivial. Qed.

   (* result : C ∨ (A ∧ B)*)

.. coq:: none

   End NUREG_Example_VII_10.

Sample IMA Architecture
-----------------------

This example is from the technical report
:cite:`siuSafeOptimalTechniques2019`, p12, section 4.1.1 "Example 1 – Sample IMA Architecture".

.. coq:: none

   Module Sample_IMA_Architecture.

In this example, we first define the fault tree of the system as a collection of basic events. :coq:`Basic_event_event_value` maps a basic_event to its probability of occurence.

.. coq::

   Open Scope float_scope.
   Import PropF_Notations.

   Inductive basic_event : Set :=
       IRU1 | IRU2 | IRU3 | RIU2 | RIU6 | RIU7 | NCD | GCD.

We define helper function for equality.

.. coq::

   Scheme Equality for basic_event.

   Lemma basic_event_reflect: forall x y : basic_event,
       Bool.reflect (x = y) (basic_event_beq x y).
   Proof.
       induction x, y ; simpl ; auto with *.
   Qed.

Actual definition of the basic event propability values and the fault tree.

.. coq::

   Definition basic_event_value ( p : basic_event) :=
       match p with
       | IRU1 | IRU2 | IRU3 | RIU2 | RIU6 | RIU7 => 1.0e-6
       | NCD | GCD => 2.0e-10
       end.

   Definition iru1 := ltree_cons (BASIC IRU1) [].
   Definition iru2 := ltree_cons (BASIC IRU2) [].
   Definition iru3 := ltree_cons (BASIC IRU3) [].

   Definition riu2 := ltree_cons (BASIC RIU2) [].
   Definition riu6 := ltree_cons (BASIC RIU6) [].
   Definition riu7 := ltree_cons (BASIC RIU7) [].

   Definition ncd := ltree_cons (BASIC NCD) [].
   Definition gcd := ltree_cons (BASIC GCD) [].

   Definition e2n1 := ltree_cons (OR _) [ riu2; riu6; riu7 ].
   Definition e2n2 := ltree_cons (OR _) [ iru1; e2n1 ].
   Definition e2n3 := ltree_cons (OR _) [ riu2; riu6; riu7 ].
   Definition e2n4 := ltree_cons (OR _) [ iru2; e2n3 ].
   Definition e2n5 := ltree_cons (OR _) [ riu2; riu6; riu7 ].
   Definition e2n6 := ltree_cons (OR _) [ iru3; e2n5].

   Definition mg := ltree_cons (K_OUT_OF_N _ 2) [e2n2 ;e2n4 ; e2n6].
   Definition slide165 := ltree_cons (OR _) [mg; ncd; gcd].

   Compute slide165.

This fault tree has a K_OUT_OF_N gate, we eliminate it.

.. coq::

   Definition slide165' := Expand_Fault_Tree' slide165.

We check that the fault tree is syntactically valid.

.. coq::

   Fact slide165_OK : valid_static_fault_tree' slide165'.
   Proof.
       prove_valid_static_fault_tree.
   Qed.

We map it to the corresponding boolean expressions

.. coq::

   Definition slide165_bool := Map_Fault_Tree_to_BoolExpr slide165'.
   Compute slide165_bool.

We can compute and display the corresponding cutset either as a boolean expression or as a fault tree.

.. coq::

   Definition slide165_cs_bool :=
       Map_Fault_Tree_to_Cutset_PropF basic_event_beq slide165'.
   Compute slide165_cs_bool.
   (* = Var IRU1 ∧ Var IRU2
       ∨ Var IRU1 ∧ Var IRU3
           ∨ Var IRU2 ∧ Var IRU3
           ∨ Var RIU2 ∨ Var RIU6 ∨ Var RIU7 ∨ Var NCD ∨ Var GCD *)

   Definition slide165_cs :=
       Map_Fault_Tree_to_Cutset basic_event_beq slide165.
   Compute slide165_cs.

   Lemma slide165_cs_ok: slide165_cs =
   ltree_cons (OR _)
       [ltree_cons (AND _)
       [ltree_cons (BASIC IRU1) []; ltree_cons (BASIC IRU2) []];
       ltree_cons (AND _)
       [ltree_cons (BASIC IRU1) []; ltree_cons (BASIC IRU3) []];
       ltree_cons (AND _)
       [ltree_cons (BASIC IRU2) []; ltree_cons (BASIC IRU3) []];
       ltree_cons (BASIC RIU2) []; ltree_cons (BASIC RIU6) [];
       ltree_cons (BASIC RIU7) []; ltree_cons (BASIC NCD) [];
       ltree_cons (BASIC GCD) []].
    Proof. trivial. Qed.

Finally, we check that the computed probability value is consistent.
*Note: we do not get the exact same value due to rounding introduced by Coq.*

.. coq::

   Lemma slide165_ok:
       Compute_Fault_Tree'' slide165_cs basic_event_value =
       Some 3.0004029999999996e-06.
   Proof. trivial. Qed.

.. coq:: none

   End Sample_IMA_Architecture.

NUREG Example VIII-14
---------------------

This example is derived from the Pressure Tank Example from the Fault Tree Handbook (NUREG-0492) :cite:`w.e.FaultTreeHandbook1981`, chapter VIII, figure VIII-14.

.. coq:: none

   Module NUREG0492_Example_VIII_14.

.. coq::

   Open Scope float_scope.
   Import PropF_Notations.

   Inductive basic_event := VarT | VarK2 | VarS | VarK1 | VarR | VarS1.

We define helper function for equality.

.. coq::

   Scheme Equality for basic_event.

   Lemma basic_event_reflect: forall x y : basic_event,
       Bool.reflect (x = y) (basic_event_beq x y).
   Proof.
       induction x, y ; simpl ; auto with *.
   Qed.

Actual definition of the basic event propability values and the fault tree.

.. coq::

   Definition basic_event_values (b : basic_event) :=
       match b with
           | VarT  => 5e-6
           | VarK2  => 3e-5
           | VarS  => 1e-4
           | VarK1  => 3e-5
           | VarR  => 1e-4
           | VarS1  => 3e-5
       end.

   Definition T := ltree_cons (BASIC VarT) [].
   Definition K2 := ltree_cons (BASIC VarK2) [].
   Definition S := ltree_cons (BASIC VarS) [].
   Definition K1 := ltree_cons (BASIC VarK1) [].
   Definition R := ltree_cons (BASIC VarR) [].
   Definition S1 := ltree_cons (BASIC VarS1) [].

   Definition E5 := ltree_cons (OR _) [ K1 ; R].
   Definition E4 := ltree_cons (OR _) [ S1 ; E5].
   Definition E3 := ltree_cons (AND _) [ S ; E4].
   Definition E2 := ltree_cons (OR _) [ E3 ; K2].
   Definition E1 := ltree_cons (OR _) [ T ; E2].

We prove that the fault tree is valid in :coq:`E1_OK`, map to its cutset and the cutset is correct (:coq:`E1_cs_OK`).

.. coq::

   Fact E1_OK : valid_static_fault_tree' E1.
   Proof.
       prove_valid_static_fault_tree.
   Qed.

   Definition E1_cs :=
       Map_Fault_Tree_to_Cutset basic_event_beq E1.
   Compute E1_cs.

   Lemma E1_cs_OK: forall (v: basic_event -> bool),
       Compute_Fault_Tree_2 E1 v= Compute_Fault_Tree_2 E1_cs v.
   Proof.
       unfold E1_cs.
       intros.
       apply Map_Fault_Tree_to_Cutset_sound.
       apply basic_event_eq_dec.
       apply basic_event_reflect.
       apply E1_OK.
   Qed.

The authors in  :cite:`w.e.FaultTreeHandbook1981` use some simplification heuristics and provide an approximation value of 3.4e-05. This example is also evaluated in :cite:`siuSafeOptimalTechniques2019`, section 4.1.2, p16. It conforms to the value we compute below.

.. coq::

   Lemma E1_value_OK : Compute_Fault_Tree'' E1_cs basic_event_values
                   = Some 3.5016000000000005e-05.
   Proof. trivial. Qed.

.. coq:: none

   End NUREG0492_Example_VIII_14.
