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

(*| .. coq:: none |*)
(* Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Floats. Open Scope float_scope.

(* Oqarina Library *)
Require Import Oqarina.formalisms.FaultTrees.all.
Require Import Oqarina.formalisms.Expressions.all.

(*|

Static Fault Tree Analysis
==========================

Note: in the following, we use Coq primitive floats (see :cite:t:`DBLP:conf/itp/BertholonMR19` for details) to represent the probability of occurence of some basic events. The rounding algorithms used to parse float values like 0.1 introduces some numerical discrepencies. We instruct Coq to silence those warnings and report differences from the original examples we used as a comparison.
|*)

Set Warnings "-inexact-float".

(*|

NUREG Example VII-10
--------------------

In this module, we analyze the example from
:cite:`w.e.FaultTreeHandbook1981`, figure VII-10, pVII-16.

We model it as a boolean propositions and compute its minimal cutset.

|*)

(*| .. coq:: none |*)
Module NUREG_Example_VII_10.
(*| .. coq:: |*)

(*| The definition os a fault tree requires a few steps

First, we define the basic events formally, as a collection of labels. We use Coq's notations to provide a nicer display.

|*)

Inductive NUREG_Vars : Set := VarA | VarB | VarC.
Scheme Equality for NUREG_Vars.

Notation A := (Var VarA).
Notation B := (Var VarB).
Notation C := (Var VarC).

Import PropF_Notations. (* Notations for boolean propositions *)

(*|  We define the gates for the fault tree from figure VII-10. Gate :coq:`T` is the top event. |*)

Definition E4 := A ∧ B.
Definition E2 := C ∨ E4.
Definition E3 := B ∨ C.
Definition E1 := A ∨ E3.
Definition T := E1 ∧ E2.

Compute T. (* = (A ∨ B ∨ C) ∧ (C ∨ A ∧ B) *)

(*| :coq:`T` is neither in DNF form nor in cutset. We compute these forms as intermediate steps. |*)

Compute To_DNF T.
(* = A ∧ C ∨ A ∧ A ∧ B ∨ B ∧ C ∨ B ∧ A ∧ B ∨ C ∧ C ∨ C ∧ A ∧ B *)

Compute PropF_to_cutset NUREG_Vars_beq T.
(* A ∧ B ∨ C *)

(*| We check this is consistent with the result provided p VIi-17.|*)

Lemma T_cutset_OK:
    (PropF_to_cutset NUREG_Vars_beq T) = (A ∧ B ∨ C).
Proof. trivial. Qed.

(* result : C ∨ (A ∧ B)*)

(*| .. coq:: none |*)
End NUREG_Example_VII_10.
(*| .. coq:: |*)

(*|

Sample IMA Architecture
-----------------------

This example is from the technical report
:cite:`siuSafeOptimalTechniques2019`, p12, section 4.1.1 "Example 1 – Sample IMA Architecture". |*)

(*| .. coq:: none |*)
Module Sample_IMA_Architecture.
(*| .. coq:: |*)

(*| In this example, we first define the fault tree of the system as a collection of basic events. :coq:`Basic_event_event_value` maps a basic_event to its probability of occurence. |*)

Open Scope float_scope.
Import PropF_Notations.

Inductive basic_event : Set :=
    IRU1 | IRU2 | IRU3 | RIU2 | RIU6 | RIU7 | NCD | GCD.

Definition basic_event_value ( p : basic_event) :=
    match p with
    | IRU1 | IRU2 | IRU3 | RIU2 | RIU6 | RIU7 => 1.0e-6
    | NCD | GCD => 2.0e-10
    end.

Scheme Equality for basic_event.

Definition iru1 := in_tree (BASIC IRU1) [].
Definition iru2 := in_tree (BASIC IRU2) [].
Definition iru3 := in_tree (BASIC IRU3) [].

Definition riu2 := in_tree (BASIC RIU2) [].
Definition riu6 := in_tree (BASIC RIU6) [].
Definition riu7 := in_tree (BASIC RIU7) [].

Definition ncd := in_tree (BASIC NCD) [].
Definition gcd := in_tree (BASIC GCD) [].

Definition e2n1 := in_tree (OR _) [ riu2; riu6; riu7 ].
Definition e2n2 := in_tree (OR _) [ iru1; e2n1 ].
Definition e2n3 := in_tree (OR _) [ riu2; riu6; riu7 ].
Definition e2n4 := in_tree (OR _) [ iru2; e2n3 ].
Definition e2n5 := in_tree (OR _) [ riu2; riu6; riu7 ].
Definition e2n6 := in_tree (OR _) [ iru3; e2n5].

Definition mg := in_tree (K_OUT_OF_N _ 2) [e2n2 ;e2n4 ; e2n6].
Definition slide165 := in_tree (OR _) [mg; ncd; gcd].

(*| We check that the fault tree is syntactically valid. |*)

Fact slide165_OK : valid_static_fault_tree
    (Rewrite_Fault_Tree'' slide165).
Proof.
    prove_valid_static_fault_tree.
Qed.

Compute slide165.

(*| We map it to the corresponding boolean expressions |*)

Definition slide165_bool := Map_Fault_Tree_to_BoolExpr slide165.
Compute slide165_bool.

(*| We can compute and display the corresponding cutset either as a boolean expression or as a fault tree. |*)

Definition slide165_cs_bool :=
    Map_Fault_Tree_to_Cutset basic_event_beq slide165.
Compute slide165_cs_bool.
(* = Var IRU1 ∧ Var IRU2
    ∨ Var IRU1 ∧ Var IRU3
        ∨ Var IRU2 ∧ Var IRU3
        ∨ Var RIU2 ∨ Var RIU6 ∨ Var RIU7 ∨ Var NCD ∨ Var GCD *)

Definition slide165_cs :=
    Rewrite_Fault_Tree'' (Map_BoolExpr_to_Fault_Tree slide165_cs_bool).
Compute slide165_cs.

Lemma slide165_cs_ok: slide165_cs =
in_tree (OR _)
    [in_tree (AND _)
    [in_tree (BASIC IRU1) []; in_tree (BASIC IRU2) []];
    in_tree (AND _)
    [in_tree (BASIC IRU1) []; in_tree (BASIC IRU3) []];
    in_tree (AND _)
    [in_tree (BASIC IRU2) []; in_tree (BASIC IRU3) []];
    in_tree (BASIC RIU2) []; in_tree (BASIC RIU6) [];
    in_tree (BASIC RIU7) []; in_tree (BASIC NCD) [];
    in_tree (BASIC GCD) []].
 Proof. trivial. Qed.

(*| Finally, we check that the computed probability value is consistent.
*Note: we do not get the exact same value due to rounding introduced by Coq.* |*)

Lemma slide165_ok:
    Compute_Fault_Tree'' slide165_cs basic_event_value =
    Some 3.0004029999999996e-06.
Proof. trivial. Qed.

(*| .. coq:: none |*)
End Sample_IMA_Architecture.
(*| .. coq:: |*)

(*|

NUREG Example VIII-14
---------------------

This example is derived from the Pressure Tank Example from the Fault Tree Handbook (NUREG-0492) :cite:`w.e.FaultTreeHandbook1981`, chapter VIII, figure VIII-14.

|*)

(*| .. coq:: none |*)
Module NUREG0492_Example_VIII_14.
(*| .. coq:: |*)

Open Scope float_scope.
Import PropF_Notations.

Inductive basic_event := VarT | VarK2 | VarS | VarK1 | VarR | VarS1.
Scheme Equality for basic_event.

Definition basic_event_values (b : basic_event) :=
    match b with
        | VarT  => 5e-6
        | VarK2  => 3e-5
        | VarS  => 1e-4
        | VarK1  => 3e-5
        | VarR  => 1e-4
        | VarS1  => 3e-5
    end.

Definition T := in_tree (BASIC VarT) [].
Definition K2 := in_tree (BASIC VarK2) [].
Definition S := in_tree (BASIC VarS) [].
Definition K1 := in_tree (BASIC VarK1) [].
Definition R := in_tree (BASIC VarR) [].
Definition S1 := in_tree (BASIC VarS1) [].

Definition E5 := in_tree (OR _) [ K1 ; R].
Definition E4 := in_tree (OR _) [ S1 ; E5].
Definition E3 := in_tree (AND _) [ S ; E4].
Definition E2 := in_tree (OR _) [ E3 ; K2].
Definition E1 := in_tree (OR _) [ T ; E2].

Fact E1_OK : valid_static_fault_tree E1.
Proof.
    prove_valid_static_fault_tree.
Qed.

Definition E1_cs_bool :=
    Map_Fault_Tree_to_Cutset basic_event_beq E1.
Compute E1_cs_bool.

Definition E1_cs :=
    Rewrite_Fault_Tree'' (Map_BoolExpr_to_Fault_Tree E1_cs_bool).
Compute E1_cs.

(*| The authors in  :cite:`w.e.FaultTreeHandbook1981` use some simplification heuristics and provide an approximation value of 3.4e-05. This example is also evaluated in :cite:`siuSafeOptimalTechniques2019`, section 4.1.2, p16. It conforms to the value we compute below. |*)

Lemma E1_value_OK : Compute_Fault_Tree'' E1 basic_event_values
                = Some 3.5016000000000005e-05.
Proof. trivial. Qed.

(*| .. coq:: none |*)
End NUREG0492_Example_VIII_14.
(*| .. coq:: |*)
