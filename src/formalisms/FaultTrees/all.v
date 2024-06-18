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

Require Export Oqarina.formalisms.FaultTrees.AbstractFaultTree.
Require Export Oqarina.formalisms.FaultTrees.StaticFaultTree.
Require Export Oqarina.formalisms.FaultTrees.DynamicFaultTree.
(*| .. coq:: |*)

(*|

***********
Fault Trees
***********

In this section, we provide a mechanization of fault trees.

* :doc:`formalisms__FaultTrees_AbstractFaultTree.v` provides generic definitions about fault trees.

* :doc:`formalisms__FaultTrees_StaticFaultTree.v` provides an instantiation for static fault trees.

* :doc:`formalisms__FaultTrees_DynamicFaultTree.v` provides an instantiation for dynamic fault trees.

Here is the detailed list of contents:

.. toctree::
   :maxdepth: 2

   formalisms__FaultTrees_AbstractFaultTree.v.rst
   formalisms__FaultTrees_StaticFaultTree.v.rst
   formalisms__FaultTrees_DynamicFaultTree.v.rst
|*)

(*| .. coq:: none |*)
Ltac prove_valid_static_fault_tree :=
    repeat match goal with
    | [ |- forall x : ?T, _ ] => intros t H ; destruct H ; subst
    | [ |- valid_static_fault_tree _ ] => unfold valid_static_fault_tree
    | [ |- valid_static_fault_tree' _ ] =>
        unfold valid_static_fault_tree' ; compute ; firstorder
    | [ |- valid_dynamic_fault_tree _ ] => unfold valid_dynamic_fault_tree
    | [ |- ltree_fall _ _ ] => apply ltree_fall_fix
    | [ |-  _ /\ _ ] => split
    | [ |- valid_static_fault_tree_node  _ _ ] => compute; auto
    | [ |- valid_dynamic_fault_tree_node  _ _ ] => compute; auto
    | [ H : In _ _ |- _ ] => destruct H ; subst
end.
(*| .. coq:: |*)
