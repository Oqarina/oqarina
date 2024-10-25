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

(*|
Oqarina Coq configuration
=========================

The following declarations "correct" the configuration of Coq to match our needs.

Because some Coq development exports configuration parameters to Oqarina documents, it is recommended this file is imported last.

|*)

Require Export Utf8.

Generalizable All Variables.

#[export] Set Universe Polymorphism.
#[export] Unset Universe Minimization ToSet.

(*| In the following, we control how goals in proof scripts are handled. We opted for a strict mode to ease proof readabiltiy. |*)
#[global] Set Default Goal Selector "1".
#[global] Set Bullet Behavior "Strict Subproofs". (* This is disabled by ssreflect *)

Definition fun_compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Notation " g ∘ f " := (fun_compose g f)
  (at level 40, left associativity).

Notation idmap := (λ x, x).

(*| Configure the solver for the :coq:`intuition` tactic. |*)
Ltac intuition_solver ::= auto with *.
