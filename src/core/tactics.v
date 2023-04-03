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

Require Import List.
Require Import Lists.ListDec.
Require Import Coq.Bool.Bool.

Require Export Oqarina.coq_utils.all.

(*| We define general tactics to prove decidability results. It is
made of two parts: a hint databse and a tactic.

* The database :coq:`well_known_dec` shall be populated with the non-trivial results necessary to conclude the proof.
|*)

Create HintDb well_know_wf_dec.

(*|

* :coq:`prove_dec` is a general tactic for decidability results {P x} + {~ P x }. It gathers most of the general pattern required to prove decidability results.

|*)

Ltac prove_dec :=
    repeat match goal with
    | [ |- forall x : ?T, _ ] => intros
    | [ |- dec_sumbool _ ] => unfold dec_sumbool
    | [ |- { In _ _ } + {~ In _ _ } ] => apply In_dec
    | [ |- { _ -> False } + { (_ -> False) -> False} ] =>
        apply dec_sumbool_not
    | [ |- { _ _ /\ _ _ } + {~ (_ _ /\ _ _)} ] =>
        apply dec_sumbool_and
    | [ |- { _ _ \/ _ _ } + {~ (_ _ \/ _ _)} ] =>
        apply dec_sumbool_or
    | [ |- {True} + {~ True} ] => auto
    | [ |- {All _ _} + {~ All _ _} ] => apply sumbool_All_dec
    | [ |- {?X _} + {~ ?X _} ] =>
        auto ; try auto with well_know_wf_dec ; unfold X
    | [ |- {?X _ _} + {~ ?X _ _} ] =>
        try auto with well_know_wf_dec ; unfold X
    | [ |- {?X _ _ _} + {~ ?X _ _ _} ] =>
        try auto with well_know_wf_dec ; unfold X
    | [ |- {?X _ _ _ _} + {~ ?X _ _ _ _} ] =>
        try auto with well_know_wf_dec ; unfold X

    | [ |- {NoDup _} + {~ NoDup _} ] => apply NoDup_dec
    | H : context [ match ?x with _ => _ end ] |- _ =>
        destruct x eqn:? ; auto
    | |- context [ match ?x with _ => _ end ] =>
        destruct x eqn:? ; auto
    | |- {_ = true} + {_  <> true} => apply bool_dec
    end.
