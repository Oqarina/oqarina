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

Require Export Oqarina.coq_utils.all.

(*| We define general tactics to prove basic decidability results. It is
made of two parts: a hint databse and a tactic. The database well_known_dec
shall be populated with the non-trivial results necessary to conclude the proof.
|*)

Create HintDb well_know_wf_dec.

(*| prove_dec is a general tactic for decidability results {P x} + {~ P x } |*)

Ltac prove_dec :=
    repeat match goal with
    | [ |- forall x : ?T, _ ] => intros
    | [ |- { _ _ /\ _ _ } + {~ (_ _ /\ _ _)} ] => apply dec_sumbool_and
    | [ |- {?X _} + {~ ?X _} ] =>
        try auto with well_know_wf_dec ; unfold X
    | [ |- {All _ _} + {~ All _ _} ] => apply sumbool_All_dec
    end.

Ltac prove_dec2 :=
    repeat match goal with
    | [ |- forall x : ?T, _ ] => intros
    | [ |- {?X _ _} + {~ ?X _ _} ] =>
        try auto with well_know_wf_dec ; unfold X
    | [ |- {All _ _} + {~ All _ _} ] => apply sumbool_All_dec
    end.
