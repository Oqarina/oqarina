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
(** * Some lemma on decidability using [sumbool]*)
Require Import Oqarina.coq_utils.list_utils.
(* begin hide *)
Section Sumbool_Decidability.
(* end hide *)

  (** The following defines a shortcut to use sumbool-based definition for decidability. See %\cite{appel2018software}%, chapter "Programming with Decision Procedures" for details. *)

  Variable A : Prop.
  Hypothesis HA : { A } + {~ A}.

  Variable B : Prop.
  Hypothesis HB : { B } + {~ B}.

  Definition dec_sumbool (P : Prop) := { P } + { ~ P }.

  Lemma dec_sumbool_and:  { A /\ B  } + { ~ (A /\ B) }.
  Proof.
      destruct HA , HB ;
        auto ||
        right; intuition.
  Defined.

  Lemma dec_sumbool_or:  { A \/ B  } + { ~ (A \/ B) }.
  Proof.
      destruct HA , HB ;
        auto ||
        right; intuition.
  Defined.

  Lemma dec_sumbool_not: dec_sumbool ( ~ A ).
  Proof.
      destruct HA.
      - right. auto.
      - left. auto.
  Defined.

(* begin hide *)
End Sumbool_Decidability.

Section Lists.
(* end hide *)
  Variable T : Type.
  Variable P : T -> Prop.
  Hypothesis HP' : forall t : T, {P t} + {~ P t}.

  Lemma sumbool_All_dec (l : list T): { All P l } + {~ All P l}.
  Proof.
    induction l.
    - unfold All. auto.
    - simpl. apply dec_sumbool_and.
      * apply HP'.
      * apply IHl.
  Qed.

(* begin hide *)
End Lists.
(* end hide *)