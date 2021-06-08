Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

(*+ Identifiers *)

Inductive identifier :=
| Id (name : string).

Scheme Equality for identifier.

Lemma identifier_beq_eq: forall id1 id2,
    identifier_beq id1 id2 = true <-> id1 = id2.
Proof.
  split.
  - apply internal_identifier_dec_bl.
  - apply internal_identifier_dec_lb.
Qed.

Lemma id_beqP :  forall id1 id2,
    reflect (id1 = id2) (identifier_beq id1 id2).
Proof.
  intros. apply iff_reflect. symmetry. apply identifier_beq_eq.
Qed.

Inductive ps_qname :=
| PSQN (psname : string) (name : string).

Scheme Equality for ps_qname.
