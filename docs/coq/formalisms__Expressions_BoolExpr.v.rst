.. coq::


.. coq:: none

   Require Import Coq.Bool.Bool.

Boolean Expressions
====================

We define boolean expressions (:coq:`bexp`) and associated evaluation functions.

.. coq::

   Inductive bexp : Type :=
     | TRUE
     | FALSE
     | NOT (b1: bexp)
     | AND (b1: bexp) (b2: bexp)
     | OR (b1: bexp) (b2: bexp).

   Fixpoint beval (b: bexp)  : bool :=
     match b with
     | TRUE => true
     | FALSE => false
     | NOT b1 => negb (beval b1)
     | AND b1 b2 => beval b1 && beval b2
     | OR b1 b2 => beval b1 || beval b2
     end.
