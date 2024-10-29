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
Require Import Category.Lib.
Require Import Category.Construction.Product.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Section SymmetricMonoidal.
(*| .. coq:: |*)

(*|

Symmetric Monoidal Activities
=============================

We introduce a variant of the Symmetric Monoidal Category to use an Isomorphism instead of using a Braided category first.

|*)

Context {C : Category}.

Class SymmetricMonoidal := {
    
  symmetric_is_monoidal : @Monoidal C;

  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_isomorphism {x y} : @Isomorphism C (x ⨂ y) (y ⨂ x);

  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

}.

End SymmetricMonoidal.
