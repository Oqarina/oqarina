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
(** Coq Library *)
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.Bool.Sumbool.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.component.

Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.
(*| .. coq::  |*)

(*|

AADL package
------------

An AADL package is a named-list of AADL components.
|*)

(*| .. coq:: none |*)
Section AADL_Package.
(*| .. coq::  |*)

Inductive package :=
    | Package : identifier -> list component -> package.

(* From this definition; we also define a decidable equality principle, projection functions, etc. |*)

Lemma package_eq_dec : eq_dec package.
Proof.
    unfold eq_dec.
    repeat decide equality.
Qed.

Definition projectionPackageId (p : package) : identifier :=
    match p with
    | Package id _ => id
    end.

Definition projectionPackageComponents (p : package) : list component :=
    match p with
    | Package  _ lp => lp
    end.

#[global] Instance package_id : Element_id package := {|
    get_id := projectionPackageId;
|}.

(*| .. coq:: none |*)
End AADL_Package.
(*| .. coq:: |*)

Notation "p '->components' " := (projectionPackageComponents p)
    (at level 80, right associativity).
