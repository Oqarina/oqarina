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
(* begin hide *)
(** Coq Library *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.core.all.
Require Export Oqarina.AADL.property_sets.aadl_project.
Require Export Oqarina.AADL.property_sets.deployment_properties.
Require Export Oqarina.AADL.property_sets.communication_properties.
Require Export Oqarina.AADL.property_sets.thread_properties.
Require Export Oqarina.AADL.property_sets.timing_properties.
(* end hide *)

(** [AADL_Predeclared_Property_Sets] lists all predeclared property sets. *)

Definition AADL_Predeclared_Property_Sets :=
    [ AADL_Project_PS ; Communication_Properties_PS ;
      Deployment_Properties_PS ;Thread_Properties_PS ; Timing_Properties_PS ] .

Lemma AADL_Predeclared_Properties_PS_Valid :
    typecheck_property_sets AADL_Predeclared_Property_Sets = true.
Proof.
    trivial.
Qed.

Fixpoint Get_AADL_Predeclared_Property_Set_Name' (ps : list property_set) (p : identifier) :=
    match ps with
    | nil => empty_identifier
    | h :: t => match in_propertyset p h with
                | Some _ =>  property_set_name  h
                | None => Get_AADL_Predeclared_Property_Set_Name' t p
                end
    end.

Definition Get_AADL_Predeclared_Property_Set_Name (p : string) :=
    (Get_AADL_Predeclared_Property_Set_Name' AADL_Predeclared_Property_Sets (Id p))->toString.
