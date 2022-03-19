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
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.utils.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.property_sets.aadl_project.
(* end hide *)

(** %\N \texttt{communication\_properties}% as Coq/AADL property_types. *)

Definition Deployment_Properties_PS :=
    PropertySet (Id "Deployment_Properties") [

    (* Actual_Processor_Binding: inherit list of reference (processor, virtual processor, system, device, abstract)
		applies to (thread, thread group, process, system, virtual processor, device);*)

    "Actual_Processor_Binding" :prop PT_Reference
      => None applies [CompCat thread ; CompCat threadGroup ; CompCat process ; CompCat system ;
                       CompCat virtualProcessor ; CompCat device] ;

    (* Scheduling_Protocol: inherit list of Supported_Scheduling_Protocols
		applies to (virtual processor, processor, system);*)

    "Scheduling_Protocol" :prop PT_TypeRef (PSQN "AADL_Project" "Supported_Scheduling_Protocols")
        => None applies [ CompCat virtualProcessor; CompCat processor ; CompCat system ]

    ].

Lemma Deployment_Properties_PS_Valid :
  typecheck_property_sets [AADL_Project_PS ; Deployment_Properties_PS] = true.
Proof.
  trivial.
Qed.

Definition Actual_Processor_Binding_Name := PSQN "Deployment_Properties" "Actual_Processor_Binding".

Definition Is_Actual_Processor_Binding (pa : property_association) :=
  Is_Property_Name Actual_Processor_Binding_Name pa.
