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
(** %\section{\texttt{Timing\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.AADL.Kernel.all.
Require Import Oqarina.AADL.property_sets.aadl_project.
(* end hide *)

(** %\N \texttt{timing\_properties}% as Coq/AADL property_types. *)

Definition Timing_Properties_PS :=
    PropertySet (Id "Timing_Properties") [

    (* Deadline: inherit Time => Period
		   applies to (thread, thread group, process, system, device,
                   virtual processor); *)

    "Deadline" :prop PT_TypeRef (PSQN "AADL_Project" "Time")
        => None applies [ CompCat thread ; CompCat threadGroup ; CompCat process ;
        CompCat system ; CompCat device ; CompCat virtualProcessor ];

    (* Period: inherit Time
       applies to (thread, thread group, process, system, device,
                   virtual processor); *)

    "Period" :prop PT_TypeRef (PSQN "AADL_Project" "Time")
        => None applies [ CompCat thread ; CompCat threadGroup ; CompCat process ;
        CompCat system ; CompCat device ; CompCat virtualProcessor ] ;

    (* 	Compute_Execution_Time: Time_Range
		    applies to (thread, device, subprogram, event port, event data port); *)

    "Compute_Execution_Time" :prop PT_TypeRef (PSQN "AADL_Project" "Time_Range")
      => None applies [ CompCat thread; CompCat device; CompCat subprogram ;
      FeatureCat eventPort ; FeatureCat eventDataPort]

  ].

Lemma Timing_Properties_PS_Valid :
  typecheck_property_sets [AADL_Project_PS ; Timing_Properties_PS] = true.
Proof.
  trivial.
Qed.

(**
%\paragraph{} \begin{definition}[Period (\S XXX]
 TBD
  \end{definition}% *)

Definition Period_Name := PSQN "Timing_Properties" "Period".

Definition Is_Period (pa : property_association) :=
  Is_Property_Name Period_Name pa.

Definition Map_Period (pa : list property_association) :=
  Map_PV_Int_List pa (PV_Int 0%Z) Is_Period.

(**
%\paragraph{} \begin{definition}[Deadline (\S XXX]
 TBD
  \end{definition}% *)

Definition Deadline_Name := PSQN "Timing_Properties" "Deadline".

Definition Is_Deadline (pa : property_association) :=
  Is_Property_Name Deadline_Name pa.

Definition Map_Deadline (pa : list property_association) : Z :=
  Map_PV_Int_List pa (PV_Int 0%Z) Is_Deadline.
