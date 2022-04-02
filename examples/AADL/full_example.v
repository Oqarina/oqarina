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

(*|

Basic concepts
==============

*Note:* the content of this tutorial is in :file:`examples/AADL/full_example.v`.

Being a Coq development, Oqarina leverages the fundamental features
of Coq, namely inductive types and lists. It allows reasonning on an AADL model, such as building proof out of an AADL model.

In this example, we review basic aspects of Oqarina to support modeling
with AADL. It assumes the reader has some familiarity with AADLv2.2 (see :cite:t:`DBLP:books/daglib/0030032` for a basic reference).

To use Oqarina, you will first import a collection of definitions from both the
Coq standard library, and Oqarina specific definitions.

*Note:* Oqarina defines a hierarchy of Coq modules. For each level, a :coq:`all` package provides a handy mechanism to import all definition within a hierarchy. |*)

(* Coq library *)
Require Import List.
Import ListNotations. (* from List *)

Require Import Coq.ZArith.ZArith.

(* Oqarina library *)
Require Import Oqarina.core.all. (* core definitions, identifier, time, etc. *)
Require Import Oqarina.AADL.all. (* AADL formalization. *)

(*| This following import makes visible  notations that ease
the construction of AADL model elements. |*)

Import AADL_Notations.
Open Scope aadl_scope.

(*| An AADL component instance is defined as an inductive type. It loosely follows the AADLv2 instance metamodel concepts. Some aspects are currently not addressed such as modes, others do not belong to the instance model such as arrays. |*)

Print ComponentCategory.
Print component.

(*| *Note: This level of modeling aims at capturing a fully instantiated model, for which all properties have been resolved, features are connected, etc. This level of abstraction is the root of most AADL analyses. It differs from the declarative modeling approach that is accessible from an AADL tool such as OSATE.* |*)

(*| Using Coq notation mechanism, Oqarina provides a direct way to model model elements. In the following, we create a periodic thread. |*)

Definition A_Periodic_Thread :=
    thread: "a_periodic_thread" ->| "pack::a_thread_classifier"
        features: nil
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==>| PV_Int 42 ;
            property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Periodic") ;
            property: Period_Name ==>| PV_IntU 3 (PV_Unit (Id "ms"))
        ].

(*| *Note:* Coq notations cannot overload existing symbols such as :coq:`->` or :coq:`=>`. So we use variations of these symbols here. |*)

(*| :coq:`A_Periodic_Thread` represents a periodic thread of period 3 ms, and priority 42. Oqarina provides a definition for a subset of AADL predeclared property sets. Coq provides the mechanism to review and locate these. |*)

Print AADL_Predeclared_Property_Sets.
Locate AADL_Predeclared_Property_Sets.

(*| Using Coq variables, one can then combine model elements to build a full hierarchy. Here, we define a process whose subcomponent is :coq:`A_Periodic_Thread`. |*)

Definition A_Process' :=
    process: "a_process" ->| "pack::a_process_classifier"
    features: nil
    subcomponents: [ A_Periodic_Thread ]
    connections: nil
    properties: [
        property: Actual_Processor_Binding_Name ==>|
            PV_ModelRef [ Id "a_processor" ]
    ].

(*| We then complete the model with a processor and a system. As part of the system definition, we bind the process :coq:`A_Process'` to the processor :coq:`A_Processor`. |*)

Definition A_Processor' :=
    processor: "a_processor" ->| "pack::a_processor_classifier"
    features: nil
    subcomponents: nil
    connections: nil
    properties: nil.

Definition A_System' :=
    system: "a_system" ->| "pack::a_system_classifier"
    features: nil
    subcomponents: [ A_Process' ; A_Processor' ]
    connections: nil
    properties: nil.

(*| The corresponding internal representation using native Coq inductive types is available also. You will note it is not as readable as the previous approach using notations. |*)
Compute A_System'.

(*| We show that the resulting system is well-formed. Oqarina provides several Coq tactics to discharge these obligations. Note that well-formedness rules are decidable, allowing for code extraction as well. |*)

Lemma a_system_wf :
    Well_Formed_Component_Instance A_System'.
Proof.
    prove_Well_Formed_Component_Instance.
Qed.

(*| Following a functional decomposition approach, :coq:`Well_Formed_Component_Instance` relies on a collection of short functions that check well-formedness of a model element by asserting each part is well-formed. This is illustrated by the following functions on can inspect. |*)

(*| A component instance is well-formed is equivalent to being a well-formed implementation. A well-formed implementation.

*Note:* :coq:`Unfold_Apply` is a helper function that will apply a function on the complete model hierarchy. |*)

Print Well_Formed_Component_Instance.
Print Well_Formed_Component_Implementation.
Print Well_Formed_Component_Implementation'.

(*| One can manipulate the model, e.g. to perform subcomponent resolution. |*)

Lemma Resolve_A_Processor:
    Resolve_Subcomponent
        A_System' (FQN [] (Id "a_processor") None) = Some A_Processor'.
Proof. trivial. Qed.

Lemma Resolve_A_Periodic_Thread:
    Resolve_Subcomponent
        A_System' (FQN [ Id "a_process" ] (Id "a_periodic_thread") None) =
        Some A_Periodic_Thread.
Proof. trivial. Qed.
