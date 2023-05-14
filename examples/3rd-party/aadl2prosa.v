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

Scheduling Analysis of AADL with PROSA
======================================

*Note:* the content of this tutorial is in :file:`examples/3rd-party/aadl2prosa.v`.

In this tutorial, we use the PROSA Coq library. PROSA formalizes some key results in schedulability analysis :cite:`DBLP:conf/ecrts/BozhkoB20`. In particular, it allows one to conduct a response time analysis for mono-core fixed-priority systems directly in Coq.

In the following, we illustrate how to map an AADL model to a PROSA task set and then how to prove the task set is schedulable.

The setup is similar to the previous examples: we import Coq, PROSA, and Oqarina libraries.
|*)

(* Coq library *)
Require Import List.
Import ListNotations. (* from List *)

Require Import Coq.ZArith.ZArith.

(* PROSA library *)
Require Import prosa.implementation.refinements.FP.fast_search_space.
Require Import prosa.implementation.refinements.FP.refinements.
Require Import prosa.implementation.facts.job_constructor.
Require Import prosa.results.fixed_priority.rta.fully_preemptive.
Require Import prosa.implementation.refinements.FP.preemptive_sched.
Require Import NArith.

(* Oqarina library *)
Require Import Oqarina.core.all. (* core definitions, identifier, time, etc. *)
Require Import Oqarina.AADL.all. (* AADL formalization. *)

(*| This following import makes visible  notations that ease
the construction of AADL model elements. |*)

Import AADL_Notations.

(*|
Mapping AADL to PROSA overview
------------------------------

Our goal is to define a mapping from an AADL instance model to a PROSA task model. We proceed in three steps:

* define general well-formedness rules for AADL constructs, as a minimal set of information must be present in the model
* define PROSA-specific well-formedness rules: PROSA can only analyse a specific class of systems
* define the :coq:`Map_AADL_Root_System_to_PROSA_concrete_task_seq` mapping function.

As a goal, we want to offer this mapping iff the model matches all well-formedness rules. |*)

(*|
General well-formedness rules for scheduling
--------------------------------------------

Mapping an AADL component definition to a PROSA model is a rather straightforward process. PROSA defines the type :coq:`concrete_task` which is a record that captures a typical task specification, following Burns Scheduling Notation :cite:`10.1145/2597457.2597458`: :math:`\tau = \{C, T, D, P \}`.

We first define a general predicate that asserts that an AADL thread component is properly configured. For now, we consider that a thread is valid iff. the following properties are defined: :file:`Dispatch_Protocol`, :file:`Period`, :file:`Compute_Execution_Time`.

*Note:* We use the Resolute build-in functions ported to Coq to define predicates on AADL model elements, see :ref:`Resolute Queries` for more details.

*Note:* we might consider adding a predicate that checks that if the :file:`Deadline` property is set, then :math:`Deadline < Period`. However, this is not necessaary: PROSA does not need this hypothesis.

|*)

Definition Thread_Has_Valid_Scheduling_Parameters (c : component) :=
    is_thread c /\
    has_property c Dispatch_Protocol_Name /\
    has_property c Period_Name /\
    has_property c Compute_Execution_Time_Name.

(*| .. coq:: none |*)
Lemma Thread_Has_Valid_Scheduling_Parameters_dec: forall (c: component),
    { Thread_Has_Valid_Scheduling_Parameters c } +
    {~ Thread_Has_Valid_Scheduling_Parameters c}.
Proof.
    prove_dec.
Defined.
(*| .. coq:: |*)

(*| We now extend this definition to an AADL root system. Both predicates are trivially decidable. |*)

Definition System_Has_Valid_Scheduling_Parameters (r: component) :=
    All Thread_Has_Valid_Scheduling_Parameters (thread_set r).

(*| .. coq:: none |*)
Lemma System_Has_Valid_Scheduling_Parameters_dec: forall (r: component),
    { System_Has_Valid_Scheduling_Parameters r } +
    { ~ System_Has_Valid_Scheduling_Parameters r }.
Proof.
    prove_dec.
Defined.
(*| .. coq:: |*)

(*|
PROSA well-formedness rules for scheduling
------------------------------------------

In addition to these constraints, we place ourselves in the scope of the abstract RTA analysis provided by PROSA:

* the system is uniprocessor. |*)

Definition Is_Uniprocessor_System (r: component) :=
    List.length (processor_set r) = 1%nat.

(*| .. coq:: none |*)
Lemma Is_Uniprocessor_System_dec: forall (r: component),
    { Is_Uniprocessor_System r } + { ~ Is_Uniprocessor_System r }.
Proof.
    prove_dec.
    destruct (Datatypes.length (processor_set r)).
    auto.
    apply PeanoNat.Nat.eq_dec.
Defined.
(*| .. coq:: |*)

(*| * the system only uses fixed priority. |*)

Definition Is_Fixed_Priority (r: component) :=
    let procs := hd_error (processor_set r) in
    match procs with
        | None => False
        | Some proc => Map_Scheduling_Protocol (proc->properties) =
            POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL
    end.

(*|*Note:* this definition may seem incomplete: one could misuse the POSIX API
and have dynamic priority. However, a conforming code generation strategy from AADL would enforce fixed priority. |*)

(*| .. coq:: none |*)
Lemma Is_Fixed_Priority_dec: forall (r: component),
    { Is_Fixed_Priority r } + { ~ Is_Fixed_Priority r }.
Proof.
    prove_dec.
    destruct (hd_error (processor_set r) ).
    apply Scheduling_Protocol_eq_dec.
    apply Scheduling_Protocol_eq_dec.
Defined.
(*| .. coq:: |*)

(*|
General precondition for mapping an AADL model to PROSA
-------------------------------------------------------

Hence, a precondition for mapping an AADL model to a PROSA task set is that the previous well-formedness rules are checked.

|*)

Definition Check_aRTA_Hypotheses (r: component) :=
    System_Has_Valid_Scheduling_Parameters r /\
    Is_Uniprocessor_System r /\
    Is_Fixed_Priority r.

(*| .. coq:: none |*)
Lemma Check_aRTA_Hypotheses_dec: forall (r: component),
    { Check_aRTA_Hypotheses r } + { ~ Check_aRTA_Hypotheses r }.
Proof.
    intros.
    unfold Check_aRTA_Hypotheses.
    repeat apply dec_sumbool_and.
    apply System_Has_Valid_Scheduling_Parameters_dec.
    apply Is_Uniprocessor_System_dec.
    apply Is_Fixed_Priority_dec.
Defined.
(*| .. coq:: |*)

(*|
Mapping an AADL model to a PROSA taskset
----------------------------------------

PROSA defines a more general notion of arrival that replaces the notion of period in the previous model, it defines a general arrival prefix, in addition to periodic and sporadic arrival models. |*)

(*| We proceed in multiple basic steps: we map each AADL concept to the
corresponding concept in PROSA.

First, we map the AADL :file:`Dispatch_Protocol` property value to the
corresponding PROSA arrival bound. |*)

Definition Map_AADL_Dispatch_Protocol_to_PROSA_task_arrivals_bound
    (c: component)
    : task_arrivals_bound_T
:=
    let dispatch_protocol := Map_Dispatch_Protocol (c->properties) in
    match dispatch_protocol with
        | Periodic => Periodic_T
            (Z.to_N (Map_Period (c->properties)))

        | Sporadic => Sporadic_T
            (Z.to_N (Map_Period (c->properties)))

        | _ => ArrivalPrefix_T (0%N, [::(0%N, 0%N)])
    end.

(*| Then, :coq:`Map_AADL_Deadline_to_PROSA_deadline` extracts the deadline of a
thread. The deadlne may either be set explicitly by the property Deadline. if
not, we default to the period.
|*)

Definition Map_AADL_Deadline_to_PROSA_deadline (c: component) :=
    match Is_Property_Defined_dec Deadline_Name (c->properties) with
    | left _ => Z.to_N (Map_Deadline (c->properties))
    | right _ => Z.to_N (Map_Period (c->properties))
    end.

(*| Finally, we can define the general mapping function, first for
a thread component, then for a complete thread hierarchy. |*)

Definition Map_AADL_Thread_to_PROSA_concrete_task
    (c: component)
    : task_T
:= {|
    task_id_T := 0%N; (* dummy value, no semantics *)
    task_cost_T :=  Z.to_N (snd (Map_Compute_Execution_Time (c->properties)));
    task_arrival_T := Map_AADL_Dispatch_Protocol_to_PROSA_task_arrivals_bound c ;
    task_priority_T := Z.to_N (Map_Priority (c->properties));
    task_deadline_T := Map_AADL_Deadline_to_PROSA_deadline c
|}.

Definition Map_AADL_Root_System_to_PROSA_concrete_task_seq_unsafe
    (r : component)
:=
    map Map_AADL_Thread_to_PROSA_concrete_task (thread_set r).

(*| We have defined
:coq:`Map_AADL_Root_System_to_PROSA_concrete_task_seq_unsafe` as an unsafe
mapping function: this function does not check the validity of the model, it
blindly translates the model.

Thus, we define a variant that operates only on those models that match aRTA hypotheses: to call this function, one has to *prove* that the model is correct. |*)

Definition Map_AADL_Root_System_to_PROSA_concrete_task_seq
    (c: {c : component | Check_aRTA_Hypotheses c})
:=
    Map_AADL_Root_System_to_PROSA_concrete_task_seq_unsafe (proj1_sig c).

(*|

Fortunately, the burden of the proof is not an issue thanks to Coq automation.
See the example below.

Example
-------

AADL model and its mapping to a PROSA taskset
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In the following, we create an AADL task set that mimics one of the example provided in PROSA for validation purposes. The model is made of three tasks, the deadline is not specified. Following typical conventions, we assume the deadline to be equal to the period.

* :math:`\tau_1 = \{C = 100, T = 500, D = ., P = 3\}`.

|*)

(*| .. coq:: none |*)
Open Scope aadl_scope.
(*| .. coq:: |*)

Example Task_1 :=
    thread: "task_1" ->| "pack::a_thread_classifier.impl"
        extends: None
        features: nil
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==>| PV_Int 3 ;
            property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Periodic") ;
            property: Period_Name ==>| PV_IntU 500 (PV_Unit (Id "ms")) ;
            property: Compute_Execution_Time_Name ==>|
                PV_IntRange (PV_IntU 0 (PV_Unit (Id "ms")))
                            (PV_IntU 100 (PV_Unit (Id "ms")))
        ].

(*| * :math:`\tau_2 = \{C = 100, T = 500, D = ., P = 2\}`. |*)

Example Task_2 :=
    thread: "task_2" ->| "pack::a_thread_classifier.impl"
        extends: None
        features: nil
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==>| PV_Int 2 ;
            property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Periodic") ;
            property: Period_Name ==>| PV_IntU 500 (PV_Unit (Id "ms")) ;
            property: Compute_Execution_Time_Name ==>|
                PV_IntRange (PV_IntU 0 (PV_Unit (Id "ms")))
                            (PV_IntU 100 (PV_Unit (Id "ms")))
        ].

(*| * :math:`\tau_3 = \{C = 100, T = 500, D = ., P = 2\}`. |*)

Example Task_3 :=
    thread: "task_3" ->| "pack::a_thread_classifier.impl"
        extends: None
        features: nil
        subcomponents: nil
        connections: nil
        properties: [
            property: Priority_Name ==>| PV_Int 1 ;
            property: Dispatch_Protocol_Name ==>| PV_Enum (Id "Sporadic") ;
            property: Period_Name ==>| PV_IntU 500 (PV_Unit (Id "ms")) ;
            property: Compute_Execution_Time_Name ==>|
                PV_IntRange (PV_IntU 0 (PV_Unit (Id "ms")))
                            (PV_IntU 100 (PV_Unit (Id "ms")))
        ].

(*| All three tasks are colocated in the same process, and bound to the same
processor.|*)

Definition A_Process :=
    process: "a_process" ->| "pack::a_process_classifier.impl"
    extends: None
    features: nil
    subcomponents: [ Task_1 ; Task_2 ; Task_3 ]
    connections: nil
    properties: [
        property: Actual_Processor_Binding_Name ==>|
            PV_ModelRef [ Id "a_processor" ]
    ].

(*| An AADL processor is an abstraction of both a processor and the RTOS it
executes. We indicate the scheduling discipline used at the processor level. |*)

Definition A_Processor :=
    processor: "a_processor" ->| "pack::a_processor_classifier.impl"
    extends: None
    features: nil
    subcomponents: nil
    connections: nil
    properties: [
        property: Scheduling_Protocol_Name ==>|
        PV_Enum (Id "POSIX_1003_HIGHEST_PRIORITY_FIRST_PROTOCOL")
    ].

(*| :coq:`A_System` is the root system that we will consider when performing scheduling analysis. |*)

Definition A_System :=
    system: "a_system" ->| "pack::a_system_classifier.impl"
    extends: None
    features: nil
    subcomponents: [ A_Process ; A_Processor ]
    connections: nil
    properties: nil.

(*| .. coq:: none |*)
Close Scope aadl_scope.
(*| .. coq:: |*)

(*| First, we check that :coq:`A_System` is a well-formed AADL mode, i.e. the
containment hierarchy is respected, properties are correctly applied, etc. |*)

Lemma A_System_wf :
    Well_Formed_Component_Instance A_System.
Proof.
    prove_Well_Formed_Component_Instance.
Qed.

(*| Second, we check that :coq:`A_System` is well-formed and matches aRTA
hypotheses. The proof is trivial and we can brute-force it: we just need to
assess basic equalities.|*)

Lemma Check_aRTA_Hypothesis_A_System : Check_aRTA_Hypotheses A_System.
Proof.
    (* Compute all possible values *)
    compute.

    (* We have several basic conjunctions, we split and discharge them *)
    repeat split ; auto.
Qed.

(*| Finally, we can  map the AADL model *and its accompanying proofs* to
a PROSA task set. |*)

Definition ts_aadl :=
    Map_AADL_Root_System_to_PROSA_concrete_task_seq
    (exist _ A_System Check_aRTA_Hypothesis_A_System).

Compute ts_aadl.

(*|
Proof of schedulability
^^^^^^^^^^^^^^^^^^^^^^^

In this section, we illustrate how to finalize the verification that the model
is schedulable. PROSA expects the user to carry several proof to ultimately
demonstrate that the system is schedulable.

We unfold these steps. For more details, please refer to PROSA documentation.

*Note:* these proofs are likely to evolve as PROSA development team is actively
working on improving this part as part of the POET companion toolset that will generate proof scripts.

First, we build a clean version of the task set from :coq:`ts_aadl` through an explict evaluation.
|*)

Definition ts := Eval compute in ts_aadl.

(*| .. coq:: none |*)
(* We define this constant only to help in the hd below. *)
Definition null_tsk := {|
    task_id_T := 0%N;
    task_cost_T := 0%N;
    task_deadline_T := 0%N;
    task_arrival_T := Periodic_T 0%N ;
    task_priority_T := 0%N |}.
(*| .. coq:: |*)

(*| *Note:* In the following, we only prove that :coq:`tsk`, the first task in :coq:`ts_aadl`, is schedulable. The proof for the other tasks follows the same pattern.
|*)

#[local] Existing Instance ideal.processor_state.
#[local] Existing Instance fully_preemptive_job_model.
#[local] Existing Instance NumericFPAscending.

Definition tsk := Eval compute in hd null_tsk ts_aadl.

Definition L := 100%N. (* length of the busy interval *)
Definition R := 100%N. (* upper bound of the reponse time *)

(*| .. coq:: none |*)
Section Certificate.
(*| .. coq:: |*)

(* Becauae the notation "==" is defined in multiple contexts, we force a specific scope so that the next proofs can typecheck correctly. *)

Open Scope bool_scope.

(*| Proving the schedulability of the task set builds on the following intermediate results, see :cite:`DBLP:conf/ecrts/BozhkoB20` for more details. |*)

(*| 1. the arrival curve presented in the task set is valid, i.e. the arrival curve is a monotonic function. See the following definitions: |*)

Lemma arrival_curve_is_valid :
    valid_taskset_arrival_curve (map taskT_to_task ts) max_arrivals.
Proof.
    move => task IN.
    split.
    { repeat (move: IN; rewrite in_cons => /orP [/eqP -> | IN]); apply/eqP; last by done.
      all: rewrite /max_arrivals /MaxArrivals /MaxArrivals.
      all: by clear; rewrite [_ == _]refines_eq; vm_compute. }
    { repeat (move: IN; rewrite in_cons => /orP [/eqP -> | IN]); last by done.
      all: rewrite /max_arrivals /MaxArrivals /concrete_max_arrivals /task_arrival.
      have TR1 := leq_steps_is_transitive.
      all: apply extrapolated_arrival_curve_is_monotone;
        [ by apply/eqP/eqP; clear; rewrite [_ == _]refines_eq; vm_compute
        | by rewrite /sorted_leq_steps -[sorted _  _]eqb_id; clear;
          rewrite [_ == _]refines_eq; vm_compute ]. }
Qed.

(*| 2. the task set has valid arrivals. All our tasks are  periodic, this is therefore trivial. |*)

Lemma task_set_has_valid_arrivals:
    task_set_with_valid_arrivals (map taskT_to_task ts).
Proof.
    intros task IN.
    repeat (move: IN; rewrite in_cons => /orP [/eqP EQtsk | IN]); subst; last by done.
    all: try by (* apply/eqP/eqP; *) clear; rewrite [_ == _]refines_eq; vm_compute.
    all: by apply/valid_arrivals_P; rewrite [valid_arrivals _]refines_eq; vm_compute.
Qed.

(*| 3. :coq:`L` is a fixed-point of the total cost function of all higher-or equal-priority jobs. |*)

Lemma L_fixed_point:
    total_hep_rbf (map taskT_to_task ts) (taskT_to_task tsk) L = L.
Proof.
    rewrite /tsk; apply /eqP.
    by clear; rewrite [_ == _]refines_eq; vm_compute.
Qed.

(*| From these 3 initial results, we can now instantite the schedulabiltiy problem. First we build a couple of hypotheses from the task set. |*)

Variable arr_seq : arrival_sequence Job.
Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.
Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq (map taskT_to_task ts).
Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
Hypothesis H_valid_job_cost: arrivals_have_valid_job_costs arr_seq.
Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq (map taskT_to_task ts).

Instance sequential_ready_instance : JobReady Job (ideal.processor_state Job) :=
sequential_ready_instance arr_seq.

(*| We instantiate a uni-processor schedule from the set of Jobs generated by the task set. |*)

Definition sched := uni_schedule arr_seq.

(*| This intermediate lemma is purely technical, refer to section 3.7 of
:cite:`DBLP:conf/ecrts/BozhkoB20` for details. |*)

Lemma A_in_search_space:
    forall (A : duration),
        is_in_search_space (taskT_to_task tsk) L A ->
        A \in search_space_emax_FP (taskT_to_task tsk) L.
Proof.
    move => A IN.
    eapply search_space_subset_FP.
    - by apply task_set_has_valid_arrivals.
    - by clear; apply/eqP/eqP; clear; rewrite [_ == _]refines_eq; vm_compute.
    - by clear; rewrite !in_cons /tsk eq_refl.
    - rewrite mem_filter.
    apply /andP; split; first by done.
    by rewrite mem_iota; move: IN => /andP[LT _].
Qed.

Let Fs : seq N := [:: R%N].

(*| The following lemmas go further, first we assess that R is actually an upper bound for the response time.|*)

Lemma R_is_maximum:
    forall (A : duration),
        is_in_search_space (taskT_to_task tsk) L A ->
        exists (F : duration),
            task_rbf (taskT_to_task tsk) (A + ε) + total_ohep_rbf (map taskT_to_task ts) (taskT_to_task tsk) (A + F) <= A + F /\
            F <= R.
Proof.
    move => A SS; move: (A_in_search_space A SS) => IN; clear SS.
    move: A IN; apply forall_exists_implied_by_forall_in_zip with
    (P_bool := check_point_FP (map taskT_to_task ts) (taskT_to_task tsk) R).
    by intros; split; intros; apply/andP.
    exists (map nat_of_bin Fs); split.
    - by apply/eqP; clear; rewrite [_ == _]refines_eq; vm_compute.
    - by clear; rewrite [_ == _]refines_eq; vm_compute.
Qed.

Ltac find_refl :=
    match goal with
    | [  |-  (is_true (?X == ?X) ) \/ _ ] => left; apply eq_refl
    | _ => right
    end.

Theorem uniprocessor_response_time_bound_fully_preemptive_fp_inst:
    task_response_time_bound arr_seq sched (taskT_to_task tsk) R.
Proof.
    move: (sched_valid arr_seq) => [ARR READY].
    specialize (sequential_readiness_nonclairvoyance arr_seq) => NON_CL.
    eapply uniprocessor_response_time_bound_fully_preemptive_fp
    with (ts := (map taskT_to_task ts)) (H3 := concrete_max_arrivals) (L := L).
    - by done.
    - by done.
    - by done.
    - by apply arrival_curve_is_valid.
    - by done.
    - by rewrite !in_cons /tsk; repeat(apply/orP; find_refl).
    - by done.
    - by apply NFPA_is_reflexive.
    - by apply NFPA_is_transitive.
    - by apply uni_schedule_work_conserving.
    - by apply respects_policy_at_preemption_point.
    - by clear; rewrite [_ < _]refines_eq; vm_compute.
    - by symmetry; apply L_fixed_point.
    - by apply R_is_maximum.
Qed.

(*| The final conclusion is that all deadlines are respected, i.e., R is an upperbound of the response-time and this uppoer-bound is less than the task_deadline. |*)

Corollary deadline_is_respected:
    task_response_time_bound arr_seq sched (taskT_to_task tsk) R /\ R <= task_deadline (taskT_to_task tsk).
Proof.
    split.
    - by apply uniprocessor_response_time_bound_fully_preemptive_fp_inst.
    - by clear; rewrite [_ <= _]refines_eq; vm_compute.
Qed.

(*| .. coq:: none |*)
End Certificate.
(*| .. coq:: |*)
