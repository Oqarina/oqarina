(** %\section{\texttt{Communication\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.

(** Oqarina library *)
Require Import Oqarina.property_sets.aadl_aadl_project.
Require Import Oqarina.coq_utils.utils.
(* end hide *)

(** ** %\texttt{Communication\_Properties}% as Coq native types

%\define{Queue\_Processing\_Protocol (Coq)}{}{TBD} %
*)

Inductive Queue_Processing_Protocol :=
| FIFO.

(** %\define{IO\_Time\_Spec (Coq)}{}{TBD} % *)

Inductive IO_Time_Spec :=
| Dispatch
| Start : AADL_Time -> IO_Time_Spec
| Completion : AADL_Time -> IO_Time_Spec
| NoIo.

Scheme Equality for IO_Time_Spec.

Definition Default_IO_Time_Spec := Dispatch.

Inductive input_time :=
| Input_Time : list IO_Time_Spec -> input_time.

Lemma input_time_eq_dec : eq_dec input_time.
Proof.
  unfold eq_dec.
  decide equality.
  apply list_eq_dec; apply IO_Time_Spec_eq_dec.
Defined.

Definition projectionIO_Time_Spec (i : input_time) :=
  match i with
  | Input_Time t => t
end.

(** %\define{IO\_Time\_Spec Well-formedness rule (Coq)}{}
  {An input time is well-formed iff. there is no duplicate in the list of IO\_Time\_Spec.} %
*)

Definition input_time_wf  (i : input_time) :=
  NoDup (projectionIO_Time_Spec i).

Definition input_time_wf_dec : forall i : input_time, dec_sumbool (input_time_wf i).
Proof.
  unfold dec_sumbool.
  intros.
  unfold input_time_wf.
  apply NoDup_dec'.
  apply IO_Time_Spec_eq_dec.
Defined.
