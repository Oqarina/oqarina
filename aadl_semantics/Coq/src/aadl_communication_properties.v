(** %\section{\texttt{Communication\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)

(** AADL library *)
Require Import aadl_aadl_project.
Require Import utils.
(* end hide *)

(** ** %\texttt{Communication\_Properties}% as Coq native types

%
  \begin{definition}[IO\_Time\_Spec (Coq)]
 TBD. This version
  \end{definition} %
*)

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
Qed.

Definition projectionIO_Time_Spec (i : input_time) :=
  match i with
  | Input_Time t => t
end.
