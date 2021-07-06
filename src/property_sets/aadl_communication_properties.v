(** %\section{\texttt{Communication\_Properties}} %*)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.coq_utils.utils.
Require Import Oqarina.properties.all.
Require Import Oqarina.property_sets.aadl_aadl_project.
Require Import Oqarina.aadl_categories.
(* end hide *)

Definition Communication_Properties_PS :=
    PropertySet (Id "Communication_Properties") [

    (* Overflow_Handling_Protocol: enumeration (DropOldest, DropNewest, Error)
       => DropOldest applies to (event port, event data port,
                                 subprogram access); *)

      "Overflow_Handling_Protocol" :prop PT_Enumeration [
        Id "DropOldest"; Id "DropNewest"; Id "Error" ]
        => (Some (PV_Enum (Id "DropOldest"))) applies [];

    (* Queue_Size: aadlinteger 0 .. Max_Queue_Size => 1
          applies to (event port, event data port, subprogram access); *)

    "Queue_Size" :prop aadlinteger
          => (Some (PV_Int 1%Z)) applies [  ]
    ].

(** %
  \begin{definition}[Queue\_Size (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Queue_Size_Name := PSQN "communication_properties" "queue_size".

Definition Is_Queue_Size (pa : property_association) :=
  Is_Property_Name Queue_Size_Name pa.

Definition Map_Queue_Size (pa : list property_association) : Z :=
    Map_PV_Int_List pa 1%Z Is_Queue_Size.

(** %
  \begin{definition}[Overflow\_Handling\_Protocol (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Overflow_Handling_Protocol_Name := PSQN "communication_properties" "overflow_handling_protocol".

Definition Is_Overflow_Handling_Protocol(pa : property_association) :=
  Is_Property_Name Overflow_Handling_Protocol_Name pa.

Inductive Overflow_Handling_Protocol :=
Overflow_Handling_Protocol_Unspecified | DropOldest | DropNewest | Error.
Scheme Equality for Overflow_Handling_Protocol.

Definition Map_Overflow_Handling_Protocol_pv (pa : property_association) : Overflow_Handling_Protocol :=
  match pa.(PV) with
    | (PV_Enum (Id "dropoldest")) => DropOldest
    | (PV_Enum (Id "dropnewest")) => DropNewest
    | (PV_Enum (Id "error")) => Error
    | _ => DropOldest
  end.

Definition Map_Overflow_Handling_Protocol (pa : list property_association) :=
  match filter Is_Overflow_Handling_Protocol pa with
  | nil => DropOldest
  | v :: _ => Map_Overflow_Handling_Protocol_pv v
  end.

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
