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

(** %\N \texttt{communication\_properties}% as Coq/AADL property_types. *)

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
          => (Some (PV_Int 1%Z)) applies [] ;

    (* IO_Reference_Time: type enumeration
        (Dispatch, Start, Completion, Deadline, NoIO, Dynamic); *)

    "IO_Reference_Time" :type PT_Enumeration [
      Id "Dispatch" ; Id "Start" ;  Id "Completion" ; Id "Deadline" ;
      Id "NoIO" ; Id "Dynamic" ];

    (* IO_Time_Spec: type record (
        Offset: Time_Range;
        Time: IO_Reference_Time; ); *)

    "IO_Time_Spec" :type PT_Record [
      FieldDecl (Id "Offset") (PT_TypeRef (PSQN "AADL_Project" "Time_Range")) ;
      FieldDecl (Id "Time")
        (PT_TypeRef (PSQN "Communication_Properties" "IO_Reference_Time")) ];

    (* Input_Time: list of IO_Time_Spec =>
        ([Time => Dispatch; Offset => 0 ns .. 0 ns;])
		    applies to (feature); *)

    "Input_Time" :prop PT_List
                  (PT_TypeRef (PSQN "Communication_Properties" "IO_Time_Spec"))
      => (Some (PV_List
                [ PV_Record [
                  FieldVal (Id "Time") (PV_Enum (Id "Dispatch")) ;
                  FieldVal (Id "Offset")
                      (PV_IntRange (PV_IntU 0 (PV_Unit (Id "ns")))
                                  (PV_IntU 0 (PV_Unit (Id "ns"))))
                     ]]))
        applies []

  ].

  Lemma Communication_Properties_PS_Valid :
    typecheck_property_sets [AADL_Project_PS ; Communication_Properties_PS] = true.
  Proof.
      trivial.
  Admitted. (* XXX cannot typecheck Input_Time, issue in checking the default value *)

(** %
  \begin{definition}[Queue\_Size (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Queue_Size_Name := PSQN "Communication_Properties" "Queue_Size".

Definition Is_Queue_Size (pa : property_association) :=
  Is_Property_Name Queue_Size_Name pa.

Definition Map_Queue_Size (pa : list property_association) : Z :=
    let pv := resolve_default_value [Communication_Properties_PS] Queue_Size_Name in
      match pv with
      | None => -1%Z (* should never be executed *)
      | Some pv_ => Map_PV_Int_List pa pv_ Is_Queue_Size
      end.

(** %
  \begin{definition}[Overflow\_Handling\_Protocol (AADLv2.2 \S XXX]
 TBD
  \end{definition}
% *)

Definition Overflow_Handling_Protocol_Name := PSQN "Communication_Properties" "Overflow_Handling_Protocol".

Definition Is_Overflow_Handling_Protocol(pa : property_association) :=
  Is_Property_Name Overflow_Handling_Protocol_Name pa.

Inductive Overflow_Handling_Protocol :=
Overflow_Handling_Protocol_Unspecified | DropOldest | DropNewest | Error.
Scheme Equality for Overflow_Handling_Protocol.

Definition Map_Overflow_Handling_Protocol_pv
  (pv : property_value) : Overflow_Handling_Protocol :=
  match pv with
    | (PV_Enum (Id "DropOldest")) => DropOldest
    | (PV_Enum (Id "DropnNewest")) => DropNewest
    | (PV_Enum (Id "Error")) => Error
    | _ => Overflow_Handling_Protocol_Unspecified
  end.

Definition Map_Overflow_Handling_Protocol (pa : list property_association) :=
  match filter Is_Overflow_Handling_Protocol pa with
  | nil =>
    let pv := resolve_default_value [
      Communication_Properties_PS] Overflow_Handling_Protocol_Name in
      match pv with
      | None => Overflow_Handling_Protocol_Unspecified
      | Some pv => Map_Overflow_Handling_Protocol_pv pv
      end
  | v :: _ => Map_Overflow_Handling_Protocol_pv v.(PV)
  end.

(** %\define{Queue\_Processing\_Protocol (Coq)}{}{TBD} %
*)

Inductive Queue_Processing_Protocol :=
| FIFO.

(** %\define{IO\_Time\_Spec (Coq)}{}{TBD} % *)

Inductive IO_Time_Spec :=
| Dispatch
| Start : AADL_Time -> IO_Time_Spec
| Completion : AADL_Time -> IO_Time_Spec
| NoIo
| IO_Time_Spec_Unspecified.

Scheme Equality for IO_Time_Spec.

Definition Unspecified_IO_Time_Spec := IO_Time_Spec_Unspecified.

Definition Map_IO_Time_Spec (pv : property_value) :=
  match pv with
  | PV_Record l =>
    let time := Get_Record_Member l (Id "Time") in
    match time with
    | None => Unspecified_IO_Time_Spec
    | Some (FieldVal (Id "Time") (PV_Enum (Id "Dispatch"))) => Dispatch
    | Some (FieldVal (Id "Time") (PV_Enum (Id "NoIo"))) => NoIo
    (** XXX TBD *)
    | _ => Unspecified_IO_Time_Spec
    end
  | _ => Unspecified_IO_Time_Spec
  end.

Fixpoint Map_IO_Time_Spec_list (pv : list property_value) :=
  match pv with
  | nil => nil
  | h :: t => Map_IO_Time_Spec h :: Map_IO_Time_Spec_list t
  end.

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

(** %\define{Input\_Time (Coq)}{}{TBD} % *)

Definition Input_Time_Name := PSQN "Communication_Properties" "Input_Time".

Definition Is_Input_Time (pa : property_association) :=
  Is_Property_Name Input_Time_Name pa.

Definition Unspecified_Input_Time := Input_Time [ ] .

Definition Map_Input_Time_pv (pv : property_value) :=
  match pv with
  | PV_List l => Input_Time (Map_IO_Time_Spec_list l)
  | _ => Unspecified_Input_Time
  end.

Definition Map_Input_Time (pa : list property_association) : input_time :=
  match filter Is_Input_Time pa with
  | nil =>
    let pv := resolve_default_value [Communication_Properties_PS] Input_Time_Name in
    match pv with
    | None => Unspecified_Input_Time (* should never be executed *)
    | Some pv_ => Map_Input_Time_pv pv_
    end
  | v :: _ => Map_Input_Time_pv v.(PV)
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
