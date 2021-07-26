(** %\section{\texttt{AADL\_Project}} %*)

(** Loose mapping of aadl_project.aadl to define common types, units, etc. *)

(* begin hide *)
(** Coq Library *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.core.identifiers.
Require Import Oqarina.core.time.
Require Import Oqarina.AADL.Kernel.all.
(* end hide *)

Definition AADL_Time : Type := Z.

Definition AADL_Project_PS :=
    PropertySet (Id "AADL_Project") [

    (* Supported_Dispatch_Protocols:
       type enumeration (Periodic, Sporadic, Aperiodic, Timed,
                         Hybrid, Background, Interrupt);
     *)

    "Supported_Dispatch_Protocols" :type PT_Enumeration [
        Id "Periodic"; Id "Sporadic"; Id "Aperiodic";
        Id "Timed"; Id "Hybrid"; Id "Background"
      ];

    (* Time_Units: type units (
        ps,
        ns => ps * 1000,
        us => ns * 1000,
        ms => us * 1000,
        sec => ms * 1000,
        min => sec * 60,
        hr => min * 60); *)

    "Time_Units" :type PT_Units [
       BaseUnit (Id "ps") ;
       DerivedUnit (Id "ns") (Id "ps") 1000 ;
       DerivedUnit (Id "us") (Id "ns") 1000 ;
       DerivedUnit (Id "ms") (Id "us") 1000 ;
       DerivedUnit (Id "sec") (Id "ms") 1000 ;
       DerivedUnit (Id "min") (Id "sec") 60 ;
       DerivedUnit (Id "hr") (Id "min") 60
    ];

    (* Time: type aadlinteger units Time_Units; *)

    "Time" :type PT_Number aadlinteger None
      (Some (PT_TypeRef (PSQN "AADL_Project_PS" "Time_Units")));

    (* Time_Range: type range of Time; *)

    "Time_Range" :type PT_Range
        (PT_TypeRef (PSQN "AADL_Project_PS" "Time_Units"))

  ].

Lemma AADLProject_PS_Valid : typecheck_property_sets [AADL_Project_PS] = true.
Proof.
    trivial.
Qed.

Definition Time_Range := (prod AADL_Time AADL_Time).

Definition Map_Time_Ramge (pv : property_value) : Time_Range :=
  match pv with
    | PV_IntRange (PV_Int min) (PV_Int max) => (min, max)
    | _ => (0, 0)
  end.
