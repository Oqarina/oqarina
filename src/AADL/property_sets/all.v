(* begin hide *)
(** Coq Library *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.all.

Require Export Oqarina.AADL.property_sets.aadl_aadl_project.
Require Export Oqarina.AADL.property_sets.aadl_communication_properties.
Require Export Oqarina.AADL.property_sets.aadl_thread_properties.
Require Export Oqarina.AADL.property_sets.aadl_timing_properties.
(* end hide *)

(** [AADL_Predeclared_Property_Sets] lists all predeclared property sets. *)

Definition AADL_Predeclared_Property_Sets :=
    [ AADL_Project_PS ; Communication_Properties_PS ;
      Thread_Properties_PS ; Timing_Properties_PS ] .

Lemma Timing_Properties_PS_Valid :
    typecheck_property_sets AADL_Predeclared_Property_Sets = true.
  Proof.
    trivial.
  Admitted. (* See not on Communication_Properties_PS *)
