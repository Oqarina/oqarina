(** %\chapter{\texttt{AADL\_Project}} %*)

(** Loose mapping of aadl_project.aadl to define common types, units, etc.

Some elemenets like Support_xxx enumerators are defined in the corresponding property set mappings. It does not make sense to separate them, and never ever do we want to allow them to be modified by the user
*)

Require Import time.

Definition AADL_Time : Type := NaturalTime.Time.