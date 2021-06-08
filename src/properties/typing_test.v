Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

From ReductionEffect Require Import PrintingEffect.

Require Import identifiers.
Require Import properties.
Require Import typecheck.

(*! Tests for Type Checking *)

Check [Id "a"; Id "x"; Id "b"].

Compute @existsb (identifier) (identifier_beq (Id "x")) [Id "a"; Id "x"; Id "b"].

Example ehtR0: Model [] |- PV_Bool true ∈ aadlboolean.
Proof.
  eapply HT_Bool; reflexivity.
Qed.

Example ehtR1: ~ (Model [] |- PV_Int 5 ∈ aadlstring).
Proof.
  intros H. inversion H; discriminate.
Qed.

Example ehtR2: Model [] |- PV_Real 5 ∈ aadlreal.
Proof.
  eapply HT_Real; reflexivity.
Qed.

Compute Model [] |= PV_Real 5 ∈ aadlreal.

Definition Supported_Dispatch_Protocols :=
  PT_Enumeration [
      Id "Periodic"; Id "Sporadic"; Id "Aperiodic"; Id "Timed"; Id "Hybrid"; Id "Background"
    ].

Definition PS0 :=
  PropertySet (Id "PS0") [
                "Supported_Dispatch_Protocols" :type Supported_Dispatch_Protocols;
              "int0" :type aadlinteger;
              "int1" :type aadlinteger;
              "int00" :type PT_TypeRef (PSQN "PS0" "int0");
              "int10" :type PT_TypeRef (PSQN "PS0" "int1")
              ].

Definition PS1 :=
  PropertySet (Id "PS1") [
    "Time_Units" :type PT_Units [
       BaseUnit (Id "s")
    ];
    "Time" :prop PT_Number aadlreal None (Some (PT_TypeRef (PSQN "PS1" "Time_Units"))) => None
        applies [];
              "Supported_Distributions" :type PT_Enumeration [Id "Fixed"; Id "Uniform"];
              "Rate_Spec" :type PT_Record [
                        (FieldDecl (Id "Value_Range") (PT_Range aadlreal));
                        (FieldDecl (Id "Rate_Unit") (PT_Enumeration [Id "PerSecond"; Id "PerDispatch"]));
                        (FieldDecl (Id "Rate_Distribution") (PT_TypeRef (PSQN "PS1" "Supported_Distributions")))
                          ]

  ].

Definition M := Model [PS1; PS0].

Goal same_type M (PT_TypeRef (PSQN "PS0" "int00")) (PT_TypeRef (PSQN "PS0" "int10")) = true.
Proof. simpl. reflexivity. Qed.

Goal Model [] |- PV_Enum (Id "Sporadic") ∈ Supported_Dispatch_Protocols.
Proof.
  eapply HT_Enum; try reflexivity.
  econstructor; try reflexivity.
  repeat (try (left; reflexivity); right).
Qed.

Example ehtR3: Model [PS0] |- PV_Enum (Id "Sporadic") ∈ PT_TypeRef (PSQN "PS0" "Supported_Dispatch_Protocols").
Proof.
  eapply HT_TypeRef.
  - reflexivity.
  - esplit. split.
    + apply Exists_cons_hd. split.
      * reflexivity.
      * apply Exists_cons_hd. simpl. split; reflexivity.
    + reflexivity.
  - eapply HT_Enum.
    + reflexivity.
    + econstructor.
      * reflexivity.
      * repeat (try (left; reflexivity); right).
Qed.

Goal in_enum (Id "Sporadic") Supported_Dispatch_Protocols = true.
Proof. trivial. Qed.

Goal M |= PV_Enum (Id "Sporadic") ∈ Supported_Dispatch_Protocols = true.
Proof. trivial. Qed.

Compute M |= PV_Enum (Id "Sporadic") ∈ Supported_Dispatch_Protocols.

Example eht3 :
  M |= PV_Enum (Id "Sporadic") ∈
    PT_TypeRef (PSQN "PS0" "Supported_Dispatch_Protocols") = true.
Proof. trivial. Qed.

Compute resolve_type (Model [PS1])
        (PT_Number aadlreal None (Some (PT_TypeRef (PSQN "PS1" "Time_Units")))).

Compute resolve_type (Model [PS1]) (PT_TypeRef (PSQN "PS1" "Time_Units")).

Example eht4 :
  M |= PV_RealU 5 (PV_Unit (Id "s")) ∈
    PT_Number aadlreal None (Some (PT_TypeRef (PSQN "PS1" "Time_Units"))) = true.
Proof. trivial. Qed.

Definition MyRate :=
  PV_Record [
      (FieldVal (Id "Value_Range") (PV_RealRange (PV_Real 1) (PV_Real 2)));
      (FieldVal (Id "Rate_Distribution") (PV_Enum (Id "Uniform")))
    ].

Goal M |- MyRate ∈ PT_TypeRef (PSQN "PS1" "Rate_Spec").
Proof.
  eapply HT_TypeRef; try reflexivity.
  - esplit; split; try reflexivity.
    + apply Exists_cons_hd. split; try reflexivity.
      * repeat (try (apply Exists_cons_hd; split; reflexivity); apply Exists_cons_tl).
  - eapply HT_Record_hd; try split; try reflexivity.
    + eapply HT_RealRange; try eapply HT_Real; reflexivity.
    + eapply HT_Record_tl; try reflexivity.
      eapply HT_Record_tl; try reflexivity.
      eapply HT_Record_hd; try split; try reflexivity.
      eapply HT_TypeRef; try reflexivity.
      esplit; split; try reflexivity.
      apply Exists_cons_hd; split; try reflexivity.
      repeat (try (apply Exists_cons_hd; split; reflexivity); apply Exists_cons_tl).
      eapply HT_Enum; try reflexivity.
      econstructor; try reflexivity.
      repeat (try (left; reflexivity); right).
  all: eapply HT_Record_nil; try reflexivity.
Qed.

Compute (has_type' 10 M (PT_TypeRef (PSQN "PS1" "Rate_Spec")) MyRate).

Goal M |= MyRate ∈ PT_TypeRef (PSQN "PS1" "Rate_Spec") = true.
Proof. auto. Qed.


Compute typecheck_model M.
