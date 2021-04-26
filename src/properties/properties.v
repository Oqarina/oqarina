Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import String.
Require Import ZArith.ZArith.

Open Scope string_scope.

Inductive identifier :=
| Id (name : string).

Definition eqb_id (id1 id2 : identifier): bool :=
  match id1, id2 with
  | Id s1, Id s2 => s1 =? s2
  end.

(*! Property Types *)

(* should we use this? *)
Inductive enumeration_literal :=
| EnumLiteral (name : identifier).

Definition enumeration_type :=
  list identifier.
(* ! unique identifiers *)

Inductive unit_literal :=
| BaseUnit (name : identifier)
| DerivedUnit (name : identifier) (base: identifier) (factor: nat).            

Definition units_type :=
  list unit_literal.
(* ! unique identifiers, derived unit consistency *)


Inductive property_type :=
| EnumerationType (literals : list identifier)
| UnitsType (units: units_type)
| NumberType (p: property_type) (* must be aadlinteger or aadlreal *)
(* range to limit values *)
             (units: option property_type) (* can be defined locally or reference units type *)
| RangeType (p : property_type)
| ClassifierType
| ReferenceType
| RecordType (fields: list field_decl)
| TypeRef (name : identifier) (* includes predef types aadlboolen, ... *)
with field_decl :=
| FieldDecl (name: identifier) (* list of? *) (type: property_type).

(* Predefined types *)
Definition aadlboolean := TypeRef (Id "aadlboolean").
Definition aadlstring := TypeRef (Id "aadlstring").
Definition aadlinteger := TypeRef (Id "aadlinteger").
Definition aadlreal := TypeRef (Id "aadlreal").

(* Examples *)

Check TypeRef (Id "aadlboolean") : property_type.
Check aadlboolean : property_type.
Check UnitsType [BaseUnit (Id "m"); DerivedUnit (Id "cm") (Id "m") 100] : property_type.
Check NumberType aadlinteger None : property_type.      
Check RangeType aadlinteger : property_type.      

Definition is_numeric_predef (p : property_type) : bool :=
  match p with
  | TypeRef (Id name) => eqb name "aadlinteger" || eqb name "aadlreal"
  | _ => false
  end.

Definition property_type_wf (t : property_type) : bool :=
  match t with
  | NumberType p _ => is_numeric_predef p
  | RangeType p => is_numeric_predef p
  (* FIX add more *)
  | _ => true
  end.

(*! Property Expressions and Values *)

Inductive property_value :=
| PV_Bool (b : bool)
| PV_String (s : string)
| PV_Int (n : nat) (unit : option identifier)
| PV_Real (r : nat) (unit : option identifier)
| PV_Enum (i : identifier)
| PV_Unit (i : identifier)
| PV_Range (min max : property_type)
| PV_Class (* TBD *)
| PV_Ref (* TBD *)
| PV_Record (* TBD *)
| PV_List (elements: list property_value)
| PV_Const (* TBD *)
| PV_Prop (* TBD *).

(*! Property Constants *)

(*! Property Definitions *)

(*! Property Sets *)

Inductive property_set_declaration :=
| PropertyTypeDecl (name : identifier) (type : property_type)
| PropertyConstantDecl (name : identifier) (type: property_type)
| PropertyDecl (name : identifier) (type: property_type)
               (*default: property_expression*)
               (*appliesTo : list identifier*).

Notation "s ':type' t" := (PropertyTypeDecl (Id s) t) (at level 75).
Notation "s ':const' t" := (PropertyConstantDecl (Id s) t) (at level 75).
Notation "s ':prop' t" := (PropertyDecl (Id s) t) (at level 75).


(*! AADL Model *)

Inductive model_unit :=
| PropertySet (name : identifier) (declarations : list property_set_declaration). 

Inductive aadl_model :=
| Model (modelUnits : list model_unit).

Definition my_model :=
  Model [
    PropertySet (Id "") [
                "aadlboolean" :type TypeRef (Id "");
                "aadlstring" :type TypeRef (Id "");
                "aadlinteger" :type TypeRef (Id "");
                "aadlreal" :type TypeRef (Id"")
    ];
    PropertySet (Id "PS1") [
    ]
  ].

(*! Type Checking *)

Check [Id "a"; Id "x"; Id "b"].

Compute @existsb (identifier) (eqb_id (Id "x")) [Id "a"; Id "x"; Id "b"].

Definition contains (t : property_type) (i : identifier) : bool  :=
  match t with
  | EnumerationType literals => existsb (eqb_id i) literals
  | _ => false
  end.

Definition In_Enum (id : identifier) (t : property_type) : Prop :=
  match t with
  | EnumerationType literals => In id literals
  | _ => False
  end.

Definition Is_Unit_Id (id : identifier) (unit : unit_literal) : Prop :=
  match unit with
  | BaseUnit uid
  | DerivedUnit uid _ _ => id = uid
  end.

Definition In_Units (id : identifier) (t : property_type) : Prop :=
  match t with
  | UnitsType units => Exists (Is_Unit_Id id) units
  | NumberType _ None => True
(*  | NumberType _ (Some units) => Exists (Is_Unit_Id id) units *)
  | _ => False
  end.

Definition Is_Decl_Type (id : identifier) (t : property_type) (d : property_set_declaration) : Prop :=
  match d with
  | PropertyTypeDecl id' t' => id' = id /\ t' = t 
  | _ => False
  end.

Definition In_PropertySet_Type (id : identifier) (t : property_type) (mu : model_unit) : Prop :=
  match mu with
  | PropertySet id' decls => Exists (Is_Decl_Type id t) decls
  end.

Definition In_Model_Type (id : identifier) (t : property_type) (m : aadl_model) : Prop :=
  match m with
  | Model model_units => Exists (In_PropertySet_Type id t) model_units
  end.

Fixpoint Is_Resolved' (n : nat) (m : aadl_model) (t: property_type) (r: property_type) : Prop :=
  match n with
  | 0 => False
  | S n' =>
    match t with
    | TypeRef (Id "aadlboolean") as t'
    | TypeRef (Id "aadlstring") as t'
    | TypeRef (Id "aadlinteger") as t'
    | TypeRef (Id "aadlreal") as t' => r = t'
    | TypeRef id => exists t', In_Model_Type id t' m -> r = t' \/ Is_Resolved' n' m t' r
    | _ => r = t
    end
  end.

Definition Is_Resolved := Is_Resolved' 10.

Inductive has_typeR' (t : property_type) : property_value ->  Prop :=
| HT_Bool (b : bool) :
    t = aadlboolean -> has_typeR' t (PV_Bool b)
| HT_String (s : string) :
    t = aadlstring -> has_typeR' t (PV_String s)
| HT_Int (n : nat) :
    t = NumberType aadlinteger None -> has_typeR' t (PV_Int n None)
| HT_Real (r: nat) (unit : option identifier) :
    t = NumberType aadlreal None -> unit = None -> has_typeR' t (PV_Real r unit)
| HT_Enum (i : identifier) :
    In_Enum i t -> has_typeR' t (PV_Enum i)
| HT_Unit (i : identifier) :
    In_Units i t -> has_typeR' t (PV_Unit i).

Reserved Notation "m '|-' v ':' t" (at level 60, v at next level).

Inductive has_typeR (m : aadl_model) (t : property_type) (v : property_value) : Prop :=
| HT_Resolved (r : property_type) :
    Is_Resolved m t r -> has_typeR' r v -> m |- v : t
where "m '|-' v ':' t" := (has_typeR m t v).

Example ehtR0: Model [] |- PV_Bool true : aadlboolean.
Proof.
  eapply HT_Resolved.
  - unfold Is_Resolved. simpl. reflexivity.
  - constructor. reflexivity.
Qed.

Example ehtR1: ~ (Model [] |- PV_Int 5 None : aadlstring).
Proof.
  intros H. inversion H.
  unfold Is_Resolved in H0. simpl in H0. subst.
  inversion H1. discriminate.
Qed.

Example ehtR2: Model [] |- PV_Int 5 None : NumberType aadlinteger None.
Proof.
    eapply HT_Resolved.
    - unfold Is_Resolved. simpl. reflexivity.
    - constructor. reflexivity.
Qed.

Example e_in: In (Id "x") [Id "x"; Id "y"].
Proof. repeat (try (left; reflexivity); right). Qed.

Definition Supported_Dispatch_Protocols := EnumerationType [Id "Periodic"; Id "Sporadic"; Id "Aperiodic"; Id "Timed"; Id "Hybrid"; Id "Background"].

Definition PS0 :=
  PropertySet (Id "PS0") [
      "Supported_Dispatch_Protocols" :type Supported_Dispatch_Protocols
    ].

Goal Model [] |- PV_Enum (Id "Sporadic") : Supported_Dispatch_Protocols.
Proof.
    eapply HT_Resolved.
    - unfold Is_Resolved. simpl. reflexivity.
    - apply HT_Enum. unfold In_Enum. simpl.
      repeat (try (left; reflexivity); right).
Qed.


Lemma l1: Is_Decl_Type (Id "Supported_Dispatch_Protocols") Supported_Dispatch_Protocols
     ("Supported_Dispatch_Protocols" :type Supported_Dispatch_Protocols).
Proof.
  split; reflexivity.
Qed.

Goal In_PropertySet_Type (Id "Supported_Dispatch_Protocols") Supported_Dispatch_Protocols PS0.
Proof.
  econstructor. apply l1.
Qed.
 
Goal In_Model_Type (Id "Supported_Dispatch_Protocols") Supported_Dispatch_Protocols (Model [PS0]).
Proof.
  repeat (econstructor; try (split; reflexivity)). 
Qed.

Example exht1: Model [PS0] |- PV_Enum (Id "Sporadic") : TypeRef (Id "Supported_Dispatch_Protocols").
Proof.
  econstructor.
  - econstructor. intros.
    inversion H.
    + inversion H1.
      * inversion H4. rewrite <- H7 in *. auto.
      * auto.
    + auto.
  - constructor. repeat (try (left; reflexivity); right).
Admitted. (* proof finished but Qed. doesn't work *)


