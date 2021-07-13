(* begin hide *)

(** Coq Library *)
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.Decidable.

(** Oqarina library *)
Require Import Oqarina.aadl_categories.
Require Import Oqarina.core.identifiers.
Require Import Oqarina.coq_utils.utils.
(* end hide *)

Open Scope Z_scope.
Open Scope string_scope.

Definition INT := Z.
Definition REAL := Z.

(*+ Property Types *)

(* should we use this? *)
Inductive enumeration_literal :=
| EnumLiteral (name : identifier).

Definition enumeration_type :=
  list identifier.
(* !!! unique identifiers *)

Inductive unit_literal :=
| BaseUnit (name : identifier)
| DerivedUnit (name : identifier) (base: identifier) (factor: nat).

Definition units_type :=
  list unit_literal.
(* !!! unique identifiers, derived/base unit consistency, factor int or real *)

Inductive int_range_constraint :=
  IRC (min max : INT).

Inductive real_range_constraint :=
  RRC (rmin rmax : REAL).

Inductive range_constraint :=
| C_IntRange (irc : int_range_constraint)
| C_RealRange (rrc : real_range_constraint).

(** XXX TODO
- wellformedness of a property set, of a property type
- property value correctly applies to a component
- add units to range constraints
- inherit?
- reference to property constant in proprety type? see aadl_thread_properties, definition of urgency
*)

Inductive property_type :=
(* Predeclared types are constructors for performance *)
| aadlboolean | aadlstring | aadlinteger | aadlreal
| PT_Enumeration (literals : list identifier)
| PT_Units (units : units_type)
| PT_Number (p : property_type) (* must be aadlinteger or aadlreal *)
            (range: option range_constraint)
            (units: option property_type)
| PT_Range (p : property_type) (* must be numeric *)
| PT_Classifier (* TBD *)
| PT_Reference (* TBD *)
| PT_Record (fields: list field_decl)
| PT_List (of: property_type) (* not allowed in named types in AADL2 (why???) *)
| PT_TypeRef (qname : ps_qname)
with field_decl :=
| FieldDecl (name: identifier) (type: property_type).

Lemma unit_literal_eq_dec : eq_dec unit_literal.
Proof.
  unfold eq_dec.
  decide equality ;
   apply identifier_eq_dec ||
   apply PeanoNat.Nat.eq_dec.
Qed.

Lemma units_type_eq_dec : eq_dec units_type.
Proof.
  unfold eq_dec.
  apply list_eq_dec.
  apply unit_literal_eq_dec.
Qed.

Lemma int_range_constraint_eq_dec (a b : int_range_constraint): {a=b}+{a<>b}.
Proof.
  decide equality;
  apply Z.eq_dec.
Qed.

Lemma real_range_constraint_eq_dec (a b : real_range_constraint): {a=b}+{a<>b}.
Proof.
  decide equality;
  apply Z.eq_dec.
Qed.

Lemma range_constraint_eq_dec (a b : range_constraint): {a=b}+{a<>b}.
Proof.
  decide equality.
  apply int_range_constraint_eq_dec.
  apply real_range_constraint_eq_dec.
Qed.

Local Hint Resolve units_type_eq_dec identifier_eq_dec range_constraint_eq_dec:core.

Lemma property_type_eq_dec (a b : property_type) : {a=b}+{a<>b}
  with field_decl_eq_dec (a b : field_decl): {a=b}+{a<>b}.
Proof.
  (* proof for property_type *)
  repeat decide equality.

  (* proof for field_decl_eq *)
  decide equality.
Qed.

(*! Examples *)

Check PT_TypeRef (PSQN "ps" "pt") : property_type.
Check aadlboolean : property_type.
Check PT_Units [BaseUnit (Id "m"); DerivedUnit (Id "cm") (Id "m") 100] : property_type.
Check PT_Number aadlinteger None None : property_type.
Check PT_Range aadlinteger : property_type.

Definition is_numeric_predef (p : property_type) : bool :=
  match p with
  | aadlinteger | aadlreal => true
  | _ => false
  end.

Inductive is_numeric_predefR : property_type -> Prop :=
| Predef_Int : is_numeric_predefR aadlinteger
| Predef_Real : is_numeric_predefR aadlstring.

Definition property_type_wf (t : property_type) : bool :=
  match t with
  | PT_Number p _ _ => is_numeric_predef p
  | PT_Range p => is_numeric_predef p
  (* !!! add more *)
  | _ => true
  end.

(*+ Property Expressions and Values *)

Inductive property_value :=
| PV_Bool (b : bool)
| PV_String (s : string)
| PV_Int (n : Z)
| PV_Real (r : REAL)
| PV_IntU (n : Z) (unit : property_value)
| PV_RealU (r : REAL) (unit : property_value)
| PV_Enum (i : identifier)
| PV_Unit (i : identifier)
| PV_IntRange (min max : property_value)
| PV_RealRange (min max : property_value)
| PV_IntRangeD (min max : property_value) (delta : property_value)
| PV_RealRangeD (min max : property_value) (delta : property_value)
| PV_PropertyRef (qname : ps_qname) (* ref to property or constant *)
| PV_Classifier (* TBD *)
| PV_ModelRef (path : list identifier)
| PV_Record (fields : list field_value)
| PV_List (elements: list property_value)
| PV_Computed (function : string)
with field_value :=
| FieldVal (name : identifier) (value : property_value).

Local Hint Resolve bool_dec string_dec Z.eq_dec ps_qname_eq_dec: core.

Lemma property_value_eq_dec (a b : property_value) : {a=b}+{a<>b}
with field_value_eq_dec (a b : field_value) : {a=b}+{a<>b}.
Proof.
  decide equality;
  apply list_eq_dec; auto || auto.

  decide equality.
Qed.

(*+ Property Sets *)

Inductive property_set_declaration :=
| PropertyTypeDecl (name : identifier) (type : property_type)
| PropertyConstantDecl (name : identifier) (type: property_type)
                       (value: property_value)
| PropertyDecl (name : identifier) (type: property_type)
               (default: option property_value)
               (appliesTo : list ComponentCategory).

Notation "s ':type' t" := (PropertyTypeDecl (Id s) t) (at level 75).
Notation "s ':const' t '=>' v" := (PropertyConstantDecl (Id s) t v)
                                   (at level 75, t at next level).
Notation "s ':prop' t '=>' d 'applies' a" :=
  (PropertyDecl (Id s) t d a)
    (at level 75, t at next level, d at next level, a at next level ).

Definition Applicable_ComponentCategory (p : property_set_declaration) :=
  match p with
  | PropertyDecl _ _ _ lcat => lcat
  | _ => nil
  end.

(** Property Association *)

(** %\begin{definition}[Property association]
A property association binds a property value to a property type.
  \end{definition} %

  XXX this seems incomplete, we need to fetch the corresponding PropertyDecl to get default and appliesTo field. either resolve, or change the definition.
  *)

Record property_association := {
    P : ps_qname;
    PV : property_value }.

Lemma property_association_eq_dec (a b : property_association): {a=b}+{a<>b}.
Proof.
  decide equality.
  apply property_value_eq_dec.
Qed.

(*! AADL Property set *)

Inductive property_set :=
| PropertySet (name : identifier) (declarations : list property_set_declaration).

Definition property_sets := list property_set.
