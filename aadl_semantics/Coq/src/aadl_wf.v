(** %\chapter{Well-formedness rules of an AADL model}\label{chap::aadl_wf}% *)

(* begin hide *)

(** Coq Library *)
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.ListDec.

(** AADL library *)

Require Import aadl.
Require Import identifiers.
Require Import utils.
(* end hide *)

(**

In this section, we define several well-formedness rules for model elements.

For each rule, we define a basic predicate that operate on a component only,
without recursion. We demonstrate that this predicate is decidable.

*)
(* begin hide *)
Section WellFormedness_Rules.
(* end hide *)

  (** * Generic rules

  The AADL language defines some basic rules that are evaluated during the
  parsing of the model itself. We define them as a first validation step:
   any component validates these rules.

  *)

  (** ** Well-formedness of component identifiers *)

  (** A component identifier is well-formed iff. the identifier is well-formed. *)

  Definition Well_Formed_Component_Id (c : component) : Prop :=
    (Well_Formed_Identifier_prop (c->id)).

  (** Well_Formed_Component_Id is a decidable property. *)

  Lemma Well_Formed_Component_Id_dec : forall c : component,
    { Well_Formed_Component_Id c } + {~ Well_Formed_Component_Id c }.
  Proof.
    (* Hint: this is a direct consequence of the decidability of the
       well-formedness rule of identifiers *)
    intros.

    (* unfold the various definitions *)
    unfold dec_sumbool.
    unfold Well_Formed_Component_Id.

    (* apply decidability result on Identifier *)
    apply Well_Formed_Identifier_prop_dec.
  Qed.

  (** _Note: we add this result to the core hint database. Hence, we can
    use the "auto" tactics instead of "apply foo_dec"_.
    *)
  Hint Resolve Well_Formed_Component_Id_dec : core.

  (** ** Properties type checking rules *)

  (** In the previous sectionm we have defined property types and property values.
      The following illustrate how to use them.

      First, we define the %\textsc{Source\_Language}% property, then a value and finallly a subprogram that uses it.

      %\begin{lstlisting}
      subprogram hello_world
      properties
        Source_Language => C;
      end hello_world;
      \end{lstlisting}%

  This corresponds to the following Coq formalization:

      *)

  Definition Source_Language : property_type :=
    Property_Type [ subprogram ] aadlstring_t.

  Definition A_Source_Language :=
    Property_Value Source_Language (aadlstring (Ident "C")).

  Definition A_Subprogram :=
    Component (Ident "Hello_World") (subprogram) (Ident "spg") nil nil
    [A_Source_Language] nil.

  (** From this example, we can deduce the two rules to check:
  - a property value is well-formed
  - a property value is correctly applied. *)

  (** A property value is well-formed iff the base type of its corresonding property type
  matches the type of the value of the property. *)

  Definition Well_Formed_Property_Value (p : property_value) : Prop :=
  match Get_Base_Value p with
  | aadlstring _ => Base_Type (Get_Property_Type p) = aadlstring_t
  | aadlboolean _  => Base_Type (Get_Property_Type p) = aadlboolean_t
  | aadlinteger _  => Base_Type (Get_Property_Type p) = aadlinteger_t
  | aadlreal _  => Base_Type (Get_Property_Type p) = aadlreal_t
  | aadllist _ => False (* TBD *)
  | aadlrecord _ => False (* TBD *)
  end.

  Lemma Well_Formed_Property_Value_dec : forall p : property_value,
    dec_sumbool (Well_Formed_Property_Value p).
  Proof.
    intros.
    unfold dec_sumbool.
    unfold Well_Formed_Property_Value.
    destruct (Get_Property_Type p).

    (* produce trivial goals for each possible value that are either an
    equality or False, previous decidability results terminate those proofs.
    *)
    destruct (Get_Base_Value p);
      unfold Base_Type; apply Property_Base_Type_eq_dec || auto.
  Qed.

  Definition Property_Correctly_Applies_To (c : component) (p : property_value) :=
    In (c->category) (Applicable_ComponentCategory (Get_Property_Type p)).

  Lemma Property_Correctly_Applies_To_dec :
    forall (p : property_value) (c : component),
        { Property_Correctly_Applies_To c p  } + { ~ Property_Correctly_Applies_To c p } .
  Proof.
    intros p c.
    unfold Property_Correctly_Applies_To.
    apply in_dec.
    unfold eq_dec.
    apply ComponentCategory_eq_dec.
  Qed.

  (** In pure functional language fashion, we introduce intermediate functions that operates
    first on lists of %\coqdocvar{property\_value}%, then on the component itself.
    Such modularity eases the construction of proofs.
    *)

  Definition List_Property_Correctly_Applies_To
    (lp : list property_value) (c : component) :=
      All (Property_Correctly_Applies_To c) lp.

  Lemma List_Property_Correctly_Applies_To_dec :
    forall (lp : list property_value) (c : component),
      { List_Property_Correctly_Applies_To lp c } + { ~ List_Property_Correctly_Applies_To lp c }.
  Proof.
    unfold List_Property_Correctly_Applies_To.
    intros.
    apply sumbool_All_dec.
    intros.
    apply Property_Correctly_Applies_To_dec.
  Qed.

  Definition Well_Formed_Properties (c : component) : Prop :=
    List_Property_Correctly_Applies_To (c->properties) c .

  Lemma Well_Formed_Properties_dec :
    forall (c:component), { Well_Formed_Properties c } + {~Well_Formed_Properties c}.
  Proof.
    unfold dec_sumbool.
    unfold Well_Formed_Properties.
    intros.
    apply List_Property_Correctly_Applies_To_dec.
  Qed.

  Hint Resolve Well_Formed_Properties_dec : core.

  (** * AADL legality and consistency rules *)

  (** ** Naming rule 4.5 (N1) *)
  (** 4.5 (N1) The defining identifier of a subcomponent declaration placed in a
  component implementation must be unique within the local namespace of the
  component implementation that contains the subcomponent.

  _Hint: In other words, the list of identifiers built from the list of subcomponents has no duplicates_.

  First, we define a predicate on list of subcomponents, and demonstrate it is decidable.

  *)

  Definition Subcomponents_Identifiers_Are_Well_Formed (l : list component) : Prop :=
    (NoDup (Components_Identifiers l)).

  Lemma Subcomponents_Identifiers_Are_Well_Formed_dec :
    forall l : list component,
      dec_sumbool (Subcomponents_Identifiers_Are_Well_Formed l).
  Proof.
    intros.

    (* unfold the various definitions *)
    unfold dec_sumbool.
    unfold Subcomponents_Identifiers_Are_Well_Formed.

    apply NoDup_dec. (* NoDup is decidable, from Coq.Lists.ListDec *)

    (* Last bit is to rely on identifier equality being also decidable *)
    unfold decidable_eq. (* from Coq.Lists.ListDec *)
    apply identifier_eq_dec. (* from utils *)
  Qed.

  (** We can now "implement" the predicate for rule 4.5 (N1) *)

  Definition Rule_4_5_N1 (c : component) : Prop :=
    Subcomponents_Identifiers_Are_Well_Formed (c->subcomps).

  Lemma Rule_4_5_N1_dec :
    forall c : component, { Rule_4_5_N1 c } + { ~ Rule_4_5_N1 c } .
  Proof.
    unfold Rule_4_5_N1.
    intros.
    apply Subcomponents_Identifiers_Are_Well_Formed_dec.
  Qed.

  (* begin hide *)
  Hint Resolve Rule_4_5_N1_dec : core.
  (* end hide *)
  
  (** ** Consistency rule 4.5 (C1) *)
  (** 4.5 (C1)	The classifier of a subcomponent cannot recursively contain
    subcomponents with the same component classifier. In other words, there cannot
    be a cyclic containment dependency between components.

  *)

  (* TBD *)

  (** * General validation rules *)

  (** A component hierarchy verifies all the rules above.
      These two master theorem combines them.

  %\paragraph{}\begin{wfrule}[Master theorem \#1]
  A component is well-formed iff. all the previous rules are validated:
  \begin{itemize}
    \item the component identifier is well-formed and
    \item its properties are correctly applied and
    \item subcomponents identifiers are well-formed  (Rule 4.5 N1) and
  \end{itemize}
  \end{wfrule}%


    *)

  Definition Well_Formed_Component (c : component) : Prop :=
   Well_Formed_Component_Id (c) /\
   Well_Formed_Properties (c) /\
   Rule_4_5_N1 (c).

  Lemma Well_Formed_Component_dec :
    forall c : component, dec_sumbool (Well_Formed_Component c).
  Proof.
    (* Unfold all definitions *)
    intros.
    unfold Well_Formed_Component.

    (* Apply decidability results *)
    repeat apply dec_sumbool_and; auto.

    (* Note: auto requires all theorems to be part of the core hints
    database, see above "Hint Resolve Rule_4_5_N1_dec : core."  *)
  Defined.

  (** This theorem does not consider the component hierarchy, it is local to
  the component passed as parameter. THis is addressed by the following theorem.

  %\paragraph{}\begin{wfrule}[Master theorem \# 2]
  A component hierarchy is well-formed iff a component and its subcomponent are well-formed.
  \end{wfrule}%
  *)

  Definition Well_Formed_Component_Hierarchy (c : component ) : Prop :=
    Unfold_Apply Well_Formed_Component c.

  Lemma Well_Formed_Component_Hierarchy_dec:
    forall c : component, { Well_Formed_Component_Hierarchy c } + { ~Well_Formed_Component_Hierarchy c}.
  Proof.
    intros.
    unfold Well_Formed_Component_Hierarchy.
    apply Unfold_Apply_dec.
    apply Well_Formed_Component_dec.
  Qed.

(**  This second theorem is the main theorem to assess a component is well-formed. It applies the previous rules on the whole component hierarchy. *)

(* begin hide *)
End WellFormedness_Rules.

Global Hint Resolve Well_Formed_Component_Hierarchy_dec : core.

(* end hide *)
