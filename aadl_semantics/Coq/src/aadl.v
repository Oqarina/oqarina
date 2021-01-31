(** %\chapter{Mechanizing the AADL Instance model}% *)

Set Warnings "-parsing".
(** printing -> %\ensuremath{\rightarrow}% *)


(* begin hide *)
(** Coq Library *)

Require Import Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.

(** AADL library *)

Require Import identifiers.
Require Import utils.
(* end hide *)

(**

In this chapter, we define some core elements of the AADL component instance model.
Our objective is to define the core concepts of AADL, helper functions to build models
and to iterate over a hierarchy of AADL models.

This chapter assumes some familiarity of the AADL language version 2.2 %\cite{DBLP:books/daglib/0030032}%
and of the Coq specification language. We used the book by A. Chlipala %\cite{DBLP:books/daglib/0035083}%
as a reference to model AADL concepts using inductive dependent types.

*)

(** * AADL concepts definition

  In this section, we provide the core definition of AADL model elements. The names and hierarchy
  reflects an interpretation of the notional AADL instance model.

  %\textbf{\textit{XXX The names of the various entities could be revisited to be closer to AADL metamodel. Check with Lutz.}}%

 *)

 (* begin hide *)
Section AADL_Definitions.
(* end hide *)

  (** ** Component Categories

    The %\coqdocvar{Component\_Category}% type denotes AADL component categories
    as a finite set of enumerators. *)

  Inductive Component_Category : Type :=
  (* Hybrid categories *)
  | system | abstract
  (* Software categories *)
  | process | thread | threadGroup | subprogram | subprogramGroup | data
  (* Hardware categories *)
  | processor| virtualProcessor | memory | device | bus| virtualBus
  .

  (** ** Feature Categories

    The %\coqdocvar{Feature\_Category}% type denotes AADL feature categories.

  *)

  Inductive Feature_Category : Type :=
    eventPort | dataPort | eventDataPort | busAccess.

  (** ** Feature Directions

    The %\coqdocvar{Feature\_Direction}% type denotes AADL feature direction.

    _Note: we had to use the 'F' suffix to avoid conflict with Coq keyword %\coqdocvar{in}%_.

  *)

  Inductive Feature_Direction : Type :=
    inF | outF | inoutF | requiresF | providesF.

  (** ** Property Types and values *)

  (** AADL defines the concept of property definition and property value.
      We replicated this separation so that we can typecheck that
      a property value matches its definition.

      XXX defines corresponding typechecking rule
  *)

  Inductive Property_Base_Type : Type :=
    | aadlboolean_t | aadlinteger_t | aadlstring_t | aadlreal_t.

  Inductive property_base_value : Type :=
    | aadlboolean : bool -> property_base_value
    | aadlinteger : nat -> property_base_value
    | aadlstring : identifier -> property_base_value
    | aadlreadl : nat (* XXX *) -> property_base_value
    | aadllist : list property_base_value -> property_base_value
    | aadlrecord : list property_base_value -> property_base_value
    .

  Inductive property_type : Type :=
  | Property_Type : list Component_Category ->
                    list Property_Base_Type ->
                    property_type.

  Inductive property_value : Type :=
  | Property_Value : property_type ->
                    property_base_value  ->
                    property_value.

  (** ** Component Instance

  An AADL component instance is made of an identifier, a category, a list of features
  a list of subcomponents %\footnote{Properties will be added in a subsequent iteration.
  Flows and modes are subject to further discussions.}%.

  Per definition of the AADL component model, features and subcomponents also list component instance as their parts.
  From a Coq perspective, we must define all three types as mutually dependent types at once.
  The following defines actually those 3 types: component, subcomponent and feature.
  *)

  Inductive component :=
  | Component : identifier ->         (* its unique identifier *)
                Component_Category -> (* its category *)
                list feature ->       (* its features *)
                list subcomponent ->  (* subcomponents *)
                list property_value -> (* properties *)
                component
  with subcomponent :=
    | Subcomponent : identifier -> (* its unique identifier *)
                    component ->   (* corresponding component instance *)
                    (* XXX do subcomponents have properties? *)
                    subcomponent
  with feature :=
    | Feature : identifier -> (* its unique identifier *)
                Feature_Direction ->
                Feature_Category -> (* *)
                component ->  (* corresponding component instance *)
                list property_value -> (* properties *)
                feature
  .

(* begin hide *)
End AADL_Definitions.
(* end hide *)

(** ** Accessor functions

The following projections extract information from a component *)
(* begin hide *)
Section AADL_Accessors.
(*end hide *)

  (** **** Projections *)

  (** Projections are function returning parts of an inductive type. *)

  (** - Component *)

  Definition projectionComponentId (c : component) : identifier :=
    match c with
    | Component id _ _ _ _ => id
  end.

  Definition projectionComponentCategory (c:component) : Component_Category :=
    match c with
    | Component _ category _ _ _ => category
  end.

  Definition projectionComponentFeatures (c:component) : list feature :=
    match c with
    | Component _ _ features _ _ => features
  end.

  Definition projectionComponentSubComponents (c:component) : list subcomponent :=
    match c with
    | Component _ _ _ subComponents _ => subComponents
  end.

  (** - Subcomponent *)

  Definition projectionSubomponentId (c : subcomponent) : identifier :=
    match c with
    | Subcomponent id _ => id
  end.

  Definition projectionSubcomponentComponent (c : subcomponent) : component :=
    match c with
    | Subcomponent _ comp => comp
  end.

  (** - Feature *)

  Definition projectionFeatureComponent (c : feature) : component :=
    match c with
    | Feature _ _ _ comp _ => comp
  end.

  (** *** Helper functions *)

  (** These helper functions extract informations from component subclauses. *)

  (** Subcomponents_Components return the list of components in l.*)

  Definition Features_Components (l : list feature) : list component :=
      map (fun x => projectionFeatureComponent x) l.

  (** Subcomponent_Identifiers return the list of identifiers in l. *)

  Definition Subcomponents_Identifiers (l : list subcomponent) : list identifier :=
    map (fun x => projectionSubomponentId x) l.

  (** Subcomponents_Components return the list of components in l.*)

  Definition Subcomponents_Components (l : list subcomponent) : list component :=
      map (fun x => projectionSubcomponentComponent x) l.

End AADL_Accessors.

(** ** Notations

  These are helper notations to use the projections above

*)

Notation "c '->id' " := (projectionComponentId c)
  (at level 80, right associativity).
Notation "c '->category' " := (projectionComponentCategory c)
  (at level 80, right associativity).
Notation "c '->subcomps' " := (projectionComponentSubComponents c)
  (at level 80, right associativity).
Notation "c '->comp' " := (projectionSubcomponentComponent c)
  (at level 80, right associativity).
Notation "c '->features' " := (projectionComponentFeatures c)
  (at level 80, right associativity).

(** * Iteration over AADL models

Many properties or transformation rely on a traversal of the AADL model. In this section,
we propose some reusable mechanisms for iterating over AADL models.

*)

(* begin hide *)
Section AADL_Iterators.
(* end hide *)

  (** ** Iteration over list of components *)

  (** In this section, we define a couple of mechanisms to evaluate
    a decidable predicate on a list of components. *)

  (** Let us suppose we have a predicate %\coqdocvar{P}% that is decidable. *)

  (* begin show *)
  Variable P : component -> Prop.
  Hypothesis HP : forall c : component, decidable (P c).
  (* end show *)

  (** Component_Iterate_List_prop applies predicate P on all elements of l, a list of
  component%\footnote{We are leveraging Coq section mechanism, therefore \coqdocvar{P}
  and \coqdocvar{HP} are part of the definition context, we do not need to make them visible
  in the definitions.}%. We then demonstrate that it yields a decidable proposition if P is decidable. *)

  Definition Component_Iterate_List_prop (l : list component) : Prop :=
    All P l.

  Lemma Component_Iterate_List_prop_dec :
    forall l : list component, decidable (Component_Iterate_List_prop (l)).
  Proof.
    apply All_dec.
    apply HP.
  Qed.

  (** Component_prop applies P on c, its features and its subcomponents.
   Let us note that this call does not recurse on the features and subcomponents,
   it is certainly not that useful. %\textbf{XXX should we keep it?}%
  *)

  Definition Component_prop (c : component) : Prop :=
    P c /\
    Component_Iterate_List_prop (Features_Components (c->features)) /\
    Component_Iterate_List_prop (Subcomponents_Components (c->subcomps)).

  Lemma Component_prop_dec :
    forall c : component, decidable(Component_prop c).
  Proof.
    intros.
    unfold Component_prop.
    apply dec_and.
    - apply HP.
    - apply dec_and.
      * apply Component_Iterate_List_prop_dec.
      * apply Component_Iterate_List_prop_dec.
  Qed.

  (** ** Iteration over a component hierarchy  *)

  (**

  Actually, we may want a more generic iterator that would iterate on the whole hierarchy.
  A component is nothing but a representation of a tree of AADL components. We could
  imagine implementing a traversal algorithm based on a visitor pattern like the following.

  However, Coq has a strict definition of recursive functions, and the following is rejected

<<
    Fixpoint Component_prop (lc : list component) : Prop :=
      match lc with
      | [ ] => True
      | c :: l' => P c /\
      Component_prop (Features_Components (c->features)) /\
      Component_prop (Subcomponents_Components (c->subcomps)) /\
      Component_prop (l')
      end.
>>

  Such a definition is rejected: it is not strictly decreasing on the main argument lc because
  of the recursive call  %\texttt{Features\_Components (c->features)}% and %\texttt{Subcomponents\_Components (c->subcomps)}%

  Instead, we have to define properly an induction principle for our component case. We follow the
  approach proposed in %\S 3.8% from %\cite{DBLP:books/daglib/0035083}%. The definition is an
  expansion of the pattern from A. Chlipala book, adapted to the two nested types in a component.

  *)

  Section component_ind'.

  (** We define a predicate on component, and the application of the same predicate on
    components that are 'parts' of a component. *)

    Definition Ps (s : subcomponent) : Prop :=
      match s with
      | Subcomponent _ c => P c
      end.

    Lemma Ps_dec : forall s: subcomponent, decidable (Ps  s).
    Proof.
      intros.
      unfold Ps.
      destruct s.
      apply HP.
    Qed.

    Definition Pf (f : feature) : Prop :=
      match f with
      | Feature _ _ _ c _ => P c
      end.

    Lemma Pf_dec : forall f: feature, decidable (Pf f).
    Proof.
      intros.
      unfold Pf.
      destruct f.
      apply HP.
    Qed.

    (** This is our induction hypothesis: %\textit{"if Pc is true for all components that are either in feature or in
      subcomponent instance, then it is sufficient to assess it on the component
      that is built from their combination."}%
      *)

    Hypothesis component_case :
      forall (id : identifier) (cat : Component_Category) (lf : list feature)
              (ls : list subcomponent) (lp : list property_value),
      All Pf lf /\ All Ps ls -> P (Component id cat lf ls lp).

    (** We can now define our induction principle. *)

    Fixpoint component_ind' (c : component) : P c :=
      match c return P c with
      | Component id cat lf ls lp =>
        component_case id cat lf ls lp
        (conj
         (* Iterate on all features of c *)
          ((fix feature_ind (lf : list feature) : All (Pf) (lf) :=
            match lf return All _ lf  with
            | nil => I
            | Feature _ _ _ c' _ :: lf' =>
                conj (component_ind' c')
                      (feature_ind lf')
          end)
          lf)

        (* Iterate on all subcomponents of c*)
          ((fix subComponent_ind (ls : list subcomponent) : All (Ps) (ls) :=
            match ls return All _ ls  with
            | nil => I
            | Subcomponent _ c' :: ls' =>
                conj (component_ind' c')
                    (subComponent_ind ls')
            end)
          ls))
    end.

  End component_ind'.

(* begin hide *)
End AADL_Iterators.
(* end hide *)

(** * Examples

  Some naive definitions to use the concept we have defined so far.

*)

(** Definition of the Priority property *)

Definition Priority : property_type :=
  Property_Type (thread::nil) (aadlinteger_t::nil).

Definition A_Priority_Value :=
Property_Value Priority (aadlinteger 42).

(* Definition of a component *)

Definition A_Component : component :=
  Component (Ident "id") (abstract) nil nil nil.

Definition A_Component_2 : component :=
  Component (Ident "") (abstract) nil nil nil.

Check A_Component.
Print A_Component.

Eval compute in Subcomponents_Identifiers [ (Subcomponent (Ident "foo") A_Component) ].

Definition A_Component_Impl :=
  Component (Ident "id.impl") (abstract) nil (cons (Subcomponent (Ident "foo") A_Component) nil).

Definition A_Component_Impl_2 :=
  Component (Ident "id.impl") (abstract) nil [ (Subcomponent (Ident "foo") A_Component) ; (Subcomponent (Ident "foo") A_Component)  ].

Definition A_Feature := Feature (Ident "coinc") inF eventPort nil_component.

(** * Well-formedness rules

In this section, we define several well-formedness rules for model elements.

*)
(* begin hide *)
Section WellFormedness_Rules.
(* end hide *)

  (** ** Well-formedness of component identifiers *)

  (** A component identifier is well-formed iff. the identifier is well-formed. *)

  Definition Well_Formed_Component_Id (c : component) : Prop :=
    (Well_Formed_Identifier_prop (c->id)).

  (** Well_Formed_Component_Id is a decidable property. *)

  Lemma Well_Formed_Component_Id_dec : forall c : component,
    decidable (Well_Formed_Component_Id  c).
  Proof.
    (* Hint: this is a direct consequence of the decidability of the
       well-formedness rule of identifiers *)
    intros.

    (* unfold the various definitions *)
    unfold decidable.
    unfold Well_Formed_Component_Id.

    (* apply decidability result on Identifier *)
    apply Well_Formed_Identifier_prop_dec.
  Qed.

  (** ** Naming rule 4.5 (N1) *)
  (** 4.5 (N1) The defining identifier of a subcomponent declaration placed in a
  component implementation must be unique within the local namespace of the
  component implementation that contains the subcomponent.

  _Hint: In other words, the list of identifiers built from the list of subcomponents has no duplicates_.

  *)

  Definition Subcomponents_Identifiers_Are_Well_Formed (l : list subcomponent) : Prop :=
    (NoDup (Subcomponents_Identifiers l)).

  Lemma Subcomponents_Identifiers_Are_Well_Formed_dec :
    forall l : list subcomponent,
      decidable (Subcomponents_Identifiers_Are_Well_Formed l).
  Proof.
    intros.

    (* unfold the various definitions *)
    unfold decidable.
    unfold Subcomponents_Identifiers_Are_Well_Formed.

    apply NoDup_decidable. (* NoDup is decidable, from Coq.Lists.ListDec *)

    (* Last bit is to rely on identifier equality being also decidable *)
    unfold decidable_eq. (* from Coq.Lists.ListDec *)
    apply ident_dec. (* from utils *)
  Qed.

  (** ** Consistency rule 4.5 (C1)*)
  (** 4.5 (C1)	The classifier of a subcomponent cannot recursively contain
    subcomponents with the same component classifier.
    In other words, there cannot be a cyclic containment dependency between components.
  *)

  (* TBD *)

  (** ** Well-formedness of a component instance *)
  (** A component type is well-formed iff.
    - the component identifier is well-formed and
    - subcomponents identifiers are well-formed and
    - subcomponents are well-formed
    *)

  (* TBD *)

(* begin hide *)
End WellFormedness_Rules.
(* end hide *)

End Sandbox.

