(** %\chapter{Mechanizing the AADL Instance model}\label{chap::aadl_mecha}% *)

Set Warnings "-parsing".
(** printing -> %\ensuremath{\rightarrow}% *)


(* begin hide *)
(** Coq Library *)

Require Import Bool.
Require Import Coq.Floats.PrimFloat.
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

In this chapter, we define some core elements of the AADL component instance model in Coq.
Our objective is to define the core concepts of AADL, helper functions to build models
and to iterate over a hierarchy of AADL conponents.

This chapter assumes some familiarity of the AADL language version 2.2 %\cite{DBLP:books/daglib/0030032}%
and of the Coq specification language. We used the book by A. Chlipala %\cite{DBLP:books/daglib/0035083}%
as a reference to model AADL concepts using inductive dependent types.

*)

(** * AADL Instance Model -- Concepts Definition

  In this section, we provide the core definition of AADL model elements. The names and hierarchy
  follows the textual grammar of the AADL Instance model. This Xtext grammar%\footnote{See
  \href{https://github.com/osate/osate2/blob/master/core/org.osate.aadl2.instance.textual/src/org/osate/aadl2/instance/textual/Instance.xtext}{Instance.xtext}}%
  provides a concise definition of the concepts that form an AADL Instance model.

  In the following, we provide a formalization of the AADL Instance model
  gramamr as a collection of Coq inductive types.

  _Note: Coq is imposing in order type definitions, the order differs from the
  original Xtext file_.

 *)

 (* begin hide *)
Section AADL_Definitions.
(* end hide *)

  (** ** Component Categories

    The %\coqdocvar{Component\_Category}% type denotes AADL component categories.

    _Note: we need to diverge from the AADL standard and add an explicit null component
    category for the rare situations where we need to define the absence of a component
    attach to a model element such as an event port_.

  *)

  (* begin hide *)
  (* From OSATE

  ComponentCategory returns aadl2::ComponentCategory: 'abstract' | 'bus'|'data'
    | 'device' | 'memory' | 'process' | 'processor' | 'subprogram'
    | 'subprogram' 'group' | 'system' | 'thread' 'group'
    | 'thread' | 'virtual' 'bus' | 'virtual' 'processor';

  *)
  (* end hide *)

  Inductive ComponentCategory : Type :=
  (* Hybrid categories *)
  | system | abstract
  (* Software categories *)
  | process | thread | threadGroup | subprogram | subprogramGroup | data
  (* Hardware categories *)
  | processor| virtualProcessor | memory | device | bus | virtualBus
  (* Mechanization addition -- not part of AADL standard *)
  | null (* denote an explicitely null or invalid component *)
  .

  (** ** Feature Categories

    The %\coqdocvar{FeatureCategory}% type denotes AADL feature categories.

  *)

  (* begin hide *)
  (* From OSATE:

  FeatureCategory returns instance::FeatureCategory:
    'dataPort' | 'eventPort' | 'eventDataPort' | 'parameter' |
    'busAccess' | 'dataAccess'| 'subprogramAccess' | 'subprogramGroupAccess' |
    'featureGroup' | 'abstractFeature'
  ;
  *)
  (* end hide *)

  Inductive FeatureCategory : Type :=
    dataPort | eventPort | eventDataPort | parameter |
	  busAccess | dataAccess| subprogramAccess | subprogramGroupAccess |
	  featureGroup | abstractFeature.

  (** ** Feature Directions

    The %\coqdocvar{Feature\_Direction}% type denotes AADL feature direction.

    _Note: we had to use the 'F' suffix to avoid conflict with Coq concept %\coqdocvar{in}%_.

  *)

  (* begin hide *)
  (* From OSATE

  DirectionType returns aadl2::DirectionType:
    'in' | 'out' | 'in' 'out'
  ;

  *)
  (* end hide *)

  Inductive DirectionType : Type :=
    inF | outF | inoutF .

  (** ** Property Types and values *)

  (** AADL defines the concept of property definition and property value.
      We replicated this separation so that we can typecheck that
      a property value matches its definition.

      %\textbf{XXX change to match AADL Instance Textual notation}%

  *)

  Inductive Property_Base_Type : Type :=
    | aadlboolean_t | aadlinteger_t | aadlstring_t | aadlreal_t.

  Inductive property_base_value : Type :=
    | aadlboolean : bool -> property_base_value
    | aadlinteger : nat -> property_base_value
    | aadlstring : identifier -> property_base_value
    | aadlreal : float -> property_base_value
    | aadllist : list property_base_value -> property_base_value
    | aadlrecord : list property_base_value -> property_base_value.

  Inductive property_type : Type :=
  | Property_Type : list ComponentCategory -> (* applies to categories *)
                    Property_Base_Type -> (* the type of the property *)
                    property_type.

  Inductive property_value : Type :=
  | Property_Value : property_type -> (* property type *)
                    property_base_value  -> (* actual value *)
                    property_value.

  (** ** Component Instance

  An AADL component instance is made of an identifier, a category, a list of features
  a list of subcomponents %\footnote{Properties will be added in a subsequent iteration.
  Flows and modes are subject to further discussions.}%.

  Per definition of the AADL component model, features and subcomponents also list component instance as their parts.
  From a Coq perspective, we must define all three types as mutually dependent types at once.
  The following defines actually those 4 types: component, subcomponent, feature and
  connection.

<<
  <component_category> <classifier>
  features
    <list feature>
  subcomponents
    <list subcomponent>
  properties
    <list property>
  connection
    <list connection>
  end
>>


  *)

  (* begin hide *)
  (* From OSATE

    FeatureInstance returns instance::FeatureInstance:
      direction=DirectionType category=FeatureCategory name=ID ('[' index=Long ']')? ':' feature=[aadl2::Feature|DeclarativeRef] ('{' (
        featureInstance+=FeatureInstance |
        ownedPropertyAssociation+=PropertyAssociationInstance
      )* '}')?
    ;

    ComponentInstance returns instance::ComponentInstance:
      category=ComponentCategory classifier=[aadl2::ComponentClassifier|ClassifierRef]? name=ID ('[' index+=Long ']')*
      ('in' 'modes' '(' inMode+=[instance::ModeInstance] (',' inMode+=[instance::ModeInstance])*')')?
      ':' subcomponent=[aadl2::Subcomponent|DeclarativeRef] ('{' (
        featureInstance+=FeatureInstance |
        componentInstance+=ComponentInstance |
        connectionInstance+=ConnectionInstance |
        flowSpecification+=FlowSpecificationInstance |
        endToEndFlow+=EndToEndFlowInstance |
        modeInstance+=ModeInstance |
        modeTransitionInstance+=ModeTransitionInstance |
        ownedPropertyAssociation+=PropertyAssociationInstance
      )* '}')?
    ;

  *)
  (* end hide *)


  Inductive component :=
  | Component : identifier ->          (* classifier *)
                ComponentCategory ->   (* category *)
                identifier ->          (* classifier *)
                list feature ->        (* features *)
                list subcomponent ->   (* subcomponents *)
                list property_value -> (* properties *)
                list connection ->
                component
    with feature :=
      | Feature : identifier -> (* its unique identifier *)
                  DirectionType ->
                  FeatureCategory -> (* *)
                  component ->  (* corresponding component instance *)
                  list property_value -> (* properties *)
                  feature
    with subcomponent :=
    | Subcomponent : identifier -> (* its unique identifier *)
                    component ->   (* corresponding component instance *)
                    (* XXX do subcomponents have properties? no in ocarina *)
                    subcomponent
    with connection :=
    | Connection : identifier ->
                   list identifier -> (* path to the source feature *)
                   list identifier -> (* path to the destination feature *)
                   connection
    .

  (* Definition of an empty component *)
  Definition nil_component := Component empty_identifier (null) empty_identifier nil nil nil nil.

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
    | Component id _ _ _ _ _ _ => id
  end.

  Definition projectionComponentCategory (c:component) : ComponentCategory :=
    match c with
    | Component _ category _ _ _ _ _ => category
  end.

  Definition projectionComponentFeatures (c:component) : list feature :=
    match c with
    | Component _ _ _ features _ _ _ => features
  end.

  Definition projectionComponentSubComponents (c:component) : list subcomponent :=
    match c with
    | Component _ _ _ _ subComponents _ _ => subComponents
  end.

  Definition projectionComponentProperties (c:component) : list property_value :=
    match c with
    | Component _ _ _ _ _ properties _ => properties
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

  (** - Property type *)

  Definition Base_Type (p : property_type) :=
    match p with
    | Property_Type  _ pbt => pbt
    end.

  Definition Applicable_ComponentCategory (p : property_type) :=
    match p with
    | Property_Type lcat _ => lcat
    end.

  (** - Property value *)

  Definition Get_Property_Type (p : property_value) :=
    match p with
    | Property_Value pType _ => pType
    end.

  Definition Get_Base_Value (p : property_value) :=
    match p with
    | Property_Value _ pv => pv
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

(* begin hide *)
End AADL_Accessors.
(* end hide *)

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
Notation "c '->properties' " := (projectionComponentProperties c)
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

      (*
    Hypothesis component_case :
      forall (id : identifier) (cat : ComponentCategory) (lf : list feature)
              (ls : list subcomponent) (lp : list property_value) (lc : list connection),
      All Pf lf /\ All Ps ls -> P (Component id cat cla lf ls lp lc).
*)
    (** We can now define our induction principle. *)
(*
    Fixpoint component_ind' (c : component) : P c :=
      match c return P c with
      | Component id cat lf ls lp lc =>
        component_case id cat lf ls lp lc
        (conj
          ((fix feature_ind (lf : list feature) : All (Pf) (lf) :=
            match lf return All _ lf  with
            | nil => I
            | Feature _ _ _ c' _ :: lf' =>
                conj (component_ind' c')
                      (feature_ind lf')
          end)
          lf)

          ((fix subComponent_ind (ls : list subcomponent) : All (Ps) (ls) :=
            match ls return All _ ls  with
            | nil => I
            | Subcomponent _ c' :: ls' =>
                conj (component_ind' c')
                    (subComponent_ind ls')
            end)
          ls))
    end.
*)
  End component_ind'.

(* begin hide *)
End AADL_Iterators.
(* end hide *)

(** * Examples

  Some naive definitions to use the concept we have defined so far.

*)

(** Definition of the Priority property *)

Definition Priority : property_type :=
  Property_Type [ thread ] aadlinteger_t.

Definition A_Priority_Value :=
Property_Value Priority  (aadlinteger 42).

(** Definition of a component *)

Definition A_Component : component :=
  Component (Ident "id") (abstract) (Ident "something") nil nil nil nil.

Check A_Component.
Print A_Component.

Eval compute in Subcomponents_Identifiers [ (Subcomponent (Ident "foo") A_Component) ].

Definition A_Component_Impl :=
  Component (Ident "id_impl") (abstract) (Ident "somthing.impl") nil
  [ (Subcomponent (Ident "foo") A_Component) ].

Definition A_Component_Impl_2 :=
  Component (Ident "id_mpl") (abstract) (Ident "somthing.impl") nil
  [ (Subcomponent (Ident "foo") A_Component) ;
    (Subcomponent (Ident "foo2") A_Component)  ].

Definition A_Feature := Feature (Ident "coinc") inF eventPort nil_component.

(** * Well-formedness rules

In this section, we define several well-formedness rules for model elements.

For each rule, we define a basic predicate that operate on a component only,
without recursion. We demonstrate that this predicate is decidable.

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
    Component (Ident "Hello_World") (subprogram) (Ident "spg") nil nil [A_Source_Language] nil.

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

  (** We prove an intermediate lemma before demonstrating this property is decidable. *)

  Lemma Property_Base_Type_eq_dec :
    forall pbt1 pbt2 : Property_Base_Type , decidable(pbt1 = pbt2).
  Proof.
    unfold decidable.
    repeat decide equality.
  Qed.

  Lemma Well_Formed_Property_Value_dec : forall p : property_value,
    decidable (Well_Formed_Property_Value p).
  Proof.
    intros.
    unfold Well_Formed_Property_Value.
    destruct (Get_Property_Type p).

    (* produce trivial goals for each possible value that are either an
    equality or False, previous decidability results terminate those proofs.
    *)
    destruct (Get_Base_Value p);
      unfold Base_Type; apply Property_Base_Type_eq_dec ||  apply dec_False.
  Qed.

  Definition Property_Correctly_Applies_To (c : component) (p : property_value) :=
    In (c->category) (Applicable_ComponentCategory (Get_Property_Type p)).

  (* begin hide *)

  (* The following lemma asserts equality on ComponentCategory is
    decidable.

    _Note: the definition differs from Property_Base_Type_eq_dec as
    In_decidable that we use below depends on decidable_eq in its hypotheses. *)

  Lemma Component_Categoy_eq_dec  : decidable_eq ComponentCategory.
  Proof.
    unfold decidable_eq.
    unfold decidable.
    repeat decide equality.
  Qed.
  (* end hide *)

  Lemma Property_Correctly_Applies_To_dec :
    forall (p : property_value) (c : component),
        decidable (Property_Correctly_Applies_To c p ).
  Proof.
    intros p c.
    unfold Property_Correctly_Applies_To.
    apply In_decidable.
    apply Component_Categoy_eq_dec.
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
      decidable (List_Property_Correctly_Applies_To lp c).
  Proof.
    unfold List_Property_Correctly_Applies_To.
    intros.
    apply All_dec.
    intros.
    apply Property_Correctly_Applies_To_dec.
  Qed.

  Definition Well_Formed_Properties (c : component) : Prop :=
    List_Property_Correctly_Applies_To (c->properties) c .

  Lemma Well_Formed_Properties_dec :
    forall (c:component), decidable (Well_Formed_Properties c).
  Proof.
    unfold Well_Formed_Properties.
    intros.
    apply List_Property_Correctly_Applies_To_dec.
  Qed.

  Hint Resolve Well_Formed_Properties_dec : core.

  (** ** Naming rule 4.5 (N1) *)
  (** 4.5 (N1) The defining identifier of a subcomponent declaration placed in a
  component implementation must be unique within the local namespace of the
  component implementation that contains the subcomponent.

  _Hint: In other words, the list of identifiers built from the list of subcomponents has no duplicates_.

  First, we define a predicate on list of subcomponents, and demonstrate it is decidable.

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

  (** We can now "implement" the predicate for rule 4.5 (N1) *)

  Definition Rule_4_5_N1 (c : component) : Prop :=
    Subcomponents_Identifiers_Are_Well_Formed (c->subcomps).

  Lemma Rule_4_5_N1_dec :
    forall c : component, decidable (Rule_4_5_N1 c).
  Proof.
    unfold Rule_4_5_N1. intros.
    apply Subcomponents_Identifiers_Are_Well_Formed_dec.
  Qed.

  Hint Resolve Rule_4_5_N1_dec : core.

  (** ** Consistency rule 4.5 (C1)*)
  (** 4.5 (C1)	The classifier of a subcomponent cannot recursively contain
    subcomponents with the same component classifier.
    In other words, there cannot be a cyclic containment dependency between components.
  *)

  (* TBD *)

  (** ** Master theorem %\# 1%: well-formedness of a component instance *)

  (** A component type is well-formed iff.
    - the component identifier is well-formed and
    - its properties are correctly applied and
    - subcomponents identifiers are well-formed  (Rule 4.5 N1) and
    - TBD
    *)

  Definition Well_Formed_Component (c : component) : Prop :=
   Well_Formed_Component_Id (c) /\
   Well_Formed_Properties (c) /\
   Rule_4_5_N1 (c).

  Lemma Well_Formed_Component_dec :
    forall c : component, decidable (Well_Formed_Component c).
  Proof.
    (* Unfold all definitions *)
    intros.
    unfold Well_Formed_Component.

    (* Apply decidability results *)
    repeat apply dec_and; auto.
  Defined.

  (** ** Master theorem %\# 2%: well-formedness of a component hierarchy *)

(* TBD *)

(* begin hide *)
End WellFormedness_Rules.
(* end hide *)
