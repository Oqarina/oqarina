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

In this chapter, we define some core elements of the AADL component instance model in Coq. Our objective is to define the core concepts of AADL, helper functions to build models and to iterate over a hierarchy of AADL conponents.

This chapter assumes some familiarity of the AADL language version 2.2 %\cite{DBLP:books/daglib/0030032}% and of the Coq specification language. We used the book by A. Chlipala %\cite{DBLP:books/daglib/0035083}% as a reference to model AADL concepts using inductive dependent types.

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

    _Note: we need to diverge from the AADL standard and add an explicit null component category for the rare situations where we need to define the absence of a component attach to a model element such as an event port_.

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

      %\textbf{XXX change to match AADL Instance Textual notation??}%

  *)

  Inductive Property_Base_Type : Type :=
    | aadlboolean_t | aadlinteger_t | aadlstring_t | aadlreal_t.

  Inductive property_base_value : Type :=
    | aadlboolean : bool -> property_base_value
    | aadlinteger : nat -> property_base_value
    | aadlstring : identifier -> property_base_value
    | aadlreal : float -> property_base_value
    | aadllist : list property_base_value -> property_base_value
    | aadlrecord : list property_base_value -> property_base_value
    (* | aadlreference -> component -> property_base_value ...*)
    .

  Inductive property_type : Type :=
  | Property_Type : list ComponentCategory -> (* applies to categories *)
                    Property_Base_Type -> (* the type of the property *)
                    property_type.

  Inductive property_value : Type :=
  | Property_Value : property_type -> (* property type *)
                    property_base_value  -> (* actual value *)
                    property_value.

  (** ** Definition of AADL Components

  An AADL component is made of an identifier, a category, a list of features a list of subcomponents %\footnote{Properties will be added in a subsequent iteration. Flows and modes are subject to further discussions.}%.

  Per definition of the AADL component model, features and subcomponents also list component instance as their parts. From a Coq perspective, we must define all three types as mutually dependent types at once. The following defines actually those 4 types: component, subcomponent, feature and connection.

  _Note: actually, this definition allows also for the definition of component type, implementation and instance._

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
                list component ->      (* subcomponents *)
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

(** * Examples

  From the previous definitions, one can build a couple of examples showing how to build
  an AADL instance model. Note that one benefit of Coq is that we can build partial
  instance models as intermediate variables.

*)

(** Definition of the Priority property *)

Definition Priority : property_type :=
  Property_Type [ thread ] aadlinteger_t.

Definition A_Priority_Value :=
  Property_Value Priority (aadlinteger 42).

(** Definition of a component *)

Definition A_Component := Component (Ident "a_component") (abstract)
  (Ident "foo_classifier") nil nil nil nil.

Definition A_Component_Impl :=
  Component (Ident "another_component_impl") (abstract) (Ident "bar_classifier.impl") nil
  [ A_Component ] nil nil.

Definition A_Feature := Feature (Ident "a_feature") inF eventPort nil_component.

(** * Accessor functions

The following projections extract information from a component *)
(* begin hide *)
Section AADL_Accessors.
(*end hide *)

  (** ** Projections *)

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

  Definition projectionComponentSubComponents (c:component) : list component :=
    match c with
    | Component _ _ _ _ subComponents _ _ => subComponents
  end.

  Definition projectionComponentProperties (c:component) : list property_value :=
    match c with
    | Component _ _ _ _ _ properties _ => properties
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

  (** ** Helper functions *)

  (** These helper functions extract informations from component subclauses. *)

  (** %\coqdocdefinition{Features\_Components}% return the list of components in l.*)

  Definition Features_Components (l : list feature) : list component :=
    map (fun x => projectionFeatureComponent x) l.

  (** %\coqdocdefinition{Components\_Identifiers}% return the list of identifiers in l. *)

  Definition Components_Identifiers (l : list component) : list identifier :=
    map (fun x => projectionComponentId x) l.

  (** %\coqdocdefinition{Unfold}% returns the list of components that are parts of c (e.g. as subcomponents) %\textbf{XXX features ??}%
  *)

  Fixpoint Unfold (c : component) : list component :=
    c ::
    ((fix Unfold_subcomponents (ls : list component) : list component:=
      match ls with
      | nil => nil
      | c :: lc  => Unfold (c) ++ Unfold_subcomponents (lc)
      end ) (projectionComponentSubComponents c)).

(* begin hide *)
End AADL_Accessors.
(* end hide *)

(** ** Notations

  These are helper notations to use the projections over AADL components: *)

Notation "c '->id' " := (projectionComponentId c)
  (at level 80, right associativity).
Notation "c '->category' " := (projectionComponentCategory c)
  (at level 80, right associativity).
Notation "c '->subcomps' " := (projectionComponentSubComponents c)
  (at level 80, right associativity).
Notation "c '->features' " := (projectionComponentFeatures c)
  (at level 80, right associativity).
Notation "c '->properties' " := (projectionComponentProperties c)
  (at level 80, right associativity).

(** * Iteration over AADL models

  Many properties or transformation rely on a traversal of the AADL model. In this section, we propose some reusable mechanisms for iterating over AADL models.

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

  (** Component_Iterate_List_prop applies predicate P on all elements of l, a list of component%\footnote{We are leveraging Coq section mechanism, therefore \coqdocvar{P} and \coqdocvar{HP} are part of the definition context, we do not need to make them visible in the definitions.}%. We then demonstrate that it yields a decidable proposition if P is decidable. *)

  Definition Component_Iterate_List_prop (l : list component) : Prop :=
    All P l.

  Lemma Component_Iterate_List_prop_dec :
    forall l : list component, decidable (Component_Iterate_List_prop (l)).
  Proof.
    apply All_dec.
    apply HP.
  Qed.

  (** Component_prop applies P on c, its features and its subcomponents.
   Let us note that this call does not recurse on the features and subcomponents.
    %\textbf{XXX should we keep it?}%
  *)

  Definition Component_prop (c : component) : Prop :=
    P c /\
    Component_Iterate_List_prop (Features_Components (c->features)) /\
    Component_Iterate_List_prop (c->subcomps).

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

  Actually, we may want a more generic iterator that would iterate on the whole hierarchy. A component is nothing but a representation of a tree of AADL components. We could imagine implementing a traversal algorithm based on a visitor pattern like the following.

  However, Coq has a strict definition of recursive functions, and the following is rejected

<<
    Fixpoint Component_prop (lc : list component) : Prop :=
      match lc with
      | [ ] => True
      | c :: l' => P c /\
      Component_prop (Features_Components (c->features)) /\
      Component_prop (l')
      end.
>>

  Such a definition is rejected: it is not strictly decreasing on the main argument lc because of the recursive call  %\texttt{Features\_Components (c->features)}%.
*)

(** **** Iterating via unfolding:

  one possible work-around is to apply P on the list of components built
  recursively from component c using %\coqdocdefinition{Unfold}%.
  The decidability of the resulting function is a direct result of the decidablity of
  %\coqdocdefinition{All P}% for %\coqdocdefinition{P}% decidable. *)

Definition Unfold_Apply (c : component) : Prop :=
  All P (Unfold c).

 Theorem Unfold_Apply_dec : forall c : component,
  decidable (Unfold_Apply c).
 Proof.
   intros.
   unfold Unfold_Apply.
   apply All_dec.
   apply HP.
 Qed.

 (* begin hide *)
 (** **** Iterating via recursion over the component hierarchy. *)

(* TBD, prototype is easy to build, the issue is on proving its decidability.
  Crafting and using the correct induction principle seems problematic. *)

 (* end hide *)


(* begin hide *)
End AADL_Iterators.
(* end hide *)
