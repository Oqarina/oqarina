(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)
(*| .. coq:: none |*)

(** Coq Library *)
Require Import Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Decimal.
Require Import Coq.Logic.Decidable.
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Lists.ListDec.
Require Import Sumbool.

(** Oqarina library *)
Require Import Oqarina.core.all.
Require Import Oqarina.coq_utils.all.
Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.AADL.Kernel.properties.
Open Scope list_scope.
(*| .. coq:: |*)

(*|

Components
==========

In this section, we define some core elements of the AADL component model in Coq. Our objective is to define the core concepts of AADL, constructors to build models, and helper functions to iterate over a hierarchy of AADL conponents.

The names and hierarchy follows the names and conventions of the AADLv2 meta-model. The AADL component model is defined as a collection of Coq inductive types.

|*)

(*| .. coq:: none |*)
Section AADL_Definitions.
(*| .. coq:: |*)

 (*|
Definition of AADL Components
-----------------------------

An AADL component is made of an identifier, a category, a list of features, a list of properties, a list of subcomponents %\footnote{Flows and modes are subject to further discussions.}%. Per definition of the AADL component model, features and subcomponents list components as their parts. From a Coq perspective, we must define these three types as mutually dependent types at once.

_Note: actually, this definition allows also for the definition of component type, implementation and instance. This is discussed in the next chapters_.

|*)

  Inductive component :=
    | Component : identifier ->          (* component identifier *)
                  ComponentCategory ->   (* category *)
                  fq_name ->             (* classifier, e.g. A::B::c.impl *)
                  option fq_name ->      (* extends *)
                  list feature ->        (* features *)
                  list component ->      (* subcomponents *)
                  list property_association -> (* properties *)
                  list connection -> (* XXX change order *)
                  component
  with feature :=
    | Feature : identifier -> (* its unique identifier *)
                DirectionType -> (* its direction *)
                FeatureCategory -> (* category of the feature *)
                component ->  (* corresponding component *)
                list property_association -> (* properties *)
                feature
  with connection :=
    | Connection : identifier ->
                    feature_ref -> (* path to the source feature *)
                    feature_ref -> (* path to the destination feature *)
                    connection.

(*| * Definition of an empty component |*)

  Definition nil_component :=
    Component empty_identifier (null) empty_fqname None nil nil nil nil.

(*| * Definition of an invalid feature |*)

  Definition Invalid_Feature :=
    Feature (Id "invalid" ) inF invalid nil_component nil.

(*| .. coq:: none |*)
End AADL_Definitions.
(*| .. coq::  |*)

(*|

Examples
--------

From the previous definitions, one can build a couple of examples showing how to build a set of AADL components. Note that one benefit of Coq is that we can build partial component elements as intermediate variables.

|*)

(*| * Definition of a component type and implementation |*)

Example A_Component := Component (Id "a_component") (abstract)
  (FQN [Id "pack1" ] (Id "foo_classifier") None) None nil nil nil nil.

Example A_Component_Impl :=
  Component (Id "a_component_impl")
  (abstract)
  (FQN [Id "pack1" ] (Id "foo_classifier") (Some (Id "impl")))  None nil
  [ A_Component ] nil nil.

(*| * Definition of a feature |*)

Example A_Feature := Feature (Id "a_feature") inF eventPort nil_component.

(*|

Most of AADL model manipulations revolve around comparison of model subelements and iterations. Hence, decidability results are important. Oqarina provides decidability proofs for all types.

Foloowing Coq conventions, for each type :coq:`foo`, a lemma :coq:`foo_eq_dec`
exists that shows the equality is decidable. |*)

(*| .. coq:: none |*)
Section AADL_Component_Decidability.

(** For other types, we manually define and prove decidability for equality *)

  Lemma connection_eq_dec (a b : connection) : {a=b}+{a<>b}.
  Proof.
      repeat decide equality.
  Qed.

  Lemma list_connection_eq_dec (a b : list connection) : {a=b}+{a<>b}.
  Proof.
      generalize list_eq_dec connection_eq_dec.
      decide equality.
  Defined.

  Hint Resolve connection_eq_dec DirectionType_eq_dec
      identifier_eq_dec ComponentCategory_eq_dec FeatureCategory_eq_dec
      property_association_eq_dec fq_name_eq_dec
      : core.

  (* Since component and features are mutually dependent, we first define a function that returns wether two components (resp. features) are equal. Then, we demonstrate the lemma for component.*)

  Fixpoint component_eq_dec' (a b : component) : {a=b}+{a<>b}
    with feature_eq_dec' (a b : feature) : {a=b}+{a<>b}.
  Proof.
    generalize identifier_eq_dec ComponentCategory_eq_dec
               fq_name_eq_dec list_eq_dec
               connection_eq_dec property_association_eq_dec.
    repeat decide equality.

    generalize identifier_eq_dec FeatureCategory_eq_dec
               DirectionType_eq_dec list_eq_dec
               property_association_eq_dec.
    decide equality.
  Defined.

  Lemma component_eq_dec:
      forall (a :component) (b : component) , {a=b}+{a<>b}.
  Proof.
      generalize identifier_eq_dec ComponentCategory_eq_dec
                 fq_name_eq_dec component_eq_dec'
                 feature_eq_dec' connection_eq_dec
                 property_association_eq_dec list_eq_dec.
      repeat decide equality.
  Defined.

  Lemma list_component_eq_dec (a b : list component) : {a=b}+{a<>b}.
  Proof.
      generalize list_eq_dec component_eq_dec.
      decide equality.
  Defined.

  Lemma feature_eq_dec:
      forall (a : feature) (b : feature) , {a=b}+{a<>b}.
  Proof.
      generalize identifier_eq_dec FeatureCategory_eq_dec
                 DirectionType_eq_dec component_eq_dec'
                 list_eq_dec property_association_eq_dec.
      decide equality.
  Defined.

  Lemma list_feature_eq_dec (a b : list feature) : {a=b}+{a<>b}.
  Proof.
      generalize list_eq_dec feature_eq_dec.
      decide equality.
  Defined.

Definition component_beq (x : component) (y: component) : bool :=
  match component_eq_dec x y with
  | left _ => true
  | _ => false
  end.

Definition feature_beq (x : feature) (y: feature) : bool :=
  match feature_eq_dec x y with
  | left _ => true
  | _ => false
  end.

(* XXX
  Definition component_beq: forall (x y: component), bool.
  Proof.
      generalize identifier_eq_dec ComponentCategory_eq_dec
                  fq_name_eq_dec component_eq_dec
                  feature_eq_dec connection_eq_dec
                  property_association_eq_dec ;
                  boolean_equality.
  Defined.

  Definition feature_beq: forall (x y: feature), bool.
  Proof.
    generalize identifier_eq_dec ComponentCategory_eq_dec
                DirectionType_eq_dec FeatureCategory_eq_dec
                fq_name_eq_dec component_eq_dec'
                feature_eq_dec' connection_eq_dec
                property_association_eq_dec ;
                boolean_equality.
  Defined.
*)
End AADL_Component_Decidability.

Global Hint Resolve connection_eq_dec property_association_eq_dec
  DirectionType_eq_dec identifier_eq_dec ComponentCategory_eq_dec
  FeatureCategory_eq_dec component_eq_dec feature_eq_dec
  list_component_eq_dec list_connection_eq_dec
  : core.
(*| .. coq::  |*)

(*|

Accessor functions
------------------

  .. coq:: none |*)
Section AADL_Accessors.
(*| .. coq::  |*)

  (*| * Component |*)

  Definition projectionComponentId (c : component) : identifier :=
    match c with
    | Component id _ _ _ _ _ _ _ => id
  end.

  Definition projectionComponentCategory (c:component) : ComponentCategory :=
    match c with
    | Component _ category _ _ _ _ _ _ => category
  end.

  Definition projectionComponentClassifier (c:component) : fq_name :=
    match c with
    | Component _ _ fq_name _ _ _ _  _ => fq_name
  end.

  Definition projectionComponentExtends (c:component) : option fq_name :=
    match c with
    | Component _ _ _ extends _ _ _  _ => extends
  end.

  Definition projectionComponentFeatures (c:component) : list feature :=
    match c with
    | Component _ _ _ _ features _ _ _ => features
  end.

  Definition projectionComponentSubComponents (c:component) : list component :=
    match c with
    | Component _ _ _ _ _ subComponents _ _ => subComponents
  end.

  Definition projectionComponentProperties (c:component) : list property_association :=
    match c with
    | Component _ _ _ _ _ _ properties _ => properties
  end.

  Definition projectionComponentConnections (c:component) : list connection :=
    match c with
    | Component _ _ _ _ _ _ _ connections => connections
  end.

  (*| * Feature |*)

  Definition projectionFeatureIdentifier (f : feature) : identifier :=
  match f with
  | Feature id _ _ _ _ => id
  end.

  Definition projectionFeatureDirection (f : feature) : DirectionType :=
    match f with
    | Feature _ d _ _ _ => d
  end.

  Definition projectionFeatureCategory (f : feature) : FeatureCategory :=
    match f with
    | Feature _ _ c _ _ => c
  end.

  Definition projectionFeatureComponent (f : feature) : component :=
    match f with
    | Feature _ _ _ comp _ => comp
    end.

  Definition projectionFeatureProperties (f : feature) : list property_association :=
    match f with
    | Feature _ _ _ _ lp => lp
    end.

  (*| * Connections |*)

Definition projectionConnectionIdentifier (c : connection) :=
  match c with
  | Connection id _ _ => id
  end.

Definition projectionConnectionSource (c : connection) :=
  match c with
  | Connection _ src _ => src
  end.

Definition projectionConnectionDestination (c : connection) :=
  match c with
  | Connection _ _ dst => dst
  end.

  (*| These helper functions extract informations from component subclauses. |*)

  (*| * :coq:`Features_Components` returns the list of components from the list of features :coq:`l`. |*)

  Definition Features_Components (l : list feature) : list component :=
    map (fun x => projectionFeatureComponent x) l.

  Definition Features_Identifiers (l : list feature) : list identifier :=
    map (fun x => projectionFeatureIdentifier x) l.

  (*| * :coq:`Components_Identifiers` returns the list of identifiers in l. |*)

  Definition Components_Identifiers (l : list component) : list identifier :=
    map (fun x => projectionComponentId x) l.

  (*| * :coq:`Unfold` returns the list of components that are parts of c (e.g. as subcomponents) |*)

  Fixpoint Unfold (c : component) : list component :=
    c ::
    ((fix Unfold_subcomponents (ls : list component) : list component :=
      match ls with
      | nil => nil
      | c :: lc  => Unfold (c) ++ Unfold_subcomponents (lc)
      end ) (projectionComponentSubComponents c)).

(*| .. coq:: none |*)
End AADL_Accessors.
(*| .. coq::  |*)

(*|

These are helper notations to use the projections over AADL components:

We inherit the :coq:`->id` notation frmo the typeclass :coq:`Element_Id`.
|*)

#[global] Instance component_id : Element_id component := {|
  get_id := projectionComponentId;
|}.

#[global] Instance feature_id : Element_id feature := {|
  get_id := projectionFeatureIdentifier;
|}.

#[global] Instance connection_id : Element_id connection := {|
  get_id := projectionConnectionIdentifier;
|}.

Class Get_Category (A B: Type) := {
  get_category : A -> B ; }.

Notation "c '->category' " := (get_category c)
  (at level 80, right associativity).

#[global] Instance Component_Category : Get_Category component _ := {|
  get_category := projectionComponentCategory;
|}.

#[global] Instance Feature_Category : Get_Category feature _ := {|
  get_category := projectionFeatureCategory;
|}.

Class Get_Classifier (A : Type) := {
  get_classifier : A -> fq_name ; }.

Notation "c '->classifier' " := (projectionComponentClassifier c)
  (at level 80, right associativity).

#[global] Instance Component_Classifier : Get_Classifier component := {|
  get_classifier := projectionComponentClassifier;
|}.

#[global] Instance Feature_Classifier : Get_Classifier feature := {|
  get_classifier := (fun x => projectionComponentClassifier (projectionFeatureComponent x));
|}.

Notation "c '->subcomps' " := (projectionComponentSubComponents c)
  (at level 80, right associativity).
Notation "c '->features' " := (projectionComponentFeatures c)
  (at level 80, right associativity).

Class Get_Properties (A : Type) := {
    get_properties : A -> list property_association ; }.

Notation "c '->properties' " := (get_properties c)
    (at level 80, right associativity).

#[global] Instance Component_Properties : Get_Properties component := {|
  get_properties := projectionComponentProperties;
|}.

#[global] Instance Feature_Properties : Get_Properties feature := {|
  get_properties := projectionFeatureProperties
|}.

Notation "c '->connections' " := (projectionComponentConnections c)
  (at level 80, right associativity).

Notation "c '->src' " := (projectionConnectionSource c)
  (at level 80, right associativity).

Notation "c '->dest' " := (projectionConnectionDestination c)
  (at level 80, right associativity).

(*|

Iteration over AADL models
--------------------------

Many properties or transformation rely on a traversal of the AADL model. In this section, we propose some reusable mechanisms for iterating over AADL models.

|*)

(*| .. coq:: none |*)
Section AADL_Iterators.
(*| .. coq::  |*)

(*|

In this section, we define a couple of mechanisms to evaluate a decidable predicate on a list of components.

Let us suppose we have a predicate :coq:`P` that is decidable.

|*)

  Variable P : component -> Prop.
  Hypothesis HP : forall c : component, { P c } + { ~P c }.

(*| * :coq:`Component_Iterate_List_prop` applies predicate P on all elements of l, a list of component. We then demonstrate that it yields a decidable proposition if P is decidable. |*)

  Definition Component_Iterate_List_prop (l : list component) : Prop :=
    All P l.

  Lemma Component_Iterate_List_prop_dec :
    forall l : list component, { Component_Iterate_List_prop (l) } +
                               { ~ Component_Iterate_List_prop (l) }.
  Proof.
    prove_dec.
 Qed.

(*| * :coq:`Component_prop` applies P on c, its features and its subcomponents. Let us note that this call does not recurse on the features and subcomponents.
|*)

  Definition Component_prop (c : component) : Prop :=
    P c /\
    Component_Iterate_List_prop (Features_Components (c->features)) /\
    Component_Iterate_List_prop (c->subcomps).

  Lemma Component_prop_dec :
    forall c : component, { Component_prop c } + {~ Component_prop c }.
  Proof.
    prove_dec.
  Qed.

(*|

Actually, we may want a more generic iterator that would iterate on the whole hierarchy. A component is nothing but a representation of a tree of AADL components. We could imagine implementing a traversal algorithm based on a visitor pattern like the following.

However, Coq has a strict definition of recursive functions, and the following is rejected
|*)

  Fail Fixpoint Component_prop (lc : list component) : Prop :=
      match lc with
      | [ ] => True
      | c :: l' => P c /\
        Component_prop (Features_Components (c->features)) /\
        Component_prop (l')
      end.

(*|
Such a definition is rejected as it is not strictly decreasing on the main argument :coq:`lc` because of the recursive call :coq:`Features_Components (c->features)`.

One possible work-around is to apply P on the list of components built recursively from component c using :coq:`Unfold`. The decidability of the resulting function is a direct result of the decidablity of :coq:`All P` for all decidable propositions :coq:`P`. |*)

Definition Unfold_Apply (c : component) : Prop :=
  All P (Unfold c).

 Theorem Unfold_Apply_dec : forall c : component,
  { Unfold_Apply c } + { ~ Unfold_Apply c }.
 Proof.
   prove_dec.
 Qed.

(*| .. coq:: none |*)
End AADL_Iterators.
(*| .. coq::  |*)

(*| .. coq:: none |*)
Section AADL_Name_Resolution.
(*| .. coq:: |*)

(*| * Resolution of element by name: |*)

Variable A : Type.
Context `{Element_id A}.

Definition Get_Element_By_Name (l : list A) (name : identifier) :=
  find (fun x => identifier_beq (x->id) name) l.

Lemma Get_Element_By_Name_destruct:
  forall (a x: A) (l: list A),
      Get_Element_By_Name l (a ->id) = Some x
          -> In x l /\ (identifier_beq (x->id) (a->id) = true).
Proof.
  unfold Get_Element_By_Name.
  intros.
  eapply find_some in H0.
  trivial.
Qed.

Definition Elements_Identifiers (l : list A) : list identifier :=
  map (fun x => x->id) l.

End AADL_Name_Resolution.
