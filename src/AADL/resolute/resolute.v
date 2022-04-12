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
Require Import Oqarina.AADL.Kernel.component.
Require Import Oqarina.AADL.Kernel.properties.
Require Import Oqarina.AADL.Kernel.features_helper.
Require Import Oqarina.AADL.Kernel.properties_helper.
Open Scope list_scope.
(*| .. coq::  |*)

(*|
Resolute Queries
================

In this module, we provide a Coq variant of built-in functions defined by Resolute :cite:`DBLP:conf/nfm/LiuBCG16`. Resolute provides its own language to define predicates, inspired by Prolog. Instead, we rely on Coq syntax and notation to define lemma like the REAL annex language :cite:`hugues08idm`.

Built-in functions for named elements
-------------------------------------

We use a Coq typeclass to define a common interface for accessing :coq`named_elements`. In the context of Resolute, a named_element can be a component, a feature, or a connection. See the definition of named_element_interface below:

* :coq:`name(<named_element>): string` - returns the name of the named element: IMPLEMENTED

* :coq:`has_property(<named_element>, <property>): Boolean` - the named element has the property.

* :coq:`property(<named_element>, <property>, <default value>): value` - returns the value of the property. A default value must be supplied, it is returned if the element does not have the property value.

* :coq:`type(<named_element>): Classifier` - returns the classifier of a component, feature, or connection. In the case of a connection, the type is that of the connection source (if not present the destination) feature.

* :coq:`property(<property>) value` - returns the value of the property constant.

* :coq:`property_member(<record_property_value>, <field name>): Boolean`  return the value of the record field.
|*)

Class named_element_interface A : Type := {
    name : A -> identifier ;
    type : A -> fq_name ;
    has_property : A -> ps_qname -> Prop ;
    has_property_dec : forall (a: A) (name : ps_qname), { has_property a name } + {~ has_property a name } ;
    property : A -> ps_qname
        -> property_association -> property_association ;
}.

(*| * Implementation for components |*)

Definition has_property_c (c : component) (name : ps_qname) :=
    Is_Property_Defined name (c->properties).

Lemma has_property_c_dec: forall (c: component) (name : ps_qname),
    { has_property_c c name } + {~ has_property_c c name }.
Proof.
    prove_dec2 ; apply ps_qname_eq_dec.
Defined.

Definition property_c
    (c : component)
    (name : ps_qname)
    (default : property_association)
:=
    let pvs := filter (fun x => ps_qname_beq x.(P) name) (projectionComponentProperties c) in
    hd default pvs.

#[global]Instance component' : named_element_interface component := {
    name := projectionComponentId ;
    type := projectionComponentClassifier ;
    has_property := has_property_c ;
    has_property_dec := has_property_c_dec ;
    property := property_c ;
}.

(*| * Implementation for features |*)

Definition has_property_f (f : feature) (name : ps_qname) :=
    Is_Property_Defined name (projectionFeatureProperties f).

Lemma has_property_f_dec: forall (f : feature) (name : ps_qname),
    { has_property_f f name } + {~ has_property_f f name }.
Proof.
    prove_dec2 ; apply ps_qname_eq_dec.
Defined.

Definition property_f
    (f : feature)
    (name : ps_qname)
    (default : property_association)
:=
    let pvs := filter (fun x => ps_qname_beq x.(P) name) (projectionFeatureProperties f) in
    hd default pvs.

Definition property_member (pv : property_value) (name : identifier) :=
    match pv with
    | PV_Record l => Get_Record_Member l name
    | _ => None
    end.

#[global]Instance feature' : named_element_interface feature := {
    name :=  projectionFeatureIdentifier ;
    type :=  Feature_Classifier ;
    has_property := has_property_f ;
    has_property_dec := has_property_f_dec ;
    property := property_f ;
}.

(*| * :coq:`has_type (named_element): Boolean` - returns true if the named element has a classifier. The named element can be a component, feature, or connection instance. In the case of a connection, the type of the feature is the connection end. *)

Definition has_type
    (A : Type) {H : named_element_interface A} (e : A) :=
    type e <> empty_fqname.

(*| * :coq:`is_of_type(<named_element>, <classifier>): Boolean` - true if the named element has the classifier or one of its type extensions. The named element must have a type. The named element can be a component, feature, or connection instance. In the case of a connection, the type of the feature is the connection end. |*)

Definition is_of_type
    (A : Type) {H : named_element_interface A}
    (e : A) (t : fq_name) :=
    type e = t.

(*
has_parent(<named_element>): Boolean - returns true if the component has an enclosing model element

parent(<named_element>): named_element - returns the parent of the named element. The parent must exist.

has_member(<component>, <string>): Boolean - true if the component has a member with the specified name (string). Members are features, subcomponents, etc. The component can be a component instance or a component classifier.

    Note: Feature instances representing feature groups can have feature instances as members, but they are not handled by this function. See pre-declared library below for flattening feature instances in feature groups.

is_in_array(<component>): Boolean - returns true if the component instance in in an array, i.e., has an index into the array.

has_prototypes(<component>): Boolean - returns true if component classifier contains prototype declarations.

has_modes(<component>): Boolean - returns true if component directly contains mode instances.
|*)

(*|
Built-in Functions for Component categories
-------------------------------------------

* :coq:`is_procesor(<component>): Boolean` - true if the component instance is a processor. Other built-in component category tests are: is_virtual_procesor, is_system, is_bus, is_virtual_bus, is_device, is_memory, is_thread, is_process, is_data, is_subprogram.

|*)

Definition is_processor (c: component) := c->category = processor.

Lemma is_processor_dec: forall (c : component),
    { is_processor c} + {~ is_processor c }.
Proof. prove_dec. Qed.

Definition is_processorb (c : component) :=
    ComponentCategory_beq (c->category) processor.

Definition processor_set (c: component) :=
    filter is_processorb (Unfold c).

Definition is_thread (c: component) := c->category = thread.

Lemma is_thread_dec: forall (c : component),
    { is_thread c} + {~ is_thread c }.
Proof. prove_dec. Defined.

Definition is_threadb (c : component) :=
    ComponentCategory_beq (c->category) thread.

Definition thread_set (c: component) :=
    filter is_threadb (Unfold c).

(*|

Built-in Functions for Features
-------------------------------

* :coq:`direction(<feature>)` - returns the direction of a feature instance as string (in, out, in out/in_out). Access features do not have direction.|*)

Definition direction (f : feature) :=
    projectionFeatureDirection f.

(*| * :coq:`is_event_port(<feature>): Boolean` - true if the feature instance is an event port or event data port.  See also :coq:`Is_Triggering_Feature`. *)

Definition is_event_port (f : feature) :=
    In (projectionFeatureCategory f) [ eventPort ; eventDataPort ].

Lemma is_event_port_dec: forall (f: feature),
    { is_event_port f} + {~ is_event_port f}.
Proof. prove_dec. Qed.

(*| * :coq:`is_data_port(<feature>): Boolean` - true if the feature instance is an data port or event data port|*)

Definition is_data_port (f : feature) :=
    In (projectionFeatureCategory f) [ dataPort ; eventDataPort ].

Lemma is_data_port_dec: forall (f: feature),
    { is_data_port f} + {~ is_data_port f}.
Proof. prove_dec. Qed.

(*| * :coq:`is_port(<feature>): Boolean` - true if the feature instance is a port |*)

Definition is_port (f : feature) :=
    In (projectionFeatureCategory f)
        [ dataPort ; eventDataPort ; eventDataPort ].

Lemma is_port_dec: forall (f: feature),
    { is_port f} + {~ is_port f}.
Proof. prove_dec. Qed.

(*| :coq:`is_abstract_feature(<feature>): Boolean` - true if the feature instance is an abstract feature|*)

Definition is_abstract_feature (f : feature) :=
    In (projectionFeatureCategory f) [ abstractFeature ].

Lemma is_abstract_feature_dec: forall (f: feature),
    { is_abstract_feature f} + {~ is_abstract_feature f}.
Proof. prove_dec. Qed.
