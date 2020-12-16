(** * aadl.v *)

(** This file defines some core elements of the AADL language *)

Require Import utils.
Require Import Bool.
Require Import Coq.Init.Datatypes.
Require Import List.
Import ListNotations.

(* Set Implicit Arguments.
Set Asymmetric Patterns.
*)

(** ** Component definition *)

(** *** AADL Component Categories

The Component_Category type denotes AADL component categories *)

Inductive Component_Category : Type :=
| abstract
| process
| thread
| threadGroup
| subprogram
| subprogramGroup
| processor
| virtualProcessor
| memory
| device
| bus
| virtualBus
| system.

(** *** AADL Component Type and implementation

An AADL component type is made of
- an identifier
- a category
- ...

An AADL component implementation is made of
- an identifier
- a component type it implements
- a list of subcomponents
- ...

Note: The following defines actually 3 types: component, subcomponent and feature.
We take advantage of Coq syntax for mutually dependent type definitions.

 *)

Inductive component :=
| componentInstance : identifier ->         (* its unique identifier *)
                   Component_Category -> (* its category *)
                   list feature ->       (* its features *)
                   list subcomponent ->  (* subcomponents *)
                   component
with subcomponent :=
  | Subcomponent : identifier ->
                   component ->
                   subcomponent
with feature :=
  | Feature : identifier ->
              component ->
              feature
.

Definition nil_component := componentInstance empty_identifier (abstract) nil nil.

(** The following projections extract information from a component *)

Definition projectionComponentId (c : component) : identifier :=
  match c with
  | componentInstance id _ _ _ => id
  end.

Fixpoint projectionComponentCategory (c:component) : Component_Category :=
  match c with
  | componentInstance _ category _ _ => category
  end.

Definition projectionComponentSubComponents (c:component) : list subcomponent :=
  match c with
  | componentInstance _ _ _ subComponents => subComponents
  end.

(** *** Notations

  These are helper notations to use the projections above

*)

Notation "c '->id' " := (projectionComponentId c) (at level 80, right associativity).
Notation "c '->category' " := (projectionComponentCategory c) (at level 80, right associativity).
Notation "c '->subcomps' " := (projectionComponentSubComponents c) (at level 80, right associativity).

(** ** Tests *)
Definition A_Component : component :=
  componentInstance (Ident "id") (abstract) nil nil.

Definition A_Component_2 : component :=
  componentInstance (Ident "") (abstract) nil nil.

Check A_Component.

Definition A_Component_Impl :=
  componentInstance (Ident "id.impl") (abstract) nil (cons (Subcomponent (Ident "foo") A_Component) nil).

Definition A_Component_Impl_2 :=
  componentInstance (Ident "id.impl") (abstract) nil [ (Subcomponent (Ident "foo") A_Component) ].

Check A_Component_Impl.
Check A_Component_Impl = A_Component_Impl_2.

Eval compute in A_Component->id.
Eval compute in A_Component->category.

Eval compute in A_Component_Impl->id.
Eval compute in A_Component_Impl->category.
Eval compute in A_Component_Impl->subcomps.

Definition A_Feature := Feature (Ident "coinc") nil_component.
Check A_Feature.

(** ** Well-formedness rules

 *)

(** A component identifier is well-formed iff. the identifier is well-formed *)
Definition Well_Formed_Component_Id (c : component) : bool :=
  (Well_Formed_Identifier (c->id)).

Eval compute in Well_Formed_Component_Id A_Component.

(** A component type is well-formed iff. the conponent identifier is well-formed *)
Definition Well_Formed_ComponentInstance (c : component) : bool :=
  Well_Formed_Component_Id c.

Eval compute in Well_Formed_ComponentInstance A_Component.
Eval compute in Well_Formed_ComponentInstance A_Component_2.

(* 4.5 (N1)	The defining identifier of a subcomponent declaration placed in a component
   implementation must be unique within the local namespace of the component implementation
   that contains the subcomponent.
*)

(* 4.5 (C1)	The classifier of a subcomponent cannot recursively contain subcomponents with the
  same component classifier.  In other words, there cannot be a cyclic containment
  dependency between components.
  *)
