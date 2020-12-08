(** * aadl.v *)

(** This file defines some core elements of the AADL language *)

Require Import utils.
Require Import Bool.

(** ** Component definition *)

(** *** AADL Component Categories

The Component_Category type denotes AADL component categories *)

Inductive Component_Category : Type :=
| abstract
| process
| thread
| threadgroup
| subprogram
| subprogramgroup
| processor
| virtualprocessor
| memory
| device
| bus
| virtualbus
| system.

(** *** AADL Component Type

An AADL component type is made of
- an identifier
- a category
- ...

*)

Inductive component_type :=
| Component_Type : identifier ->         (* its unique identifier *)
                   Component_Category -> (* its category*)
                   component_type.

(** The following projections extract information from a component_type *)

Definition projectionComponentTypeId (c : component_type) : identifier :=
  match c with
  | Component_Type id category => id
  end.

Definition projectionComponentTypeCategory (c:component_type)
  : Component_Category :=
  match c with
  | Component_Type id category => category
  end.

(** *** AADL Component Implementation

    An AADL component implementation is made of
    - an identifier
    - a component type it implements
    - a list of subcomponents
    - ...

 *)

Inductive component_implementation :=
| Component_Implementation : identifier ->
                             component_type ->
                             list component_implementation ->
                             component_implementation.

(** The following projections extract information from a
    component_implementation *)

Definition projectionComponentImplId (c : component_implementation) : identifier :=
  match c with
  | Component_Implementation id ctype subComponents => id
  end.

Definition projectionComponentImplParent (c:component_implementation) : component_type :=
  match c with
  | Component_Implementation id ctype subComponents => ctype
  end.

Definition projectionComponentImplSubComponents (c:component_implementation) : list component_implementation :=
  match c with
  | Component_Implementation id ctype subComponents => subComponents
  end.

Definition projectionComponentImplCategory (c:component_implementation) : Component_Category :=
  let ctype := projectionComponentImplParent c in
  projectionComponentTypeCategory ctype.

(** *** Component Root type

  We introduce component as a root type for component types and implementations.
  This will facilitate some operations when processing models.

 *)

Inductive component : Set :=
| IsComponentType (c : component_type)
| IsComponentImplementation (c : component_implementation).

Coercion IsComponentType : component_type >-> component.
Coercion IsComponentImplementation : component_implementation >-> component.

Definition projectionComponentId (c : component) : identifier :=
  match c with
  | IsComponentType c => projectionComponentTypeId  c
  | IsComponentImplementation c => projectionComponentImplId  c
  end.

Definition projectionComponentCategory (c : component) : Component_Category :=
  match c with
  | IsComponentType c => projectionComponentTypeCategory  c
  | IsComponentImplementation c => projectionComponentImplCategory c
  end.

(** *** Notations

  These are helper notations to use the projections above

*)

Notation "c '->id' " := (projectionComponentId c) (at level 80, right associativity).
Notation "c '->category' " := (projectionComponentCategory c) (at level 80, right associativity).
Notation "c '->parent' " := (projectionComponentImplParent c) (at level 80, right associativity).
Notation "c '->subcomps' " := (projectionComponentImplSubComponents c) (at level 80, right associativity).

(** ** Tests *)
Definition A_Component : component_type :=
  Component_Type (Ident "id") (abstract).

Definition A_Component_2 : component_type :=
  Component_Type (Ident "") (abstract).

Check A_Component.

Definition A_Component_Impl :=
  Component_Implementation (Ident "id.impl") (A_Component) nil.

Definition A_Component_Impl_2 :=
  Component_Implementation (Ident "id2.impl") (A_Component) nil.

Check A_Component_Impl.

Eval compute in A_Component->id.
Eval compute in A_Component->category.

Eval compute in A_Component_Impl->id.
Eval compute in A_Component_Impl->category.
Eval compute in A_Component_Impl->parent.
Eval compute in A_Component_Impl->subcomps.

(** ** Well-formedness rules



 *)

(** A component identifier is well-formed iff. the identifier is well-formed *)
Definition Well_Formed_Component_Id (c : component) : bool :=
  (Well_Formed_Identifier (c->id)).

Eval compute in Well_Formed_Component_Id A_Component.

(** A component type is well-formed iff. the conponent identifier is well-formed *)
Definition Well_Formed_ComponentType (c : component_type) : bool :=
  Well_Formed_Component_Id c.

Eval compute in Well_Formed_ComponentType A_Component.
Eval compute in Well_Formed_ComponentType A_Component_2.

(** A component implementation identifier is well-formed  iff XXXX *)

Definition Well_Formed_CompomentImplementation_Id (c : component_implementation) : bool :=
  ((Well_Formed_Component_Id c) &&
   (let ctype:= projectionComponentImplParent c in
    let ctypeid := ctype->id in
    let cid := c->id in
    cid == ctypeid)).

(** A component implementation is well-formed iff.
    - its identifier is well formed and
    - its parent component type is well-formed
 *)

Definition Well_Formed_ComponentImplementation (c : component_implementation) : bool :=
  (
    (Well_Formed_CompomentImplementation_Id c) &&
    (Well_Formed_ComponentType (c->parent))
  ).

Eval compute in Well_Formed_ComponentImplementation A_Component_Impl.

(** A component is well-formed iff it is either a well-formed component type
    or a well-formed component implementaiton
*)

Definition Well_Formed_Component (c : component) : bool :=
  match c with
  | IsComponentType c => Well_Formed_ComponentType c
  | IsComponentImplementation c => Well_Formed_ComponentImplementation c
  end.

Eval compute in Well_Formed_Component A_Component_Impl.
Eval compute in Well_Formed_Component A_Component.

Eval compute in Well_Formed_Component A_Component_Impl_2.
