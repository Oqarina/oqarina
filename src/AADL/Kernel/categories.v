(* begin hide *)
Section AADL_Categories.
(* end hide *)

  (** ** Component Categories

    The %\coqdocvar{Component\_Category}% type denotes AADL component categories.

    _Note: we need to diverge from the AADL standard and add an explicit null component category for the rare situations where we need to define the absence of a component attach to a model element such as an event port_.

  *)

  Inductive ComponentCategory : Type :=
  (* Hybrid categories *)
  | system | abstract
  (* Software categories *)
  | process | thread | threadGroup | subprogram | subprogramGroup | data
  (* Hardware categories *)
  | processor| virtualProcessor | memory | device | bus | virtualBus
  (* Mechanization addition -- not part of AADL standard *)
  | null (* denote an explicitely null or invalid component *).

  (** ** Feature Categories

    The %\coqdocvar{FeatureCategory}% type denotes AADL feature categories.
    The [invalid] category is an addition used to denote an invalid feature.

  *)

  Inductive FeatureCategory : Type :=
    | dataPort | eventPort | eventDataPort | parameter
    | busAccess | virtualBusAccess | dataAccess| subprogramAccess
    | subprogramGroupAccess | featureGroup | abstractFeature
    | invalid.

  (** ** Feature Directions

    The %\coqdocvar{Feature\_Direction}% type denotes AADL feature direction.

    _Note: we had to use the 'F' suffix to avoid conflict with Coq concept %\coqdocvar{in}%_.

  *)

  Inductive DirectionType : Type :=
    inF | outF | inoutF | nullDirection.

    (* begin hide *)
  Scheme Equality for ComponentCategory.
  Scheme Equality for FeatureCategory.
  Scheme Equality for DirectionType.

End AADL_Categories.
(* end hide *)