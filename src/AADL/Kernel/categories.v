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

    The [FeatureCategory] type denotes AADL feature categories.
    The [invalid] category is an addition used to denote an invalid feature.

  *)

  Inductive FeatureCategory : Type :=
    | dataPort | eventPort | eventDataPort | parameter
    | busAccess | virtualBusAccess | dataAccess| subprogramAccess
    | subprogramGroupAccess | featureGroup | abstractFeature
    | invalid.

  Inductive MetaModelCategory : Type :=
    | connection.

(** ** AppliesTo Categories

The [AppliesToCategory] type is an aggreagate type used in [applies to] clauses in AADL. AADL properties may apply to different categories: components, features, meta model elements, etc. Hence the need for such an aggregate.

*)

  Inductive AppliesToCategory : Type :=
    | CompCat : ComponentCategory -> AppliesToCategory
    | FeatureCat : FeatureCategory -> AppliesToCategory
    | MetaCat : MetaModelCategory -> AppliesToCategory
    | all.

  (** ** Feature Directions

    The %\coqdocvar{Feature\_Direction}% type denotes AADL feature direction.

    _Note: we had to use the 'F' suffix to avoid conflict with Coq concept %\coqdocvar{in}%_.

  *)

  Inductive DirectionType : Type :=
    inF | outF | inoutF | nullDirection.

    (* begin hide *)
  Scheme Equality for ComponentCategory.
  Scheme Equality for FeatureCategory.
  Scheme Equality for AppliesToCategory.
  Scheme Equality for DirectionType.

End AADL_Categories.
(* end hide *)