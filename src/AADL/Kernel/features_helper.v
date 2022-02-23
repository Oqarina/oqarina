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
(** %\chapter{Feature Helpers}% *)

(** The following defines helper functions to manipulate feature of a component *)

(* begin hide *)
(** Coq Library *)
Require Import List.
Import ListNotations. (* from List *)
Require Import Coq.Bool.Bool.

(** Oqarina library *)
Require Import Oqarina.AADL.Kernel.categories.
Require Import Oqarina.AADL.Kernel.component.
Require Import Oqarina.coq_utils.all.
(* end hide *)

Definition Is_Input_Port (f : feature) :=
  (DirectionType_beq (projectionFeatureDirection f) inF) ||
  (DirectionType_beq (projectionFeatureDirection f) inoutF).

Definition Is_Output_Port (f : feature) :=
    DirectionType_beq (projectionFeatureDirection f) outF ||
    DirectionType_beq (projectionFeatureDirection f) inoutF.

Definition Is_Triggering_Feature (f : feature) :=
  (FeatureCategory_beq (projectionFeatureCategory f) eventPort) ||
  (FeatureCategory_beq (projectionFeatureCategory f) eventDataPort) ||
  (FeatureCategory_beq (projectionFeatureCategory f) subprogramAccess) ||
  (FeatureCategory_beq (projectionFeatureCategory f) subprogramGroupAccess).

Definition Is_Triggering_Feature_p (f : feature) :=
  In (projectionFeatureCategory f) [ eventPort ; eventDataPort ;
                                     subprogramAccess ; subprogramGroupAccess].

Definition Is_Data_Port (f : feature) :=
  (projectionFeatureCategory f) = dataPort.

Definition Is_Data_Portb (f : feature) : bool :=
  FeatureCategory_beq (projectionFeatureCategory f) dataPort.

Definition Get_Input_Features (l : list feature) :=
  filter Is_Input_Port l.

Definition Get_Output_Features (l : list feature) :=
  filter Is_Output_Port l.
