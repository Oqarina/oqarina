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

Require Import Coq.Strings.String.
Require Import Oqarina.core.all.

Require Export Oqarina.AADL.Kernel.categories.
Require Export Oqarina.AADL.Kernel.component.
Require Export Oqarina.AADL.Kernel.components_helper.
Require Export Oqarina.AADL.Kernel.properties.
Require Export Oqarina.AADL.Kernel.typecheck.
Require Export Oqarina.AADL.Kernel.properties_helper.
Require Export Oqarina.AADL.Kernel.features_helper.

Module AADL_Notations.

Declare Scope aadl_scope.

(*| Notation for component features (partial XXX) |*)

Notation "'feature:' 'in_event' x" := (Feature (Id x) inF eventPort nil_component nil) (at level 200) : aadl_scope.

Notation "'feature:' 'out_event' x" := (Feature (Id x) outF eventPort nil_component nil) (at level 200).

(*| Properties |*)

Notation "'property:' x ==>| y" := {| P := x ; PV := y|} (at level 200) : aadl_scope.

(*| Connections |*)

Definition Build_Connection (id : string) (source : string) (destination : string) : connection :=
    Connection (Id id) (parse_feature_ref_name source) (parse_feature_ref_name destination).

Notation "'connection:' id '#' src --> dst" :=
    (Build_Connection id src dst) (at level 200).

(*| Notation for AADL component categories |*)

Definition Build_Component
    (id : string) (cat : ComponentCategory)
    (classifier : string) (features : list feature) (subcomponents : list component) (connections : list connection) (properties : list property_association): component :=
    Component (Id id) (cat)
    (parse_fq_name classifier) features subcomponents properties connections.

Notation "'abstract:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id abstract classifier lf ls lc lp) (at level 200).

Notation "'system:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id system classifier lf ls lc lp) (at level 200).

Notation "'process:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id process classifier lf ls lc lp) (at level 200).

Notation "'thread:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id thread classifier lf ls lc lp) (at level 200).

Notation "'threadGroup:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id threadGroup classifier lf ls lc lp) (at level 200).

Notation "'subprogram' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id subprogram classifier lf ls lc lp) (at level 200).

Notation "'subprogramGroup' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id subprogramGroup classifier lf ls lc lp) (at level 200).

Notation "'data:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id data classifier lf ls lc lp) (at level 200).

Notation "'processor:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id processor classifier lf ls lc lp) (at level 200).

Notation "'virtualProcessor:' id ->| classifier features: lf subcomponents: ls  connections: lc properties: lp" :=
    (Build_Component id virtualProcessor classifier lf ls lc lp) (at level 200).

Notation "'memory:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id memory classifier lf ls lc lp) (at level 200).

Notation "'device:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id device classifier lf ls lc lp) (at level 200).

Notation "'bus:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id bus classifier lf ls lc lp) (at level 200).

Notation "'virtualBus:' id ->| classifier features: lf subcomponents: ls connections: lc properties: lp" :=
    (Build_Component id virtualBus classifier lf ls lc lp) (at level 200).

End AADL_Notations.
