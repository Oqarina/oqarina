# Architecture of Oqarina

This file provides a high-level overview of the Oqarina source code.

_Note: this is a work-in-progress, the organization may evolve as we add more elements to the formalization._

## Organization of the code base

### Library elements

* `CoqExt`: extensions to the Coq standard library
* `coq_utils`: additonal elements not found in the Coq standard library;
* `core`: reusable libraries for basic types, e.g. identifiers, queues, etc.;
* `formalisms`: abstract types for expressing formalisms such as Labelled Transition Systems, DEVS, etc.
* `MoC`: model of computations

### Definition of AADL models

The directory `AADL` holds the definitions that capture core AADL concepts.

It is organized as a collection of "packages". Following Coq conventions, each directory has a `all` module that exports all definitions from that directory.

* AADL generic AADL component definition: `AADL/Kernel`
    * `categories.v`, `component.v`: definition of a generic AADL component

    * `properties.v`, `typecheck.v`: definition of properties and typing rules
    * `<_>_helper`, ..: helper routines to manipulate features, components, etc. One package per concept

* AADL default property sets: `AADL/property_sets`
    * this directory provides an implementation of AADL default property sets. The names match the name of the corresponding AADL property set.

* AADL legality rules: `AADL/legality_rules`
    Implementation of (a subset of) AADL legality rules, organized by concepts: components, categories, etc. It is worth mentioning that the definition of the legality rules in the core standard document has limited dependences on the concept of declarative and instance model.

    - One package`<_>_wf.v` per concept

* AADL declarative model: `AADL/declarative`

* AADL instance model: `AADL/instance`

* JSON front-end: `AADL/json_frontend`
    Ocarina can export instance model as XML files, then converted to JSON (see AADlib for the process). This package provides a translator fron JSON format to AADL instance files.

* AADL dynamic semantics: `AADL/behavior`
    * For each component category, a file `<category>.v` is defined

    Similar to the static semantics, the dynamic semantics requires a partial definition of a component implementation reduced to the components and its direct subcomponents.
