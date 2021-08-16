# Architecture of Oqarina

This file provides a high-level overview of the Oqarina source code.

_Note: this is a work-in-progress, the organization may evolve as we add more elements to the formalization._

## Organization of the code base

### Library elements

* `coq_utils`: additonal elements not found in the Coq standard library;
* `core`: reusable libraries for basic types, e.g. identifiers, queues, etc.;
* `formalisms`: abstract types for expressing formalisms such as Labelled Transition Systems, actor/director model, etc.

### Definition of AADL models:

The directory `AADL` holds the definitions that capture core AADL concepts.

It is organized as a collection of "packages". Following Coq conventions, each directory has a `all` module that exports all definitions from that directory.

* AADL generic AADL component definition: `AADL/Kernel`
    * `categories.v`, `component.v`: definition of a generic AADL component

    * `properties.v`, `typecheck.v`: definition of properties and typing rules
    * `features_helper`, `properties_helper`: helper routines to access features and properties

* AADL default property sets: `AADL/property_sets`
    * this directory provides an implementation of AADL default property sets. The names match the name of the corresponding AADL property set.

* AADL legality rules: `AADL/legality_rules`
    Implementation of (a subset of) AADL legality rules, organized by concepts: components, categories, etc. It is worth mentioning that the definition of the legality rules in the core standard document has limited dependences on the concept of declarative and instance model.

    - `categories_wf.v`: well-formedness rules for each AADL component category
    - `component_wf.v`: well-formedness rules of a generic AADL component

* AADL declarative model: `AADL/declarative`

* AADL instance model: `AADL/instance`

* JSON front-end: `AADL/json_frontend`
    Ocarina can export instance model as XML files, then converted to JSON (see AADlib for the process). This package provides a translator fron JSON format to AADL instance files.

* AADL Textual Instance Notation front-end: `AADL/atin_frontend`
    OSATE can export instance model into a textual notation. This package is an attempt to parse this notation. Unfortunately, this is a dead end: the instance notation is not self-contained and miss critical information like corresponding instances for feature classifiers. In addition, parsing properties is challenging with a LR(1) parser.

    This directory is kept as a reference on how to use Menhir to build a parser.

## THE PARTS BELOW MUST BE REORGANIZED

* AADL dynamic semantics
    * For each component category, a file `aadl_dynamic_<category>.v` is defined

    Similar to the static semantics, the dynamic semantics requires a partial definition of a component implementation reduced to the components and its direct subcomponents.
