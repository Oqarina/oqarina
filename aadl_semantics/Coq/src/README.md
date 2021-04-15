# Architecture of Oqarina

This file provides a high-level overview of the Oqarina source code.

This is a work-in-progress, the organization may evolve as we add more elements to the formalization.

## Library elements

* `coq_utils.v`: additonal elements not found in the Coq standard library;
* `core`: reusable libraries for basic types, e.g. identifiers, queues, etc.;
* `formalisms`: abstract types for expressing formalisms such as Labelled Transition Systems, timed automata. etc.
* `extraction.v` is a "for fun" experiment at extracting OCaml code from some pieces, only exploratory at this stage.

## AADL formalization

* AADL generic AADL component
    * `aadl.v`: definition of a generic AADL component
    * `aadl_wf.v`; well-formedness rules of a generic AADL component

* AADL declarative and instance model
    * `aadl_declatative.v` and `aadl_instance.v`

* AADL static semantics
    * For each component category, a file `aadl_static_<category>.v` must be defined.

* AADL dynamic semantics
    * For each component category, a file `aadl_dynamic_<category>.v` must be defined

* Helper packages
    * `aadl_thread_properties.v`: accessor to manipulate some of the properties from AADL property set thread_properties. This package could be generated from AADL property sets