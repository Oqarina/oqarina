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
    * For each component category, a file `aadl_static_<category>.v` is defined.

    It is worth mentioning that the definition of the static semantics as it is in the core standard document has limited dependences on the concept of declarative and instance model. It is usually sufficient to define two well-formedness rules, one for component types and one for component implementations.

* AADL dynamic semantics
    * For each component category, a file `aadl_dynamic_<category>.v` is defined

    Similar to the static semantics, the dynamic semantics requires a partial definition of a component implementation reduced to the components and its direct subcomponents.

    XXX TBH, it is only when we define the global semantics of an instanticated system as the combination of the semantics of its parts that we need the complete instance model. In this case, the instance model is equivalent to one generic component representing the full hierarchy.

* Helper packages
    * `aadl_communication_properties.v`: accessor to manipulate some of the properties from AADL property set `communication_properties`.
    * `aadl_thread_properties.v`: accessor to manipulate some of the properties from AADL property set `thread_properties`.
    * `aadl_feature_helper`: helper function to manipulate features

    XXX This package could be generated from AADL property sets.