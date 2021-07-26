# Architecture of Oqarina

This file provides a high-level overview of the Oqarina source code.

This is a work-in-progress, the organization may evolve as we add more elements to the formalization.

## Library elements

* `coq_utils`: additonal elements not found in the Coq standard library;
* `core`: reusable libraries for basic types, e.g. identifiers, queues, etc.;
* `formalisms`: abstract types for expressing formalisms such as Labelled Transition Systems, timed automata. etc.

## Organization of the code base

### Definition of AADL models:

Directory `AADL` holds the definitions of that capture AADL concepts. It is organized as a collection of "packages":

* AADL generic AADL component definition: `AADL/Kernel`
    * `aadl_categories.v`, `component.v`: definition of a generic AADL component
    * `component_wf.v`: well-formedness rules of a generic AADL component
    * `properties.v`, `typecheck.v`: definition of properties and typing rules
    * `properties_helper`: helper rountine

* AADL default property sets: `AADL/property_sets`
    * this directory provides an implementation of AADL default property set. The names match the name of the corresponding AADL property set.

* AADL declarative and instance model
    * `aadl_declatative.v` and `aadl_instance.v`

* AADL static semantics
    * For each component category, a file `aadl_static_<category>.v` is defined.

    It is worth mentioning that the definition of the static semantics as it is in the core standard document has limited dependences on the concept of declarative and instance model. It is usually sufficient to define two well-formedness rules, one for component types and one for component implementations.

* AADL dynamic semantics
    * For each component category, a file `aadl_dynamic_<category>.v` is defined

    Similar to the static semantics, the dynamic semantics requires a partial definition of a component implementation reduced to the components and its direct subcomponents.

* Helper packages
    * `aadl_feature_helper`: helper function to manipulate features

