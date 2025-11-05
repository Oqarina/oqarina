.. coq::


.. coq:: none

   Require Export Oqarina.AADL.behavior.port_variable.
   Require Export Oqarina.AADL.behavior.thread.
   Require Export Oqarina.AADL.behavior.system.

Behavior
========

In this chapter, we leverage the previous definitions of AADL concepts and provide a description of the behavioral semantics of AADL. This description starts with the description of AADL port variables, representing features, then present AADL runtime services to finally present the semantics of each components category.

.. toctree::
    :maxdepth: 2

    AADL__behavior_port_variable.v.rst
    AADL__behavior_thread.v.rst
    AADL__behavior_system.v.rst
