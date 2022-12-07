# Oqarina -- Coq mechanization of AADL ![GitHub Action](https://github.com/Oqarina/Oqarina/actions/workflows/main.yml/badge.svg)

Oqarina is a mechanization of AADL in Coq. It provides a collection of libraries to manipulate AADL models as Coq types, and a formalization of the behavioral semantics of AADL faithful to the AADL standard v2.3.



## Directory structure

* `examples`: tutorial and examples to illustrate Oqarina
* `extraction` : wrapper to extract code and compile a binary
* `src`: Coq sources for AADL mechanization
* `testsuite`: some tests for the extracted code
* `tools`: misc. helper scripts for maintenance

## Required software

Oqarina has been tested using Coq version 8.16 and either VSCoq extension for Visual Code or Proof General.

### Additional packages

The following packages should be installed separately using opam:

* `https://github.com/liyishuai/coq-json`: JSON manipulation
* `https://github.com/Lysxia/coq-simple-io`: IO monad with user-definable primitive operations
* `https://github.com/coq-community/coq-ext-lib`: Additional theories for Coq
* `https://github.com/DmxLarchey/Kruskal-Trees`: rose tree library with proper (nested) induction principles
* `https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs`: PROSA scheduling library

Use `make install_deps` to install them.

## Usage

You may either
- just run from a makefile, type `make` for available targets

- play with the Coq files from VSCode. In this case, make sure the Coq directory is the only one in your workspace. Then from the terminal, run

  ```make build```

- compile extracted code, e.g.

  ```make build build_bin```

  then, run

  ```./_build/default/extraction/extraction.native  --parse testsuite/car.impl.json```

- build using provided docker container

  ```make test_build_docker```

## Suggested reading

Many (free) books exist for Coq, the following one is a good introduction for the style of modeling we are using:

- Chlipala, Adam. Certified Programming with Dependent Types - A Pragmatic Introduction to the Coq Proof Assistant. MIT Press, 2013. http://mitpress.mit.edu/books/certified-programming-dependent-types.

  This book is available from the author website: http://adam.chlipala.net/cpdt/

- An additional reference is the collection of books from https://softwarefoundations.cis.upenn.edu/

- This list gathers many other relevant projects and links: https://project-awesome.org/coq-community/awesome-coq
