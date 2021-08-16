# Oqarina -- Coq mechanization of AADL

Oqarina provides elements of a formalization of AADLv2. It aligns with AADLv2.3.

## Directory structure

* `extra` : additional material for producing HTML from Coq
* `extraction` : wrapper to extract code and compile a binary
* `latex-src` : LaTeX source code of the corresponding TR.
* `src`: Coq sources for AADL mechanization

## Required software

Oqarina has been tested using Coq version 8.13.2 and either VSCoq extension for Visual Code or Proof General.

## Additional packages

The following packages should be installed separately using opam:

* `http://gallium.inria.fr/~fpottier/menhir/`: parser generator
* `http://coq.io/`: additional elements to read from files, helper for code extractions
* `https://github.com/liyishuai/coq-json`: JSON manipulation

Use `make install_deps` (no extraction) or `make install_deps` (extraction) to install them.

## Usage

You may either
- just run from a makefile, type `make` for available targets

- play with the Coq files from VSCode. In this case, make sure the Coq directory is the only one in your workspace. Then from the terminal, run

    ```make build_makefile compile ```

- extract code, e.g.

  ```make build_makefile compile build_bin```

  then, run

  ```./extraction/main.native --parse testsuite/car.impl.json```

- build using Dune, in this case no extraction is performed

  ```make build_dune```

- build using provided docker container, no extraction

  ```make test_build_docker```

## Suggested reading

Many (free) books exist for Coq, the following one is a good introduction for the style of modeling we are using:

- Chlipala, Adam. Certified Programming with Dependent Types - A Pragmatic Introduction to the Coq Proof Assistant. MIT Press, 2013. http://mitpress.mit.edu/books/certified-programming-dependent-types.

  This book is available from the author website: http://adam.chlipala.net/cpdt/

- An additional reference is the collection of books from https://softwarefoundations.cis.upenn.edu/

- This list gathers many other relevant projects and links: https://project-awesome.org/coq-community/awesome-coq
