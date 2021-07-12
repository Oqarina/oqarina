# Oqarina -- Coq mechanization of AADL

Oqarina provides elements of a formalization of AADL.

## Directory structure

* `extra` : additional material for producing HTML from coq
* `latex-src` : LaTeX source code of the corresponding TR.
* `src`: Coq sources for AADL mechanization
* `parser`: prototype area for AADL parser for AADL textual notation

## Required software

Oqarina has been tested using Coq version 8.13.1 and VSCoq extension for Visual Code.

## Additional packages

The following packages should be installed separately using opam:

* `https://github.com/clarus/coq-list-string`: some string manipulation functions
* `http://gallium.inria.fr/~fpottier/menhir/`: parser generator
* `http://coq.io/`: additional elements to read from files, helper for code extractions

Use `make install_deps` to install these packages.

## Usage

You may either
- just run from a makefile, type `make` for available targets or
- play with the Coq files from VSCode. In this case, make sure the Coq directory is the only one in your workspace. Then from the terminal, run

    ```make build_makefile ; make compile ```

## Suggested reading

Many (free) books exist for Coq, the following one is a good introduction for the style of modeling we are using:

- Chlipala, Adam. Certified Programming with Dependent Types - A Pragmatic Introduction to the Coq Proof Assistant. MIT Press, 2013. http://mitpress.mit.edu/books/certified-programming-dependent-types.

  This book is available from the author website: http://adam.chlipala.net/cpdt/

- An additional reference is the collection of books from https://softwarefoundations.cis.upenn.edu/

- This list gathers many other relevant projects and links: https://project-awesome.org/coq-community/awesome-coq
