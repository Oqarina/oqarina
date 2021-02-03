# AADL/Coq

This folder is a very preliminary attempt at formalizing some aspects of AADL using Coq.

## Directory structure

* `extra` : additional material for producing HTML from coq
* `latex-src` : LaTeX source code of the corresponding TR.
* `src`: Coq sources

## Required software

This demo has been tested using Coq version 8.12.1 and VSCoq extension for Visual Code.

## Usage

You may either
- just run from a makefile, type `make` for available targets or
- play with the Coq files from VSCode. In this case, make sure the Coq directory is the only one in your workspace. Then from the terminal, run

    ```make build_makefile ; make compile ```

## Suggested reading

Many (free) books exist for Coq, the following one is a good introduction for the style of modeling we are using:

- Chlipala, Adam. Certified Programming with Dependent Types - A Pragmatic Introduction to the Coq Proof Assistant. MIT Press, 2013. http://mitpress.mit.edu/books/certified-programming-dependent-types.

  This book is available from the author website: http://adam.chlipala.net/cpdt/

An additional reference is the collection of books from https://softwarefoundations.cis.upenn.edu/
