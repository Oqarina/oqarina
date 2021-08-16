FROM coqorg/coq:8.13-ocaml-4.11-flambda
RUN opam repo add coq-released --all-switches https://coq.inria.fr/opam/released && \
    opam repo add coq-extra-dev --all-switches https://coq.inria.fr/opam/extra-dev && \
    opam install -y coq-ext-lib menhir coq-menhirlib coq-json coq-io-system
WORKDIR /work