(lang dune 3.8)
(using coq 0.7)
(name coq-oqarina)

(generate_opam_files true)

(source (github oqarina/oqarina))
(license BSD)
(authors "Jerome Hugues" "Will Klieber" "Lutz Wrage")
(maintainers "jhugues@andrew.cmu.edu")

(package
 (name coq-oqarina)
 (synopsis "mechanization of AADL in Coq")
 (description "Oqarina is a mechanization of AADL in Coq. It provides a collection of libraries to manipulate AADL models as Coq types, and a formalization of the behavioral semantics of AADL faithful to the AADL standard v2.3.")
 (depends
  (dune (>= 3.8))
  (coq (and :dev (>= 8.16))) ;; LGPLv2.1, https://github.com/coq/coq/blob/master/LICENSE
  (coq-ext-lib :dev)         ;; BSD 2-Clause, https://github.com/coq-community/coq-ext-lib/blob/master/LICENSE
  (coq-simple-io (>= 1.6.0)) ;; MIT, https://github.com/Lysxia/coq-simple-io/blob/master/LICENSE
  (coq-json :dev)            ;; BSD 3-Clause, https://github.com/liyishuai/coq-json/blob/comrade/LICENSE
  (coq-kruskal-trees (>= 1.0))   ;; CeCILL-B, https://github.com/DmxLarchey/Kruskal-Trees
  ;(coq-prosa (= 0.5))           ;; BSD 2-Clause, https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs/-/blob/master/LICENSE
  (coq-mathcomp-finmap (>= 1.5.2))
  (coq-mathcomp-multinomials (>= 1.6.0))
  (coq-coqeal (>= 1.1.3))
))
