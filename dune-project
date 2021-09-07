(lang dune 2.8)
(using coq 0.2)
(name coq-oqarina)

(generate_opam_files true)

(source (github oqarina/oqarina))
(license BSD)
(authors "Jerome Hugues" "Will Klieber" "Lutz Wrage")
(maintainers "jhugues@andrew.cmu.edu")

(package
 (name coq-oqarina)
 (synopsis "Oqarina is a mechanization of AADL in Coq.")
 (description "Oqarina is a mechanization of AADL in Coq. It provides a collection of libraries to manipulate AADL models as Coq types, and a formalization of the behavioral semantics of AADL faithful to the AADL standard v2.3.")
 (depends
  (dune (> 2.5))
  (coq (and :dev (>= 8.13))) ;; LGPLv2.1, https://github.com/coq/coq/blob/master/LICENSE
  (coq-ext-lib :dev)         ;; BSD 2-Clause, https://github.com/coq-community/coq-ext-lib/blob/master/LICENSE
  (coq-io (>= 4.0.0))        ;; MIT, https://github.com/coq-io/io/blob/master/LICENSE
  (coq-io-system (>= 2.4.1)) ;; MIT, https://github.com/coq-io/system/blob/master/LICENSE
  (coq-json :dev)            ;; BSD 3-Clause, https://github.com/liyishuai/coq-json/blob/comrade/LICENSE
))

