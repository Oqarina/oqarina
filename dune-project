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
 (synopsis "Oqarina provides a collection of libraries to manipulate AADL models as Coq types.")
 (description "Oqarina provides a collection of libraries to manipulate AADL models as Coq types.")
 (depends
  (dune (> 2.5))
  (coq  (and :dev (>= 8.13)))
  (coq-ext-lib :dev)
  (coq-io (>= 4.0.0))
  (coq-io-system (>= 2.4.1))
  (coq-json :dev)
  (coq-menhirlib :dev)
  (menhir :dev)))
