(lang dune 3.6)
(name coq-stdlib-doc)

; We use directory targets in documentation
(using directory-targets 0.1)

(license LGPL-2.1-only)
(maintainers "The Coq development team <coqdev@inria.fr>")
(authors "The Coq development team, INRIA, CNRS, and contributors")
; This generates bug-reports and dev-repo
(source (github coq/coq))
(homepage https://coq.inria.fr/)
(documentation "https://coq.github.io/doc/")
(version dev)

(package
 (name coq-stdlib-doc)
 (license "OPUBL-1.0")
 (depends
  (conf-python-3 :build)
  (coq (and :build (= :version))))
 (synopsis "The Coq Proof Assistant Standard Library --- Reference Manual")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the Reference Manual for the Standard Library."))

(package
 (name coq-stdlib)
 (synopsis "dummy package to satisfy dune"))
