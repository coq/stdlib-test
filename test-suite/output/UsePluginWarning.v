(* -*- mode: coq; coq-prog-args: ("-w" "-extraction-logical-axiom") -*- *)
Require TestSuite.extraction.
Axiom foo : Prop.

Extraction foo.

