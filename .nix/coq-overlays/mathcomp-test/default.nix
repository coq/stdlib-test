{ mkCoqDerivation, coq, mathcomp, version ? null }:

mkCoqDerivation {
  pname = "math-comp-test";
  repo = "math-comp";
  owner = "math-comp";
  inherit version;

  propagatedBuildInputs = [ mathcomp coq.ocamlPackages.ocaml ];

  buildFlags = [ "test-suite" ];

  installPhase = ''
    echo "nothing to install"
  '';
}
