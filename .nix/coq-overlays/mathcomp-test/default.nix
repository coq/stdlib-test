{ mkCoqDerivation, mathcomp, version ? null }:

mkCoqDerivation {
  pname = "math-comp-test";
  repo = "math-comp";
  owner = "math-comp";
  inherit version;

  propagatedBuildInputs = [ mathcomp ];

  buildFlags = [ "test-suite" ];

  installPhase = ''
    echo "nothing to install"
  '';
}
