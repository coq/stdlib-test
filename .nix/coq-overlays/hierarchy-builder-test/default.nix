{ mkCoqDerivation, hierarchy-builder, version ? null }:

mkCoqDerivation {
  pname = "hierarchy-builder-test";
  repo = "hierarchy-builder";
  owner = "math-comp";
  inherit version;

  propagatedBuildInputs = [ hierarchy-builder ];

  buildFlags = [ "test-suite" ];

  installPhase = ''
    echo "nothing to install"
  '';
}
