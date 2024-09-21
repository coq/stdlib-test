{ mkCoqDerivation, coq-elpi, version ? null }:

mkCoqDerivation {
  pname = "coq-elpi-test";
  repo = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  propagatedBuildInputs = [ coq-elpi ];

  useDune = true;

  buildPhase = ''
    export DUNE_build_FLAGS="--release"
    make test-core
    make examples
    make test-apps
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
