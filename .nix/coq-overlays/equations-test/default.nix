{ mkCoqDerivation, equations, version ? null }:

mkCoqDerivation {
  pname = "equations-test";
  repo = "Coq-Equations";
  owner = "mattam82";
  inherit version;

  propagatedBuildInputs = [ equations ];

  mlPlugin = true;

  buildFlags = [ "test-suite" "examples" ];

  preBuild = ''
    coq_makefile -f _CoqProject -o Makefile.coq
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
