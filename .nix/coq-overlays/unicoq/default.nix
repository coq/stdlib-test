{ lib, mkCoqDerivation, coq, version ? null }:

mkCoqDerivation {
  pname = "unicoq";
  owner = "unicoq";
  inherit version;
  defaultVersion = null;  # no released version

  mlPlugin = true;

  preBuild = ''
    coq_makefile -f _CoqProject -o Makefile
  '';
}
