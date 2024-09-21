{ lib, mkCoqDerivation, coq, mathcomp-word, version ? null }:

mkCoqDerivation {
  pname = "jasmin";
  owner = "jasmin-lang";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ mathcomp-word ];

  makeFlags = [ "-C proofs" ];
}
