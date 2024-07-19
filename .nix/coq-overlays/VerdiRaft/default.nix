{ lib, mkCoqDerivation, coq, Verdi, version ? null }:

mkCoqDerivation {
  pname = "verdi-raft";
  owner = "uwplse";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ Verdi ];
}
