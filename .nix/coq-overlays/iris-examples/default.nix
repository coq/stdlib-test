{ lib, mkCoqDerivation, coq, iris, autosubst, version ? null }:

mkCoqDerivation {
  pname = "iris-examples";
  domain = "gitlab.mpi-sws.org";
  owner = "iris";
  repo = "examples";
  inherit version;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ iris autosubst ];

  preBuild = ''
    if [[ -f coq-lint.sh ]]
    then patchShebangs coq-lint.sh
    fi
  '';
}
