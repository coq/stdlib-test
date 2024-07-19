{ lib, bash, ncurses, python3, mkCoqDerivation, coq, stdlib, version ? null }:

mkCoqDerivation {
  pname = "coq-tools";
  owner = "JasonGross";
  inherit version;
  defaultVersion = null;  # no released version

  nativeBuildInputs = [ bash ncurses python3 ];
  propagatedBuildInputs = [ stdlib ];

  preConfigure = ''
    for f in $(find . -name "*.sh") ; do patchShebangs $f ; done
    for f in $(find . -name "*.py") ; do patchShebangs $f ; done
  '';

  buildFlags = [ "check" ];

  installPhase = "";
}
