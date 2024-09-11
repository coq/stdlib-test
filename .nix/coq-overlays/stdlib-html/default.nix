{ graphviz, stdlib, coqPackages }:

coqPackages.lib.overrideCoqDerivation {
  pname = "stdlib-html";

  overrideBuildInputs = stdlib.buildInputs ++ [ graphviz ];

  preBuild = ''
    patchShebangs doc/stdlib/make-library-index
  '';

  buildFlags = [ "stdlib-html" ];
} stdlib
