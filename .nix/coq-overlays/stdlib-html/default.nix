{ graphviz, stdlib, coqPackages }:

coqPackages.lib.overrideCoqDerivation {
  pname = "stdlib-html";

  overrideBuildInputs = stdlib.buildInputs ++ [ graphviz ];

  buildPhase = ''
    patchShebangs doc/stdlib/make-library-index
    dev/with-rocq-wrap.sh dune build @stdlib-html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '';

  installPhase = ''
    echo "nothing to install"
    touch $out
  '';
} stdlib
