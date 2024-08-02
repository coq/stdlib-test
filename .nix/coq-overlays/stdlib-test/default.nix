{ rsync, coq, stdlib, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "stdlib-test";

  propagatedBuildInputs = [ rsync stdlib ]
    ++ (with coq.ocamlPackages; [ ocaml findlib zarith ]);

  useDune = false;

  configurePhase = ''
    echo "nothing to configure"
  '';

  buildPhase = ''
    cd test-suite
    make -j $NIX_BUILD_CORES
  '';

  installPhase = ''
    echo "nothing to install"
  '';
} stdlib
