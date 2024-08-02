{ rsync, coq, stdlib, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "stdlib-test";

  propagatedBuildInputs = [ rsync stdlib ]
    ++ (with coq.ocamlPackages; [ ocaml findlib zarith ]);

  useDune = false;

  preBuild = ''
    cd test-suite
  '';

  installPhase = ''
    echo "nothing to install"
  '';
} stdlib
