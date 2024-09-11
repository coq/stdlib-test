{ rsync, coq, stdlib, coqPackages }:

coqPackages.lib.overrideCoqDerivation {

  pname = "stdlib-test";

  propagatedBuildInputs = [ rsync stdlib ]
    ++ (with coq.ocamlPackages; [ ocaml findlib zarith ]);

  preBuild = ''
    cd test-suite
  '';

  installPhase = ''
    echo "nothing to install"
  '';
} stdlib
