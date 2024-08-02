{ rsync, coq, stdlib }:

stdlib.overrideAttrs {
  propagatedBuildInputs = [ rsync stdlib ]
    ++ (with coq.ocamlPackages; [ ocaml findlib zarith ]);

  preBuild = ''
    cd test-suite
  '';

  installPhase = ''
    echo "nothing to install"
  '';
}
