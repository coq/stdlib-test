{ graphviz, stdlib }:
stdlib.overrideAttrs (o: {
  buildInputs = o.buildInputs ++ [ graphviz ];

  preBuild = ''
    patchShebangs doc/stdlib/make-library-index
  '';

  buildFlags = [ "stdlib-html" ];
})
