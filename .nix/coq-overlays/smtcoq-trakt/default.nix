{ smtcoq, trakt, coqPackages, version ? null }:
coqPackages.lib.overrideCoqDerivation {
  pname = "smtcoq-trakt";
  repo = "smtcoq";
  inherit version;
  overrideBuildInputs = smtcoq.buildInputs ++ [ trakt ];
} smtcoq
