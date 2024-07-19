{ smtcoq, trakt, version ? null }:
(smtcoq.override { inherit version; }).overrideAttrs (o: {
  pname = "smtcoq-trakt";
  propagatedBuildInputs = o.propagatedBuildInputs ++ [ trakt ];
})
