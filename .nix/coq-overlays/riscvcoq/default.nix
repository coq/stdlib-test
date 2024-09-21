let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = if owner == "mit-plv" then "https://${domain}/${owner}/fiat-crypto"
        else "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

{ lib, mkCoqDerivation, coq, coqutil, version ? null }@args:

mkCoqDerivation {
  pname = "riscvcoq";
  repo = "riscv-coq";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ coqutil ];

  makeFlags = [ "EXTERNAL_COQUTIL=1" ];

  buildFlags = [ "all" ];

  preBuild = "cd rupicola/bedrock2/deps/riscv-coq || true";
}
