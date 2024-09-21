{ lib, mkCoqDerivation, coq, stdlib, version ? null }:

let
  fetcher = { domain, owner, repo, rev, sha256 ? null, ...}:
    fetchGit {
      url = "https://${domain}/${owner}/${repo}";
      ref = rev;
      submodules = true;
    };
in

mkCoqDerivation {
  pname = "cross-crypto";
  owner = "mit-plv";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  preConfigure = ''
    for f in $(find . -name "*.v") ; do sed -i $f -e 's/micromega.Lia/Lia/' ; done
  '';

  installPhase = ''
    echo "no install target"
  '';
}
