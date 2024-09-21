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
  pname = "perennial";
  owner = "mit-pdos";
  inherit version fetcher;
  defaultVersion = null;  # no released version

  propagatedBuildInputs = [ stdlib ];

  buildFlags = [ "TIMED=false" "lite" ];

  installPhase = ''
    echo "not installing anything"
  '';
}
