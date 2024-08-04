with builtins; with (import <nixpkgs> {}).lib;
{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "stdlib";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  coqproject = "theories/_CoqProject";

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  # cachix.coq-community = {};
  
  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  
  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"
  
  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "coq-master";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles = let
    ## In some cases, light overrides are not available/enough
    ## in which case you can use either
    # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
    ## or a "long" overlay to put in `.nix/coq-overlays
    ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
    ## to automatically retrieve the one from nixpkgs
    ## if it exists and is correctly named/located

    ## You can override Coq and other coqPackages
    ## through the following attribute
    ## If <ocaml-pkg> does not support light overrides,
    ## you may use `overrideAttrs` or long overlays
    ## located in `.nix/ocaml-overlays`
    ## (there is no automation for this one)
    #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

    ## You can also override packages from the nixpkgs toplevel
    # <nix-pkg>.override.overrideAttrs = o: <overrides>;
    ## Or put an overlay in `.nix/overlays`

    ## you may mark a package as a main CI job (one to take deps and
    ## rev deps from) as follows
    # coqPackages.<main-pkg>.main-job = true;
    ## by default the current package and its shell attributes are main jobs

    ## you may mark a package as a CI job as follows
    #  coqPackages.<another-pkg>.job = "test";
    ## It can then built through
    ## nix-build --argstr bundle "default" --arg job "test";
    ## in the absence of such a directive, the job "another-pkg" will
    ## is still available, but will be automatically included in the CI
    ## via the command genNixActions only if it is a dependency or a
    ## reverse dependency of a job flagged as "main-job" (see above).

    ## Run on push on following branches (default [ "master" ])
    # push-branches = [ "master" "branch2" ];

    master = [
      "aac-tactics"
      "argosy"
      "async-test"
      "atbr"
      "autosubst"
      "bbv"
      "bedrock2"
      "bignums"
      "bignums-test"
      "category-theory"
      "ceres"
      "Cheerios"
      "coinduction"
      "CoLoR"
      # "compcert" # -> overlay
      "coqprime"
      "coquelicot"
      "coqutil"
      # "coq-elpi" # -> overlay
      # "coq-elpi-test" # -> overlay
      "coq-ext-lib"
      "coq-hammer"
      "coq-hammer-tactics"
      "coq-performance-tests"
      # "coq-tools" # -> overlay
      # "corn" # -> overlay
      # "cross-crypto" # -> overlay
      "deriving"
      "engine-bench"
      # TODO fcsl_pcm -> wait for MC 2 port
      # "fiat-crypto" # -> overlay
      # TODO fiat_parsers
      # TODO fiat_crypto_legacy
      # "flocq" # -> overlay
      "fourcolor"
      "hierarchy-builder"
      "hierarchy-builder-test"
      "http"
      "InfSeqExt"
      "iris"
      "iris-examples"
      "itauto"
      "ITree"
      "itree-io"
      # "json" # -> overlay
      # "kami" # -> overlay
      "mathcomp"
      "mathcomp-analysis"
      "mathcomp-bigenough"
      "mathcomp-finmap"
      "mathcomp-test"
      "mathcomp-zify"
      # "math-classes" # -> overlay
      "MenhirLib"
      "neural-net-coq-interp"
      "odd-order"
      "paco"
      "paramcoq-test"
      "parsec"
      "perennial"
      # "QuickChick" # -> overlay
      # "quickchick-test" # -> overlay
      "relation-algebra"
      # "rewriter" # -> overlay
      "riscvcoq"
      "rupicola"
      "sf"
      "simple-io"
      "stalmarck-tactic"
      "stdpp"
      "StructTact"
      "Verdi"
      "VerdiRaft"
      # "vst" # -> overlay
    ];
    coq-master = [
      "dpdgraph-test"
      "smtcoq"
      "trakt"
      "waterproof"
    ];
    main = [
      # "equations" # -> overlay
      # "equations-test" # -> overlay
      "jasmin"
      "mathcomp-word"
      # "metacoq" # -> overlay
    ];
    common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // listToAttrs (forEach coq-master (p:
      { name = p; value.override.version = "coq-master"; }))
    // listToAttrs (forEach main (p:
      { name = p; value.override.version = "main"; }))
    // { tlc.override.version = "master-for-coq-ci";
         smtcoq-trakt.override.version = "with-trakt-coq-master";
    } // {
      stdlib-refman-html.job = true;
      stdlib-subcomponents.job = true;
      stdlib-test.job = true;
      compcert.override.version = "proux01:stdlib_repo";
      coq-elpi.override.version = "proux01:stdlib_repo";
      coq-elpi-test.override.version = "proux01:stdlib_repo";
      coq-tools.override.version = "proux01:stdlib_repo";
      corn.override.version = "stdlib_repo";
      cross-crypto.override.version = "proux01:stdlib_repo";
      equations.override.version = "proux01:stdlib_repo";
      equations-test.override.version = "proux01:stdlib_repo";
      fiat-crypto.override.version = "proux01:stdlib_repo";
      flocq.override.version = "stdlib_repo";
      json.override.version = "proux01:stdlib_repo";
      kami.override.version = "proux01:stdlib_repo";
      math-classes.override.version = "stdlib_repo";
      metacoq.override.version = "proux01:stdlib_repo";
      QuickChick.override.version = "proux01:stdlib_repo";
      quickchick-test.override.version = "proux01:stdlib_repo";
      rewriter.override.version = "proux01:stdlib_repo";
      vst.override.version = "proux01:stdlib_repo";

      # Free overlays (can be merged independently of the PR)
      # aac-tactics.override.version = "stdlib_repo";
      # argosy.override.version = "proux01:stdlib_repo";
      # atbr.override.version = "stdlib_repo";
      # autosubst.override.version = "stdlib_repo";
      # bbv.override.version = "proux01:stdlib_repo";
      # bedrock2.override.version = "proux01:stdlib_repo";
      # category-theory.override.version = "proux01:stdlib_repo";
      # CoLoR.override.version = "proux01:stdlib_repo";
      # coq-ext-lib.override.version = "stdlib_repo";
      # coq-hammer.override.version = "proux01:stdlib_repo";
      # coq-hammer-tactics.override.version = "proux01:stdlib_repo";
      # coq-performance-tests.override.version = "proux01:stdlib_repo";
      # coqutil.override.version = "proux01:stdlib_repo";
      # engine-bench.override.version = "proux01:stdlib_repo";
      # iris.override.version = "proux:stdlib_repo";
      # ITree.override.version = "proux01:stdlib_repo";
      # mathcomp.override.version = "proux01:stdlib_repo";
      # mathcomp-test.override.version = "proux01:stdlib_repo";
      # neural-net-coq-interp.override.version = "proux01:stdlib_repo";
      # paramcoq-test.override.version = "stdlib_repo";
      # perennial.override.version = "proux01:stdlib_repo";
      # riscvcoq.override.version = "proux01:stdlib_repo";
      # rupicola.override.version = "proux01:stdlib_repo";
      # sf.override.version = "proux01:stdlib_repo";
      # simple-io.override.version = "proux01:stdlib_repo";
      # tlc.override.version = "proux01:stdlib_repo";
      # waterproof.override.version = "proux01:stdlib_repo";
    };
  in {
    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "proux01:stdlib_repo";
    };
    "coq-master".ocamlPackages = {
      elpi.override.version = "1.19.2";
    };
  };
}
