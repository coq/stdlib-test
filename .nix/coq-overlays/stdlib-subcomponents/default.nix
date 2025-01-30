# CI job to test that we don't break the subcomponent structure of the stdlib,
# as described in the graph doc/stdlib/depends

{ coq, stdlib, coqPackages }:

let
  # stdlib subcomponents with their dependencies
  # when editing this, ensure to keep doc/stdlib/depends in sync
  components = {
    "corelib-wrapper" = [ ];
    "logic" = [ ];
    "relations" = [ "corelib-wrapper" ];
    "program" = [ "corelib-wrapper" "logic" ];
    "classes" = [ "program" "relations" ];
    "bool" = [ "classes" ];
    "structures" = [ "bool" ];
    "arith-base" = [ "structures" ];
    "positive" = [ "arith-base" ];
    "narith" = [ "positive" ];
    "zarith-base" = [ "narith" ];
    "lists" = [ "arith-base" ];
    "ring" = [ "zarith-base" "lists" ];
    "arith" = [ "ring" ];
    "strings" = [ "arith" ];
    "lia" = [ "arith" ];
    "zarith" = [ "lia" ];
    "qarith-base" = [ "ring" ];
    "field" = [ "qarith-base" "zarith" ];
    "lqa" = [ "field" ];
    "qarith" = [ "field" ];
    "nsatz" = [ "zarith" "qarith-base" ];
    "classical-logic" = [ "arith" ];
    "sets" = [ "classical-logic" ];
    "vectors" = [ "lists" ];
    "sorting" = [ "lia" "sets" "vectors" ];
    "orders-ex" = [ "strings" "sorting" ];
    "unicode" = [ ];
    "primitive-int" = [ "unicode" "zarith" ];
    "primitive-floats" = [ "primitive-int" ];
    "primitive-array" = [ "primitive-int" ];
    "primitive-string" = [ "primitive-int" "orders-ex" ];
    "reals" = [ "nsatz" "lqa" "qarith" "classical-logic" "vectors" ];
    "fmaps-fsets-msets" = [ "orders-ex" "zarith" ];
    "extraction" = [ "primitive-string" "primitive-array" "primitive-floats" ];
    "funind" = [ "arith-base" ];
    "wellfounded" = [ "lists" ];
    "streams" = [ "logic" ];
    "rtauto" = [ "positive" "lists" ];
    "compat" = [ "rtauto" "fmaps-fsets-msets" "funind" "extraction" "reals" "wellfounded" "streams" ];
    "all" = [ "compat" ];
  };

  stdlib_ = component: let
    pname = "stdlib-${component}";
    stdlib-deps = map stdlib_ components.${component};
    in coqPackages.lib.overrideCoqDerivation ({
      inherit pname;
      propagatedBuildInputs = stdlib-deps;
      useDune = false;
      mlPlugin = true;
    } // (if component != "all" then {
      buildPhase = ''
        make ''${enableParallelBuilding:+-j $NIX_BUILD_CORES} build-${component}
      '';
      installPhase = ''
        make COQLIBINSTALL=$out/lib/coq/${coq.coq-version}/user-contrib install-${component}
      '';
    } else {
      buildPhase = ''
        echo "nothing left to build"
      '';
      installPhase = ''
        echo "nothing left to install"
      '';
    })) stdlib;
in stdlib_ "all"
