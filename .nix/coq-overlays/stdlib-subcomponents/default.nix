# CI job to test that we don't break the subcomponent structure of the stdlib,
# as described in the graph doc/stdlib/depends

{ stdlib }:

let
  # stdlib subcomponents with their dependencies
  # when editing this, ensure to keep doc/stdlib/depends in sync
  components = {
    "logic" = [ ];
    "relations" = [ ];
    "program" = [ "logic" ];
    "classes" = [ "program" "relations" ];
    "bool" = [ "classes" ];
    "structures" = [ "bool" ];
    "arith-base" = [ "structures" ];
    "positive" = [ "arith-base" ];
    "narith" = [ "positive" ];
    "zarith-base" = [ "narith" ];
    "list" = [ "arith-base" ];
    "ring" = [ "zarith-base" "list" ];
    "arith" = [ "ring" ];
    "string" = [ "arith" ];
    "lia" = [ "arith" ];
    "zarith" = [ "lia" ];
    "qarith-base" = [ "ring" ];
    "field" = [ "qarith-base" "zarith" ];
    "lqa" = [ "field" ];
    "qarith" = [ "field" ];
    "nsatz" = [ "zarith" "qarith-base" ];
    "classical-logic" = [ "arith" ];
    "sets" = [ "classical-logic" ];
    "vectors" = [ "list" ];
    "sorting" = [ "lia" "sets" "vectors" ];
    "orders-ex" = [ "string" "sorting" ];
    "unicode" = [ ];
    "primitive-int" = [ "unicode" "zarith" ];
    "primitive-floats" = [ "primitive-int" ];
    "primitive-array" = [ "primitive-int" ];
    "primitive-string" = [ "primitive-int" "orders-ex" ];
    "reals" = [ "nsatz" "lqa" "qarith" "classical-logic" "vectors" ];
    "fmaps-fsets-msets" = [ "orders-ex" "zarith" ];
    "extraction-base" = [ ];
    "extraction" = [ "extraction-base" "primitive-string" "primitive-array" "primitive-floats" ];
    "funind" = [ "extraction-base" "arith-base" ];
    "wellfounded" = [ "list" ];
    "streams" = [ "logic" ];
    "derive" = [ ];
    "rtauto" = [ "positive" "list" ];
    "compat" = [ "rtauto" "fmaps-fsets-msets" "funind" "extraction" "reals" "wellfounded" "streams" "derive" ];
    "all" = [ "compat" ];
  };

  stdlib_ = component: let
    pname = "stdlib-${component}";
    stdlib-deps = map stdlib_ components.${component};
    in stdlib.overrideAttrs ({
      inherit pname;
      propagatedBuildInputs = stdlib-deps;
    } // (if component != "all" then {
      buildFlags = [ "build-${component}" ];
      installTargets = [ "install-${component}" ];
    } else {
      buildPhase = ''
        echo "nothing left to build"
      '';
      installPhase = ''
        echo "nothing left to install"
      '';
    }));
in stdlib_ "all"
