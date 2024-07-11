#!/bin/sh

# this should be call from root as
# % dev/tools/make-depends.sh

(echo "digraph stdlib_deps {";
coqdep -R theories Coq theories | sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*v//p' | \
    while read src dst; do
        for d in $dst; do
            d=${d#theories.}
            echo "\"${src#theories.}\" -> \"${d%.vo}\" ;"
        done
    done;
echo "}") | tred \
| sed -e 's/"Arith[.]All[.][^"]*"/"coq-stdlib-arith"/g' \
| sed -e 's/"Arith[.]Base[.][^"]*"/"coq-stdlib-arith-base"/g' \
| sed -e 's/"Numbers[.]NumPrelude"/"coq-stdlib-arith-base"/g' \
| sed -e 's/"Numbers[.]NatInt[.][^"]*"/"coq-stdlib-arith-base"/g' \
| sed -e 's/"Numbers[.]Natural[.]Abstract[.][^"]*"/"coq-stdlib-arith-base"/g' \
| sed -e 's/"Classes[.]Arith[.][^"]*"/"coq-stdlib-arith-base"/g' \
| sed -e 's/"Bool[.][^"]*"/"coq-stdlib-bool"/g' \
| sed -e 's/"Classes[.]All[.][^"]*"/"coq-stdlib-classes"/g' \
| sed -e 's/"Logic[.]Classical[.][^"]*"/"coq-stdlib-classical-logic"/g' \
| sed -e 's/"Compat[.][^"]*"/"coq-stdlib-compat"/g' \
| sed -e 's/"derive[.][^"]*"/"coq-stdlib-derive"/g' \
| sed -e 's/"extraction[.]All[.][^"]*"/"coq-stdlib-extraction"/g' \
| sed -e 's/"extraction[.]Base[.][^"]*"/"coq-stdlib-extraction-base"/g' \
| sed -e 's/"QArith[.]Field[.][^"]*"/"coq-stdlib-field"/g' \
| sed -e 's/"setoid_ring[.]Q[.][^"]*"/"coq-stdlib-field"/g' \
| sed -e 's/"FSets[.][^"]*"/"coq-stdlib-fmaps-fsets-msets"/g' \
| sed -e 's/"MSets[.][^"]*"/"coq-stdlib-fmaps-fsets-msets"/g' \
| sed -e 's/"funind[.][^"]*"/"coq-stdlib-funind"/g' \
| sed -e 's/"omega[.][^"]*"/"coq-stdlib-lia"/g' \
| sed -e 's/"micromega[.]Zify[.][^"]*"/"coq-stdlib-lia"/g' \
| sed -e 's/"micromega[.]Lia[.][^"]*"/"coq-stdlib-lia"/g' \
| sed -e 's/"Lists[.][^"]*"/"coq-stdlib-list"/g' \
| sed -e 's/"Numbers[.]NaryFunctions"/"coq-stdlib-list"/g' \
| sed -e 's/"Logic[.]Lists[.][^"]*"/"coq-stdlib-list"/g' \
| sed -e 's/"Classes[.]Lists[.][^"]*"/"coq-stdlib-list"/g' \
| sed -e 's/"Logic[.]Base[.][^"]*"/"coq-stdlib-logic"/g' \
| sed -e 's/"micromega[.]Lqa[.][^"]*"/"coq-stdlib-lqa"/g' \
| sed -e 's/"NArith[.][^"]*"/"coq-stdlib-narith"/g' \
| sed -e 's/"nsatz[.][^"]*"/"coq-stdlib-nsatz"/g' \
| sed -e 's/"Structures[.]Ex[.][^"]*"/"coq-stdlib-orders-ex"/g' \
| sed -e 's/"Numbers[.]AltBinNotations"/"coq-stdlib-orders-positive"/g' \
| sed -e 's/"PArith[.][^"]*"/"coq-stdlib-positive"/g' \
| sed -e 's/"Array[.][^"]*"/"coq-stdlib-primitive-array"/g' \
| sed -e 's/"Floats[.][^"]*"/"coq-stdlib-primitive-floats"/g' \
| sed -e 's/"Numbers[.]Cyclic[^"]*"/"coq-stdlib-primitive-int"/g' \
| sed -e 's/"micromega[.]Int63[^"]*"/"coq-stdlib-primitive-int"/g' \
| sed -e 's/"Strings[.]PString"/"coq-stdlib-primitive-string"/g' \
| sed -e 's/"Program[.]All[.][^"]*"/"coq-stdlib-program"/g' \
| sed -e 's/"QArith[.]All[.][^"]*"/"coq-stdlib-qarith"/g' \
| sed -e 's/"Numbers[.]Q[.][^"]*"/"coq-stdlib-qarith"/g' \
| sed -e 's/"QArith[.]Base[.][^"]*"/"coq-stdlib-qarith-base"/g' \
| sed -e 's/"Reals[.][^"]*"/"coq-stdlib-reals"/g' \
| sed -e 's/"setoid_ring[.]R[.][^"]*"/"coq-stdlib-reals"/g' \
| sed -e 's/"micromega[.]Lra[.][^"]*"/"coq-stdlib-reals"/g' \
| sed -e 's/"Numbers[.]R[.][^"]*"/"coq-stdlib-reals"/g' \
| sed -e 's/"Relations[.]All[.][^"]*"/"coq-stdlib-relations"/g' \
| sed -e 's/"ZArith[.]Ring[.][^"]*"/"coq-stdlib-ring"/g' \
| sed -e 's/"setoid_ring[.]Z[.][^"]*"/"coq-stdlib-ring"/g' \
| sed -e 's/"rtauto[.][^"]*"/"coq-stdlib-rtauto"/g' \
| sed -e 's/"Sets[.][^"]*"/"coq-stdlib-sets"/g' \
| sed -e 's/"Sorting[.][^"]*"/"coq-stdlib-sorting"/g' \
| sed -e 's/"Streams[.][^"]*"/"coq-stdlib-streams"/g' \
| sed -e 's/"Strings[.][^"]*"/"coq-stdlib-string"/g' \
| sed -e 's/"Numbers[.]Strings[.][^"]*"/"coq-stdlib-string"/g' \
| sed -e 's/"Structures[.]Def[.][^"]*"/"coq-stdlib-structures"/g' \
| sed -e 's/"Unicode[.][^"]*"/"coq-stdlib-unicode"/g' \
| sed -e 's/"Vectors[.][^"]*"/"coq-stdlib-vectors"/g' \
| sed -e 's/"Wellfounded[.][^"]*"/"coq-stdlib-wellfounded"/g' \
| sed -e 's/"Numbers[.]Natural[.]Binary[.][^"]*"/"coq-stdlib-zarith"/g' \
| sed -e 's/"ZArith[.]All[.][^"]*"/"coq-stdlib-zarith"/g' \
| sed -e 's/"Numbers[.]Integer[.]Binary[.][^"]*"/"coq-stdlib-zarith"/g' \
| sed -e 's/"Numbers[.]Integer[.]NatPairs[.][^"]*"/"coq-stdlib-zarith"/g' \
| sed -e 's/"Numbers[.]Z[.][^"]*"/"coq-stdlib-zarith"/g' \
| sed -e 's/"btauto[.][^"]*"/"coq-stdlib-zarith"/g' \
| sed -e 's/"Numbers[.]Integer[.]Abstract[.][^"]*"/"coq-stdlib-zarith-base"/g' \
| sed -e 's/"ZArith[.]Base[.][^"]*"/"coq-stdlib-zarith-base"/g' \
| tail -n +2 | head -n -1 \
| sort | uniq \
> depends_core

(echo "digraph stdlib_deps {";
echo "node [shape=ellipse, style=filled, color=lightblue];";
awk -f dev/tools/depends-rm-loops.awk depends_core;
echo "}") | tred > depends

rm -f depends_core
