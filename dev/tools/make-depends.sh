#!/bin/sh

DIR= $(dirname $0)
echo "DIR = \"$DIR\""


# (echo "digraph stdlib_deps {";
# echo "node [shape=ellipse, style=filled, color=lightblue];";
# coqdep -R ../coq/theories Coq ../coq/theories | sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*v//p' | \
#     while read src dst; do
#         for d in $dst; do
#             d=${d#...coq.theories.}
#             echo "\"${src#...coq.theories.}\" -> \"${d%.vo}\" ;"
#         done
#     done;
# echo "}") | tred >> depends
