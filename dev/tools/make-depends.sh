#!/bin/bash

# this should be called from root as
# % dev/tools/make-depends.sh

THEORIES="theories"

declare -A FILE_PKG

# Associate each *.v source file to its corresponding <pkg>,
# according to theories/Make.<pkg>
FILE_PKG["All.v"]="all"
for makefile in theories/Make.* ; do
    PKG=${makefile#theories/Make.}
    for f in $(cat ${makefile} | sed -e 's/#.*//;s/-.*//' | grep -v '^[ \t]*$') ; do
        f=$(echo ${f} | sed -e 's,/_[^/]*,,')
        if [ -n ${FILE_PKG[${f}]:-""} ] ; then
            echo "Error: File ${f} appears in both theories/Make.${FILE_PKG[${f}]} and theories/Make.${PKG}."
            exit 1
        fi
        FILE_PKG[${f}]=${PKG}
    done
done

# Check that each *.v file in theories appears in some <pkg>
for f in $(find ${THEORIES} -name "*.v") ; do
    f=$(echo ${f} | sed -e "s,${THEORIES}/,,")
    if [ -z ${FILE_PKG[${f}]} ] ; then
        echo "Error: File ${f} is not listed in any theories/Make.* file."
        exit 1
    fi
done

# Retrieve dependencies and build graph
(echo "digraph stdlib_deps {";
echo "node [shape=rectangle, style=filled, color=\"#ff540a\", URL=\"#\\N\"];";
rocq dep -Q ${THEORIES} Stdlib ${THEORIES} | sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*v//p' | \
    while read src dst; do
        src=${src#theories.}
        srcf="$(echo ${src%.vo} | tr '.' '/').v"
        for d in $dst; do
            d=${d#theories.}
            df="$(echo ${d%.vo} | tr '.' '/').v"
            if [ -z ${FILE_PKG[${df}]:-""} ] ; then continue ; fi
            # File dependencies
            # echo "\"(${src}) ${FILE_PKG[${srcf}]}\" -> \"${FILE_PKG[${df}]} (${d%.vo})\" ;"
            # Subcomponent dependencies
            echo "\"${FILE_PKG[${srcf}]}\" -> \"${FILE_PKG[${df}]}\" ;"
        done
    done
echo "}") | tred
