#!/bin/sh

# Check for duplicate files
# Those would yield ambiguity when doing "From Stdlib Require File.".
# There are already a few in the prelude, let's not add more.

# Files that are already duplicate
DUPLICATE_FILES=" \
  Byte.v \
  Tactics.v \
  Tauto.v \
  Wf.v \
"

ALL_FILES=all_files__
ALL_FILES_UNIQ=all_files_uniq__

rm -f ${ALL_FILES} ${ALL_FILES_UNIQ}
(for f in $(find theories -name "*.v" -type f) ; do basename $f ; done) | sort > ${ALL_FILES}
(uniq ${ALL_FILES} ; for f in ${DUPLICATE_FILES} ; do echo $f ; done) | sort > ${ALL_FILES_UNIQ}

if $(diff -q ${ALL_FILES_UNIQ} ${ALL_FILES} > /dev/null) ; then
  echo "No files with duplicate name."
else
  echo "Error: Some files bear the same name:"
  diff ${ALL_FILES_UNIQ} ${ALL_FILES}
  exit 1
fi

rm -f ${ALL_FILES} ${ALL_FILES_UNIQ}
