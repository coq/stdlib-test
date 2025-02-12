#!/bin/sh

# Check that theories/All/All.v is up to date

ALL_FILES=all_files__
ACTUAL_FILES=actual_files__

rm -f ${ALL_FILES} ${ACTUAL_FILES}
grep "Require" theories/All/All.v | sed -e 's/From.*Require.*Export.*[.]\([a-zA-Z]\)/\1/' | sort > ${ALL_FILES}
(for f in $(find theories -name "*.v" -type f) ; do basename ${f%v} ; done) | grep -v "^All[.]$" | sort > ${ACTUAL_FILES}

if $(diff -q ${ALL_FILES} ${ACTUAL_FILES} > /dev/null) ; then
  echo "theories/All/All.v is up to date."
else
  echo "Error: theories/All/All.v needs some update:"
  diff -u ${ALL_FILES} ${ACTUAL_FILES}
  exit 1
fi

rm -f ${ALL_FILES} ${ACTUAL_FILES}
