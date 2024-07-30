#!/bin/sh

MAKE_ALL=theories/Make.all
MAKE_OTHERS=$(find theories -name "Make.*" | grep -v "Make.all")

FILES_ALL=files_all__
FILES_OTHERS=files_others__

rm -f ${FILES_ALL} ${FILES_OTHERS}
grep "[.]v" ${MAKE_ALL} | sort > ${FILES_ALL}
grep "[.]v" ${MAKE_OTHERS} | sed -e 's/.*://' | sort > ${FILES_OTHERS}

if $(diff -q ${FILES_ALL} ${FILES_OTHERS} > /dev/null) ; then
  echo "Make.all and others Make.* do match"
else
  echo "Make.all and others Make.* don't match"
  diff ${FILES_ALL} ${FILES_OTHERS}
  exit 1
fi

rm -f ${FILES_ALL} ${FILES_OTHERS}
