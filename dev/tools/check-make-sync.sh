#!/bin/sh

MAKE_FILES=$(find theories -name "Make.*")

FILES_OTHERS=files_others__
FILES_ALL=files_all__

rm -f ${FILES_OTHERS} ${FILES_ALL}
grep "[.]v" ${MAKE_FILES} | sed -e 's/.*://' | sort > ${FILES_OTHERS}
find theories -name "*.v" | sed -e 's_theories/__' | sort > ${FILES_ALL}

if $(diff -q ${FILES_OTHERS} ${FILES_ALL} > /dev/null) ; then
  echo "Make.* match files in theories/"
else
  echo "Make.* and files in theories/ don't match"
  diff ${FILES_OTHERS} ${FILES_ALL}
  exit 1
fi

rm -f ${FILES_OTHERS} ${FILES_ALL}
