#!/bin/sh

# List of all files in the coq repo
FILES_PRELUDE="\
  ArrayAxioms.v \
  Basics.v \
  BinNums.v \
  CMorphisms.v \
  CRelationClasses.v \
  CarryType.v \
  Datatypes.v \
  Decimal.v \
  Equivalence.v \
  FloatAxioms.v \
  FloatClass.v \
  FloatOps.v \
  Hexadecimal.v \
  Init.v \
  IntDef.v \
  ListDef.v \
  Logic.v \
  Ltac.v \
  Morphisms.v \
  Morphisms_Prop.v \
  Nat.v \
  NatDef.v \
  Notations.v \
  Number.v \
  Peano.v \
  PosDef.v \
  Prelude.v \
  PrimArray.v \
  PrimFloat.v \
  PrimInt63.v \
  PrimString.v \
  PrimStringAxioms.v \
  RelationClasses.v \
  Relation_Definitions.v \
  Setoid.v \
  SetoidTactics.v \
  Sint63Axioms.v \
  SpecFloat.v \
  Specif.v \
  Sumbool.v \
  Tactics.v \
  Uint63Axioms.v \
  Utils.v \
  Wf.v \
  ssrbool.v \
  ssrclasses.v \
  ssreflect.v \
  ssrfun.v \
  ssrmatching.v \
  ssrsetoid.v \
  ssrunder.v"

ALL_FILES=all_files__
ALL_FILES_UNIQ=all_files_uniq__

rm -f ${ALL_FILES} ${ALL_FILES_UNIQ}
(for f in ${FILES_PRELUDE} $(find . -name "*.v") ; do basename $f ; done) | sort > ${ALL_FILES}
uniq ${ALL_FILES} > ${ALL_FILES_UNIQ}

if $(diff -q ${ALL_FILES_UNIQ} ${ALL_FILES} > /dev/null) ; then
  echo "No files with duplicate name"
else
  echo "Some files with the same name"
  diff ${ALL_FILES_UNIQ} ${ALL_FILES}
  exit 1
fi

rm -f ${ALL_FILES} ${ALL_FILES_UNIQ}
