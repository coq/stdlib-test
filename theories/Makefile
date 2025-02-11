ROCQBIN?=$(dir $(shell which rocq))
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=

build-%: Makefile-%.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS)

Makefile-%.coq: Make.%
	for f in $$(cat $< | sed -e 's/#.*//;s/-.*//' | grep -v '^[ \t]*$$') ; do \
	  d=$$(dirname $${f}) ; \
	  if [ $${d%/_*} != $${d} ] ; then \
	    mkdir -p $${d} ; \
	    ln -sf ../$$(basename $${f}) $${d} ; \
	  fi ; \
	done
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< -o $@

install-%: Makefile-%.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) install
