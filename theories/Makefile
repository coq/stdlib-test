ROCQBIN?=$(dir $(shell which rocq))
ROCQMAKEFILE?=$(ROCQBIN)rocq makefile
ROCQMAKEOPTIONS?=
ROCQMAKEFILEOPTIONS?=

build-%: Makefile-%.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS)

Makefile-%.coq: Make.%
	$(ROCQMAKEFILE) $(ROCQMAKEFILEOPTIONS) -f $< -o $@

install-%: Makefile-%.coq
	+$(MAKE) -f $< $(ROCQMAKEOPTIONS) install
