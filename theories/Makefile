COQBIN?=$(dir $(shell which coqtop))
COQMAKEFILE?=$(COQBIN)coq_makefile
COQMAKEOPTIONS?=
COQMAKEFILEOPTIONS?=

build-%: Makefile-%.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS)

Makefile-%.coq: Make.%
	$(COQMAKEFILE) $(COQMAKEFILEOPTIONS) -f $< -o $@

install-%: Makefile-%.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS) install
