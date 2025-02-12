DUNE=dev/with-rocq-wrap.sh dune

all install:
	+$(MAKE) -C theories $@

dune:
	$(DUNE) build -p rocq-stdlib @install

dune-install:
	$(DUNE) install --root . rocq-stdlib

build-% install-%:
	+$(MAKE) -C theories $@

# Make of individual .vo
theories/%.vo:
	+$(MAKE) -C theories $*.vo

refman-html:
	$(DUNE) build --root . --no-buffer @refman-html

stdlib-html:
	$(DUNE) build --root . @stdlib-html

include Makefile.ci
