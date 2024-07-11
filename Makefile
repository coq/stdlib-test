all:
	+$(MAKE) -C theories

install:
	+$(MAKE) -C theories install

# Make of individual .vo
theories/%.vo:
	+$(MAKE) -C theories ${@#theories/}

refman-html:
	dune build --no-buffer @refman-html
