Installing From Sources
=======================

To install and use Rocq, we recommend relying on [the Rocq
platform](https://github.com/coq/platform/) or on a package manager
(e.g. opam or Nix).

See https://coq.inria.fr/download and
https://github.com/coq/coq/wiki#coq-installation to learn more.

If you need to build the stdlib from sources manually (e.g. to
contribute to the stdlib or to write a Rocq package), the remainder of this
file explains how to do so.

Build Requirements
------------------

To compile the stdlib yourself, you need:

- [Rocq](https://github.comq/coq/coq)
  Look into [rocq-stdlib.opam](./rocq-stdlib.opam) for supported versions.

Opam (https://opam.ocaml.org/) is recommended to install Rocq.

    $ opam switch create rocq --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
    $ eval $(opam env)
    $ opam install rocq-core

should get you a reasonable Rocq environment to compile the stdlib.
See the OPAM documentation for more help.

Nix users can also get all the required dependencies by running:

    $ nix-shell

Build and install procedure
---------------------------

To build and install the stdlib do:

    $ make
    $ make install

Then, the recommended way to require standard library modules is `From
Stdlib Require {Import,Export,} <LibraryModules>.`, except for `Byte`
(use `From Stdlib.Strings` or `From Stdlib.Init`), `Tactics` (use
`From Stdlib.Program` or `From Stdlib.Init`), `Tauto` (use `From
Stdlib.micromega` of `From Stdlib.Init`) and `Wf` (use `From
Stdlib.Program` or `From Stdlib.Init`).
