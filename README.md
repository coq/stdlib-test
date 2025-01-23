# The Standard Library of the Rocq Prover

[![Zulip][zulip-badge]][zulip-link]
[![Discourse][discourse-badge]][discourse-link]

[discourse-badge]: https://img.shields.io/badge/Discourse-forum-informational.svg
[discourse-link]: https://coq.discourse.group/

[zulip-badge]: https://img.shields.io/badge/Zulip-chat-informational.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/channel/478198-Stdlib-devs-.26-users

The [Rocq Prover](https://rocq-prover.org)  is an interactive theorem prover,
or proof assistant. It provides a formal language to write
mathematical definitions, executable algorithms and theorems together with an
environment for semi-interactive development of machine-checked proofs.

This repository contains the standard library of the Rocq Prover.

## Installation

Information on how to build and install from sources can be found in
[`INSTALL.md`](INSTALL.md).

Then, the recommended way to require standard library modules is `From
Stdlib Require {Import,Export,} <LibraryModules>.`, except for `Byte`
(use `From Stdlib.Strings` or `From Stdlib.Init`), `Tactics` (use
`From Stdlib.Program` or `From Stdlib.Init`), `Tauto` (use `From
Stdlib.micromega` of `From Stdlib.Init`) and `Wf` (use `From
Stdlib.Program` or `From Stdlib.Init`).

## Documentation

The sources of the documentation can be found in directory [`doc`](doc).
See [`doc/README.md`](/doc/README.md) to learn more about the documentation,
in particular how to build it. The
documentation of the last released version is available on the Rocq Prover
web site at [rocq-prover.org/docs](https://rocq-prover.org/docs).

The documentation of the master branch is continuously deployed.  See:
- [Reference Manual (master)][refman-master]
- [Documentation of the standard library (master)][stdlib-master]

[refman-master]: https://rocq-prover.org/doc/master/refman-stdlib
[stdlib-master]: https://rocq-prover.org/doc/master/stdlib

## Changes

The [Recent
changes](https://rocq-prover.org/doc/master/refman-stdlib/changes.html) chapter
of the reference manual explains the differences and the
incompatibilities of each new version of the standard library. If you upgrade,
please read it carefully as it contains important advice on how to
approach some problems you may encounter.

## Questions and discussion

We have a number of channels to reach the user community and the
development team:

- Our [Zulip chat][zulip-link], for casual and high traffic discussions.
- Our [Discourse forum][discourse-link], for more structured and easily browsable discussions and Q&A.

See also [rocq-prover.org/community](https://rocq-prover.org/community), which
lists several other active platforms.

## Bug reports

Please report any bug / feature request in [our issue tracker](https://github.com/coq/stdlib/issues).

To be effective, bug reports should mention
the Rocq version (`rocq -v`), the configuration
used, and include a complete source example leading to the bug.

## Contributing to the Standard Library of the Rocq Prover

Guidelines for contributing in various ways are listed in the [contributor's guide](CONTRIBUTING.md).
