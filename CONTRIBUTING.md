# Guide to contributing to the Standard Library of Rocq #

## Foreword ##

As with any documentation, this guide is most useful if it's promptly
updated to reflect changes in processes, development tools, or the Rocq
ecosystem.  If you notice anything inaccurate or outdated, please
signal it in a new issue, or fix it in a new pull request.  If you
find some parts are not sufficiently clear, you may open an issue as
well.

## Table of contents ##

- [Guide to contributing to the Standard Library of Rocq](#guide-to-contributing-to-the-standard-library-of-rocq)
  - [Foreword](#foreword)
  - [Table of contents](#table-of-contents)
  - [Introduction](#introduction)
  - [Issues](#issues)
    - [Reporting a bug, requesting an enhancement](#reporting-a-bug-requesting-an-enhancement)
    - [Helping triage existing issues](#helping-triage-existing-issues)
  - [Code changes](#code-changes)
    - [Using GitHub pull requests](#using-github-pull-requests)
      - [Fixing bugs and performing small changes](#fixing-bugs-and-performing-small-changes)
      - [Seeking early feedback on work-in-progress](#seeking-early-feedback-on-work-in-progress)
    - [Taking feedback into account](#taking-feedback-into-account)
      - [Understanding automatic feedback](#understanding-automatic-feedback)
        - [Test-suite failures](#test-suite-failures)
        - [Linter failures](#linter-failures)
        - [Library failures](#library-failures)
      - [Understanding reviewers' feedback](#understanding-reviewers-feedback)
      - [Fixing your branch](#fixing-your-branch)
    - [Improving the official documentation](#improving-the-official-documentation)
    - [Contributing to the standard library](#contributing-to-the-standard-library)
  - [Becoming a maintainer](#becoming-a-maintainer)
    - [Reviewing pull requests](#reviewing-pull-requests)
      - [Collaborating on a pull request](#collaborating-on-a-pull-request)
    - [Merging pull requests](#merging-pull-requests)
      - [Additional notes for pull request reviewers and assignees](#additional-notes-for-pull-request-reviewers-and-assignees)
      - [Joining / leaving maintainer team](#joining--leaving-maintainer-team)
  - [Release management](#release-management)
    - [Packaging Rocq](#packaging-rocq)
  - [Additional resources](#additional-resources)
    - [Developer documentation](#developer-documentation)
      - [Where to find the resources](#where-to-find-the-resources)
      - [Building the Standard Library](#building-the-standard-library)
      - [Continuous integration](#continuous-integration)
        - [Restarting failed jobs](#restarting-failed-jobs)
      - [Style guide](#style-guide)
      - [Git documentation, tips and tricks](#git-documentation-tips-and-tricks)
      - [GitHub documentation, tips and tricks](#github-documentation-tips-and-tricks)
        - [Watching the repository](#watching-the-repository)
        - [Draft pull requests](#draft-pull-requests)
          - [Turning a PR into draft mode](#turning-a-pr-into-draft-mode)
    - [Online forum and chat to talk to developers](#online-forum-and-chat-to-talk-to-developers)

## Introduction ##

Thank you for your interest in contributing to the Standard Library of Rocq!
There are many ways to contribute, and we appreciate all of them.

People often begin by making small contributions, and contributions to
the ecosystem, before working their way up incrementally to the core
parts of the system, and start to propose larger changes, or take an
active role in maintaining the system.  So this is the way this
contributing guide is organized.  However, it is by no means necessary
that you go through these steps in this order.  Feel free to use this
guide as a reference and quickly jump to the part that is most
relevant to you at the current time.

This document is specific to the Standard Library. For more generic
information about contributing to the Rocq ecosystem as a whole,
one can browse the [contributing guide of Rocq itself][rocq-contributing-guide].

## Issues ##

### Reporting a bug, requesting an enhancement ###

Bug reports are enormously useful to identify issues; we
can't fix what we don't know about.  To report a bug, please open an
issue in the [Rocq issue tracker][Rocq-issue-tracker] (you'll need a
GitHub account).

It would help if you search the existing issues before reporting a
bug. This can be difficult, so consider it extra credit.  We don't
mind duplicate bug reports.  If unsure, you are always very welcome to
ask on our [Discourse forum][Discourse] or [Zulip chat][Zulip]
before, after, or while writing a bug report.

It is better if you can test that your bug is still present in the
current testing or development version before reporting it, but if you can't, it
should not discourage you from reporting it.

When it applies, it's extremely helpful for bug reports to include sample
code, and much better if the code is self-contained and complete. It's not
necessary to minimize your bug or identify precisely where the issue is,
since someone else can often do this if you include a complete example. We
tend to include the code in the bug description itself, but if you have a
very large input file then you can add it as an attachment.

If you want to minimize your bug (or help minimize someone else's) for
more extra credit, then you can use the [Rocq bug
minimizer][JasonGross-coq-tools] (specifically, the bug minimizer is
the `find-bug.py` script in that repo). Nowadays, the easiest way to
use the Rocq bug minimizer is to call it through `@coqbot`, as documented
[here][coqbot-minimize].

### Helping triage existing issues ###

Rocq has too many bug reports for its core developers alone to manage.
You can help a lot by:

- confirming that reported bugs are still active with the current
  version of Rocq;
- determining if the bug is a regression (new, and unexpected,
  behavior from a recent Rocq version);
- more generally, by reproducing a bug, on another system,
  configuration, another version of Rocq, and by documenting what you
  did;
- giving a judgement about whether the reported behavior is really a
  bug, or is expected but just improperly documented, or expected and
  already documented;
- producing a trace if it is relevant and you know how to do it;
- producing another example exhibiting the same bug, or minimizing the
  initial example using the bug minimizer mentioned above;
- using `git bisect` to find the commit that introduced a regression;
- fixing the bug if you have an idea of how to do so (see the
  [following section](#code-changes)).

## Code changes ##

### Using GitHub pull requests ###

If you want to contribute a documentation update, bug fix or feature
yourself, pull requests (PRs) on the [GitHub
repository][stdlib-repository] are the way to contribute directly to the
Rocq implementation (all changes, even the smallest changes from core
developers, go through PRs).  You will need to create a fork of the
repository on GitHub and push your changes to a new "topic branch" in
that fork (instead of using an existing branch name like `master`).

PRs should always target the `master` branch.  Make sure that your
copy of this branch is up-to-date before starting to do your changes,
and that there are no conflicts before submitting your PR.  If you
need to fix conflicts, we generally prefer that you rebase your branch
on top of `master`, instead of creating a merge commit.

If you are not familiar with `git` or GitHub, Sections [Git
documentation, tips and tricks](#git-documentation-tips-and-tricks),
and [GitHub documentation, tips and
tricks](#github-documentation-tips-and-tricks), should be helpful (and
even if you are, you might learn a few tricks).

Once you have submitted your PR, it may take some time to get
feedback, in the form of reviews from maintainers, and test results
from our continuous integration system.  Our code owner system will
automatically request reviews from relevant maintainers.  Then, one
maintainer should self-assign the PR (if that does not happen after a
few days, feel free to ping the maintainers).
The PR assignee will then become your main point of contact
for handling the PR: they should ensure that everything is in order
and merge when it is the case (you can ping them if the PR is ready
from your side but nothing happens for a few days).

After your PR is accepted and merged, it may get backported to a
release branch if appropriate, and will eventually make it to a
release.  You do not have to worry about this, it is the role of the
assignee and the release manager to do so (see Section [Release
management](#release-management)).  The milestone should give you an
indication of when to expect your change to be released (this could be
several months after your PR is merged).  That said, you can start
using the latest `master` branch to take advantage of all the new
features, improvements, and fixes.

#### Fixing bugs and performing small changes ####

Before fixing a bug, it is best to check that it was reported before:

- If it was already reported and you intend to fix it, self-assign the
  issue (if you have the permission), or leave a comment marking your
  intention to work on it (and a contributor with write-access may
  then assign the issue to you).

- If the issue already has an assignee, you should check with them if
  they still intend to work on it.  If the assignment is several
  weeks, months, or even years (!) old, there are good chances that it
  does not reflect their current priorities.

- If the bug has not been reported before, it can be a good idea to
  open an issue about it, while stating that you are preparing a fix.
  The issue can be the place to discuss about the bug itself while the
  PR will be the place to discuss your proposed fix.

It is generally a good idea to add a regression test to the
test-suite. See the test-suite [README][test-suite-README] for how to
do so.

Small fixes do not need any documentation, or changelog update.  New,
or updated, user-facing features, and major bug fixes do.  See the
[corresponding section](#improving-the-official-documentation) for
on how to contribute to the documentation, and the README in
[`doc/changelog`][user-changelog] for how to add a changelog entry.

#### Seeking early feedback on work-in-progress ####

You should always feel free to open your PR before the documentation,
changelog entry and tests are ready.  That's the purpose of the
checkboxes in the PR template which you can leave unticked.  This can
be a way of getting reviewers' approval before spending time on
writing the documentation (but you should still do it before your PR
can be merged).

If even the implementation is not ready but you are still looking for
early feedback on your code changes, please use the [draft
PR](#draft-pull-requests) mechanism.

If you are looking for feedback on the design of your change, rather
than on its implementation, then please refrain from opening a PR.
You may open an issue to start a discussion.

### Taking feedback into account ###

#### Understanding automatic feedback ####

When you open or update a PR, you get automatically some feedback.
The tests will run on a
commit merging your branch with the base branch, so if there is a
conflict and this merge cannot be performed automatically,
the tests won't run.

If a test fails, you will see in the GitHub PR interface,
both the failure of the whole pipeline, and of the specific failed
job.  Most of these failures indicate problems that should be
addressed, but some can still be due to synchronization issues out of
your control. In case of doubt, ask the reviewers.

To re-run a specific failed job, you can use the Re-run jobs button
in the GitHub interface (if you have the rights).

##### Test-suite failures #####

If you broke the test-suite, you should get many failed jobs, because
the test-suite is run multiple times in various settings.  You should
get the same failure locally by running `make test-suite`
(after having done `make` and `maje install`). It's
helpful to run this locally and ensure the test-suite is not broken
before submitting a PR as this will spare a lot of runtime on distant
machines.

To learn more about the test-suite, you should refer to its
[README][test-suite-README].

##### Linter failures #####

We have a linter that checks a few different things:

- **Every commit can build.** This is an important requirement to
  allow the use of `git bisect` in the future.  It should be possible
  to build every commit, and in principle even the test-suite should
  pass on every commit (but this isn't tested in CI because it would
  take too long).  A good way to test this locally is to use
  `git rebase master --exec "make"`.
- **No tabs or end-of-line spaces on updated lines**.  We are trying
  to get rid of all tabs and all end-of-line spaces from the code base
  (except in some very special files that need them).  This checks not
  only that you didn't introduce new ones, but also that updated lines
  are clean (even if they were there before).  You can avoid worrying
  about tabs and end-of-line spaces by installing our [pre-commit git
  hook][git-hook], which will fix these issues at commit time.
  If you are
  encountering these issues nonetheless, you can fix them by rebasing
  your branch with `git rebase --whitespace=fix`.
- **All files should end with a single newline**.  See the section
  [Style guide](#style-guide) for additional style recommendations.

You may run the linter yourself with `dev/lint-repository.sh`.

##### Library failures #####

Such a failure can indicate either a bug in your branch, or a breaking
change that you introduced voluntarily.  All such breaking changes
should be properly documented in the [user changelog][user-changelog].
Furthermore, a backward-compatible fix should be found, properly
documented in the changelog when non-obvious, and this fix should be
merged in the broken projects *before* your PR to the Rocq repository
can be.

Note that once the breaking change is well understood, it should not
feel like it is your role to fix every project that is affected: as
long as reviewers have approved and are ready to integrate your
breaking change, you are entitled to (politely) request project
authors / maintainers to fix the breakage on their own, or help you
fix it.  Obviously, you should leave enough time for this to happen
(you cannot expect a project maintainer to allocate time for this as
soon as you request it) and you should be ready to listen to more
feedback and reconsider the impact of your change.

#### Understanding reviewers' feedback ####

The reviews you get are highly dependent on the kind of changes you
did.  In any case, you should always remember that reviewers are
friendly volunteers that do their best to help you get your changes in.
But at
the same time, they try to ensure that code that is introduced or
updated is of the highest quality and will be easy to maintain in the
future, and that's why they may ask you to perform small or even large
changes.  If you need a clarification, do not hesitate to ask.

Here are a few labels that reviewers may add to your PR to track its
status.  In general, this will come in addition to comments from the
reviewers, with specific requests.

- [needs: fixing][needs-fixing] indicates the PR needs a fix, as
  discussed in the comments.
- [needs: documentation][needs-documentation] indicates the PR
  introduces changes that should be documented before it can be merged.
  This label may be used to reflect that the corresponding checkbox is
  not yet checked in the PR template (so that we don't forget when
  we intend to merge the PR).
- [needs: changelog entry][needs-changelog] indicates the PR introduces
  changes that should be documented in the [user
  changelog][user-changelog]. Similarly to the previous label, this
  may be used to reflect that the corresponding checkbox is not yet
  checked in the PR template.
- [needs: test-suite update][needs-test-suite] indicates that tests
  should be added to the test-suite / modified to ensure that the
  changes are properly tested. Similarly to the previous two labels,
  this may be used to reflect that the corresponding checkbox is not
  yet checked in the PR template.

More generally, such labels should come with a description that should
allow you to understand what they mean.

#### Fixing your branch ####

If you have changes to perform before your PR can be merged, you might
want to do them in separate commits at first to ease the reviewers'
task, but we generally appreciate that they are squashed with the
commits that they fix before merging.  This is especially true of
commits fixing previously introduced bugs or failures.

### Improving the official documentation ###

The documentation is usually a good place to start contributing,
because you can get used to the pull request submitting and review
process, without needing to learn about the code source of Rocq at the
same time.

The official documentation is formed of two components:

- the [reference manual][refman],
- the [documentation of the standard library][stdlib-doc].

The sources of the reference manual are located in the
[`doc/sphinx`][refman-sources] directory.  They are written in rst
(Sphinx) format with some Rocq-specific extensions, which are
documented in the [README][refman-README] in the above directory.
This README was written to be read from begin to end.  As soon as your
edits to the documentation are more than changing the textual content,
we strongly encourage you to read this document.

The documentation of the standard library is generated with
[coqdoc][coqdoc-documentation] from the comments in the sources of the
standard library.

The [README in the `doc` directory][doc-README] contains more
information about the documentation's build dependencies, and the
`make` targets.

You can browse through the list of open documentation issues using the
[kind: documentation][kind-documentation] label, or the [user
documentation GitHub project][documentation-github-project] (you can
look in particular at the "Writing" and "Fixing" columns).

### Contributing to the standard library ###

Contributing to the standard library is also made easier by not having
to learn about Rocq's internals, and its implementation language.

Due to the compatibility constraints created by the many projects that
depend on it, proposing breaking changes, will usually require to go
through a specific process, with a deprecation phase.  Additions, such
as contributing new lemmas on existing definitions, and clean-ups of
existing proofs are easier contributions to start with. In case of
doubt, ask in an issue before spending too much time preparing your PR.

If you create a new file, it needs to be listed in
`doc/stdlib/index-list.html`.

Add coqdoc comments to extend the [standard library
documentation][stdlib-doc].  See the [coqdoc
documentation][coqdoc-documentation] to learn more.

## Becoming a maintainer ##

### Reviewing pull requests ###

You can start reviewing PRs as soon as you feel comfortable doing so
(anyone can review anything, although some designated reviewers
will have to give a final approval before a PR can be merged, as is
explained in the next sub-section).

Reviewers should ensure that the code that is changed or introduced is
in good shape and will not be a burden to maintain, is unlikely to
break anything, or the compatibility-breakage has been identified and
validated, includes documentation, changelog entries, and test files
when necessary.  Reviewers can use `needs:` labels, or change requests
to further emphasize what remains to be changed before they can approve
the PR.  Once reviewers are satisfied (regarding the part they
reviewed), they should formally approve the PR, possibly stating what
they reviewed.

That being said, reviewers should also make sure that they do not make
the contributing process harder than necessary: they should make it
clear which comments are really required to perform before approving,
and which are just suggestions.  They should strive to reduce the
number of rounds of feedback that are needed by posting most of their
comments at the same time.  If they are opposed to the change, they
should clearly say so from the beginning to avoid the contributor
spending time in vain. They should avoid making nitpick comments when
in fact, they have larger concerns that should be addressed first
(these larger concerns should then be made very clear).

Furthermore, when reviewing a first contribution (GitHub highlights
first-time contributors), be extra careful to be welcoming, whatever
the decision on the PR is. When approving a PR, consider thanking the
newcomer for their contribution, even if it is a very small one (in
cases where, if the PR had come from a regular contributor, it would
have felt OK to just merge it without comment). When rejecting a PR,
take some extra steps to explain the reasons, so that it doesn't feel
hurtful. Don't hesitate to still thank the contributor and possibly
redirect them to smaller tasks that might be more appropriate for a
newcomer.

#### Collaborating on a pull request ####

Beyond making suggestions to a PR author during the review process,
you may want to collaborate further by checking out the code, making
changes, and pushing them.  There are two main ways of doing this:

- **Pull requests on pull requests:** You can checkout the PR branch
  (GitHub provides the link to the remote to pull from and the branch
  name on the top and the bottom of the PR discussion thread),
  checkout a new personal branch from there, do some changes, commit
  them, push to your fork, and open a new PR on the PR author's fork.
- **Pushing to the PR branch:** If the PR author has not unchecked the
  "Allow edit from maintainers" checkbox, and you have write-access to
  the repository (i.e. you are in the **@coq/contributors** team),
  then you can also push (and even force-push) directly to the PR
  branch, on the main author's fork.  Obviously, don't do it without
  coordinating with the PR author first (in particular, in case you
  need to force-push).

When several people have co-authored a single commit (e.g. because
someone fixed something in a commit initially authored by someone
else), this should be reflected by adding ["Co-authored-by:"
tags][GitHub-co-authored-by] at the end of the commit message.  The
line should contain the co-author name and committer e-mail address.

### Merging pull requests ###

Our [CODEOWNERS][] file associates a team of maintainers to each
component.  When a PR is opened (or a [draft PR](#draft-pull-requests)
is marked as ready for review), GitHub will automatically request
reviews to maintainer teams of affected components.  As soon as it is
the case, one available member of a team that was requested a review
should self-assign the PR, and will act as its shepherd from then on.

The PR assignee is responsible for making sure that all the proposed
changes have been reviewed by relevant maintainers (at least one
reviewer for each component that is significantly affected), that
change requests have been implemented, that CI is passing, and
eventually will be the one who merges the PR.

The PR assignee may use their own judgement to decide to merge a PR that
has not received reviews from all maintainers of affected components,
depending on how large or controversial the changes to these components
are. It is also admissible to have an assignee who is not a maintainer
of any of the affected components, in case relevant maintainers are not
available, and as long as the assignee has push right
and is able to understand the changes in the PR.

*If you have already frequently contributed to a component, we would
be happy to have you join the maintainer team.*

#### Additional notes for pull request reviewers and assignees ####

- Before merging, the assignee must also select a milestone for the PR
  (see also Section [Release management](#release-management)).

- When a PR has [overlays][user-overlays], then:

  - the overlays should have been merged *before* the PR
    can be merged; the overlays should then be cleaned up and CI relaunched
    without them to ensure everything is fine before merging.

#### Joining / leaving maintainer team ####

We are always happy to have more people involved in the PR reviewing
and merging process, so do not hesitate to propose yourself if you
already have experience on a component.

Maintainers can leave at any time but you should always
announce it to other maintainers.

## Release management ##

TBD, likely to follow Rocq releases

### Packaging Rocq ###

The RM role does not include the task of making Rocq available through
the various package managers out there: several contributors (most
often external to the development team) take care of this, and we
thank them for this.  If your preferred package manager does not
include Rocq, it is a very worthy contribution to make it available
there.  But be careful not to let a package get outdated, as this
could lead some users to install an outdated version of Rocq without
even being aware of it. Beyond packaging Rocq, you might want to
consider packaging the rest of Rocq packages available to users through
the [Rocq Platform][Rocq-Platform]. In this case, it would be helpful if
you try to favor the same versions as in the Rocq Platform.

The Windows and macOS installers are created as part of the preparation
of the Rocq Platform.

## Additional resources ##

### Developer documentation ###

#### Where to find the resources ####

- You can find developer resources in the `dev` directory, and more
  specifically developer documentation in `dev/doc`. The
  [README][dev-README] in the `dev` directory lists what's available.

  For example, [`dev/doc/README.md`][dev-doc-README] is a beginner's
  guide to hacking Rocq, and documentation on debugging Rocq can be
  found in [`dev/doc/debugging.md`][debugging-doc].

- When it makes sense, the documentation is kept even closer to the
  sources, in README files in various directories (e.g. the test-suite
  [README][test-suite-README] or the refman [README][refman-README]).

#### Building the Standard Library ####

The standard library depends on Rocq itself.
Run `make` to build everything, then `make install` to install.

#### Continuous integration ####

Continuous integration (CI) testing is key in ensuring that the
`master` branch is kept in a well-functioning state at all times, and
that no accidental compatibility breakages are introduced.  Our CI is
quite extensive since it includes testing many external projects, some
of them taking more than an hour to compile.  However, you can get
partial results much more quickly (when our CI is not overloaded).

The main documentation resource on our CI is the [README][CI-README].

##### Restarting failed jobs #####

When CI has a few failures which look spurious, restarting the
corresponding jobs is a good way to ensure this was indeed the case.
Most failed jobs can be restarted directly from the "Checks" tab on
GitHub.

#### Style guide ####

TBD

#### Git documentation, tips and tricks ####

Lots of resources about git, the version control system, are available
on the web, starting with the [official website][git].

We recommend a setup with two configured remotes, one for the official
Rocq repository, called `upstream`, and one for your fork, called
`origin`.  Here is a way to do this for a clean clone:

``` shell
git clone https://github.com/coq-community/stdlib -o upstream
cd stdlib
git remote add origin git@github.com:$YOURNAME/stdlib
# Make sure you click the fork button on GitHub so that this repository exists
cp dev/tools/pre-commit .git/hooks/ # Setup the pre-commit hook
```

Then, if you want to prepare a fix:

``` shell
# Make sure we start from an up-to-date master
git checkout master
git pull --ff-only # If this fails, then your master branch is messy
git checkout -b my-topic-branch
# Modify some files
git add .
# Every untracked or modified file will be included in the next commit
# You can also replace the dot with an explicit list of files
git commit -m "My commit summary.

You can add more information on multiple lines,
but you need to skip a line first."
git push -u origin my-topic-branch
# Next time, you push to this branch, you can just do git push
```

When you push a new branch for the first time, GitHub gives you a link
to open a PR.

If you need to fix the last commit in your branch (typically, if your
branch has a single commit on top of `master`), you can do so with

```
git add .
git commit --amend --no-edit
```

If you need to fix another commit in your branch, or if you need to
fix a conflict with `master`, you will need to learn about `git rebase`.
GitHub provides [a short introduction][GitHub-rebase] to `git rebase`.

#### GitHub documentation, tips and tricks ####

GitHub has [extensive documentation][GitHub-doc] about everything you
can do on the platform, and tips about using `git` as well.  See in
particular, [how to configure your commit e-mail
address][GitHub-commit-email] and [how to open a PR from a
fork][GitHub-PR-from-fork].

##### Watching the repository #####

["Watching" this repository][GitHub-watching] can result in a very
large number of notifications.  We recommend you, either, [configure
your mailbox][notification-email] to handle incoming notifications
efficiently, or you read your notifications within a web browser.  You
can configure how you receive notifications in [your GitHub
settings][GitHub-notification-settings], you can use the GitHub
interface to mark as read, save for later or mute threads. Nowadays,
you have also the option to watch only part of the activity (only
issues, only PRs, only releases, etc.).

##### Draft pull requests #####

[Draft PRs][GitHub-draft-PR] are a mechanism proposed by GitHub to
open a pull request before it is ready for review.

Opening a draft PR is a way of announcing a change and seeking early
feedback without formally requesting maintainers' reviews.  Indeed,
you should avoid cluttering our maintainers' review request lists
before a change is ready on your side.

When opening a draft PR, make sure to give it a descriptive enough
title so that interested developers still notice it in their
notification feed.  You may also advertise it by talking about it in
our [chat][Zulip].  If you know which developer would be
able to provide useful feedback to you, you may also ping them.

###### Turning a PR into draft mode ######

If a PR was opened as ready for review, but it turns out that it still
needs work, it can be transformed into a draft PR.

In this case, previous review requests won't be removed automatically.
Someone with write access to the repository should remove them
manually.  Afterwards, upon marking the PR as ready for review,
someone with write access will have to manually add the review
requests that were previously removed.

### Online forum and chat to talk to developers ###

We have a [Discourse forum][Discourse] (see in particular the [Rocq
development][Discourse-development-category] category) and a [Zulip
chat][Zulip].  Feel free to join any of them and ask questions.
People are generally happy to help and very reactive.

Obviously, the issue tracker is also a good place to ask questions,
especially if the development processes are unclear, or the developer
documentation should be improved.

[coq-contributing-guide]: https://github.com/coq/coq/blob/master/CONTRIBUTING.md
[stdlib-repository]: https://github.com/coq-community/stdlib
[CI-README]: dev/ci/README.md
[CODEOWNERS]: .github/CODEOWNERS
[coqbot-minimize]: https://github.com/coq/coq/wiki/Coqbot-minimize-feature
[coqdoc-documentation]: https://coq.inria.fr/refman/practical-tools/utilities.html#documenting-coq-files-with-coqdoc
[Coq-issue-tracker]: https://github.com/coq/coq/issues
[Coq-Platform]: https://github.com/coq/platform
[debugging-doc]: dev/doc/debugging.md
[dev-doc-README]: dev/doc/README.md
[dev-README]: dev/README.md
[Discourse]: https://coq.discourse.group/
[Discourse-development-category]: https://coq.discourse.group/c/coq-development
[doc-README]: doc/README.md
[documentation-github-project]: https://github.com/orgs/coq/projects/6
[git]: https://git-scm.com/
[git-hook]: dev/tools/pre-commit
[GitHub-co-authored-by]: https://github.blog/2018-01-29-commit-together-with-co-authors/
[GitHub-commit-email]: https://help.github.com/en/articles/setting-your-commit-email-address-in-git
[GitHub-doc]: https://help.github.com/
[GitHub-draft-PR]: https://github.blog/2019-02-14-introducing-draft-pull-requests/
[GitHub-notification-settings]: https://github.com/settings/notifications
[GitHub-PR-from-fork]: https://help.github.com/en/articles/creating-a-pull-request-from-a-fork
[GitHub-rebase]: https://help.github.com/articles/about-git-rebase/
[GitHub-watching]: https://github.com/coq/coq/subscription
[JasonGross-coq-tools]: https://github.com/JasonGross/coq-tools
[kind-documentation]: https://github.com/coq/coq/issues?q=is%3Aopen+is%3Aissue+label%3A%22kind%3A+documentation%22
[needs-changelog]: https://github.com/coq/coq/labels/needs%3A%20changelog%20entry
[needs-documentation]: https://github.com/coq/coq/labels/needs%3A%20documentation
[needs-fixing]: https://github.com/coq/coq/labels/needs%3A%20fixing
[needs-rebase]: https://github.com/coq/coq/labels/needs%3A%20rebase
[needs-testing]: https://github.com/coq/coq/labels/needs%3A%20testing
[needs-test-suite]: https://github.com/coq/coq/labels/needs%3A%20test-suite%20update
[notification-email]: https://blog.github.com/2017-07-18-managing-large-numbers-of-github-notifications/#prioritize-the-notifications-you-receive
[refman]: https://coq.inria.fr/distrib/current/refman/
[refman-sources]: doc/sphinx
[refman-README]: doc/sphinx/README.rst
[release-plan]: https://github.com/coq/coq/wiki/Release-Plan
[stdlib-doc]: https://coq.inria.fr/stdlib/
[test-suite-README]: test-suite/README.md
[user-overlays]: dev/ci/user-overlays
[Zulip]: https://coq.zulipchat.com/#narrow/channel/478198-Stdlib-devs-.26-users
