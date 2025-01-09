- in several files

  + remove transitive requirements or export of theories about ``Z``,
    you may need to add explicit ``Require`` or ``Import``
    of :g:`ZArith` or :g:`Lia`
    (`#19801 <https://github.com/coq/coq/pull/19801>`_,
    by Andres Erbsen).

- in `Zbool.v`

  + definition of :g:`Zeq_bool` is now an alias for :g:`Z.eqb`,
    this is expected to simplify simultaneous compatibility with 8.20 and 9.0
    (`#19801 <https://github.com/coq/coq/pull/19801>`_,
    by Andres Erbsen).
