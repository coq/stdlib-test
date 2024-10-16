- file `Zdiv_facts.v`
  (`#19752 <https://github.com/coq/coq/pull/19752>`_,
  by Andres Erbsen).

- in file `Zdiv_facts.v`

  + lemmas :g:`Z.diveq_iff` and :g:`Z.mod_diveq_iff` that further
    genralize the same concept as :g:`Z.mod_small` to known quotients
    other than 0.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + lemmas :g:`Z.eq_mod_opp` and :g:`Z.eq_mod_abs`
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

- in file `Zdiv.v`

  + lemma :g:`Z.mod_id_iff` generalizes :g:`Z.mod_small`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + lemmas :g:`Z.mod_opp_mod_opp`, :g:`Z.mod_mod_opp_r`,
    :g:`Z.mod_opp_r_mod`, :g:`Z.mod_mod_abs_r`, :g:`Z.mod_abs_r_mod`
    combining :g:`Z.modulo` with :g:`Z.opp` or :g:`Z.abs`
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemmas :g:`cong_iff_0` and :g:`cong_iff_ex` can be used to reduce
    congruence equalities to equations where only one side is headed
    by :g:`Z.modulo`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemmas :g:`Z.gcd_mod_l` and :g:`Z.gcd_mod_r` generalize
    :g:`Z.gcd_mod`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemma :g:`Z.mod_mod_divide` generalizes :g:`Zmod_mod`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemma :g:`Z.mod_pow_l` allows pushing modulo inside exponentiation
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).
