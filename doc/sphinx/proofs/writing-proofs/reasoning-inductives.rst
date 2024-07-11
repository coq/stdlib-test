========================================
Dependent Reasoning with inductive types
========================================

.. tacn:: dependent destruction ident {? generalizing {+ ident } } {? using one_term }
   :undocumented:

   There is a long example of ``dependent destruction`` and an explanation
   of the underlying technique :ref:`here <dependent-induction-examples>`.

.. tacn:: dependent induction ident {? {| generalizing | in } {+ ident } } {? using one_term }

   The *experimental* tactic :tacn:`dependent induction ident` performs
   induction-inversion on an instantiated inductive predicate. One needs to first
   ``Require`` the `Stdlib.Program.Equality` module to use this tactic. The tactic
   is based on the BasicElim tactic by Conor McBride
   :cite:`DBLP:conf/types/McBride00` and the work of Cristina Cornes around
   inversion :cite:`DBLP:conf/types/CornesT95`. From an instantiated
   inductive predicate and a goal, it generates an equivalent goal where
   the hypothesis has been generalized over its indexes which are then
   constrained by equalities to be the right instances. This permits to
   state lemmas without resorting to manually adding these equalities and
   still get enough information in the proofs.

   :n:`{| generalizing | in } {+ ident }`
     First generalizes the goal by the given variables so that they are universally
     quantified in the goal.  This is generally what one wants to do with
     variables that are inside constructors in the induction hypothesis.  The other
     ones need not be further generalized.

   There is a long example of :tacn:`dependent induction ident` and an explanation
   of the underlying technique :ref:`here <dependent-induction-examples>`.

   .. example::

      .. coqtop:: reset all

         Lemma lt_1_r : forall n:nat, n < 1 -> n = 0.
         intros n H ; induction H.

      Here we did not get any information on the indexes to help fulfill
      this proof. The problem is that, when we use the ``induction`` tactic, we
      lose information on the hypothesis instance, notably that the second
      argument is 1 here. Dependent induction solves this problem by adding
      the corresponding equality to the context.

      .. coqtop:: reset all

         From Stdlib.Program Require Import Equality.
         Lemma lt_1_r : forall n:nat, n < 1 -> n = 0.
         intros n H ; dependent induction H.

      The subgoal is cleaned up as the tactic tries to automatically
      simplify the subgoals with respect to the generated equalities. In
      this enriched context, it becomes possible to solve this subgoal.

      .. coqtop:: all

         reflexivity.

      Now we are in a contradictory context and the proof can be solved.

      .. coqtop:: all abort

         inversion H.

      This technique works with any inductive predicate. In fact, the
      :tacn:`dependent induction ident` tactic is just a wrapper around the ``induction``
      tactic. One can make its own variant by just writing a new tactic
      based on the definition found in ``Stdlib.Program.Equality``.

   .. seealso:: :tacn:`functional induction term`

.. example:: Using ``inversion_sigma``

   Let us consider the following inductive type of
   length-indexed lists, and a lemma about inverting equality of cons:

   .. coqtop:: reset all

      From Stdlib.Logic Require Import Eqdep_dec.

      Inductive vec A : nat -> Type :=
      | nil : vec A O
      | cons {n} (x : A) (xs : vec A n) : vec A (S n).

      Lemma invert_cons : forall A n x xs y ys,
               @cons A n x xs = @cons A n y ys
               -> xs = ys.

      Proof.
      intros A n x xs y ys H.

   After performing inversion, we are left with an equality of existTs:

   .. coqtop:: all

      inversion H.

   We can turn this equality into a usable form with inversion_sigma:

   .. coqtop:: all

      inversion_sigma.

   To finish cleaning up the proof, we will need to use the fact that
   that all proofs of n = n for n a nat are eq_refl:

   .. coqtop:: all

      let H := match goal with H : n = n |- _ => H end in
      pose proof (Eqdep_dec.UIP_refl_nat _ H); subst H.
      simpl in *.

   Finally, we can finish the proof:

   .. coqtop:: all

      assumption.
      Qed.

.. seealso:: :tacn:`functional inversion`

.. _dependent-induction-examples:

Examples of :tacn:`dependent destruction ident` / :tacn:`dependent induction ident`
-----------------------------------------------------------------------------------

The tactics :tacn:`dependent induction ident` and :tacn:`dependent destruction ident` are another
solution for inverting inductive predicate instances and potentially
doing induction at the same time. It is based on the ``BasicElim`` tactic
of Conor McBride which works by abstracting each argument of an
inductive instance by a variable and constraining it by equalities
afterwards. This way, the usual induction and destruct tactics can be
applied to the abstracted instance and after simplification of the
equalities we get the expected goals.

The abstracting tactic is called generalize_eqs and it takes as
argument a hypothesis to generalize. It uses the JMeq datatype
defined in Stdlib.Logic.JMeq, hence we need to require it before. For
example, revisiting the first example of the inversion documentation:

.. coqtop:: in reset

   From Stdlib.Logic Require Import JMeq.

   Inductive Le : nat -> nat -> Set :=
        | LeO : forall n:nat, Le 0 n
        | LeS : forall n m:nat, Le n m -> Le (S n) (S m).

   Parameter P : nat -> nat -> Prop.

   Goal forall n m:nat, Le (S n) m -> P n m.

   intros n m H.

.. coqtop:: all

   generalize_eqs H.

The index ``S n`` gets abstracted by a variable here, but a corresponding
equality is added under the abstract instance so that no information
is actually lost. The goal is now almost amenable to do induction or
case analysis. One should indeed first move ``n`` into the goal to
strengthen it before doing induction, or ``n`` will be fixed in the
inductive hypotheses (this does not matter for case analysis). As a
rule of thumb, all the variables that appear inside constructors in
the indices of the hypothesis should be generalized. This is exactly
what the ``generalize_eqs_vars`` variant does:

.. coqtop:: all abort

   generalize_eqs_vars H.
   induction H.

As the hypothesis itself did not appear in the goal, we did not need
to use an heterogeneous equality to relate the new hypothesis to the
old one (which just disappeared here). However, the tactic works just
as well in this case, e.g.:

.. coqtop:: none

   From Stdlib.Program Require Import Equality.

.. coqtop:: in

   Parameter Q : forall (n m : nat), Le n m -> Prop.
   Goal forall n m (p : Le (S n) m), Q (S n) m p.

.. coqtop:: all

   intros n m p.
   generalize_eqs_vars p.

One drawback of this approach is that in the branches one will have to
substitute the equalities back into the instance to get the right
assumptions. Sometimes injection of constructors will also be needed
to recover the needed equalities. Also, some subgoals should be
directly solved because of inconsistent contexts arising from the
constraints on indexes. The nice thing is that we can make a tactic
based on discriminate, injection and variants of substitution to
automatically do such simplifications (which may involve the axiom K).
This is what the ``simplify_dep_elim`` tactic from ``Stdlib.Program.Equality``
does. For example, we might simplify the previous goals considerably:

.. coqtop:: all abort

   induction p ; simplify_dep_elim.

The higher-order tactic ``do_depind`` defined in ``Stdlib.Program.Equality``
takes a tactic and combines the building blocks we have seen with it:
generalizing by equalities calling the given tactic with the
generalized induction hypothesis as argument and cleaning the subgoals
with respect to equalities. Its most important instantiations
are :tacn:`dependent induction ident` and :tacn:`dependent destruction ident` that do induction or
simply case analysis on the generalized hypothesis. For example we can
redo what we've done manually with dependent destruction:

.. coqtop:: in

   Lemma ex : forall n m:nat, Le (S n) m -> P n m.

.. coqtop:: in

   intros n m H.

.. coqtop:: all abort

   dependent destruction H.

This gives essentially the same result as inversion. Now if the
destructed hypothesis actually appeared in the goal, the tactic would
still be able to invert it, contrary to dependent inversion. Consider
the following example on vectors:

.. coqtop:: in

   Set Implicit Arguments.

.. coqtop:: in

   Parameter A : Set.

.. coqtop:: in

   Inductive vector : nat -> Type :=
            | vnil : vector 0
            | vcons : A -> forall n, vector n -> vector (S n).

.. coqtop:: in

   Goal forall n, forall v : vector (S n),
            exists v' : vector n, exists a : A, v = vcons a v'.

.. coqtop:: in

   intros n v.

.. coqtop:: all

   dependent destruction v.

In this case, the ``v`` variable can be replaced in the goal by the
generalized hypothesis only when it has a type of the form ``vector (S n)``,
that is only in the second case of the destruct. The first one is
dismissed because ``S n <> 0``.


A larger example
~~~~~~~~~~~~~~~~

Let's see how the technique works with induction on inductive
predicates on a real example. We will develop an example application
to the theory of simply-typed lambda-calculus formalized in a
dependently-typed style:

.. coqtop:: in reset

   Inductive type : Type :=
            | base : type
            | arrow : type -> type -> type.

.. coqtop:: in

   Notation " t --> t' " := (arrow t t') (at level 20, t' at next level).

.. coqtop:: in

   Inductive ctx : Type :=
            | empty : ctx
            | snoc : ctx -> type -> ctx.

.. coqtop:: in

   Notation " G , tau " := (snoc G tau) (at level 20, tau at next level).

.. coqtop:: in

   Fixpoint conc (G D : ctx) : ctx :=
            match D with
            | empty => G
            | snoc D' x => snoc (conc G D') x
            end.

.. coqtop:: in

   Notation " G ; D " := (conc G D) (at level 20).

.. coqtop:: in

   Inductive term : ctx -> type -> Type :=
            | ax : forall G tau, term (G, tau) tau
            | weak : forall G tau,
                       term G tau -> forall tau', term (G, tau') tau
            | abs : forall G tau tau',
                      term (G , tau) tau' -> term G (tau --> tau')
            | app : forall G tau tau',
                      term G (tau --> tau') -> term G tau -> term G tau'.

We have defined types and contexts which are snoc-lists of types. We
also have a ``conc`` operation that concatenates two contexts. The ``term``
datatype represents in fact the possible typing derivations of the
calculus, which are isomorphic to the well-typed terms, hence the
name. A term is either an application of:


+ the axiom rule to type a reference to the first variable in a
  context
+ the weakening rule to type an object in a larger context
+ the abstraction or lambda rule to type a function
+ the application to type an application of a function to an argument


Once we have this datatype we want to do proofs on it, like weakening:

.. coqtop:: in abort

   Lemma weakening : forall G D tau, term (G ; D) tau ->
                     forall tau', term (G , tau' ; D) tau.

The problem here is that we can't just use induction on the typing
derivation because it will forget about the ``G ; D`` constraint appearing
in the instance. A solution would be to rewrite the goal as:

.. coqtop:: in abort

   Lemma weakening' : forall G' tau, term G' tau ->
                      forall G D, (G ; D) = G' ->
                      forall tau', term (G, tau' ; D) tau.

With this proper separation of the index from the instance and the
right induction loading (putting ``G`` and ``D`` after the inducted-on
hypothesis), the proof will go through, but it is a very tedious
process. One is also forced to make a wrapper lemma to get back the
more natural statement. The :tacn:`dependent induction ident` tactic alleviates this
trouble by doing all of this plumbing of generalizing and substituting
back automatically. Indeed we can simply write:

.. coqtop:: in

   From Stdlib.Program Require Import Tactics Equality.

.. coqtop:: in

   Lemma weakening : forall G D tau, term (G ; D) tau ->
                     forall tau', term (G , tau' ; D) tau.

.. coqtop:: in

   Proof with simpl in * ; simpl_depind ; auto.

.. coqtop:: in

   intros G D tau H. dependent induction H generalizing G D ; intros.

This call to :tacn:`dependent induction ident` has an additional arguments which is
a list of variables appearing in the instance that should be
generalized in the goal, so that they can vary in the induction
hypotheses. By default, all variables appearing inside constructors
(except in a parameter position) of the instantiated hypothesis will
be generalized automatically but one can always give the list
explicitly.

.. coqtop:: all

   Show.

The ``simpl_depind`` tactic includes an automatic tactic that tries to
simplify equalities appearing at the beginning of induction
hypotheses, generally using trivial applications of ``reflexivity``. In
cases where the equality is not between constructor forms though, one
must help the automation by giving some arguments, using the
``specialize`` tactic for example.

.. coqtop:: in

   destruct D... apply weak; apply ax. apply ax.

.. coqtop:: in

   destruct D...

.. coqtop:: all

   Show.

.. coqtop:: all

   specialize (IHterm G0 empty eq_refl).

Once the induction hypothesis has been narrowed to the right equality,
it can be used directly.

.. coqtop:: all

   apply weak, IHterm.

Now concluding this subgoal is easy.

.. coqtop:: in

   constructor; apply IHterm; reflexivity.
