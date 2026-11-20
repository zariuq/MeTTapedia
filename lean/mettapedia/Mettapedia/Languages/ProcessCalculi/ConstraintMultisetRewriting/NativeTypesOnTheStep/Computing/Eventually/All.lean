import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Normalizer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Unfold
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Comparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Tower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Instances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Limits
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Search
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Consequences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Detour
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Erasing

/-!
# Eventual success of the fuelled executable functions

* `Normalizer`: the tree's executable normalizer is a leftmost-outermost full normalizer; under strong
  normalization of typed terms and with a complete root evaluator it returns the unique normal form of every
  typed term at some budget and at every larger one.
* `Unfold`: one unfolding of each executable comparison, for any reducer.
* `Comparison`: the executable comparison succeeds eventually on every typed equal pair of every package with
  a complete algorithmic equality, for every reducer that eventually returns weak-head normal reducts.
* `Tower`: the cumulative tower as an instance.
* `Instances`: the vectors package (complete root evaluator, items 1, 2 and 4 under strong normalization of
  its typed terms) and the executable package (strong normalization proved).
* `Limits`: no fixed budget suffices; a looping row, at which strong normalization, weak-head
  normalization and algorithmic completeness fail together; the comparison cannot refuse; the checker's
  boundary.
* `Detour`: a typed term with a normal form and a weak-head normal form, and a complete root evaluator,
  on which the full normalizer fails at every budget: a row that inspects its second argument, beside
  a first argument that unfolds into a copy of the whole term.
* `Erasing`: a qualified package, not strongly normalizing, whose typed terms all have weak-head normal
  forms, with one complete root evaluator (`complete_root_eq`), with which the full normalizer fails at
  every budget on the typed term `d zero`, because its traversal reduces the recursor's successor case
  before the inspected scrutinee; a traversal that steps arguments first reaches the normal form
  (`argFirst_normalizes`). So in the normalizer's theorem (`qualified_normalize_eventually`) strong
  normalization cannot be weakened to weak-head normalization. Of the comparison it shows only that
  the tree's normalizer is not a reducer meeting its hypothesis there
  (`normalizer_not_whnfEventually`); whether the comparison needs strong normalization is not
  decided.
* `Search`: the search for the least sufficient budget is total on typed equal pairs.
* `Consequences`: the round's conversion scan and the converting step's row checks.
-/
