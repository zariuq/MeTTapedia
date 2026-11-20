import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Tower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Coherence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Decision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Variants
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.FastPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.CanonicalStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Observed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Remainder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Dialects

/-!
# Numbers on the step

Which numeric types exist, which operations belong to them, which conversions may be silent, and
what a fast path owes the value. The carrier is the number lens's model of stored numbers: an
integer, or a fraction that may happen to be whole, read through its value.

* `Tower`: the value law (an observer family factors through the value exactly when its types are
  types of the value lens); the naturals, whole numbers and rationals as types of the value lens,
  strictly included; being stored as an integer is no type; the closure table of addition,
  subtraction, multiplication, exact division, the quotient and remainder of whole values,
  truncated subtraction and comparison, every cell a theorem or a counterexample.
* `Coherence`: a language over a tower of types with silent conversions and its elaborations; all
  elaborations agree exactly when the conversions compose and every operation and test commutes with
  every conversion, the converse in general form; with equality in scope the silent conversions are
  exactly the injective homomorphisms. The tower of naturals, whole numbers and rationals with the
  named quotient is coherent; truncated subtraction and the storage-dependent division are not. No
  conversion into finitely many values is injective, and no addition on them commutes with the
  inclusion into the rationals.
* `OnTheStep`: a grounded table inside the knowledge of the first-order step; the knowledge
  identifies stored numbers of equal value, and identifies every pair of storage variants exactly
  when the table respects the value lens; then re-storing every numeral of a program, its knowledge
  and its query changes no answer, for counts and for none queries, over every run; the converse by a
  one-row program; a computing rule that fires, with its answer, as witness.
* `Decision`: evaluation commutes with substitution; under the value law the knowledge's equality is
  one evaluation and one comparison, and without it that test is not even stable under substitution.
* `Variants`: re-storing numerals position by position, in the patterns, tells and checks of every
  rule, in the knowledge and in the query: a bisimulation of runs, and the same answers.
* `FastPaths`: a licensed fast path answers what the value operation answers or hands over; the
  composite equals the value operation and regions compose in any order; the 64-bit paths are
  licensed; HE's measured integer table is the fast path with an error outside its region; erroring
  and wrapping are controls; a table of licensed paths keeps representation independence on the
  step.
* `CanonicalStorage`: on canonical storage the storage lens and the value lens have the same types,
  and the storage-dependent division respects the value lens, yet it does not commute with the
  conversion from whole numbers to rationals.
* `Observed`: the runs are the runs of the tree's program step; soft numbers are observed by
  counting, through the tree's observability theorems.
* `Remainder`: the truncated remainder of rationals agrees with the remainder of the integers on
  whole values; HE's `%`, modelled, respects the value lens.
* `Dialects`: the verdicts on the measured behaviours; the cliff at the 64-bit width against the
  licensed composite; truncated and floored quotients both meet every law and differ in the
  symmetry they keep.
-/
