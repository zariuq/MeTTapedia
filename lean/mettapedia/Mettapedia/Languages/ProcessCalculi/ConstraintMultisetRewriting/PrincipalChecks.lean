import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# Principal-answer transport retains check arguments and physical worlds

Equality, absence and exact-count checks depend on their term arguments and
every occurrence value in the observed world. Once those terms are retained
in a principal interface, asking a check in every model is equivalent to
asking it after every residual instantiation of the principal answer.

A single successful concrete instantiation never proves that universal ask.
The physical occurrence world remains explicit, including duplicate-valued
occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

def Check.terms : Check T → List T
  | .equal left right => [left, right]
  | .absent pattern | .count pattern _ => [pattern]

private theorem equality_iff (A : SubstitutionAction T S) {left right left' right' : T}
    (leftSame : A.E left left') (rightSame : A.E right right') :
    A.E left right ↔ A.E left' right' := by
  constructor
  · intro same
    exact A.equivalence.trans (A.equivalence.symm leftSame) (A.equivalence.trans same rightSame)
  · intro same
    exact A.equivalence.trans leftSame (A.equivalence.trans same (A.equivalence.symm rightSame))

/-- Changing representations of observed values must preserve the check,
with the same actual occurrence identities. -/
theorem Check.holds_congr (A : SubstitutionAction T S) (first second : S)
    (label : O → T) (world : Finset O) (check : Check T)
    (arguments : ∀ term ∈ check.terms, A.E (A.apply first term) (A.apply second term))
    (values : ∀ occurrence ∈ world,
      A.E (A.apply first (label occurrence)) (A.apply second (label occurrence))) :
    check.Holds A first label world ↔ check.Holds A second label world := by
  cases check with
  | equal left right =>
      exact equality_iff A (arguments left (by simp [Check.terms]))
        (arguments right (by simp [Check.terms]))
  | absent pattern =>
      have comparisons : ∀ occurrence ∈ world,
          A.E (A.apply first pattern) (A.apply first (label occurrence)) ↔
            A.E (A.apply second pattern) (A.apply second (label occurrence)) := fun occurrence member =>
        equality_iff A (arguments pattern (by simp [Check.terms])) (values occurrence member)
      constructor
      · intro absent occurrence member same
        exact absent occurrence member ((comparisons occurrence member).mpr same)
      · intro absent occurrence member same
        exact absent occurrence member ((comparisons occurrence member).mp same)
  | count pattern number =>
      have regions : Check.matches A first label world pattern = Check.matches A second label world pattern := by
        classical
        ext occurrence
        simp only [Check.matches, Finset.mem_filter]
        exact and_congr_right fun member =>
          equality_iff A (arguments pattern (by simp [Check.terms])) (values occurrence member)
      change (Check.matches A first label world pattern).card = number ↔
        (Check.matches A second label world pattern).card = number
      rw [regions]

/-- All residual answers must satisfy the transported check, and the
interface must retain its arguments and every observed occurrence value. -/
theorem SubstitutionAction.PrincipalOn.check_iff (A : SubstitutionAction T S)
    {store : EquationStore T} {answer : S} {observed : List T}
    (principal : A.PrincipalOn store answer observed)
    (label : O → T) (world : Finset O) (check : Check T)
    (arguments : ∀ term ∈ check.terms, term ∈ observed)
    (values : ∀ occurrence ∈ world, label occurrence ∈ observed) :
    A.Entails store (fun assignment => check.Holds A assignment label world) ↔
      ∀ residual, check.Holds A (A.compose residual answer) label world := by
  apply SubstitutionAction.PrincipalOn.entails_iff A principal
  intro first second same
  exact Check.holds_congr A first second label world check
    (fun term member => same term (arguments term member))
    (fun occurrence member => same (label occurrence) (values occurrence member))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
