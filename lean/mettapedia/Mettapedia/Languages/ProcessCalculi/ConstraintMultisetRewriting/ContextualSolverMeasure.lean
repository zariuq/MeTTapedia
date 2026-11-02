import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidWeight

/-!
# Three actual solver measures with a well-founded lexicographic order

The coordinates are active candidate-image size, active parameter count and
total equation-tree weight. They describe logical solver progress, with no
claim about native allocation or compressed storage cost. Successful rigid
normalization cannot increase any coordinate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

abbrev Work := Nat × (Nat × Nat)

def Smaller : Work → Work → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem wellFounded : WellFounded Smaller :=
  WellFounded.prod_lex Nat.lt_wfRel.wf (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

theorem of_image_lt {after before : Work} (strict : after.1 < before.1) : Smaller after before :=
  Prod.lex_iff.mpr (.inl strict)

theorem of_interface_lt {after before : Work} (images : after.1 ≤ before.1)
    (strict : after.2.1 < before.2.1) : Smaller after before := by
  by_cases smaller : after.1 < before.1
  · exact of_image_lt smaller
  · have same : after.1 = before.1 := by omega
    exact Prod.lex_iff.mpr (.inr ⟨same, Prod.lex_iff.mpr (.inl strict)⟩)

theorem of_equation_lt {after before : Work} (images : after.1 ≤ before.1)
    (parameters : after.2.1 ≤ before.2.1) (strict : after.2.2 < before.2.2) : Smaller after before := by
  by_cases smaller : after.1 < before.1
  · exact of_image_lt smaller
  · have sameImages : after.1 = before.1 := by omega
    by_cases smallerParameters : after.2.1 < before.2.1
    · exact of_interface_lt images smallerParameters
    · have sameParameters : after.2.1 = before.2.1 := by omega
      exact Prod.lex_iff.mpr (.inr ⟨sameImages, Prod.lex_iff.mpr (.inr ⟨sameParameters, strict⟩)⟩)

theorem strict_then_bounds {first middle last : Work} (strict : Smaller first middle)
    (images : middle.1 ≤ last.1) (parameters : middle.2.1 ≤ last.2.1) (equations : middle.2.2 ≤ last.2.2) :
    Smaller first last := by
  rcases Prod.lex_iff.mp strict with smaller | ⟨sameImages, remaining⟩
  · exact of_image_lt (lt_of_lt_of_le smaller images)
  · rcases Prod.lex_iff.mp remaining with smaller | ⟨sameParameters, smaller⟩
    · exact of_interface_lt (by omega) (lt_of_lt_of_le smaller parameters)
    · exact of_equation_lt (by omega) (by omega) (lt_of_lt_of_le smaller equations)

variable {S : Signature} {V Next : Type} [DecidableEq V]
  {source : V → MetaArity S} {next : Next → MetaArity S}

def measure (candidate : Assignment source next) (problem : Problem source) : Work :=
  (potential candidate (active problem), ContextualInterfacePotential.cost source (active problem),
    ContextualEquationWeight.weight problem)

theorem normalization_bounds [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem result : Problem source} (computed : ContextualRigidSolver.normalize problem = some result)
    (candidate : Assignment source next) :
    (measure candidate result).1 ≤ (measure candidate problem).1 ∧
      (measure candidate result).2.1 ≤ (measure candidate problem).2.1 ∧
      (measure candidate result).2.2 ≤ (measure candidate problem).2.2 :=
  ⟨ContextualRigidSupport.normalization_potential_le computed candidate,
    ContextualRigidWeight.normalization_interface_cost computed, ContextualRigidWeight.normalization_weight problem computed⟩

theorem smaller_after_normalization [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem result : Problem source} (computed : ContextualRigidSolver.normalize problem = some result)
    (candidate : Assignment source next) {after : Work} (strict : Smaller after (measure candidate result)) :
    Smaller after (measure candidate problem) := by
  have bounded := normalization_bounds computed candidate
  exact strict_then_bounds strict bounded.1 bounded.2.1 bounded.2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure
