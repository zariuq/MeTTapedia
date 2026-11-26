import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversion

/-!
# Checked comparison of an instantiated equation

The converter supplies equality evidence at the first annotation. The caller
supplies equality of the reindexed annotations so both terms are typed there.
The resulting proof refers to the particular substitution used by the check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta.Conversion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (reducer : ExecutableReduction.Reducer S.R)

include facts roots heads algebra

/-- A successful comparison certifies this equation at the checked frame. -/
theorem solves_of_compare (fuel : Nat) {Γ Δ : Context S.R} (σ : Δ ⟶ Γ)
    (equation : Equation (TotalTerm Γ))
    (annotations : TypeEq S.R Δ.raw (subst σ.substitution equation.1.1.code)
      (subst σ.substitution equation.2.1.code))
    (accepted : (ExecutableConversion.compare S.R reducer fuel Δ.raw
      (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
      (subst σ.substitution equation.1.1.code)).isSome = true) :
    (frames S.levels).Solves σ equation := by
  obtain ⟨certificate, _⟩ := Option.isSome_iff_exists.mp accepted
  exact ⟨annotations, Algorithm.sound (S := S) facts roots heads algebra certificate.down Δ.formed
    (equation.1.2.reindex σ).typed (Typed.convType (equation.2.2.reindex σ).typed annotations.symm)⟩

/-- A successful comparison after substitution witnesses singleton solvability
when the equation was formed with one annotation on both sides. -/
theorem solvable_singleton_of_compare (fuel : Nat) {Γ Δ : Context S.R} (σ : Δ ⟶ Γ)
    (equation : Equation (TotalTerm Γ)) (same : equation.2.1.code = equation.1.1.code)
    (accepted : (ExecutableConversion.compare S.R reducer fuel Δ.raw
      (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
      (subst σ.substitution equation.1.1.code)).isSome = true) :
    (frames S.levels).Solvable [equation] := by
  have annotations : TypeEq S.R Δ.raw (subst σ.substitution equation.1.1.code)
      (subst σ.substitution equation.2.1.code) := by
    rw [same]
    exact (equation.1.1.reindex σ).isType.refl
  refine ⟨Δ, σ, fun other member => ?_⟩
  rw [List.mem_singleton.mp member]
  exact solves_of_compare facts roots heads algebra reducer fuel σ equation annotations accepted

end ContextualDependentEta.Conversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
