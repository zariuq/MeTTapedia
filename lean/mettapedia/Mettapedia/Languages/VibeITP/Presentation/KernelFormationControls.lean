import Mettapedia.Languages.VibeITP.Presentation.KernelFormation

/-! # Proof identity, checked entry and execution-budget controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.KernelFormation.Controls

open ComputationalData ComputationalProofs ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def claim : Spec.Term := .lit [1]
private def declarations : List Declaration := [.axiom claim, .axiom claim]
private def theory : Spec.Theory := { initialAdmission.theory with axioms := [claim, claim] }

theorem duplicate_axioms_retain_distinct_witnesses :
    (nativeKernel theory).toChecker.check claim (.axiom 0) = true ∧
      (nativeKernel theory).toChecker.check claim (.axiom 1) = true ∧
      (ProofWitness.axiom 0 : (nativeProofSystem theory).ProofObject) ≠ .axiom 1 := by
  constructor
  · exact (native_judgment_iff _ _ _).mpr (.axiom rfl)
  constructor
  · exact (native_judgment_iff _ _ _).mpr (.axiom rfl)
  · intro same
    cases same

theorem checked_entry_accepts_the_second_occurrence :
    Applies admissionProgram dataEqualityHost "vibe:check-static"
      [encodeDeclarations declarations, encodeWitness (.axiom 1), encode claim] (.sym "True") := by
  rw [← common_host_applies "vibe:check-static" (by decide +kernel)]
  have computed := checkStatic_computes declarations (.axiom 1) claim
  have accepted : checkStatic declarations (.axiom 1) claim = true := by decide +kernel
  rw [accepted] at computed
  exact computed

theorem derivability_cannot_rescue_a_missing_occurrence :
    Spec.Derives theory claim ∧
      Applies admissionProgram dataEqualityHost "vibe:check-static"
        [encodeDeclarations declarations, encodeWitness (.axiom 2), encode claim] (.sym "False") := by
  constructor
  · exact .axiom (by simp [theory])
  · rw [← common_host_applies "vibe:check-static" (by decide +kernel)]
    have computed := checkStatic_computes declarations (.axiom 2) claim
    have refused : checkStatic declarations (.axiom 2) claim = false := by decide +kernel
    rw [refused] at computed
    exact computed

theorem zero_execution_budget_is_not_native_refusal :
    (nativeKernel theory).toChecker.check claim (.axiom 0) = true ∧
      apply admissionProgram dataEqualityHost 0 "vibe:check-static"
        [encodeDeclarations declarations, encodeWitness (.axiom 0), encode claim] = .exhausted := by
  constructor
  · exact (native_judgment_iff _ _ _).mpr (.axiom rfl)
  · rw [← common_host_apply 0 "vibe:check-static" (by decide +kernel),
      admission_apply "vibe:check-static" (by decide)]
    rfl

end Mettapedia.Languages.VibeITP.Presentation.KernelFormation.Controls
