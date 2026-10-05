import Mettapedia.Languages.MM0.Presentation.KernelFormation

/-! # MM0 supplied-proof identity and checked computational entry controls -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.KernelFormation.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions ComputationalProof
open ComputationalAdmission
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def context : Context := [.regular 0 ∅]
private def hypotheses : List Preterm := [.var 0, .var 0]
private def inputs (proof : ProofWitness) : List Term :=
  [encodeTable ([] : SignatureTable), encodeDefinitions [], encodeTheorems [], encodeContext context,
    encodeExpressions hypotheses, encodeProof proof, encode (.var 0)]

theorem duplicate_hypotheses_retain_distinct_witnesses :
    (nativeKernel {} context hypotheses).toChecker.check (.var 0) (.hyp 0) = true ∧
      (nativeKernel {} context hypotheses).toChecker.check (.var 0) (.hyp 1) = true ∧
      (ProofWitness.hyp 0 : (nativeProofSystem {} context hypotheses).ProofObject) ≠ .hyp 1 := by
  constructor
  · exact (native_judgment_iff _ _ _ _ _).mpr (.hyp rfl)
  constructor
  · exact (native_judgment_iff _ _ _ _ _).mpr (.hyp rfl)
  · intro same
    cases same

theorem checked_entry_accepts_the_second_occurrence :
    Applies admissionProgram dataEqualityHost "mm0:check-proof" (inputs (.hyp 1)) (.sym "True") :=
  (checked_entry {} context hypotheses (.hyp 1) (.var 0)).mpr (.hyp rfl)

theorem derivability_cannot_rescue_a_missing_occurrence :
    Derives (Theory.termSignature {}) (Theory.definitionSignature {}) (Theory.theoremSignature {})
      context hypotheses (.var 0) ∧
      Applies admissionProgram dataEqualityHost "mm0:check-proof" (inputs (.hyp 2)) (.sym "False") := by
  constructor
  · exact .hypothesis (by simp [hypotheses])
  · apply (checked_entry_refuses {} context hypotheses (.hyp 2) (.var 0)).mpr
    intro checked
    have computed := checked.eval
    simp [ProofWitness.proof?, hypotheses] at computed

theorem a_foreign_hypothesis_store_changes_acceptance :
    (nativeKernel {} context []).toChecker.check (.var 0) (.hyp 0) = false ∧
      (nativeKernel {} context hypotheses).toChecker.check (.var 0) (.hyp 0) = true := by
  constructor
  · change ProofWitness.check (Theory.termSignature {}) (Theory.definitionSignature {})
      (Theory.theoremSignature {}) context [] (.hyp 0) (.var 0) = false
    simp [ProofWitness.check, ProofWitness.proof?]
  · exact (native_judgment_iff _ _ _ _ _).mpr (.hyp rfl)

end Mettapedia.Languages.MM0.Presentation.KernelFormation.Controls
