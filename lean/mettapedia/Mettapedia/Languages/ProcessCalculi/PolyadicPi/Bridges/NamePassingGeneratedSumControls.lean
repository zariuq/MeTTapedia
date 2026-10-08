import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionControls
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.AssumptionContextsModel

/-!
# Generated full-motive sums under the actual compiler pullback

The generated Sigma eliminator is interpreted on the compiler's own
context category. Its result depends on both the supplied object and proof
witness. The exact compiler pullback retains this result, and a supplied
returning rho execution retains its separate certificate and endpoint.
These are native evidence calculations, not execution of guest Sigma data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedSumControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory DisplayedPresheafTransport DisplayedPresheafComprehension
open NamePassingDependentEvidence NamePassingGeneratedEvidenceControls
open Calculi.NativeDependent.AssumptionContexts
open Calculi.NativeDependent.AssumptionContexts.Interpretation

noncomputable abbrev nativeContext := Calculi.NativeDependent.AssumptionContexts.Interpretation.context
  (Calculi.NativeDependent.Examples.AssumptionContextsModel.objects ContextCategory)
  (Calculi.NativeDependent.Examples.AssumptionContextsModel.constants ContextCategory)
  (Calculi.NativeDependent.Examples.AssumptionContextsModel.predicates ContextCategory)
  Calculi.NativeDependent.Examples.AssumptionContextsModel.sumScope

noncomputable abbrev motive : DisplayedFamily nativeContext :=
  Calculi.NativeDependent.Examples.AssumptionContextsModel.fullMotive ContextCategory

noncomputable def certificate : motive.sections :=
  term
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.objects ContextCategory)
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.constants ContextCategory)
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.predicates ContextCategory)
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.declarations ContextCategory)
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.motives ContextCategory)
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.primitives ContextCategory)
    Calculi.NativeDependent.Examples.AssumptionContextsModel.eliminated

noncomputable def suppliedPair (a : Nat) (witness : Fin (a + 1)) :
    compiledPrograms ⟶ nativeContext where
  app world := TypeCat.ofHom fun _ =>
    (Calculi.NativeDependent.Examples.AssumptionContextsModel.sumPoint ContextCategory world a witness).2
  naturality _ _ _ := by ext code; rfl

noncomputable def targetCertificate (a : Nat) (witness : Fin (a + 1)) :
    (reindexDisplayed (suppliedPair a witness) motive).sections :=
  reindexDisplayedSection (suppliedPair a witness) motive certificate

noncomputable def sourceCertificate (a : Nat) (witness : Fin (a + 1)) :
    (reindexDisplayed compilerMap (reindexDisplayed (suppliedPair a witness) motive)).sections :=
  reindexDisplayedSection compilerMap (reindexDisplayed (suppliedPair a witness) motive)
    (targetCertificate a witness)

/-- The actual compiler map preserves the generated eliminator's result,
including the proof witness on which its output type depends. -/
theorem compiler_eliminated_computes (position : sourcePrograms.Elements)
    (a : Nat) (witness : Fin (a + 1)) :
    ((sourceCertificate a witness).val position).val = a + witness.val :=
  Calculi.NativeDependent.Examples.AssumptionContextsModel.eliminated_computes
    ContextCategory position.1 a witness

/-- Two proof witnesses of the same object can have different motive
types; erasing the second coordinate cannot provide this observation. -/
theorem proof_witness_changes_type (world : ContextCategoryᵒᵖ) :
    motive.obj (Calculi.NativeDependent.Examples.AssumptionContextsModel.sumPoint
      ContextCategory world 1 0) ≠
    motive.obj (Calculi.NativeDependent.Examples.AssumptionContextsModel.sumPoint
      ContextCategory world 1 1) := by
  change Fin 2 ≠ Fin 3
  intro same
  have sizes := congrArg Nat.card same
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at sizes
  exact (by decide : (2 : Nat) ≠ 3) sizes

/-- This native Sigma certificate accompanies an actual returning prefix.
The retained runtime certificate and supplied endpoint are still those
of the checked lambda/compiler execution. -/
theorem returning_execution_with_full_motive (a : Nat) (witness : Fin (a + 1)) :
    ∃ final, ∃ actual : Mettapedia.GSLT.IndexedOperational.ExecutionPath
        RhoUnaryReadback.Target (NamePassingSpineControls.process
          NamePassingCompilerReadback.Controls.start) final,
      ∃ receipt : NamePassingGeneratedEvidence.GeneratedReceipt models
          NamePassingDependentRuntimeControls.startPoint (applicationTree (a + witness.val))
          (NamePassingSpineControls.world NamePassingCompilerReadback.Controls.names)
          (NamePassingSpineControls.code NamePassingCompilerReadback.Controls.start) actual,
        receipt.history.2 = applicationTree (a + witness.val) ∧
          ((sourceCertificate a witness).val NamePassingDependentRuntimeControls.startPoint).val =
            a + witness.val ∧
          (RhoUnaryInputObservation.targetPredicate
            (NamePassingSpineControls.world NamePassingCompilerReadback.Controls.names) .zero).1 final := by
  obtain ⟨final, actual, receipt, origin, _, observed⟩ :=
    returning_execution_with_generated_certificate (a + witness.val)
  exact ⟨final, actual, receipt, origin, compiler_eliminated_computes _ a witness, observed⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedSumControls
