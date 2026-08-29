import Mettapedia.Languages.Metamath.InferenceOperationalSpecStepInversion
import Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification
import Mettapedia.Languages.Metamath.InferenceActiveHypothesisLeaf

open Mettapedia.GSLT.LanguageDef

/-!
# Canonical projected images of singleton Metamath operational steps

Singleton operational steps expose exactly the data consumed by their
constructors.  When the database and frame are the images of a successful
Metamath projection, that data has a canonical tagged preimage in the
generated calculus.

This is image completeness, not injectivity.  Operational expressions erase
source symbol tags, hypothesis steps erase source labels, and assertion steps
store a total substitution rather than its original finite representation.
The assertion result below therefore constructs the canonical frame-relative
expressions and authored finite substitution.  Its arbitrary older operational
stack suffix is retained but is not identified with a runtime stack prefix.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalProjectedImage

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepInversion
open Mettapedia.Languages.Metamath.InferenceOperationalExprReification
open Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification
open Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification
open Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification

/-! ## Active-hypothesis image -/

/-- Erasing one projected hypothesis formula gives exactly the expression
pushed by its operational hypothesis constructor. -/
@[simp] theorem pushedHypothesisExpr_operationalHyp
    (hypothesis : HypothesisView) :
    pushedHypothesisExpr (operationalHyp hypothesis) =
      operationalExpr hypothesis.formula := by
  cases hypothesis with
  | floating label typecode variableName =>
      simp [pushedHypothesisExpr, operationalHyp, operationalExpr,
        HypothesisView.formula, ConstantHeadedFormula.toRuntime,
        Metamath.Kernel.toExpr, Metamath.Kernel.toSym,
        Metamath.Verify.Sym.value]
  | essential label formula =>
      rfl

/-- Every singleton upstream hypothesis step over the projected caller frame
has some retained source hypothesis as a canonical generated leaf.  The source
label is existential because the operational hypothesis carrier erases it. -/
theorem proofValidFrom_single_projected_useHyp_image
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (initial final : List Metamath.Spec.Expr)
    (hypothesis : Metamath.Spec.Hyp)
    (hvalid : Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      initial final [Metamath.Spec.ProofStep.useHyp hypothesis]) :
    ∃ sourceHypothesis : HypothesisView,
      sourceHypothesis ∈ projection.activeHypotheses ∧
      operationalHyp sourceHypothesis = hypothesis ∧
      final = operationalExpr sourceHypothesis.formula :: initial ∧
      Nonempty (GeneratedActiveHypothesisLeaf target sourceHypothesis) := by
  have hinversion :=
    (proofValidFrom_single_useHyp_iff
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame projection.activeHypotheses)
      initial final hypothesis).1 hvalid
  have hmember : hypothesis ∈
      projection.activeHypotheses.map operationalHyp := by
    exact hinversion.1
  rcases List.mem_map.mp hmember with
    ⟨sourceHypothesis, hsourceMember, hsourceImage⟩
  refine ⟨sourceHypothesis, hsourceMember, hsourceImage, ?_, ?_⟩
  · have hfinal := hinversion.2
    rw [← hsourceImage] at hfinal
    simpa using hfinal
  · exact ⟨generatedActiveHypothesisLeaf projection target hprojection
      hsourceMember⟩

/-! ## Assertion image -/

/-- Every canonical operational actual is frame-respecting by construction. -/
theorem reifyOperationalActuals_respectsCaller
    (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView) :
    ∀ actual,
      actual ∈ reifyOperationalActuals callerActiveNames calleeActiveNames
        specSubstitution hypotheses →
      formulaSymbolsRespectFrame callerActiveNames actual = true := by
  induction hypotheses with
  | nil => simp [reifyOperationalActuals]
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp only [reifyOperationalActuals, List.mem_cons]
      all_goals
        intro actual hactual
        rcases hactual with rfl | htail
        · apply reifyOperationalExpr_respectsFrame
        · exact ih actual htail

/-- Every singleton upstream assertion step at a retained projected label has
the canonical frame-relative actual vector, result, and generated local node
as a preimage.  Operational floating typing and DV validity come directly
from inversion; all structural/tag conditions come from successful projection. -/
theorem proofValidFrom_single_projected_useAssertion_image
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef)
    (hproject : projectPrefix? db = some projection)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions)
    (specSubstitution : Metamath.Spec.Subst)
    (initial final : List Metamath.Spec.Expr)
    (hvalid : Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      initial final
      [Metamath.Spec.ProofStep.useAssertion assertion.label
        specSubstitution]) :
    ∃ remaining : List Metamath.Spec.Expr,
      initial =
          ((reifyOperationalActuals
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.hypotheses).map
              operationalExpr).reverse ++ remaining ∧
      final =
          operationalExpr
            (reifyOperationalResult
              (floatingVariableNames projection.activeHypotheses)
              (floatingVariableNames assertion.hypotheses)
              specSubstitution assertion.formula) :: remaining ∧
      Nonempty
        (GeneratedAssertionNode projection target assertion
          (reifyOperationalActuals
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.hypotheses)
          (reifyOperationalResult
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.formula)
          (reifyOperationalSubstitution
            (floatingVariableNames projection.activeHypotheses)
            specSubstitution assertion.hypotheses)) := by
  rcases (proofValidFrom_single_useAssertion_iff
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame projection.activeHypotheses)
      initial final assertion.label specSubstitution).1 hvalid with
    ⟨assertionFrame, assertionExpression, needed, remaining,
      hlookup, hdv, htyped, hneeded, hinitial, hfinal⟩
  have hprojectedLookup := projectedAssertion_toDatabaseTotal_lookup
    db projection assertion hproject hmember
  have himage : (assertionFrame, assertionExpression) =
      (operationalFrame assertion.frame assertion.hypotheses,
        operationalExpr assertion.formula) := by
    exact Option.some.inj (hlookup.symm.trans hprojectedLookup)
  cases himage
  have htypedProjected : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈
          assertion.hypotheses.map operationalHyp →
        (specSubstitution variableName).typecode = typecode := by
    simpa [operationalFrame] using htyped
  have hdvProjected : Metamath.Spec.dvOK
      ((floatingVariableNames projection.activeHypotheses).map
        Metamath.Spec.Variable.mk)
      (ToSpecDVPairs assertion.frame.dj.toList)
      (ToSpecDVPairs projection.callerFrame.dj.toList)
      specSubstitution := by
    rw [operationalFrame_vars] at hdv
    simpa [operationalFrame] using hdv
  have hnode := generatedAssertionNode_of_projectedOperational
    projection target hprojection assertion hmember specSubstitution
      htypedProjected hdvProjected
  have hactuals :
      (reifyOperationalActuals
          (floatingVariableNames projection.activeHypotheses)
          (floatingVariableNames assertion.hypotheses)
          specSubstitution assertion.hypotheses).map operationalExpr =
        needed := by
    rw [map_operationalExpr_reifyOperationalActuals]
    rw [operationalFrame_vars] at hneeded
    simp only [operationalFrame] at hneeded
    rw [hneeded]
    apply List.map_congr_left
    intro hypothesis _hmember
    cases hypothesis <;> rfl
  have hresult :
      operationalExpr
          (reifyOperationalResult
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.formula) =
        Metamath.Spec.applySubst
          ((floatingVariableNames assertion.hypotheses).map
            Metamath.Spec.Variable.mk)
          specSubstitution (operationalExpr assertion.formula) := by
    exact operationalExpr_reifyOperationalResult _ _ _ _
  refine ⟨remaining, ?_, ?_, hnode⟩
  · rw [hactuals]
    exact hinitial
  · rw [hresult]
    rw [operationalFrame_vars] at hfinal
    simpa [operationalFrame] using hfinal

/-- The exact canonical node maps back to the original singleton operational
assertion step.  Exact totalization makes the stored operational substitution
provably extensionally identical to the supplied total function, including
outside the finite callee key set. -/
theorem canonicalGeneratedAssertionNode_toProofValidFrom
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef)
    (hproject : projectPrefix? db = some projection)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions)
    (specSubstitution : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr)
    (node : GeneratedAssertionNode projection target assertion
      (reifyOperationalActuals
        (floatingVariableNames projection.activeHypotheses)
        (floatingVariableNames assertion.hypotheses)
        specSubstitution assertion.hypotheses)
      (reifyOperationalResult
        (floatingVariableNames projection.activeHypotheses)
        (floatingVariableNames assertion.hypotheses)
        specSubstitution assertion.formula)
      (reifyOperationalSubstitution
        (floatingVariableNames projection.activeHypotheses)
        specSubstitution assertion.hypotheses)) :
    Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      (((reifyOperationalActuals
        (floatingVariableNames projection.activeHypotheses)
        (floatingVariableNames assertion.hypotheses)
        specSubstitution assertion.hypotheses).map operationalExpr).reverse ++
          remaining)
      (operationalExpr
        (reifyOperationalResult
          (floatingVariableNames projection.activeHypotheses)
          (floatingVariableNames assertion.hypotheses)
          specSubstitution assertion.formula) :: remaining)
      [Metamath.Spec.ProofStep.useAssertion assertion.label
        specSubstitution] := by
  have hactualsRespect := reifyOperationalActuals_respectsCaller
    (floatingVariableNames projection.activeHypotheses)
    (floatingVariableNames assertion.hypotheses) specSubstitution
    assertion.hypotheses
  have hforward := generatedAssertionNode_toProofValidFrom
    db projection target hprojection assertion
    (reifyOperationalActuals
      (floatingVariableNames projection.activeHypotheses)
      (floatingVariableNames assertion.hypotheses)
      specSubstitution assertion.hypotheses)
    (reifyOperationalResult
      (floatingVariableNames projection.activeHypotheses)
      (floatingVariableNames assertion.hypotheses)
      specSubstitution assertion.formula)
    (reifyOperationalSubstitution
      (floatingVariableNames projection.activeHypotheses)
      specSubstitution assertion.hypotheses)
    node specSubstitution remaining hproject hmember hactualsRespect
  rw [operationalSubstitution_reifyOperationalSubstitution] at hforward
  exact hforward

/-- Canonical projected-image equivalence for one retained assertion label.
The finite witness, actuals, and result are fixed canonically; the older
operational suffix remains an explicit parameter. -/
theorem canonicalGeneratedAssertionNode_nonempty_iff_singleProofValidFrom
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedCalculusLanguageDef)
    (hproject : projectPrefix? db = some projection)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions)
    (specSubstitution : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr) :
    Nonempty
        (GeneratedAssertionNode projection target assertion
          (reifyOperationalActuals
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.hypotheses)
          (reifyOperationalResult
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.formula)
          (reifyOperationalSubstitution
            (floatingVariableNames projection.activeHypotheses)
            specSubstitution assertion.hypotheses)) ↔
      Metamath.Spec.ProofValidFrom
        (Metamath.Kernel.toDatabaseTotal db)
        (operationalFrame projection.callerFrame
          projection.activeHypotheses)
        (((reifyOperationalActuals
          (floatingVariableNames projection.activeHypotheses)
          (floatingVariableNames assertion.hypotheses)
          specSubstitution assertion.hypotheses).map
            operationalExpr).reverse ++ remaining)
        (operationalExpr
          (reifyOperationalResult
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.formula) :: remaining)
        [Metamath.Spec.ProofStep.useAssertion assertion.label
          specSubstitution] := by
  constructor
  · rintro ⟨node⟩
    exact canonicalGeneratedAssertionNode_toProofValidFrom db projection
      target hproject hprojection assertion hmember specSubstitution remaining
      node
  · intro hvalid
    rcases proofValidFrom_single_projected_useAssertion_image db projection
        target hproject hprojection assertion hmember specSubstitution
        (((reifyOperationalActuals
          (floatingVariableNames projection.activeHypotheses)
          (floatingVariableNames assertion.hypotheses)
          specSubstitution assertion.hypotheses).map
            operationalExpr).reverse ++ remaining)
        (operationalExpr
          (reifyOperationalResult
            (floatingVariableNames projection.activeHypotheses)
            (floatingVariableNames assertion.hypotheses)
            specSubstitution assertion.formula) :: remaining)
        hvalid with
      ⟨_olderSuffix, _hinitial, _hfinal, node⟩
    exact node

end Mettapedia.Languages.Metamath.InferenceOperationalProjectedImage
