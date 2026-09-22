import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLNativeMixedPreservation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternCodec

/-!
# Computational and universe-level components of the unchanged mixed profile

The full step relation includes arbitrary semantically equal universe-level
spellings.  A finite rule-data executor for beta, projections, native iota,
HOL decoding, and contexts cannot silently count as that full relation.

This module proves an exact decomposition.  The level component retains the
already present beta/projection rules, so the two components overlap; no
disjointness, evaluator priority, or new conversion rule is asserted.  The
separate head query compares the existing complete level normal forms.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedOperationalDecomposition

open Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax
open DeclarationAwarePatternCodec

abbrev jointRules := FormationSensitiveHOLProofListIntegration.rules

abbrev ComputationalStep {n : Nat} (source target : Tower.Tm n) : Prop :=
  StepCore jointRules.computation (fun _ _ => False) source target

abbrev LevelAndBetaStep {n : Nat} (source target : Tower.Tm n) : Prop :=
  StepCore RootComputation.empty jointRules.headEq source target

abbrev FullStep {n : Nat} (source target : Tower.Tm n) : Prop :=
  StepCore jointRules.computation jointRules.headEq source target

theorem computational_inclusion {n : Nat} {source target : Tower.Tm n}
    (step : ComputationalStep source target) : FullStep source target := by
  simpa only [Tm.mapHead_id] using
    step.mapHead (targetEq := jointRules.headEq) (targetRoot := jointRules.computation)
      (fun head => head) (fun impossible => impossible.elim)
      (fun evidence => by simpa only [Tm.mapHead_id] using evidence)

theorem level_inclusion {n : Nat} {source target : Tower.Tm n}
    (step : LevelAndBetaStep source target) : FullStep source target := by
  simpa only [Tm.mapHead_id] using
    step.mapHead (sourceRoot := RootComputation.empty)
      (targetEq := jointRules.headEq) (targetRoot := jointRules.computation)
      (fun head => head) (fun evidence => evidence)
      (fun impossible => impossible.elim)

/-- Every single authored contextual step comes from one component.  In
particular, moving under a binder does not require mixing two root services
inside one primitive step. -/
theorem full_step_components {n : Nat} {source target : Tower.Tm n}
    (step : FullStep source target) :
    ComputationalStep source target ∨ LevelAndBetaStep source target := by
  induction step with
  | betaPi body argument => exact .inl (.betaPi body argument)
  | betaSigmaFst first second => exact .inl (.betaSigmaFst first second)
  | betaSigmaSnd first second => exact .inl (.betaSigmaSnd first second)
  | root evidence => exact .inl (.root evidence)
  | head evidence => exact .inr (.head evidence)
  | congPiDom _ ih => exact ih.imp Step.congPiDom Step.congPiDom
  | congPiCod _ ih => exact ih.imp Step.congPiCod Step.congPiCod
  | congSigmaDom _ ih => exact ih.imp Step.congSigmaDom Step.congSigmaDom
  | congSigmaCod _ ih => exact ih.imp Step.congSigmaCod Step.congSigmaCod
  | congIdTy _ ih => exact ih.imp Step.congIdTy Step.congIdTy
  | congIdLeft _ ih => exact ih.imp Step.congIdLeft Step.congIdLeft
  | congIdRight _ ih => exact ih.imp Step.congIdRight Step.congIdRight
  | congLam _ ih => exact ih.imp Step.congLam Step.congLam
  | congAppFun _ ih => exact ih.imp Step.congAppFun Step.congAppFun
  | congAppArg _ ih => exact ih.imp Step.congAppArg Step.congAppArg
  | congPairFst _ ih => exact ih.imp Step.congPairFst Step.congPairFst
  | congPairSnd _ ih => exact ih.imp Step.congPairSnd Step.congPairSnd
  | congFst _ ih => exact ih.imp Step.congFst Step.congFst
  | congSnd _ ih => exact ih.imp Step.congSnd Step.congSnd
  | congRefl _ ih => exact ih.imp Step.congRefl Step.congRefl

theorem full_step_iff_components {n : Nat} {source target : Tower.Tm n} :
    FullStep source target ↔
      ComputationalStep source target ∨ LevelAndBetaStep source target :=
  ⟨full_step_components, fun components =>
    components.elim computational_inclusion level_inclusion⟩

theorem full_derivation_iff_components {n : Nat} {source target : Tower.Tm n} :
    Relation.ReflTransGen FullStep source target ↔
      Relation.ReflTransGen
        (fun left right => ComputationalStep left right ∨ LevelAndBetaStep left right)
        source target := by
  constructor
  · intro path
    exact Relation.ReflTransGen.mono (fun _ _ step => full_step_components step) _ _ path
  · intro path
    exact Relation.ReflTransGen.mono
      (fun _ _ step => step.elim computational_inclusion level_inclusion) _ _ path

def headEqual (left right : Tower.Head) : Bool :=
  match left, right with
  | .legacyGround, .legacyGround => true
  | .sort first, .sort second => decide (LevelNF.normalize first = LevelNF.normalize second)
  | _, _ => false

theorem headEqual_exact (left right : Tower.Head) :
    headEqual left right = true ↔ Tower.HeadEq left right := by
  cases left <;> cases right <;>
    simp [headEqual, Tower.HeadEq, LevelNF.normalize_eq_iff]

/-- A two-input query, not an enumeration of the infinitely many equivalent
universe spellings.  Malformed encodings remain outside the query interface. -/
def encodedHeadEqual (left right : Pattern) : Option Bool := do
  let first ← towerHeadCodec.decode left
  let second ← towerHeadCodec.decode right
  pure (headEqual first second)

theorem encodedHeadEqual_exact (left right : Tower.Head) :
    encodedHeadEqual (towerHeadCodec.encode left) (towerHeadCodec.encode right) = some true ↔
      Tower.HeadEq left right := by
  simp [encodedHeadEqual, towerHeadCodec.decode_encode, headEqual_exact]

theorem level_query_substitution {left right : LevelExpr}
    (equal : headEqual (.sort left) (.sort right) = true)
    (substitution : Nat → LevelExpr) :
    headEqual (.sort (LevelExpr.subst substitution left))
      (.sort (LevelExpr.subst substitution right)) = true := by
  simp only [headEqual, decide_eq_true_eq] at equal ⊢
  exact LevelNF.normalize_subst_congr equal substitution

theorem full_head_step_iff {n : Nat} (left right : Tower.Head) :
    FullStep (n := n) (.head left) (.head right) ↔ Tower.HeadEq left right := by
  constructor
  · intro step
    cases step with
    | head evidence => exact evidence
    | root evidence => cases HOLNativeMixedConversionCompletion.root_inclusion evidence
  · exact Step.head

/-- The existing normal-form algorithm decides precisely the head-step
service of this same native profile, not a separately chosen equality. -/
theorem encodedHeadEqual_native_step {n : Nat} (left right : Tower.Head) :
    encodedHeadEqual (towerHeadCodec.encode left) (towerHeadCodec.encode right) = some true ↔
      FullStep (n := n) (.head left) (.head right) := by
  rw [encodedHeadEqual_exact, full_head_step_iff]

theorem computational_preserves {n : Nat} {context : Tower.Ctx n}
    {source target type : Tower.Tm n}
    (formed : FormationSensitive.Judgment jointRules context source type)
    (step : ComputationalStep source target) :
    FormationSensitive.Judgment jointRules context target type :=
  FormationSensitiveHOLNativeMixedPreservation.step_preserves formed
    (computational_inclusion step)

theorem no_computational_head_step {n : Nat} (left right : Tower.Head) :
    ¬ ComputationalStep (n := n) (.head left) (.head right) := by
  intro step
  cases step with
  | head impossible => exact impossible.elim
  | root evidence => cases HOLNativeMixedConversionCompletion.root_inclusion evidence

/-- Distinct level expressions can agree under every valuation.  Their
native step is real and is absent from the purely computational component. -/
theorem distinct_level_spelling_control {n : Nat} :
    let left : Tower.Tm n := .head (.sort (.max (.param 0) (.param 0)))
    let right : Tower.Tm n := .head (.sort (.param 0))
    FullStep left right ∧ ¬ ComputationalStep left right := by
  constructor
  · apply Step.head
    change ∀ valuation : Nat → Nat, max (valuation 0) (valuation 0) = valuation 0
    intro valuation
    exact max_self _
  · exact no_computational_head_step _ _

theorem distinct_universes_rejected :
    headEqual (.sort (.const 0)) (.sort (.const 1)) = false := by decide

#print axioms full_step_iff_components
#print axioms full_derivation_iff_components
#print axioms headEqual_exact
#print axioms encodedHeadEqual_exact
#print axioms level_query_substitution
#print axioms encodedHeadEqual_native_step
#print axioms computational_preserves
#print axioms distinct_level_spelling_control
#print axioms distinct_universes_rejected

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedOperationalDecomposition
