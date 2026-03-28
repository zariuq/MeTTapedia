import Mettapedia.Logic.MarkovLogicDynamicTranscendence

/-!
# Dynamic Individuation: Boundary Emergence with Shell Guarantees

This module formalizes a practical bridge between:

1. **Approximate pre-closure stability** (dynamic rewriting at shell distance),
2. **Path-wise cumulative drift control** (multiple rewrites),
3. **Exact post-closure stability** once an interaction-closed shell is reached.

The workflow is:

- Start with a finite nonempty seed region (`ProtoCore`),
- Track distant rewrites with `DynamicIndividuationStep`,
- Accumulate drift bounds over a `DynamicIndividuationPath`,
- Promote to exact invariance with `DynamicIndividuationClosure`.

**Positive example.** A subsystem boundary is not fully settled yet, but
the system keeps shell agreement around a seed; local seed queries drift
only by geometric tails.

**Negative example.** If shell agreement is violated near the seed, or
if Dobrushin budgets fail, no stability guarantee is provided.
-/

namespace Mettapedia.Logic.MarkovLogicDynamicIndividuation

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.MarkovLogicDynamicTranscendence
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A proto-core is a finite nonempty seed region before full closure is known. -/
structure ProtoCore
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  seed : Region Atom
  seed_nonempty : seed.Nonempty

noncomputable def ProtoCore.shell
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (proto : ProtoCore M) (n : ℕ) : Region Atom :=
  M.iterExpandRegion proto.seed n

private theorem seed_subset_shell
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Γ : Region Atom) :
    ∀ n : ℕ, Γ ⊆ M.iterExpandRegion Γ n
  | 0 => by
      intro a ha
      simpa [ClassicalInfiniteGroundMLNSpec.iterExpandRegion] using ha
  | n + 1 => by
      intro a ha
      exact M.subset_iterExpandRegion_succ Γ n ((seed_subset_shell M Γ n) ha)

/-- One dynamic individuation step: shell agreement around a proto-core. -/
structure DynamicIndividuationStep
    (M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  proto : ProtoCore M₁
  shellDepth : ℕ
  shell_agreement : SpecAgreesOnRegion M₁ M₂
    (M₁.iterExpandRegion proto.seed shellDepth)
  budget₁ : M₁.PaperUniformSmallTotalInfluence
  budget₂ : M₂.PaperUniformSmallTotalInfluence

private noncomputable def DynamicIndividuationStep.toDynamicTranscendenceStep
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂) :
    DynamicTranscendenceStep M₁ M₂ where
  queryRegion := step.proto.seed
  shellDepth := step.shellDepth
  shell_agreement := step.shell_agreement
  budget₁ := step.budget₁
  budget₂ := step.budget₂

private noncomputable def chosenUniformConstant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) : ℝ :=
  Classical.choose (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)

private theorem chosenUniformConstant_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    0 ≤ chosenUniformConstant M hM :=
  (Classical.choose_spec (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)).1

private theorem chosenUniformConstant_lt_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    chosenUniformConstant M hM < 1 :=
  (Classical.choose_spec (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)).2.1

private theorem finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    ∀ Δ : Region Atom,
      M.finiteRegionPairwiseDobrushinConstant Δ ≤ chosenUniformConstant M hM :=
  (Classical.choose_spec (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)).2.2

noncomputable def DynamicIndividuationStep.contractionConstant
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂) : ℝ :=
  max (chosenUniformConstant M₁ step.budget₁) (chosenUniformConstant M₂ step.budget₂)

theorem DynamicIndividuationStep.contractionConstant_nonneg
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂) :
    0 ≤ step.contractionConstant := by
  exact le_trans
    (chosenUniformConstant_nonneg M₁ step.budget₁)
    (le_max_left _ _)

theorem DynamicIndividuationStep.contractionConstant_lt_one
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂) :
    step.contractionConstant < 1 := by
  refine max_lt_iff.mpr ?_
  exact ⟨chosenUniformConstant_lt_one M₁ step.budget₁,
    chosenUniformConstant_lt_one M₂ step.budget₂⟩

noncomputable def DynamicIndividuationStep.errorBound
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂) : ℝ :=
  2 * (step.proto.seed.card : ℝ) * step.contractionConstant ^ step.shellDepth

theorem DynamicIndividuationStep.errorBound_nonneg
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂) :
    0 ≤ step.errorBound := by
  unfold DynamicIndividuationStep.errorBound
  have hpow : 0 ≤ step.contractionConstant ^ step.shellDepth := by
    exact pow_nonneg step.contractionConstant_nonneg _
  nlinarith

/-- Explicit-constant shell guarantee on seed queries. -/
theorem DynamicIndividuationStep.seed_queryProb_approximately_preserved_explicit
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.proto.seed) :
    |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
      ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
        step.errorBound := by
  simpa [DynamicIndividuationStep.errorBound]
    using DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
      (step := step.toDynamicTranscendenceStep)
      (C := step.contractionConstant)
      (hC_nonneg := step.contractionConstant_nonneg)
      (hC_lt_one := step.contractionConstant_lt_one)
      (hC_bound₁ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₁ step.budget₁ Δ)
          (le_max_left _ _))
      (hC_bound₂ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₂ step.budget₂ Δ)
          (le_max_right _ _))
      μ₁ μ₂ hμ₁ hμ₂ q hq

/-- Budget-packaged shell guarantee on seed queries. -/
theorem DynamicIndividuationStep.seed_queryProb_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.proto.seed) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
        ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
          2 * (step.proto.seed.card : ℝ) * C ^ step.shellDepth := by
  simpa [DynamicIndividuationStep.toDynamicTranscendenceStep]
    using DynamicTranscendenceStep.queryProb_approximately_preserved
      (step := step.toDynamicTranscendenceStep) μ₁ μ₂ hμ₁ hμ₂ q hq

/-- WM truth-value shell guarantee on seed queries. -/
theorem DynamicIndividuationStep.seed_wmStrength_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicIndividuationStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.proto.seed) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q).toReal| ≤
          2 * (step.proto.seed.card : ℝ) * C ^ step.shellDepth := by
  simpa [queryStrength_singleton_eq_queryProb]
    using step.seed_queryProb_approximately_preserved μ₁ μ₂ hμ₁ hμ₂ q hq

-- ═══════════════════════════════════════════════════════════════════════════
-- DynamicIndividuationPath: repeated distant rewrites before full closure
-- ═══════════════════════════════════════════════════════════════════════════

/-- A finite sequence of dynamic individuation rewrites. -/
inductive DynamicIndividuationPath :
    ClassicalInfiniteGroundMLNSpec Atom ClauseId →
    ClassicalInfiniteGroundMLNSpec Atom ClauseId → Type _ where
  | single {M₀ M₁ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (first : DynamicIndividuationStep M₀ M₁) :
      DynamicIndividuationPath M₀ M₁
  | step {M₀ M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (path : DynamicIndividuationPath M₀ M₁)
      (next : DynamicIndividuationStep M₁ M₂) :
      DynamicIndividuationPath M₀ M₂

/-- The original seed tracked throughout the path. -/
noncomputable def DynamicIndividuationPath.originalSeed :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicIndividuationPath M₀ M_final → Region Atom
  | _, _, .single first => first.proto.seed
  | _, _, .step path _ => path.originalSeed

/-- Coherence: each next step still contains the original seed. -/
def DynamicIndividuationPath.Coherent :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicIndividuationPath M₀ M_final → Prop
  | _, _, .single _ => True
  | _, _, .step path next =>
      path.Coherent ∧ path.originalSeed ⊆ next.proto.seed

/-- Total accumulated explicit drift bound along the path. -/
noncomputable def DynamicIndividuationPath.totalErrorBound :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicIndividuationPath M₀ M_final → ℝ
  | _, _, .single first => first.errorBound
  | _, _, .step path next => path.totalErrorBound + next.errorBound

theorem DynamicIndividuationPath.totalErrorBound_nonneg
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (path : DynamicIndividuationPath M₀ M_final) :
    0 ≤ path.totalErrorBound := by
  induction path with
  | single first =>
      simpa [DynamicIndividuationPath.totalErrorBound] using first.errorBound_nonneg
  | step path next ih =>
      simp [DynamicIndividuationPath.totalErrorBound]
      nlinarith [ih, next.errorBound_nonneg]

/-- DLR witnesses for each stage of a dynamic individuation path. -/
inductive DynamicIndividuationPathDLR :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    (path : DynamicIndividuationPath M₀ M_final) → Type _ where
  | single {M₀ M₁ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (first : DynamicIndividuationStep M₀ M₁)
      (μ₀ : ProbabilityMeasure (InfiniteWorld Atom))
      (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
      (hμ₀ : FixedRegionCylinderDLR M₀.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₀ : Measure (InfiniteWorld Atom)))
      (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₁ : Measure (InfiniteWorld Atom))) :
      DynamicIndividuationPathDLR (.single first)
  | step {M₀ M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      {path : DynamicIndividuationPath M₀ M₁}
      {next : DynamicIndividuationStep M₁ M₂}
      (prev : DynamicIndividuationPathDLR path)
      (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
      (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₂ : Measure (InfiniteWorld Atom))) :
      DynamicIndividuationPathDLR (.step path next)

noncomputable def DynamicIndividuationPathDLR.startMeasure
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_final}
    (measures : DynamicIndividuationPathDLR path) :
    ProbabilityMeasure (InfiniteWorld Atom) := by
  induction measures with
  | single _ μ₀ _ _ _ => exact μ₀
  | step prev _ _ ih => exact ih

noncomputable def DynamicIndividuationPathDLR.endMeasure
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_final}
    (measures : DynamicIndividuationPathDLR path) :
    ProbabilityMeasure (InfiniteWorld Atom) := by
  induction measures with
  | single _ _ μ₁ _ _ => exact μ₁
  | step _ μ₂ _ => exact μ₂

theorem DynamicIndividuationPathDLR.startDLR
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_final}
    (measures : DynamicIndividuationPathDLR path) :
    FixedRegionCylinderDLR M₀.toStrictlyPositiveInfiniteGroundMLNSpec
      ((measures.startMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
        Measure (InfiniteWorld Atom)) := by
  induction measures with
  | single _ _ _ hμ₀ _ =>
      simpa [DynamicIndividuationPathDLR.startMeasure] using hμ₀
  | step prev _ _ ih =>
      simpa [DynamicIndividuationPathDLR.startMeasure] using ih

theorem DynamicIndividuationPathDLR.endDLR
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_final}
    (measures : DynamicIndividuationPathDLR path) :
    FixedRegionCylinderDLR M_final.toStrictlyPositiveInfiniteGroundMLNSpec
      ((measures.endMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
        Measure (InfiniteWorld Atom)) := by
  induction measures with
  | single _ _ _ _ hμ₁ =>
      simpa [DynamicIndividuationPathDLR.endMeasure] using hμ₁
  | step _ _ hμ₂ =>
      simpa [DynamicIndividuationPathDLR.endMeasure] using hμ₂

private theorem supported_on_originalSeed_implies_supported_on_seed
    {M₀ M_mid M_next : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_mid}
    {next : DynamicIndividuationStep M_mid M_next}
    (hsubset : path.originalSeed ⊆ next.proto.seed)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalSeed) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ next.proto.seed := by
  intro p hp
  exact hsubset (hq p hp)

/-- Cumulative drift on original-seed queries along a coherent path. -/
theorem DynamicIndividuationPathDLR.seed_queryProb_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_final}
    (measures : DynamicIndividuationPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalSeed) :
    |((infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR).queryProb q).toReal -
      ((infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR).queryProb q).toReal| ≤
        path.totalErrorBound := by
  induction path generalizing q with
  | single first =>
      cases measures with
      | single _ μ₀ μ₁ hμ₀ hμ₁ =>
          have hq' : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ first.proto.seed := by
            simpa [DynamicIndividuationPath.originalSeed] using hq
          simpa [DynamicIndividuationPath.originalSeed,
            DynamicIndividuationPath.totalErrorBound,
            DynamicIndividuationPathDLR.startMeasure,
            DynamicIndividuationPathDLR.endMeasure,
            DynamicIndividuationPathDLR.startDLR,
            DynamicIndividuationPathDLR.endDLR]
            using first.seed_queryProb_approximately_preserved_explicit μ₀ μ₁ hμ₀ hμ₁ q hq'
  | step path next ih =>
      cases measures with
      | step prev μ₂ hμ₂ =>
          have hcoh' : path.Coherent ∧ path.originalSeed ⊆ next.proto.seed := by
            simpa [DynamicIndividuationPath.Coherent] using hcoh
          rcases hcoh' with ⟨hcohPrev, hsubset⟩
          have hqPrev : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalSeed := by
            simpa [DynamicIndividuationPath.originalSeed] using hq
          have hprev := ih prev hcohPrev q hqPrev
          have hqNext : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ next.proto.seed := by
            exact supported_on_originalSeed_implies_supported_on_seed hsubset hqPrev
          have hnext :=
            next.seed_queryProb_approximately_preserved_explicit
              prev.endMeasure μ₂ prev.endDLR hμ₂ q hqNext
          let a : ℝ :=
            ((infiniteMLNMassSemantics M₀ prev.startMeasure prev.startDLR).queryProb q).toReal
          let b : ℝ :=
            ((infiniteMLNMassSemantics _ prev.endMeasure prev.endDLR).queryProb q).toReal
          let c : ℝ :=
            ((infiniteMLNMassSemantics _ μ₂ hμ₂).queryProb q).toReal
          have htri : |a - c| ≤ |a - b| + |b - c| := by
            calc
              |a - c| = |(a - b) + (b - c)| := by ring_nf
              _ ≤ |a - b| + |b - c| := abs_add_le _ _
          have hbound : |a - c| ≤ path.totalErrorBound + next.errorBound := by
            linarith [htri, hprev, hnext]
          simpa [a, b, c, DynamicIndividuationPath.totalErrorBound,
            DynamicIndividuationPathDLR.startMeasure,
            DynamicIndividuationPathDLR.endMeasure,
            DynamicIndividuationPathDLR.startDLR,
            DynamicIndividuationPathDLR.endDLR]
            using hbound

/-- WM-strength cumulative drift on original-seed queries along a coherent path. -/
theorem DynamicIndividuationPathDLR.seed_wmStrength_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicIndividuationPath M₀ M_final}
    (measures : DynamicIndividuationPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalSeed) :
    |(BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR} :
          MassState (ConstraintQuery Atom)) q).toReal -
      (BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR} :
          MassState (ConstraintQuery Atom)) q).toReal| ≤
        path.totalErrorBound := by
  simpa [queryStrength_singleton_eq_queryProb]
    using measures.seed_queryProb_cumulative_drift hcoh q hq

-- ═══════════════════════════════════════════════════════════════════════════
-- Closure promotion: once shell is closed, exact invariance is recovered
-- ═══════════════════════════════════════════════════════════════════════════

/-- A proto-core together with a shell depth where closure has emerged. -/
structure DynamicIndividuationClosure
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  proto : ProtoCore M
  closureDepth : ℕ
  shell_closed : InteractionClosed M (M.iterExpandRegion proto.seed closureDepth)

noncomputable def DynamicIndividuationClosure.toIndividuatedSubsystem
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (w : DynamicIndividuationClosure M) :
    IndividuatedSubsystem M where
  core := M.iterExpandRegion w.proto.seed w.closureDepth
  core_nonempty := by
    rcases w.proto.seed_nonempty with ⟨a, ha⟩
    exact ⟨a, seed_subset_shell M w.proto.seed w.closureDepth ha⟩
  interaction_closed := w.shell_closed

/-- After closure is reached, seed-supported queries are exactly invariant
under ontology extension that agrees on the closed shell. -/
theorem DynamicIndividuationClosure.seed_queryProb_exact_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (w : DynamicIndividuationClosure M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂
      (M₁.iterExpandRegion w.proto.seed w.closureDepth))
    (hclosed₂ : InteractionClosed M₂
      (M₁.iterExpandRegion w.proto.seed w.closureDepth))
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ w.proto.seed) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q := by
  let S := w.toIndividuatedSubsystem
  have hq_shell :
      ∀ p ∈ q,
        (p : Sigma fun _ : Atom => Bool).1 ∈
          (M₁.iterExpandRegion w.proto.seed w.closureDepth) := by
    intro p hp
    exact seed_subset_shell M₁ w.proto.seed w.closureDepth (hq p hp)
  simpa [S] using
    (w.toIndividuatedSubsystem).queryProb_invariant_under_extension
      hagree hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq_shell

/-- WM version of exact post-closure seed-query invariance. -/
theorem DynamicIndividuationClosure.seed_wmStrength_exact_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (w : DynamicIndividuationClosure M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂
      (M₁.iterExpandRegion w.proto.seed w.closureDepth))
    (hclosed₂ : InteractionClosed M₂
      (M₁.iterExpandRegion w.proto.seed w.closureDepth))
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ w.proto.seed) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q := by
  simp [queryStrength_singleton_eq_queryProb]
  exact w.seed_queryProb_exact_under_extension
    hagree hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

end Mettapedia.Logic.MarkovLogicDynamicIndividuation
