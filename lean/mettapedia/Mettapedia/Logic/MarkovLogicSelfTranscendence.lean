import Mettapedia.Logic.MarkovLogicIndividuation

/-!
# Self-Transcendence: Coherent Growth of Individuated Subsystems

This module formalizes the **dynamic** complement to individuation: a
subsystem that **grows** by absorbing new atoms while preserving the
coherence of its original identity.

A `TranscendenceStep` records:
- an old individuated subsystem with core Γ_old,
- a new individuated subsystem with core Γ_new ⊇ Γ_old,
- agreement on the old core's clauses,
- Dobrushin budget for both specs.

The preservation theorem says: queries on Γ_old have exactly the same
WM truth value before and after the growth step.

A `TranscendencePath` chains multiple steps.  The key invariant: queries
on the **original** core Γ₀ are preserved at every stage, no matter how
much the subsystem has grown.

This captures Weinbaum's "coherent navigation through transformation":
the system transcends its boundary while maintaining the coherence of
what came before.

**What this formalizes (static self-transcendence):**
The system's boundary EXPANDS.  Old clauses are preserved.  Old answers
are exactly invariant.

**What this does NOT formalize (dynamic self-transcendence):**
Old clauses being REWRITTEN (changing your mind).  This would give
approximate preservation (via boundary-stability decay), not exact.
That is future work — and connects to Goertzel's paraconsistent
p-bits and non-dual motivational architecture.

## References

- D. R. Weinbaum & V. Veitas, *Open-Ended Intelligence*, 2015.
- B. Goertzel, *Evolving Deeply Ethical and Joyously Conscious AGI
  Systems via Paraconsistency and Nonlinear Resonance*, 2026.
-/

namespace Mettapedia.Logic.MarkovLogicSelfTranscendence

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

-- ═══════════════════════════════════════════════════════════════════════════
-- TranscendenceStep: one step of coherent growth
-- ═══════════════════════════════════════════════════════════════════════════

/-- A **transcendence step** records the growth of an individuated subsystem:
    the core expands from Γ_old to Γ_new, the specification may change
    outside the old core, but old clauses are preserved and the Dobrushin
    budget holds throughout. -/
structure TranscendenceStep
    (M_old M_new : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  /-- The old individuated subsystem. -/
  old_subsystem : IndividuatedSubsystem M_old
  /-- The new individuated subsystem with a larger core. -/
  new_subsystem : IndividuatedSubsystem M_new
  /-- The core grew: old ⊆ new. -/
  core_growth : old_subsystem.core ⊆ new_subsystem.core
  /-- The specs agree on the old core's clauses. -/
  specs_agree : SpecAgreesOnRegion M_old M_new old_subsystem.core
  /-- The old core is still interaction-closed in the new spec.
      (The new spec didn't break the old boundary.) -/
  old_core_still_closed : InteractionClosed M_new old_subsystem.core
  /-- Dobrushin budget for the old spec. -/
  budget_old : M_old.PaperUniformSmallTotalInfluence
  /-- Dobrushin budget for the new spec. -/
  budget_new : M_new.PaperUniformSmallTotalInfluence

private theorem region_nonempty_of_regionSupport_mem
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Γ : Region Atom} {j : ClauseId}
    (hj : j ∈ M.regionSupport Γ) :
    Γ.Nonempty := by
  rcases M.regionSupport_sound hj with ⟨a, _, haΓ⟩
  exact ⟨a, haΓ⟩

private theorem classicalRegionSupport_mono
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ) :
    M.regionSupport Λ ⊆ M.regionSupport Δ := by
  intro j hj
  exact M.regionSupport_complete
    (clauseTouchesRegion_mono (C := M.clause j) hΛΔ (M.regionSupport_sound hj))

private theorem specAgreesOnRegion_restrict
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ Δ : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hΔΓ : Δ ⊆ Γ) :
    SpecAgreesOnRegion M₁ M₂ Δ := by
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hΛΔ hΛne
    exact hagree.regionSupport_eq Λ (fun a ha => hΔΓ (hΛΔ ha)) hΛne
  · intro j hj
    have hjΓ : j ∈ M₁.regionSupport Γ :=
      classicalRegionSupport_mono M₁ (Λ := Δ) (Δ := Γ) hΔΓ hj
    exact hagree.clause_eq j hjΓ
  · intro j hj
    have hjΓ : j ∈ M₁.regionSupport Γ :=
      classicalRegionSupport_mono M₁ (Λ := Δ) (Δ := Γ) hΔΓ hj
    exact hagree.logWeight_eq j hjΓ

private theorem specAgreesOnRegion_trans
    {M₀ M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : Region Atom}
    (h01 : SpecAgreesOnRegion M₀ M₁ Γ)
    (h12 : SpecAgreesOnRegion M₁ M₂ Γ) :
    SpecAgreesOnRegion M₀ M₂ Γ := by
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hΛ hΛne
    calc
      M₀.regionSupport Λ = M₁.regionSupport Λ := h01.regionSupport_eq Λ hΛ hΛne
      _ = M₂.regionSupport Λ := h12.regionSupport_eq Λ hΛ hΛne
  · intro j hj
    have hΓne : Γ.Nonempty := region_nonempty_of_regionSupport_mem M₀ hj
    have hj₁ : j ∈ M₁.regionSupport Γ := by
      simpa [h01.regionSupport_eq Γ (by intro a ha; exact ha) hΓne] using hj
    rw [h01.clause_eq j hj, h12.clause_eq j hj₁]
  · intro j hj
    have hΓne : Γ.Nonempty := region_nonempty_of_regionSupport_mem M₀ hj
    have hj₁ : j ∈ M₁.regionSupport Γ := by
      simpa [h01.regionSupport_eq Γ (by intro a ha; exact ha) hΓne] using hj
    rw [h01.logWeight_eq j hj, h12.logWeight_eq j hj₁]

private theorem interactionClosed_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed : InteractionClosed M₁ Γ) :
    InteractionClosed M₂ Γ := by
  intro a haΓ b hb
  rcases (M₂.mem_atomInteractionNeighborhood_iff a b).1 hb with ⟨j, hj₂, hba₂⟩
  have hsingleton_subset : ({a} : Region Atom) ⊆ Γ := by
    intro x hx
    have hx' : x = a := by simpa using hx
    subst hx'
    exact haΓ
  have hj₁ : j ∈ M₁.regionSupport ({a} : Region Atom) := by
    have hsupp :
        M₁.regionSupport ({a} : Region Atom) =
          M₂.regionSupport ({a} : Region Atom) :=
      hagree.regionSupport_eq ({a} : Region Atom) hsingleton_subset ⟨a, by simp⟩
    simpa [hsupp] using hj₂
  have hj₁Γ : j ∈ M₁.regionSupport Γ :=
    classicalRegionSupport_mono M₁ (Λ := ({a} : Region Atom)) (Δ := Γ) hsingleton_subset hj₁
  have hclause : M₁.clause j = M₂.clause j := hagree.clause_eq j hj₁Γ
  have hba₁ : b ∈ (M₁.clause j).atoms.erase a := by
    simpa [hclause] using hba₂
  have hb₁ : b ∈ M₁.atomInteractionNeighborhood a :=
    (M₁.mem_atomInteractionNeighborhood_iff a b).2 ⟨j, hj₁, hba₁⟩
  exact hclosed a haΓ hb₁

/-- **Preservation**: queries on the old core have exactly the same WM truth
    value before and after a transcendence step.

    The system grew — new atoms, new clauses, larger boundary — but the
    old core's answers are exactly preserved. -/
theorem TranscendenceStep.old_queries_preserved
    {M_old M_new : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : TranscendenceStep M_old M_new)
    (μ_old : ProbabilityMeasure (InfiniteWorld Atom))
    (μ_new : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ_old : FixedRegionCylinderDLR M_old.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ_old : Measure (InfiniteWorld Atom)))
    (hμ_new : FixedRegionCylinderDLR M_new.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ_new : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.old_subsystem.core) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M_old μ_old hμ_old} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M_new μ_new hμ_new} : MassState (ConstraintQuery Atom)) q := by
  simp only [queryStrength_singleton_eq_queryProb]
  exact queryProb_eq_of_specAgreesOnRegion
    step.specs_agree
    step.old_subsystem.interaction_closed
    step.old_core_still_closed
    step.budget_old step.budget_new
    μ_old μ_new hμ_old hμ_new q hq

-- ═══════════════════════════════════════════════════════════════════════════
-- TranscendencePath: a sequence of coherent growth steps
-- ═══════════════════════════════════════════════════════════════════════════

/-- A **transcendence path** is a finite sequence of growth steps.
    The key property: the ORIGINAL core's queries are preserved at every
    stage, no matter how far the subsystem has grown. -/
inductive TranscendencePath :
    ClassicalInfiniteGroundMLNSpec Atom ClauseId →
    ClassicalInfiniteGroundMLNSpec Atom ClauseId → Type _ where
  /-- A single coherent growth step. -/
  | single {M₀ M₁ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (first : TranscendenceStep M₀ M₁) :
      TranscendencePath M₀ M₁
  /-- Extend the path by one transcendence step. -/
  | step {M₀ M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (path : TranscendencePath M₀ M₁)
      (next : TranscendenceStep M₁ M₂) :
      TranscendencePath M₀ M₂

/-- The original core of a transcendence path: the core of the first
    subsystem in the sequence. -/
noncomputable def TranscendencePath.originalCore :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    TranscendencePath M₀ M_final → Region Atom
  | _, _, .single first => first.old_subsystem.core
  | _, _, .step path _ => path.originalCore

/-- A transcendence path is **coherent** when each new step still contains
    the original core inside its protected old subsystem.  This is the
    exact continuity condition needed for path-wise identity preservation. -/
def TranscendencePath.Coherent :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    TranscendencePath M₀ M_final → Prop
  | _, _, .single _ => True
  | _, _, .step path next =>
      path.Coherent ∧ path.originalCore ⊆ next.old_subsystem.core

private theorem TranscendencePath.invariants
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (path : TranscendencePath M₀ M_final)
    (hcoh : path.Coherent) :
    SpecAgreesOnRegion M₀ M_final path.originalCore ∧
      InteractionClosed M₀ path.originalCore ∧
      InteractionClosed M_final path.originalCore ∧
      M₀.PaperUniformSmallTotalInfluence ∧
      M_final.PaperUniformSmallTotalInfluence := by
  induction path with
  | single first =>
      simpa [TranscendencePath.originalCore] using
        (show SpecAgreesOnRegion _ _ first.old_subsystem.core ∧
            InteractionClosed _ first.old_subsystem.core ∧
            InteractionClosed _ first.old_subsystem.core ∧
            _ ∧ _ from
          ⟨first.specs_agree, first.old_subsystem.interaction_closed,
            first.old_core_still_closed, first.budget_old, first.budget_new⟩)
  | step path next ih =>
      have hcoh' : path.Coherent ∧ path.originalCore ⊆ next.old_subsystem.core := by
        simpa [TranscendencePath.Coherent] using hcoh
      rcases hcoh' with ⟨hcoh_path, hcarry⟩
      rcases ih hcoh_path with ⟨hagree₀₁, hclosed₀, hclosed₁, hbudget₀, _hbudget₁⟩
      have hrestrict : SpecAgreesOnRegion _ _ path.originalCore :=
        specAgreesOnRegion_restrict next.specs_agree hcarry
      have hagree₀₂ : SpecAgreesOnRegion _ _ path.originalCore :=
        specAgreesOnRegion_trans hagree₀₁ hrestrict
      have hclosed₂ : InteractionClosed _ path.originalCore :=
        interactionClosed_of_specAgreesOnRegion hrestrict hclosed₁
      simpa [TranscendencePath.originalCore] using
        (show SpecAgreesOnRegion _ _ path.originalCore ∧
            InteractionClosed _ path.originalCore ∧
            InteractionClosed _ path.originalCore ∧
            _ ∧ _ from
          ⟨hagree₀₂, hclosed₀, hclosed₂, hbudget₀, next.budget_new⟩)

/-- **Path preservation**: queries on the original core are preserved
    across the entire transcendence path.

    No matter how many growth steps the system has taken, its original
    identity (the truth values on the original core) is exactly maintained.

    This is Weinbaum's "coherent navigation through transformation"
    formalized: the system transcends its boundary while the coherence
    of what came before is exactly preserved. -/
theorem TranscendencePath.original_queries_stable
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (path : TranscendencePath M₀ M_final)
    (hcoh : path.Coherent)
    (μ₀ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ_final : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₀ : FixedRegionCylinderDLR M₀.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₀ : Measure (InfiniteWorld Atom)))
    (hμ_final : FixedRegionCylinderDLR M_final.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ_final : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalCore) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₀ μ₀ hμ₀} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M_final μ_final hμ_final} :
        MassState (ConstraintQuery Atom)) q := by
  rcases path.invariants hcoh with
    ⟨hagree, hclosed₀, hclosed_final, hbudget₀, hbudget_final⟩
  simp only [queryStrength_singleton_eq_queryProb]
  exact queryProb_eq_of_specAgreesOnRegion
    hagree hclosed₀ hclosed_final hbudget₀ hbudget_final
    μ₀ μ_final hμ₀ hμ_final q hq

end Mettapedia.Logic.MarkovLogicSelfTranscendence
