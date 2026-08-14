import Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout
import Mettapedia.PLN.Bridges.HOL.PLNHeytingHOLWorldModelBridge
import Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope

/-!
# Tree-witness introspection for HOL/PLN bridges

This module exposes a query interface over the existing
`ClosedTheorySet.TreeWitness` carrier.  The interface keeps source provenance,
numeric exactness needs, and cost readouts separate while reusing the already
proved provenance, BinaryEvidence, estimator-envelope, and Heyting readout
interfaces.
-/

namespace Mettapedia.PLN.Bridges.HOL.Introspection

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Bridges.HOL.HeytingWorldModel
open Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open scoped ENNReal

noncomputable section

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The introspection query handle is exactly the existing tree witness. -/
abbrev IntrospectionQuery (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :=
  ClosedTheorySet.TreeWitness (Const := Const) T φ

/-- A concrete witness exists exactly when the formula is derivable. -/
theorem treeWitness_nonempty_iff_provable
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const} :
    Nonempty (IntrospectionQuery (Const := Const) T φ) ↔
      ClosedTheorySet.Provable (Const := Const) T φ := by
  constructor
  · rintro ⟨w⟩
    exact w.provable
  · rintro ⟨Γ, hΓ, hDer⟩
    rcases DerivationTree.nonempty_of_extDerivation (Const := Const) hDer with ⟨d⟩
    exact ⟨⟨Γ, hΓ, d⟩⟩

/-- Source-provenance readout for a concrete tree witness. -/
def why {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    Set (DerivationTree.SourceToken (Base := Base) Const) :=
  w.tree.sourceSupport

/-- Source tokens whose removal could matter for this witness. -/
def sourceBreaks {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    Set (DerivationTree.SourceToken (Base := Base) Const) :=
  w.tree.sourceSupport

@[simp] theorem sourceBreaks_eq_why
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    sourceBreaks (Const := Const) w = why (Const := Const) w :=
  rfl

theorem sourceBreaks_mem_sourceIdeal
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    sourceBreaks (Const := Const) w ∈
      ClosedTheorySet.sourceIdeal (Const := Const) T φ :=
  ⟨w, fun _ hs => hs⟩

/-- BinaryEvidence readout for a concrete witness, with the payload explicit. -/
def howEvidence {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (payload : DerivationTree.GradePayload Const BinaryEvidence)
    (w : IntrospectionQuery (Const := Const) T φ) : BinaryEvidence :=
  DerivationTree.gradeWith payload w.tree

/-- Strength view of an explicit BinaryEvidence payload. -/
def howStrongly {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (payload : DerivationTree.GradePayload Const BinaryEvidence)
    (w : IntrospectionQuery (Const := Const) T φ) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (howEvidence (Const := Const) payload w)

/-- Named count-payload strength view; intentionally not the silent default. -/
def howStronglyCount {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) : ℝ≥0∞ :=
  howStrongly (Const := Const)
    (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.countPayload (Const := Const)) w

theorem howEvidence_count_eq_evGrade
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    howEvidence (Const := Const)
        (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.countPayload (Const := Const)) w =
      Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.evGrade w.tree := by
  simp [howEvidence,
    Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.gradeWith_countPayload_eq_evGrade]

/-- The count payload is a lossy point-strength view: any concrete tree reads as 1. -/
theorem howStronglyCount_eq_one
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    howStronglyCount (Const := Const) w = 1 := by
  simp [howStronglyCount, howStrongly, howEvidence,
    Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.gradeWith_countPayload_eq_evGrade]

/-- The count payload inherits the already proved count/evidence identity. -/
theorem howEvidence_count_symm
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.evGrade w.tree =
      howEvidence (Const := Const)
        (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.countPayload (Const := Const)) w :=
  (howEvidence_count_eq_evGrade (Const := Const) w).symm

/-- A formula remains tree-provable while avoiding a source token when some
existing witness avoids that token. -/
def TreeProvableAvoiding (T : ClosedTheorySet Const) (φ : ClosedFormula Const)
    (s : DerivationTree.SourceToken (Base := Base) Const) : Prop :=
  ∃ w : IntrospectionQuery (Const := Const) T φ,
    s ∉ sourceBreaks (Const := Const) w

theorem treeProvableAvoiding_of_witness
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (w : IntrospectionQuery (Const := Const) T φ)
    (hs : s ∉ sourceBreaks (Const := Const) w) :
    TreeProvableAvoiding (Const := Const) T φ s :=
  ⟨w, hs⟩

/-- Source retraction kills derivability only when every witness uses that source. -/
theorem source_retraction_kills_when_no_source_free_witness
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (hLast :
      ∀ w : IntrospectionQuery (Const := Const) T φ,
        s ∈ sourceBreaks (Const := Const) w) :
    ¬ TreeProvableAvoiding (Const := Const) T φ s := by
  rintro ⟨w, hsFree⟩
  exact hsFree (hLast w)

/-- Data saying that a source is present in every concrete witness, together with
one witness showing that the formula is currently derivable. -/
structure EssentialSource (T : ClosedTheorySet Const) (φ : ClosedFormula Const)
    (s : DerivationTree.SourceToken (Base := Base) Const) where
  witness : IntrospectionQuery (Const := Const) T φ
  all_witnesses_use :
    ∀ w : IntrospectionQuery (Const := Const) T φ,
      s ∈ sourceBreaks (Const := Const) w

theorem essentialSource_not_treeProvableAvoiding
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (e : EssentialSource (Const := Const) T φ s) :
    ¬ TreeProvableAvoiding (Const := Const) T φ s :=
  source_retraction_kills_when_no_source_free_witness (Const := Const)
    e.all_witnesses_use

theorem essentialSource_positive_negative_example
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (e : EssentialSource (Const := Const) T φ s) :
    sourceBreaks (Const := Const) e.witness ∈
        ClosedTheorySet.sourceIdeal (Const := Const) T φ ∧
      ¬ TreeProvableAvoiding (Const := Const) T φ s :=
  ⟨sourceBreaks_mem_sourceIdeal (Const := Const) e.witness,
    essentialSource_not_treeProvableAvoiding (Const := Const) e⟩

/-- Numeric side conditions needed for the deduction point formula to sit in the
certified credal interval. -/
structure DeductionExactnessNeeds (pA pB pC sAB sBC : ℝ) where
  hpA : 0 < pA
  hpB_small : pB ≤ 0.99
  feasibility : DeductionBranchFeasibility pA pB pC sAB sBC
  consistency :
    conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC
  inB_lower :
    deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC
  inB_upper :
    pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC
  outNotB_lower :
    deductionNotBBranchLower pA pB pC sAB sBC ≤
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC
  outNotB_upper :
    pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
      deductionNotBBranchUpper pA pB pC sAB sBC

/-- Numeric exactness breakpoints are the explicit side-condition bundle. -/
def exactnessBreaks {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    DeductionExactnessNeeds pA pB pC sAB sBC :=
  needs

theorem exactnessBreaks_pointFormula_mem_interval
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC needs.hpA
        needs.feasibility credibility hc
    itv.lower ≤ simpleDeductionStrengthFormula pA pB pC sAB sBC ∧
      simpleDeductionStrengthFormula pA pB pC sAB sBC ≤ itv.upper := by
  exact simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV
    pA pB pC sAB sBC needs.hpA needs.hpB_small needs.feasibility
    needs.consistency needs.inB_lower needs.inB_upper needs.outNotB_lower
    needs.outNotB_upper credibility hc

theorem exactnessBreaks_selectedDeduction_mem_interval
    (sideEvidence : BinaryEvidence)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC needs.hpA
        needs.feasibility credibility hc
    itv.lower ≤
        evidenceSelectedDeductionStrength sideEvidence pA pB pC sAB sBC
          needs.hpA needs.feasibility credibility hc ∧
      evidenceSelectedDeductionStrength sideEvidence pA pB pC sAB sBC
          needs.hpA needs.feasibility credibility hc ≤ itv.upper := by
  exact evidenceSelectedDeductionStrength_mem_deductionCredalStrengthITV
    sideEvidence pA pB pC sAB sBC needs.hpA needs.hpB_small
    needs.feasibility needs.consistency needs.inB_lower needs.inB_upper
    needs.outNotB_lower needs.outNotB_upper credibility hc

theorem exactnessBreaks_treeGrade_mem_interval
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (payload : DerivationTree.GradePayload Const BinaryEvidence)
    (w : IntrospectionQuery (Const := Const) T φ)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC needs.hpA
        needs.feasibility credibility hc
    itv.lower ≤
        evidenceSelectedDeductionStrength (howEvidence (Const := Const) payload w)
          pA pB pC sAB sBC needs.hpA needs.feasibility credibility hc ∧
      evidenceSelectedDeductionStrength (howEvidence (Const := Const) payload w)
          pA pB pC sAB sBC needs.hpA needs.feasibility credibility hc ≤
        itv.upper := by
  simpa [howEvidence] using
    gradeWithSelectedDeductionStrength_mem_deductionCredalStrengthITV
      payload w.tree pA pB pC sAB sBC needs.hpA needs.hpB_small
      needs.feasibility needs.consistency needs.inB_lower needs.inB_upper
      needs.outNotB_lower needs.outNotB_upper credibility hc

theorem exactnessBreaks_crisp_one_eq_formula
    (sideEvidence : BinaryEvidence)
    (hcrisp : (BinaryEvidence.toStrength sideEvidence).toReal = 1)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    evidenceSelectedDeductionStrength sideEvidence pA pB pC sAB sBC
        needs.hpA needs.feasibility credibility hc =
      simpleDeductionStrengthFormula pA pB pC sAB sBC :=
  evidenceSelectedDeductionStrength_crisp_one_eq_formula
    sideEvidence hcrisp pA pB pC sAB sBC needs.hpA needs.feasibility
    credibility hc

/-- The top-level `whatBreaks` query keeps source retraction data and numeric
exactness data in separate fields. -/
structure WhatBreaks (T : ClosedTheorySet Const) (φ : ClosedFormula Const)
    (pA pB pC sAB sBC : ℝ) where
  sourceTokens : Set (DerivationTree.SourceToken (Base := Base) Const)
  exactnessNeeds : DeductionExactnessNeeds pA pB pC sAB sBC

/-- Combined query interface for "what would break this answer", while preserving
the two governed components as distinct fields. -/
def whatBreaks {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    WhatBreaks (Const := Const) T φ pA pB pC sAB sBC where
  sourceTokens := sourceBreaks (Const := Const) w
  exactnessNeeds := exactnessBreaks needs

@[simp] theorem whatBreaks_sourceTokens
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    (whatBreaks (Const := Const) w needs).sourceTokens =
      sourceBreaks (Const := Const) w :=
  rfl

@[simp] theorem whatBreaks_exactnessNeeds
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    (whatBreaks (Const := Const) w needs).exactnessNeeds =
      exactnessBreaks needs :=
  rfl

theorem whatBreaks_source_mem_sourceIdeal
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    (whatBreaks (Const := Const) w needs).sourceTokens ∈
      ClosedTheorySet.sourceIdeal (Const := Const) T φ :=
  sourceBreaks_mem_sourceIdeal (Const := Const) w

theorem whatBreaks_retraction_kills_when_no_source_free_witness
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC)
    (hLast :
      ∀ w : IntrospectionQuery (Const := Const) T φ,
        s ∈ (whatBreaks (Const := Const) w needs).sourceTokens) :
    ¬ TreeProvableAvoiding (Const := Const) T φ s :=
  source_retraction_kills_when_no_source_free_witness (Const := Const)
    (fun w => by simpa using hLast w)

theorem whatBreaks_exactness_pointFormula_mem_interval
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let breaks := whatBreaks (Const := Const) w needs
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC
        breaks.exactnessNeeds.hpA breaks.exactnessNeeds.feasibility
        credibility hc
    itv.lower ≤ simpleDeductionStrengthFormula pA pB pC sAB sBC ∧
      simpleDeductionStrengthFormula pA pB pC sAB sBC ≤ itv.upper := by
  dsimp [whatBreaks, exactnessBreaks]
  exact exactnessBreaks_pointFormula_mem_interval needs credibility hc

theorem whatBreaks_negative_example
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (e : EssentialSource (Const := Const) T φ s)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    let breaks := whatBreaks (Const := Const) e.witness needs
    breaks.sourceTokens ∈ ClosedTheorySet.sourceIdeal (Const := Const) T φ ∧
      ¬ TreeProvableAvoiding (Const := Const) T φ s := by
  dsimp [whatBreaks]
  exact ⟨sourceBreaks_mem_sourceIdeal (Const := Const) e.witness,
    essentialSource_not_treeProvableAvoiding (Const := Const) e⟩

/-- Exact Nat cost of the witness tree. -/
def proofCost {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) : Nat :=
  w.tree.evalNat

/-- Cost accessor used by `worthReDeriving`. -/
def worthCost {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) : Nat :=
  proofCost (Const := Const) w

theorem proofCost_mem_costSpectrum
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    proofCost (Const := Const) w ∈
      ClosedTheorySet.costSpectrum (Const := Const) T φ :=
  ⟨w, rfl⟩

theorem proofCost_mem_costUpperBounds
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    proofCost (Const := Const) w ∈
      ClosedTheorySet.costUpperBounds (Const := Const) T φ :=
  ⟨w, le_rfl⟩

theorem worthCost_mem_costSpectrum
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    worthCost (Const := Const) w ∈
      ClosedTheorySet.costSpectrum (Const := Const) T φ :=
  proofCost_mem_costSpectrum (Const := Const) w

theorem worthCost_mem_costUpperBounds
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (w : IntrospectionQuery (Const := Const) T φ) :
    worthCost (Const := Const) w ∈
      ClosedTheorySet.costUpperBounds (Const := Const) T φ :=
  proofCost_mem_costUpperBounds (Const := Const) w

/-- Policy layer for asking whether a stale proof is cheap enough to revisit. -/
structure ReDerivationPolicy (T : ClosedTheorySet Const)
    (φ : ClosedFormula Const) where
  stale : IntrospectionQuery (Const := Const) T φ → Prop
  threshold : Nat

/-- Re-derivation is worthwhile when the witness is stale and within budget. -/
def worthReDeriving {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (policy : ReDerivationPolicy (Const := Const) T φ)
    (w : IntrospectionQuery (Const := Const) T φ) : Prop :=
  policy.stale w ∧ worthCost (Const := Const) w ≤ policy.threshold

theorem worthReDeriving_threshold_is_cost_upper_bound
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (policy : ReDerivationPolicy (Const := Const) T φ)
    (w : IntrospectionQuery (Const := Const) T φ)
    (h : worthReDeriving (Const := Const) policy w) :
    policy.threshold ∈ ClosedTheorySet.costUpperBounds (Const := Const) T φ :=
  ⟨w, h.2⟩

theorem worthReDeriving_budget_mem_costUpperBounds
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (policy : ReDerivationPolicy (Const := Const) T φ)
    (w : IntrospectionQuery (Const := Const) T φ)
    (h : worthReDeriving (Const := Const) policy w) :
    policy.threshold ∈ ClosedTheorySet.costUpperBounds (Const := Const) T φ :=
  worthReDeriving_threshold_is_cost_upper_bound (Const := Const) policy w h

theorem proofCostSpectrum_mono_derivability
    {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (hImp : ClosedTheorySet.Provable (Const := Const) T (.imp φ ψ)) :
    ∀ {n}, n ∈ ClosedTheorySet.costSpectrum (Const := Const) T φ →
      ∃ m, m ∈ ClosedTheorySet.costSpectrum (Const := Const) T ψ ∧ n ≤ m :=
  ClosedTheorySet.costSpectrum_mono_derivability (Const := Const) hImp

theorem proofCostUpperBounds_imp_slack
    {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (hImp : IntrospectionQuery (Const := Const) T (.imp φ ψ))
    {n : Nat} (hn : n ∈ ClosedTheorySet.costUpperBounds (Const := Const) T φ) :
    (1 + hImp.tree.evalNat + n) ∈
      ClosedTheorySet.costUpperBounds (Const := Const) T ψ :=
  ClosedTheorySet.costUpperBounds_imp_slack (Const := Const) hImp hn

/-- Order-faithful strength comparison from the existing Heyting separating
family.  This is the semantically meaningful strength order, unlike the lossy
point value produced by the count payload. -/
theorem orderFaithfulStrengthComparison
    {T : ClosedTheorySet (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (φ ψ : ClosedFormula (WithParams Const)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) ↔
      ∀ S,
        (heytingCrispSeparatingReadouts (Base := Base) (Const := Const)
          T hT0).mu S φ ≤
        (heytingCrispSeparatingReadouts (Base := Base) (Const := Const)
          T hT0).mu S ψ := by
  let R := heytingCrispSeparatingReadouts (Base := Base) (Const := Const) T hT0
  constructor
  · intro h S
    exact R.monotone S h
  · intro h
    exact R.separates h

/-- Crown theorem: witness existence matches derivability, readout strength order
is separated by the Heyting family, source retraction has the correct
every-witness condition, and cost reads from the existing cost spectrum. -/
theorem introspection_faithful
    {T : ClosedTheorySet (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    (∀ φ : ClosedFormula (WithParams Const),
        Nonempty (IntrospectionQuery (Const := WithParams Const) T φ) ↔
          ClosedTheorySet.Provable (Const := WithParams Const) T φ) ∧
      (∀ φ ψ : ClosedFormula (WithParams Const),
        ClosedTheorySet.Provable (Const := WithParams Const) T (.imp φ ψ) ↔
          ∀ S,
            (heytingCrispSeparatingReadouts (Base := Base) (Const := Const)
              T hT0).mu S φ ≤
            (heytingCrispSeparatingReadouts (Base := Base) (Const := Const)
              T hT0).mu S ψ) ∧
      (∀ (φ : ClosedFormula (WithParams Const))
          (s : DerivationTree.SourceToken (Base := Base) (WithParams Const)),
        (∀ w : IntrospectionQuery (Const := WithParams Const) T φ,
          s ∈ sourceBreaks (Const := WithParams Const) w) →
        ¬ TreeProvableAvoiding (Const := WithParams Const) T φ s) ∧
      (∀ (φ : ClosedFormula (WithParams Const))
          (w : IntrospectionQuery (Const := WithParams Const) T φ),
        worthCost (Const := WithParams Const) w ∈
          ClosedTheorySet.costSpectrum (Const := WithParams Const) T φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ
    exact treeWitness_nonempty_iff_provable (Const := WithParams Const)
  · intro φ ψ
    exact orderFaithfulStrengthComparison (Base := Base) (Const := Const) hT0 φ ψ
  · intro φ s hLast
    exact source_retraction_kills_when_no_source_free_witness
      (Const := WithParams Const) hLast
  · intro φ w
    exact worthCost_mem_costSpectrum (Const := WithParams Const) w

/-- Positive example: the short and long `top ∧ top` witnesses both populate the
existing cost spectrum, and the count-payload strength reads as the lossy value 1. -/
theorem topAndTop_positive_example (T : ClosedTheorySet Const) :
    let claim : ClosedFormula Const :=
      .and (.top : ClosedFormula Const) (.top : ClosedFormula Const)
    let w := ClosedTheorySet.topAndTopWitness (Const := Const) T
    sourceBreaks (Const := Const) w ∈
        ClosedTheorySet.sourceIdeal (Const := Const) T claim ∧
      howStronglyCount (Const := Const) w = 1 ∧
      worthCost (Const := Const) w = 3 ∧
      3 ∈ ClosedTheorySet.costSpectrum (Const := Const) T claim ∧
      6 ∈ ClosedTheorySet.costSpectrum (Const := Const) T claim := by
  dsimp
  refine ⟨sourceBreaks_mem_sourceIdeal (Const := Const)
      (ClosedTheorySet.topAndTopWitness (Const := Const) T), ?_, ?_, ?_, ?_⟩
  · exact howStronglyCount_eq_one (Const := Const)
      (ClosedTheorySet.topAndTopWitness (Const := Const) T)
  · simp [worthCost, proofCost, ClosedTheorySet.topAndTopWitness]
  · exact ClosedTheorySet.costSpectrum_topAndTop_contains_three (Const := Const) T
  · exact ClosedTheorySet.costSpectrum_topAndTop_contains_six (Const := Const) T

#print axioms introspection_faithful

end

end Mettapedia.PLN.Bridges.HOL.Introspection
