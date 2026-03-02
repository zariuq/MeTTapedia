import Mettapedia.Logic.GovernanceReasoning.TreatyKernelAcceptance

/-!
# Governance Acceptance Preorders

Acceptance policies should not be monotone over raw coordinatewise evidence order
(`pos` up and `neg` up), because that can force pathological acceptance behavior.

This module introduces:

- A **quality preorder** (`EvidenceQualityLE`) where better evidence means
  more positive support and no more negative support.
- A monotone-policy schema over that preorder.
- Provenance-aware admitted-trace filtering over assessed treaty events.
- Soundness lemmas connecting admitted events to admitted traces.
-/

namespace Mettapedia.Logic.GovernanceReasoning.AcceptancePreorder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.GovernanceReasoning.TreatyKernel
open Mettapedia.Logic.GovernanceReasoning.TreatyKernelAcceptance
open scoped ENNReal

/-! ## Evidence quality preorder -/

/-- Quality preorder on evidence:
`e₂` is at least as good as `e₁` if it has at least as much positive evidence and
no more negative evidence. -/
def EvidenceQualityLE (e₁ e₂ : Evidence) : Prop :=
  e₁.pos ≤ e₂.pos ∧ e₂.neg ≤ e₁.neg

theorem EvidenceQualityLE.refl (e : Evidence) : EvidenceQualityLE e e := by
  exact ⟨le_rfl, le_rfl⟩

theorem EvidenceQualityLE.trans {e₁ e₂ e₃ : Evidence}
    (h12 : EvidenceQualityLE e₁ e₂) (h23 : EvidenceQualityLE e₂ e₃) :
    EvidenceQualityLE e₁ e₃ := by
  exact ⟨le_trans h12.1 h23.1, le_trans h23.2 h12.2⟩

/-! ## Monotone acceptance over quality preorder -/

/-- Acceptance policy monotone in the quality preorder. -/
structure QualityMonotoneAcceptancePolicy where
  accepts : Evidence → Prop
  mono : ∀ {e₁ e₂}, EvidenceQualityLE e₁ e₂ → accepts e₁ → accepts e₂

/-- Rectangular acceptance in `(pos, neg)` coordinates:
minimum positive support and maximum tolerated negative support. -/
def rectangularAccept (posMin negMax : ℝ≥0∞) (e : Evidence) : Prop :=
  posMin ≤ e.pos ∧ e.neg ≤ negMax

theorem rectangularAccept_mono {posMin negMax : ℝ≥0∞} {e₁ e₂ : Evidence}
    (hLE : EvidenceQualityLE e₁ e₂)
    (hAcc : rectangularAccept posMin negMax e₁) :
    rectangularAccept posMin negMax e₂ := by
  exact ⟨le_trans hAcc.1 hLE.1, le_trans hLE.2 hAcc.2⟩

/-- Canonical rectangular policy as a quality-monotone acceptance policy. -/
def rectangularPolicy (posMin negMax : ℝ≥0∞) : QualityMonotoneAcceptancePolicy where
  accepts := rectangularAccept posMin negMax
  mono := by
    intro e₁ e₂ hLE hAcc
    exact rectangularAccept_mono hLE hAcc

/-! ## Provenance-aware acceptance for assessed treaty events -/

/-- Prop-level provenance-aware rectangular acceptance:
trusted source, enough positive evidence, and bounded negative evidence. -/
def provenanceRectangularAccepts
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    (ae : AssessedTreatyEvent Entity Pred Time Party) : Prop :=
  trusted ae.base.attestedBy = true ∧ posMin ≤ ae.ev.pos ∧ ae.ev.neg ≤ negMax

/-- Bool-level form of provenance-aware rectangular acceptance (for trace filtering). -/
noncomputable def provenanceRectangularAcceptsB
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    (ae : AssessedTreatyEvent Entity Pred Time Party) : Bool :=
  trusted ae.base.attestedBy &&
    decide (posMin ≤ ae.ev.pos) &&
    decide (ae.ev.neg ≤ negMax)

theorem provenanceRectangularAcceptsB_iff
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    (ae : AssessedTreatyEvent Entity Pred Time Party) :
    provenanceRectangularAcceptsB trusted posMin negMax ae = true ↔
      provenanceRectangularAccepts trusted posMin negMax ae := by
  simp [provenanceRectangularAcceptsB, provenanceRectangularAccepts, and_assoc]

/-- Filter assessed events by provenance-aware acceptance and project to treaty events. -/
noncomputable def admittedBaseTraceBy
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    (xs : List (AssessedTreatyEvent Entity Pred Time Party)) :
    TreatyTrace Entity Pred Time Party :=
  (xs.filter (fun ae => provenanceRectangularAcceptsB trusted posMin negMax ae))
    |>.map AssessedTreatyEvent.base

theorem admittedBaseTraceBy_subset_raw
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    (xs : List (AssessedTreatyEvent Entity Pred Time Party))
    {te : TreatyEvent Entity Pred Time Party}
    (hmem : te ∈ admittedBaseTraceBy trusted posMin negMax xs) :
    te ∈ xs.map AssessedTreatyEvent.base := by
  unfold admittedBaseTraceBy at hmem
  apply List.mem_map.mp hmem |>.elim
  intro ae hae
  refine List.mem_map.mpr ?_
  exact ⟨ae, (List.mem_filter.mp hae.1).1, hae.2⟩

theorem admitted_event_sound_by
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    {xs : List (AssessedTreatyEvent Entity Pred Time Party)}
    {ae : AssessedTreatyEvent Entity Pred Time Party}
    (hmem : ae ∈ xs)
    (hacc : provenanceRectangularAcceptsB trusted posMin negMax ae = true) :
    ae.base ∈ admittedBaseTraceBy trusted posMin negMax xs := by
  unfold admittedBaseTraceBy
  apply List.mem_map.mpr
  exact ⟨ae, List.mem_filter.mpr ⟨hmem, hacc⟩, rfl⟩

theorem admitted_implies_trusted
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    {ae : AssessedTreatyEvent Entity Pred Time Party}
    (hacc : provenanceRectangularAcceptsB trusted posMin negMax ae = true) :
    trusted ae.base.attestedBy = true := by
  have hProp := (provenanceRectangularAcceptsB_iff trusted posMin negMax ae).1 hacc
  exact hProp.1

theorem not_admitted_of_untrusted
    {Entity Pred Time Party : Type*}
    (trusted : Party → Bool)
    (posMin negMax : ℝ≥0∞)
    {ae : AssessedTreatyEvent Entity Pred Time Party}
    (huntrusted : trusted ae.base.attestedBy = false) :
    provenanceRectangularAcceptsB trusted posMin negMax ae = false := by
  simp [provenanceRectangularAcceptsB, huntrusted]

end Mettapedia.Logic.GovernanceReasoning.AcceptancePreorder
