import Mettapedia.Logic.PLNWorldModelKripkeWeighted

/-!
# Weighted Kripke WM Provenance-Overlap Layer

This module adds a separation-style compatibility layer over weighted/source-aware
Kripke WM states:

* compatibility = no source-label overlap,
* partial revision = additive merge only when compatible,
* fallback revision = left-biased state when incompatible.

It proves:

* a source-level no-double-count theorem under compatibility,
* recovery of additive weighted evidence when states are disjoint,
* lifted consequence/trusted-gate theorem wrappers through fallback revision.
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlap

open LO
open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelKripkeWeighted
open scoped ENNReal

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelKripkeWeighted.ModalQuery
abbrev PointedKripke := Mettapedia.Logic.PLNWorldModelKripkeWeighted.PointedKripke
abbrev WeightedSourcePointedKripke :=
  Mettapedia.Logic.PLNWorldModelKripkeWeighted.WeightedSourcePointedKripke
abbrev WeightedState := Mettapedia.Logic.PLNWorldModelKripkeWeighted.WeightedState

/-- Source-level provenance membership in a weighted state. -/
def sourceInState (s : String) (W : WeightedState) : Prop :=
  ∃ wp ∈ W, wp.source = s

/-- Separation-style source compatibility:
no provenance source appears in both states. -/
def compatible (W₁ W₂ : WeightedState) : Prop :=
  ∀ s : String, sourceInState s W₁ → sourceInState s W₂ → False

theorem compatible_symm {W₁ W₂ : WeightedState} :
    compatible W₁ W₂ → compatible W₂ W₁ := by
  intro h s hs₂ hs₁
  exact h s hs₁ hs₂

theorem sourceInState_add {s : String} {W₁ W₂ : WeightedState} :
    sourceInState s (W₁ + W₂) ↔ sourceInState s W₁ ∨ sourceInState s W₂ := by
  constructor
  · intro h
    rcases h with ⟨wp, hmem, hsrc⟩
    rcases Multiset.mem_add.mp hmem with hmem₁ | hmem₂
    · exact Or.inl ⟨wp, hmem₁, hsrc⟩
    · exact Or.inr ⟨wp, hmem₂, hsrc⟩
  · intro h
    rcases h with h₁ | h₂
    · rcases h₁ with ⟨wp, hmem, hsrc⟩
      exact ⟨wp, Multiset.mem_add.mpr (Or.inl hmem), hsrc⟩
    · rcases h₂ with ⟨wp, hmem, hsrc⟩
      exact ⟨wp, Multiset.mem_add.mpr (Or.inr hmem), hsrc⟩

/-- Count of weighted-state entries carrying a specific provenance source. -/
def sourceCount (s : String) (W : WeightedState) : Nat :=
  Multiset.countP (fun wp : WeightedSourcePointedKripke => wp.source = s) W

theorem sourceCount_add (s : String) (W₁ W₂ : WeightedState) :
    sourceCount s (W₁ + W₂) = sourceCount s W₁ + sourceCount s W₂ := by
  simp [sourceCount, Multiset.countP_add]

theorem sourceInState_iff_sourceCount_pos (s : String) (W : WeightedState) :
    sourceInState s W ↔ 0 < sourceCount s W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp [sourceInState, sourceCount]
  | @cons wp W ih =>
      by_cases hsrc : wp.source = s
      · constructor
        · intro _h
          simp [sourceCount, hsrc, Multiset.countP_cons_of_pos]
        · intro _h
          exact ⟨wp, by simp, hsrc⟩
      · constructor
        · intro h
          rcases h with ⟨wp', hmem, hsrc'⟩
          have hneq : wp' ≠ wp := by
            intro heq
            subst heq
            exact hsrc (by simpa using hsrc')
          have hmemW : wp' ∈ W := by
            simpa [hneq] using hmem
          have hposW : 0 < sourceCount s W := (ih.mp ⟨wp', hmemW, hsrc'⟩)
          simpa [sourceCount, hsrc, Multiset.countP_cons_of_neg] using hposW
        · intro hpos
          have hposW : 0 < sourceCount s W := by
            simpa [sourceCount, hsrc, Multiset.countP_cons_of_neg] using hpos
          rcases ih.mpr hposW with ⟨wp', hmemW, hsrc'⟩
          exact ⟨wp', by simp [hmemW], hsrc'⟩

theorem sourceCount_eq_zero_iff_not_sourceInState (s : String) (W : WeightedState) :
    sourceCount s W = 0 ↔ ¬ sourceInState s W := by
  constructor
  · intro hzero hsrc
    have hnotPos : ¬ 0 < sourceCount s W := by simp [hzero]
    exact hnotPos ((sourceInState_iff_sourceCount_pos s W).1 hsrc)
  · intro hnot
    by_cases hzero : sourceCount s W = 0
    · exact hzero
    · have hpos : 0 < sourceCount s W := Nat.pos_of_ne_zero hzero
      exact False.elim (hnot ((sourceInState_iff_sourceCount_pos s W).2 hpos))

theorem sourceCount_zero_right_of_compatible
    {W₁ W₂ : WeightedState} {s : String}
    (hcompat : compatible W₁ W₂)
    (hleft : sourceInState s W₁) :
    sourceCount s W₂ = 0 := by
  apply (sourceCount_eq_zero_iff_not_sourceInState s W₂).2
  intro hright
  exact hcompat s hleft hright

theorem sourceCount_zero_left_of_compatible
    {W₁ W₂ : WeightedState} {s : String}
    (hcompat : compatible W₁ W₂)
    (hright : sourceInState s W₂) :
    sourceCount s W₁ = 0 := by
  exact sourceCount_zero_right_of_compatible (W₁ := W₂) (W₂ := W₁)
    (s := s) (compatible_symm hcompat) hright

/-- No-double-count theorem:
under source compatibility, for each source at least one side contributes zero
occurrences. -/
theorem no_double_count_source_of_compatible
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂)
    (s : String) :
    sourceCount s W₁ = 0 ∨ sourceCount s W₂ = 0 := by
  by_cases hleft : sourceInState s W₁
  · exact Or.inr (sourceCount_zero_right_of_compatible (hcompat := hcompat) (hleft := hleft))
  · exact Or.inl ((sourceCount_eq_zero_iff_not_sourceInState s W₁).2 hleft)

/-- Source-count decomposition plus no-double-count witness. -/
theorem sourceCount_add_no_double_count_of_compatible
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂)
    (s : String) :
    sourceCount s (W₁ + W₂) = sourceCount s W₁ + sourceCount s W₂ ∧
      (sourceCount s W₁ = 0 ∨ sourceCount s W₂ = 0) := by
  constructor
  · exact sourceCount_add s W₁ W₂
  · exact no_double_count_source_of_compatible hcompat s

/-! ## Approx-safe forgetting under compatibility -/

/-- Forget/drop all entries whose source satisfies `drop`. -/
def forgetSources (drop : String → Prop) [DecidablePred drop]
    (W : WeightedState) : WeightedState :=
  W.filter (fun wp => ¬ drop wp.source)

theorem sourceInState_forgetSources_iff
    (drop : String → Prop) [DecidablePred drop]
    (s : String) (W : WeightedState) :
    sourceInState s (forgetSources drop W) ↔
      sourceInState s W ∧ ¬ drop s := by
  constructor
  · intro h
    rcases h with ⟨wp, hmemF, hsrc⟩
    rcases Multiset.mem_filter.mp hmemF with ⟨hmem, hkeep⟩
    refine ⟨⟨wp, hmem, hsrc⟩, ?_⟩
    simpa [hsrc] using hkeep
  · intro h
    rcases h with ⟨hsrcW, hkeep⟩
    rcases hsrcW with ⟨wp, hmem, hsrc⟩
    refine ⟨wp, ?_, hsrc⟩
    exact Multiset.mem_filter.mpr ⟨hmem, by simpa [hsrc] using hkeep⟩

theorem compatible_left_forgetSources_right
    (drop : String → Prop) [DecidablePred drop]
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂) :
    compatible W₁ (forgetSources drop W₂) := by
  intro s hsL hsR
  have hsR' : sourceInState s W₂ :=
    (sourceInState_forgetSources_iff drop s W₂).1 hsR |>.1
  exact hcompat s hsL hsR'

theorem no_double_count_source_of_compatible_forget_right
    (drop : String → Prop) [DecidablePred drop]
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂)
    (s : String) :
    sourceCount s W₁ = 0 ∨ sourceCount s (forgetSources drop W₂) = 0 := by
  exact
    no_double_count_source_of_compatible
      (hcompat := compatible_left_forgetSources_right drop hcompat) s

/-- Approx-safe forgetting keeps the explicit no-double-count condition on the
forgotten right branch. -/
theorem approx_safe_forgetting_no_double_count_condition
    (drop : String → Prop) [DecidablePred drop]
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂)
    (s : String) :
    sourceCount s W₁ = 0 ∨ sourceCount s (forgetSources drop W₂) = 0 := by
  exact no_double_count_source_of_compatible_forget_right drop hcompat s

/-- Partial provenance-aware revision:
merge additively only when source-compatible. -/
noncomputable def partialRevision (W₁ W₂ : WeightedState) : Option WeightedState := by
  classical
  exact if h : compatible W₁ W₂ then some (W₁ + W₂) else none

/-- Left-biased fallback policy for partial revision. -/
noncomputable def fallbackRevision (W₁ W₂ : WeightedState) : WeightedState :=
  (partialRevision W₁ W₂).getD W₁

theorem partialRevision_eq_some_add_of_compatible
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂) :
    partialRevision W₁ W₂ = some (W₁ + W₂) := by
  classical
  simp [partialRevision, hcompat]

theorem partialRevision_eq_none_of_not_compatible
    {W₁ W₂ : WeightedState}
    (hcompat : ¬ compatible W₁ W₂) :
    partialRevision W₁ W₂ = none := by
  classical
  simp [partialRevision, hcompat]

theorem fallbackRevision_eq_add_of_compatible
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂) :
    fallbackRevision W₁ W₂ = W₁ + W₂ := by
  classical
  simp [fallbackRevision, partialRevision, hcompat]

theorem fallbackRevision_eq_left_of_not_compatible
    {W₁ W₂ : WeightedState}
    (hcompat : ¬ compatible W₁ W₂) :
    fallbackRevision W₁ W₂ = W₁ := by
  classical
  simp [fallbackRevision, partialRevision, hcompat]

/-- Approx-safe forgetting theorem:
when forgetting is applied to the right state under compatibility, fallback
revision preserves source-counts for left-supported sources. -/
theorem approx_safe_forgetting_preserves_left_sourceCount
    (drop : String → Prop) [DecidablePred drop]
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂)
    {s : String}
    (hleft : sourceInState s W₁) :
    sourceCount s (fallbackRevision W₁ (forgetSources drop W₂)) = sourceCount s W₁ := by
  have hcompatF :
      compatible W₁ (forgetSources drop W₂) :=
    compatible_left_forgetSources_right drop hcompat
  rw [fallbackRevision_eq_add_of_compatible (W₁ := W₁) (W₂ := forgetSources drop W₂) hcompatF]
  rw [sourceCount_add]
  have hzero :
      sourceCount s (forgetSources drop W₂) = 0 :=
    sourceCount_zero_right_of_compatible (hcompat := hcompatF) (hleft := hleft)
  simp [hzero]

/-- Recovery theorem:
when compatible, fallback revision recovers additive weighted evidence. -/
theorem weightedEvidence_fallback_eq_add_of_compatible
    (W₁ W₂ : WeightedState) (φ : ModalQuery)
    (hcompat : compatible W₁ W₂) :
    weightedEvidence (fallbackRevision W₁ W₂) φ =
      weightedEvidence W₁ φ + weightedEvidence W₂ φ := by
  rw [fallbackRevision_eq_add_of_compatible (hcompat := hcompat)]
  exact weightedEvidence_add W₁ W₂ φ

/-- Lifted consequence theorem through provenance-aware fallback revision. -/
theorem weighted_strength_le_of_provable_imp_fallback
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (W₁ W₂ : WeightedState) (φ ψ : ModalQuery)
    (hcompat : compatible W₁ W₂)
    (hW : ∀ pk ∈ weightedExpansion (W₁ + W₂), pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (fallbackRevision W₁ W₂) φ ≤
      WorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (fallbackRevision W₁ W₂) ψ := by
  rw [fallbackRevision_eq_add_of_compatible (hcompat := hcompat)]
  exact weighted_strength_le_of_provable_imp
    (S := S) (𝓢 := 𝓢) (C := C) (W := W₁ + W₂) (φ := φ) (ψ := ψ) hW hprov

/-- Lifted trusted-gate theorem through provenance-aware fallback revision. -/
theorem trustedGate_ob_pe_strength_le_of_provable_fallback
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (trusted : String → Prop) [DecidablePred trusted]
    (W₁ W₂ : WeightedState) (φ : ModalQuery)
    (hcompat : compatible W₁ W₂)
    (hW : ∀ pk ∈ weightedExpansion (trustedGate trusted (W₁ + W₂)), pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    WorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (trustedGate trusted (fallbackRevision W₁ W₂)) (□φ) ≤
      WorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (trustedGate trusted (fallbackRevision W₁ W₂)) (◇φ) := by
  rw [fallbackRevision_eq_add_of_compatible (hcompat := hcompat)]
  exact trustedGate_ob_pe_strength_le_of_provable
    (S := S) (𝓢 := 𝓢) (C := C)
    (trusted := trusted) (W := W₁ + W₂) (φ := φ) hW hprov

/-- State-indexed WM consequence rule packaging for trusted-gate consequence on
fallback-revised states. -/
def wmTrustedGateObPeConsequenceRule_fallback
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (trusted : String → Prop) [DecidablePred trusted]
    (W₂ : WeightedState)
    (φ : ModalQuery)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    WMConsequenceRuleOn WeightedState ModalQuery where
  side := fun W₁ =>
    compatible W₁ W₂ ∧
      trustedGate trusted (fallbackRevision W₁ W₂) = W₁ ∧
      (∀ pk ∈ weightedExpansion (trustedGate trusted (W₁ + W₂)), pk.model.toFrame ∈ C)
  premise := □φ
  conclusion := ◇φ
  sound := by
    intro W₁ hSide
    rcases hSide with ⟨hcompat, hclosed, hW⟩
    have hfb :
        WorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
            (trustedGate trusted (fallbackRevision W₁ W₂)) (□φ) ≤
          WorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
            (trustedGate trusted (fallbackRevision W₁ W₂)) (◇φ) :=
      trustedGate_ob_pe_strength_le_of_provable_fallback
      (S := S) (𝓢 := 𝓢) (C := C)
      (trusted := trusted) (W₁ := W₁) (W₂ := W₂) (φ := φ)
      hcompat hW hprov
    simpa [hclosed] using hfb

end Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlap
