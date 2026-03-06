import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelNeighborhood
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Logic.EMN
import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.ED

/-!
# Neighborhood WM Proof-Theoretic Closure (Implication Fragment)

This module connects class-indexed neighborhood proof theory (`Sound`/`Complete`)
to WM singleton/multiset consequence inequalities for implication queries.
-/

namespace Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness

open LO
open LO.Modal
open Formula.Neighborhood
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelNeighborhood
open scoped ENNReal

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelNeighborhood.ModalQuery
abbrev PointedNeighborhood := Mettapedia.Logic.PLNWorldModelNeighborhood.PointedNeighborhood

/-- Pointwise implication restricted to pointed neighborhood states
whose underlying frame belongs to `C`. -/
def pointwiseImpliesOn (C : Neighborhood.FrameClass) (φ ψ : ModalQuery) : Prop :=
  ∀ pn : PointedNeighborhood, pn.model.toFrame ∈ C →
    pn.satisfies φ → pn.satisfies ψ

/-- Singleton-strength consequence restricted to frame class `C`. -/
def singletonStrengthLEOn (C : Neighborhood.FrameClass) (φ ψ : ModalQuery) : Prop :=
  ∀ pn : PointedNeighborhood, pn.model.toFrame ∈ C →
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) ψ

/-- Naming alias: singleton consequence on frame class `C`. -/
abbrev singletonConsequenceOn (C : Neighborhood.FrameClass) (φ ψ : ModalQuery) : Prop :=
  singletonStrengthLEOn C φ ψ

/-- Frame-class local singleton consequence iff pointwise implication. -/
theorem pointwiseImpliesOn_iff_singletonStrengthLEOn
    (C : Neighborhood.FrameClass) (φ ψ : ModalQuery) :
    pointwiseImpliesOn C φ ψ ↔ singletonStrengthLEOn C φ ψ := by
  constructor
  · intro himp pn hC
    by_cases hφ : pn.satisfies φ
    · have hψ : pn.satisfies ψ := himp pn hC hφ
      rw [queryStrength_singleton_of_satisfies pn φ hφ]
      rw [queryStrength_singleton_of_satisfies pn ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies pn φ hφ]
      exact zero_le _
  · intro hle pn hC hφ
    by_contra hψ
    have hsingleton := hle pn hC
    have h1 :
        WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            ({pn} : Multiset PointedNeighborhood) φ = 1 :=
      queryStrength_singleton_of_satisfies pn φ hφ
    have h0 :
        WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            ({pn} : Multiset PointedNeighborhood) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies pn ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      simp [h1, h0] at htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp_on
    (W : Multiset PointedNeighborhood)
    {p q : PointedNeighborhood → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ pn ∈ W, p pn → q pn) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      have himp_tail : ∀ pn ∈ W, p pn → q pn := by
        intro pn hmem hp
        exact himp pn (by simp [hmem]) hp
      by_cases hp : p a
      · have hq : q a := himp a (by simp) hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ (ih himp_tail)
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans (ih himp_tail) (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih himp_tail

private theorem neighborhoodEvidence_total
    (W : Multiset PointedNeighborhood) (φ : ModalQuery) :
    (neighborhoodEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pn : PointedNeighborhood => pn.satisfies φ) W +
          Multiset.countP (fun pn : PointedNeighborhood => ¬ pn.satisfies φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pn : PointedNeighborhood => pn.satisfies φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pn : PointedNeighborhood => pn.satisfies φ) W : ℝ≥0∞) +
          (Multiset.countP (fun pn : PointedNeighborhood => ¬ pn.satisfies φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold neighborhoodEvidence Evidence.total
  simpa using hcard.symm

/-- Multiset strength inequality from frame-class-local pointwise implication. -/
theorem queryStrength_le_of_pointwise_on
    (C : Neighborhood.FrameClass)
    (W : Multiset PointedNeighborhood) (φ ψ : ModalQuery)
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ C)
    (himp : pointwiseImpliesOn C φ ψ) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  let pφ : PointedNeighborhood → Prop := fun pn => pn.satisfies φ
  let pψ : PointedNeighborhood → Prop := fun pn => pn.satisfies ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (neighborhoodEvidence W φ).total = 0 then 0
      else (neighborhoodEvidence W φ).pos / (neighborhoodEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [neighborhoodEvidence_total (W := W) (φ := φ)]
    simp [neighborhoodEvidence, pφ]
  have hψ :
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (neighborhoodEvidence W ψ).total = 0 then 0
      else (neighborhoodEvidence W ψ).pos / (neighborhoodEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [neighborhoodEvidence_total (W := W) (φ := ψ)]
    simp [neighborhoodEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp_on (W := W) (p := pφ) (q := pψ) (by
        intro pn hmem hp
        exact himp pn (hW pn hmem) (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from class-indexed singleton assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLEOn
    (C : Neighborhood.FrameClass)
    (W : Multiset PointedNeighborhood) (φ ψ : ModalQuery)
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ C)
    (hsing : singletonStrengthLEOn C φ ψ) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  have himp : pointwiseImpliesOn C φ ψ :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn C φ ψ).mpr hsing
  exact queryStrength_le_of_pointwise_on C W φ ψ hW himp

/-! ## Soundness/completeness bridge from Foundation neighborhood logic -/

/-- Soundness lift: provable implication gives class-indexed singleton WM consequence. -/
theorem singletonStrengthLEOn_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    {φ ψ : ModalQuery}
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    singletonStrengthLEOn C φ ψ := by
  have himp : pointwiseImpliesOn C φ ψ := by
    intro pn hC hφ
    have hvalid : C ⊧ (φ ➝ ψ) := Sound.sound (𝓢 := 𝓢) (𝓜 := C) hprov
    have hframe : pn.model.toFrame ⊧ (φ ➝ ψ) := hvalid hC
    have hmodel : pn.model ⊧ (φ ➝ ψ) := hframe pn.model.Val
    have hworld : Formula.Neighborhood.Satisfies pn.model pn.world (φ ➝ ψ) := hmodel pn.world
    exact (Formula.Neighborhood.Satisfies.def_imp.mp hworld) hφ
  exact (pointwiseImpliesOn_iff_singletonStrengthLEOn C φ ψ).mp himp

/-- Completeness lift: class-indexed singleton WM consequence yields provable implication. -/
theorem provable_imp_of_singletonStrengthLEOn
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Complete 𝓢 C]
    {φ ψ : ModalQuery}
    (hsing : singletonStrengthLEOn C φ ψ) :
    𝓢 ⊢ (φ ➝ ψ) := by
  have himp : pointwiseImpliesOn C φ ψ :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn C φ ψ).mpr hsing
  have hvalid : C ⊧ (φ ➝ ψ) := by
    intro F hF V x
    let pn : PointedNeighborhood := {
      model := (⟨F, V⟩ : Neighborhood.Model)
      world := x
    }
    have hpx : pn.satisfies φ → pn.satisfies ψ := himp pn (by simpa [pn] using hF)
    exact Formula.Neighborhood.Satisfies.def_imp.mpr (by
      intro hx
      simpa [PointedNeighborhood.satisfies, pn] using hpx (by simpa [PointedNeighborhood.satisfies, pn] using hx))
  exact Complete.complete (𝓢 := 𝓢) (𝓜 := C) hvalid

/-- Implication-level proof-theoretic closure for class-indexed singleton WM consequence. -/
theorem provable_imp_iff_singletonStrengthLEOn
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C] [Complete 𝓢 C]
    {φ ψ : ModalQuery} :
    (𝓢 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn C φ ψ := by
  constructor
  · intro hprov
    exact singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  · intro hsing
    exact provable_imp_of_singletonStrengthLEOn (S := S) (𝓢 := 𝓢) (C := C) hsing

/-- Naming alias: proof-theoretic implication iff singleton WM consequence. -/
theorem provable_imp_iff_singletonConsequenceOn
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C] [Complete 𝓢 C]
    {φ ψ : ModalQuery} :
    (𝓢 ⊢ (φ ➝ ψ)) ↔ singletonConsequenceOn C φ ψ :=
  provable_imp_iff_singletonStrengthLEOn (S := S) (𝓢 := 𝓢) (C := C)

/-- Soundness-to-executable consequence bridge on multisets in frame class `C`. -/
theorem multiset_strength_le_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedNeighborhood} {φ ψ : ModalQuery}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  have hsing : singletonStrengthLEOn C φ ψ :=
    singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  exact multiset_strength_le_of_singletonStrengthLEOn C W φ ψ hW hsing

/-- Naming alias: soundness transfer from provability to multiset WM
consequence in frame class `C`. -/
theorem multiset_consequence_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedNeighborhood} {φ ψ : ModalQuery}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ :=
  multiset_strength_le_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hW hprov

/-! ## Concrete Foundation instantiations: E and EMN -/

theorem provable_imp_iff_singletonStrengthLEOn_E
    {φ ψ : ModalQuery} :
    (Modal.E ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Neighborhood.FrameClass.E φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.E) (C := Neighborhood.FrameClass.E)

theorem provable_imp_iff_singletonStrengthLEOn_EMN
    {φ ψ : ModalQuery} :
    (Modal.EMN ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Neighborhood.FrameClass.EMN φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.EMN) (C := Neighborhood.FrameClass.EMN)

theorem multiset_strength_le_of_provable_imp_E
    {W : Multiset PointedNeighborhood} {φ ψ : ModalQuery}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.E)
    (hprov : Modal.E ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.E) (C := Neighborhood.FrameClass.E) hW hprov

theorem multiset_strength_le_of_provable_imp_EMN
    {W : Multiset PointedNeighborhood} {φ ψ : ModalQuery}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.EMN)
    (hprov : Modal.EMN ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.EMN) (C := Neighborhood.FrameClass.EMN) hW hprov

theorem provable_imp_iff_singletonStrengthLEOn_EMT
    [Complete Modal.EMT Neighborhood.FrameClass.EMT]
    {φ ψ : ModalQuery} :
    (Modal.EMT ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Neighborhood.FrameClass.EMT φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.EMT) (C := Neighborhood.FrameClass.EMT)

theorem provable_imp_iff_singletonStrengthLEOn_ED
    [Complete Modal.ED Neighborhood.FrameClass.ED]
    {φ ψ : ModalQuery} :
    (Modal.ED ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Neighborhood.FrameClass.ED φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.ED) (C := Neighborhood.FrameClass.ED)

theorem multiset_strength_le_of_provable_imp_EMT
    {W : Multiset PointedNeighborhood} {φ ψ : ModalQuery}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.EMT)
    (hprov : Modal.EMT ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.EMT) (C := Neighborhood.FrameClass.EMT) hW hprov

theorem multiset_strength_le_of_provable_imp_ED
    {W : Multiset PointedNeighborhood} {φ ψ : ModalQuery}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.ED)
    (hprov : Modal.ED ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.ED) (C := Neighborhood.FrameClass.ED) hW hprov

end Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness
