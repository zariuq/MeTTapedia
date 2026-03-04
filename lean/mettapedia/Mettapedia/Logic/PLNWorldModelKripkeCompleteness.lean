import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelKripke
import Foundation.Modal.Kripke.Logic.K
import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KD
import Foundation.Modal.Kripke.Logic.K4

/-!
# Kripke WM Proof-Theoretic Closure (Implication Fragment)

This module connects class-indexed Kripke proof theory (`Sound`/`Complete`)
to WM singleton/multiset consequence inequalities for implication queries.
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeCompleteness

open LO
open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelKripke
open scoped ENNReal

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelKripke.ModalQuery
abbrev PointedKripke := Mettapedia.Logic.PLNWorldModelKripke.PointedKripke

/-- Pointwise implication restricted to pointed Kripke states
whose underlying frame belongs to `C`. -/
def pointwiseImpliesOn (C : Kripke.FrameClass) (φ ψ : ModalQuery) : Prop :=
  ∀ pk : PointedKripke, pk.model.toFrame ∈ C →
    pk.satisfies φ → pk.satisfies ψ

/-- Singleton-strength consequence restricted to frame class `C`. -/
def singletonStrengthLEOn (C : Kripke.FrameClass) (φ ψ : ModalQuery) : Prop :=
  ∀ pk : PointedKripke, pk.model.toFrame ∈ C →
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) ψ

/-- Frame-class local singleton consequence iff pointwise implication. -/
theorem pointwiseImpliesOn_iff_singletonStrengthLEOn
    (C : Kripke.FrameClass) (φ ψ : ModalQuery) :
    pointwiseImpliesOn C φ ψ ↔ singletonStrengthLEOn C φ ψ := by
  constructor
  · intro himp pk hC
    by_cases hφ : pk.satisfies φ
    · have hψ : pk.satisfies ψ := himp pk hC hφ
      rw [queryStrength_singleton_of_satisfies pk φ hφ]
      rw [queryStrength_singleton_of_satisfies pk ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies pk φ hφ]
      exact zero_le _
  · intro hle pk hC hφ
    by_contra hψ
    have hsingleton := hle pk hC
    have h1 :
        WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
            ({pk} : Multiset PointedKripke) φ = 1 :=
      queryStrength_singleton_of_satisfies pk φ hφ
    have h0 :
        WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
            ({pk} : Multiset PointedKripke) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies pk ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      simp [h1, h0] at htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp_on
    (W : Multiset PointedKripke)
    {p q : PointedKripke → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ pk ∈ W, p pk → q pk) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      have himp_tail : ∀ pk ∈ W, p pk → q pk := by
        intro pk hmem hp
        exact himp pk (by simp [hmem]) hp
      by_cases hp : p a
      · have hq : q a := himp a (by simp) hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ (ih himp_tail)
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans (ih himp_tail) (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih himp_tail

private theorem kripkeEvidence_total
    (W : Multiset PointedKripke) (φ : ModalQuery) :
    (kripkeEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pk : PointedKripke => pk.satisfies φ) W +
          Multiset.countP (fun pk : PointedKripke => ¬ pk.satisfies φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pk : PointedKripke => pk.satisfies φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pk : PointedKripke => pk.satisfies φ) W : ℝ≥0∞) +
          (Multiset.countP (fun pk : PointedKripke => ¬ pk.satisfies φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold kripkeEvidence Evidence.total
  simpa using hcard.symm

/-- Multiset strength inequality from frame-class-local pointwise implication. -/
theorem queryStrength_le_of_pointwise_on
    (C : Kripke.FrameClass)
    (W : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (himp : pointwiseImpliesOn C φ ψ) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  let pφ : PointedKripke → Prop := fun pk => pk.satisfies φ
  let pψ : PointedKripke → Prop := fun pk => pk.satisfies ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (kripkeEvidence W φ).total = 0 then 0
      else (kripkeEvidence W φ).pos / (kripkeEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [kripkeEvidence_total (W := W) (φ := φ)]
    simp [kripkeEvidence, pφ]
  have hψ :
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (kripkeEvidence W ψ).total = 0 then 0
      else (kripkeEvidence W ψ).pos / (kripkeEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [kripkeEvidence_total (W := W) (φ := ψ)]
    simp [kripkeEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp_on (W := W) (p := pφ) (q := pψ) (by
        intro pk hmem hp
        exact himp pk (hW pk hmem) (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from class-indexed singleton assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLEOn
    (C : Kripke.FrameClass)
    (W : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (hsing : singletonStrengthLEOn C φ ψ) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  have himp : pointwiseImpliesOn C φ ψ :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn C φ ψ).mpr hsing
  exact queryStrength_le_of_pointwise_on C W φ ψ hW himp

/-! ## Soundness/completeness bridge from Foundation Kripke logic -/

/-- Soundness lift: provable implication gives class-indexed singleton WM consequence. -/
theorem singletonStrengthLEOn_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    {φ ψ : ModalQuery}
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    singletonStrengthLEOn C φ ψ := by
  have himp : pointwiseImpliesOn C φ ψ := by
    intro pk hC hφ
    have hvalid : C ⊧ (φ ➝ ψ) := Sound.sound (𝓢 := 𝓢) (𝓜 := C) hprov
    have hframe : pk.model.toFrame ⊧ (φ ➝ ψ) := hvalid hC
    have hmodel : pk.model ⊧ (φ ➝ ψ) := hframe pk.model.Val
    have hworld : Formula.Kripke.Satisfies pk.model pk.world (φ ➝ ψ) := hmodel pk.world
    exact (Formula.Kripke.Satisfies.imp_def.mp hworld) hφ
  exact (pointwiseImpliesOn_iff_singletonStrengthLEOn C φ ψ).mp himp

/-- Completeness lift: class-indexed singleton WM consequence yields provable implication. -/
theorem provable_imp_of_singletonStrengthLEOn
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Complete 𝓢 C]
    {φ ψ : ModalQuery}
    (hsing : singletonStrengthLEOn C φ ψ) :
    𝓢 ⊢ (φ ➝ ψ) := by
  have himp : pointwiseImpliesOn C φ ψ :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn C φ ψ).mpr hsing
  have hvalid : C ⊧ (φ ➝ ψ) := by
    intro F hF V x
    let pk : PointedKripke := {
      model := (⟨F, V⟩ : Kripke.Model)
      world := x
    }
    have hpx : pk.satisfies φ → pk.satisfies ψ := himp pk (by simpa [pk] using hF)
    exact Formula.Kripke.Satisfies.imp_def.mpr (by
      intro hx
      exact hpx (by simpa [PointedKripke.satisfies, pk] using hx))
  exact Complete.complete (𝓢 := 𝓢) (𝓜 := C) hvalid

/-- Implication-level proof-theoretic closure for class-indexed singleton WM consequence. -/
theorem provable_imp_iff_singletonStrengthLEOn
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C] [Complete 𝓢 C]
    {φ ψ : ModalQuery} :
    (𝓢 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn C φ ψ := by
  constructor
  · intro hprov
    exact singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  · intro hsing
    exact provable_imp_of_singletonStrengthLEOn (S := S) (𝓢 := 𝓢) (C := C) hsing

/-- Soundness-to-executable consequence bridge on multisets in frame class `C`. -/
theorem multiset_strength_le_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedKripke} {φ ψ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  have hsing : singletonStrengthLEOn C φ ψ :=
    singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  exact multiset_strength_le_of_singletonStrengthLEOn C W φ ψ hW hsing

/-! ## Concrete Foundation instantiations: K and KT -/

theorem provable_imp_iff_singletonStrengthLEOn_K
    {φ ψ : ModalQuery} :
    (Modal.K ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Kripke.FrameClass.K φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.K) (C := Kripke.FrameClass.K)

theorem provable_imp_iff_singletonStrengthLEOn_KT
    {φ ψ : ModalQuery} :
    (Modal.KT ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Kripke.FrameClass.KT φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.KT) (C := Kripke.FrameClass.KT)

theorem multiset_strength_le_of_provable_imp_K
    {W : Multiset PointedKripke} {φ ψ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.K)
    (hprov : Modal.K ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.K) (C := Kripke.FrameClass.K) hW hprov

theorem multiset_strength_le_of_provable_imp_KT
    {W : Multiset PointedKripke} {φ ψ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KT)
    (hprov : Modal.KT ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KT) (C := Kripke.FrameClass.KT) hW hprov

theorem provable_imp_iff_singletonStrengthLEOn_KD
    {φ ψ : ModalQuery} :
    (Modal.KD ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Kripke.FrameClass.KD φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.KD) (C := Kripke.FrameClass.KD)

theorem provable_imp_iff_singletonStrengthLEOn_K4
    {φ ψ : ModalQuery} :
    (Modal.K4 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn Kripke.FrameClass.K4 φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.K4) (C := Kripke.FrameClass.K4)

theorem multiset_strength_le_of_provable_imp_KD
    {W : Multiset PointedKripke} {φ ψ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KD)
    (hprov : Modal.KD ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KD) (C := Kripke.FrameClass.KD) hW hprov

theorem multiset_strength_le_of_provable_imp_K4
    {W : Multiset PointedKripke} {φ ψ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.K4)
    (hprov : Modal.K4 ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.K4) (C := Kripke.FrameClass.K4) hW hprov

/-- Governance-facing corollary of the Kripke implication bridge:
provability of `□φ ➝ ◇φ` yields multiset WM strength inequality between the
obligation/permitted modal forms. -/
theorem multiset_ob_pe_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedKripke} {φ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W (□φ) ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W (◇φ) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C) (W := W) (φ := □φ) (ψ := ◇φ) hW hprov

/-- Kripke-side T-family convenience wrapper:
`□φ ➝ φ` provability in KT yields the multiset WM inequality `□φ ⪯ φ`. -/
theorem multiset_rexist_strength_le_of_provable_KT
    {W : Multiset PointedKripke} {φ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KT)
    (hprov : Modal.KT ⊢ (□φ ➝ φ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W (□φ) ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KT) (C := Kripke.FrameClass.KT)
      (W := W) (φ := □φ) (ψ := φ) hW hprov

/-- Kripke-side D-family convenience wrapper:
`□φ ➝ ◇φ` provability in KD yields the multiset WM inequality `□φ ⪯ ◇φ`. -/
theorem multiset_ob_pe_strength_le_of_provable_KD
    {W : Multiset PointedKripke} {φ : ModalQuery}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KD)
    (hprov : Modal.KD ⊢ (□φ ➝ ◇φ)) :
    WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W (□φ) ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W (◇φ) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KD) (C := Kripke.FrameClass.KD)
      (W := W) (φ := □φ) (ψ := ◇φ) hW hprov

end Mettapedia.Logic.PLNWorldModelKripkeCompleteness
