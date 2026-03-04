import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelFOL
import Mettapedia.Logic.PLNWorldModelCalculus
import Foundation.FirstOrder.Completeness.Completeness

/-!
# FOL WM Consequence Closure from Foundation Consequence

This module bridges Foundation first-order semantic consequence
`T ⊨[SmallStruc L] (φ ➝ ψ)` into WM multiset strength inequalities and
packages the result as `WMConsequenceRuleOn`.
-/

namespace Mettapedia.Logic.PLNWorldModelFOLCompleteness

open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelFOL
open scoped ENNReal

universe u

abbrev FOLQuery (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOL.FOLQuery L
abbrev PointedFOL (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOL.PointedFOL L
abbrev FOLState (L : Language.{u}) := Multiset (PointedFOL L)

/-- State-side condition: every pointed structure in `W` is a model of `T`. -/
def stateModelsTheory {L : Language.{u}} (T : Theory L) (W : FOLState L) : Prop :=
  ∀ S ∈ W, S ⊧* T

/-- Pointwise implication restricted to models of `T`. -/
def pointwiseImpliesOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) : Prop :=
  ∀ S : PointedFOL L, S ⊧* T → folSatisfies S φ → folSatisfies S ψ

/-- Foundation semantic consequence implies model-restricted pointwise implication. -/
theorem pointwiseImpliesOnTheory_of_consequence {L : Language.{u}}
    {T : Theory L} {φ ψ : FOLQuery L}
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    pointwiseImpliesOnTheory T φ ψ := by
  intro S hT hφ
  have hImp : S ⊧ (φ ➝ ψ) := hcons hT
  have hStep : S ⊧ φ → S ⊧ ψ :=
    (Semantics.Imp.models_imply (𝓜 := S) (φ := φ) (ψ := ψ)).mp hImp
  have hψ : S ⊧ ψ := hStep (by simpa [folSatisfies] using hφ)
  simpa [folSatisfies] using hψ

private theorem countP_le_countP_of_imp_on {L : Language.{u}}
    (W : FOLState L)
    {p q : PointedFOL L → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ S ∈ W, p S → q S) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      have himp_tail : ∀ S ∈ W, p S → q S := by
        intro S hmem hp
        exact himp S (by simp [hmem]) hp
      by_cases hp : p a
      · have hq : q a := himp a (by simp) hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ (ih himp_tail)
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans (ih himp_tail) (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih himp_tail

private theorem folEvidence_total {L : Language.{u}}
    (W : FOLState L) (φ : FOLQuery L) :
    (folEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun S : PointedFOL L => folSatisfies S φ) W +
          Multiset.countP (fun S : PointedFOL L => ¬ folSatisfies S φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun S : PointedFOL L => folSatisfies S φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun S : PointedFOL L => folSatisfies S φ) W : ℝ≥0∞) +
          (Multiset.countP (fun S : PointedFOL L => ¬ folSatisfies S φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold folEvidence Evidence.total
  simpa using hcard.symm

/-- Multiset WM strength inequality from model-restricted pointwise implication. -/
theorem queryStrength_le_of_pointwise_on {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (himp : pointwiseImpliesOnTheory T φ ψ) :
    WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  let pφ : PointedFOL L → Prop := fun S => folSatisfies S φ
  let pψ : PointedFOL L → Prop := fun S => folSatisfies S ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (folEvidence W φ).total = 0 then 0
      else (folEvidence W φ).pos / (folEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [folEvidence_total (W := W) (φ := φ)]
    simp [folEvidence, pφ]
  have hψ :
      WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (folEvidence W ψ).total = 0 then 0
      else (folEvidence W ψ).pos / (folEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [folEvidence_total (W := W) (φ := ψ)]
    simp [folEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp_on (W := W) (p := pφ) (q := pψ) (by
        intro S hmem hp
        exact himp S (hW S hmem) (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Bridge theorem requested for FOL:
Foundation semantic consequence gives WM multiset strength inequality. -/
theorem multiset_strength_le_of_consequence {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  have himp : pointwiseImpliesOnTheory T φ ψ :=
    pointwiseImpliesOnTheory_of_consequence (T := T) (φ := φ) (ψ := ψ) hcons
  exact queryStrength_le_of_pointwise_on (T := T) (W := W) (φ := φ) (ψ := ψ) hW himp

/-- Rule packaging for Foundation semantic consequence into WM inequalities. -/
def wmConsequenceRuleOn_of_consequence {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L)
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) where
  side := stateModelsTheory T
  premise := φ
  conclusion := ψ
  sound := by
    intro W hW
    exact
      multiset_strength_le_of_consequence
        (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

/-- Provability wrapper via Foundation soundness (`smallSound!`). -/
theorem multiset_strength_le_of_provable_imp {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      WorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  exact
    multiset_strength_le_of_consequence
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hprov)

/-- Rule packaging for provable implication into WM consequence rules. -/
def wmConsequenceRuleOn_of_provable_imp {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) :=
  wmConsequenceRuleOn_of_consequence
    (T := T) (φ := φ) (ψ := ψ) (smallSound! hprov)

end Mettapedia.Logic.PLNWorldModelFOLCompleteness
