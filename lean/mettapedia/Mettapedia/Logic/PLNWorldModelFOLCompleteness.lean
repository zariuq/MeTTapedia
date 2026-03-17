import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelFOL
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Foundation.FirstOrder.Completeness.Completeness

/-!
# FOL WM Consequence/Completeness Bridge from Foundation Consequence

This module bridges Foundation first-order semantic consequence
`T ⊨[SmallStruc L] (φ ➝ ψ)` into WM singleton/multiset strength inequalities,
packages the result as `WMConsequenceRuleOn`, and provides a proof-theoretic
`provable ↔ singleton consequence` bridge for implication queries over `T`-models.

## Scope note
The historical filename `*FOLCompleteness` is retained for compatibility.
This module's strongest theorem-level claim is implication-fragment bridge
equivalence over `T`-models:
`(T ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory T φ ψ`.
It is not a global completeness theorem for generic WM judgments.
-/

namespace Mettapedia.Logic.PLNWorldModelFOLCompleteness

open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelFOL
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open scoped ENNReal

universe u

abbrev FOLQuery (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOL.FOLQuery L
abbrev PointedFOL (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOL.PointedFOL L
abbrev FOLState (L : Language.{u}) := Multiset (PointedFOL L)

/-- Alias for the unified categorical endpoint surface, specialized to FOL WM
states. -/
abbrev WMCategoricalEndpointSurface {L : Language.{u}}
    (H : WMHyperdoctrine (FOLState L)) : Prop :=
  Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointSurface (H := H)

/-- State-side condition: every pointed structure in `W` is a model of `T`. -/
def stateModelsTheory {L : Language.{u}} (T : Theory L) (W : FOLState L) : Prop :=
  ∀ S ∈ W, S ⊧* T

/-- Pointwise implication restricted to models of `T`. -/
def pointwiseImpliesOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) : Prop :=
  ∀ S : PointedFOL L, S ⊧* T → folSatisfies S φ → folSatisfies S ψ

/-- Singleton-strength consequence restricted to pointed structures that model
`T`. -/
def singletonStrengthLEOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) : Prop :=
  ∀ S : PointedFOL L, S ⊧* T →
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L)
        ({S} : FOLState L) φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L)
        ({S} : FOLState L) ψ

/-- Naming alias: singleton consequence on models of `T`. -/
abbrev singletonConsequenceOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) : Prop :=
  singletonStrengthLEOnTheory T φ ψ

/-- Fixed-structure singleton WM consequence is equivalent to semantic
implication at that structure. -/
theorem singletonStrengthLE_singleton_iff_imp {L : Language.{u}}
    (S : PointedFOL L) (φ ψ : FOLQuery L) :
    (BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L)
        ({S} : FOLState L) φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L)
        ({S} : FOLState L) ψ) ↔
      (folSatisfies S φ → folSatisfies S ψ) := by
  constructor
  · intro hle hφ
    by_contra hψ
    have h1 :
        BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L)
            ({S} : FOLState L) φ = 1 :=
      Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_satisfies
        (S := S) (φ := φ) hφ
    have h0 :
        BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L)
            ({S} : FOLState L) ψ = 0 :=
      Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_not_satisfies
        (S := S) (φ := ψ) hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have h10' := hle
      rw [h1, h0] at h10'
      exact h10'
    exact (not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1)) h10
  · intro himp
    by_cases hφ : folSatisfies S φ
    · have hψ : folSatisfies S ψ := himp hφ
      rw [Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_satisfies
            (S := S) (φ := φ) hφ]
      rw [Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_satisfies
            (S := S) (φ := ψ) hψ]
    · rw [Mettapedia.Logic.PLNWorldModelFOL.queryStrength_singleton_of_not_satisfies
            (S := S) (φ := φ) hφ]
      exact zero_le _

/-- Model-restricted pointwise implication iff model-restricted singleton WM
consequence. -/
theorem pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    pointwiseImpliesOnTheory T φ ψ ↔ singletonStrengthLEOnTheory T φ ψ := by
  constructor
  · intro himp S hT
    exact
      (singletonStrengthLE_singleton_iff_imp (S := S) (φ := φ) (ψ := ψ)).2
        (himp S hT)
  · intro hsing S hT hφ
    exact
      (singletonStrengthLE_singleton_iff_imp (S := S) (φ := φ) (ψ := ψ)).1
        (hsing S hT) hφ

/-- Naming alias for the same bridge with `singletonConsequence` terminology. -/
theorem pointwiseImpliesOnTheory_iff_singletonConsequenceOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    pointwiseImpliesOnTheory T φ ψ ↔ singletonConsequenceOnTheory T φ ψ :=
  pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
    (T := T) (φ := φ) (ψ := ψ)

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

/-- Model-restricted pointwise implication yields Foundation semantic
consequence. -/
theorem consequence_of_pointwiseImpliesOnTheory {L : Language.{u}}
    {T : Theory L} {φ ψ : FOLQuery L}
    (himp : pointwiseImpliesOnTheory T φ ψ) :
    T ⊨[SmallStruc L] (φ ➝ ψ) := by
  intro S hT
  exact
    (Semantics.Imp.models_imply (𝓜 := S) (φ := φ) (ψ := ψ)).2
      (by
        intro hφ
        exact himp S hT (by simpa [folSatisfies] using hφ))

/-- Foundation semantic implication consequence iff model-restricted singleton
WM consequence. -/
theorem consequence_iff_singletonStrengthLEOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    T ⊨[SmallStruc L] (φ ➝ ψ) ↔ singletonStrengthLEOnTheory T φ ψ := by
  constructor
  · intro hcons
    exact
      (pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
        (T := T) (φ := φ) (ψ := ψ)).1
        (pointwiseImpliesOnTheory_of_consequence (T := T) (φ := φ) (ψ := ψ) hcons)
  · intro hsing
    exact
      consequence_of_pointwiseImpliesOnTheory
        ((pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
          (T := T) (φ := φ) (ψ := ψ)).2 hsing)

/-- Proof-theoretic bridge for FOL implication:
provability is equivalent to singleton WM consequence on `T`-models. -/
theorem provable_imp_iff_singletonStrengthLEOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    (T ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory T φ ψ := by
  constructor
  · intro hprov
    exact
      (consequence_iff_singletonStrengthLEOnTheory
        (T := T) (φ := φ) (ψ := ψ)).1 (smallSound! hprov)
  · intro hsing
    exact
      FirstOrder.complete
        ((consequence_iff_singletonStrengthLEOnTheory
          (T := T) (φ := φ) (ψ := ψ)).2 hsing)

/-- Naming alias: proof-theoretic implication iff singleton WM consequence on
models of `T`. -/
theorem provable_imp_iff_singletonConsequenceOnTheory {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L) :
    (T ⊢ (φ ➝ ψ)) ↔ singletonConsequenceOnTheory T φ ψ :=
  provable_imp_iff_singletonStrengthLEOnTheory (T := T) (φ := φ) (ψ := ψ)

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
  unfold folEvidence BinaryEvidence.total
  simpa using hcard.symm

/-- Multiset WM strength inequality from model-restricted pointwise implication. -/
theorem queryStrength_le_of_pointwise_on {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (himp : pointwiseImpliesOnTheory T φ ψ) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  let pφ : PointedFOL L → Prop := fun S => folSatisfies S φ
  let pψ : PointedFOL L → Prop := fun S => folSatisfies S ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    change (if (folEvidence W φ).total = 0 then 0
      else (folEvidence W φ).pos / (folEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [folEvidence_total (W := W) (φ := φ)]
    simp [folEvidence, pφ]
  have hψ :
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
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
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  have himp : pointwiseImpliesOnTheory T φ ψ :=
    pointwiseImpliesOnTheory_of_consequence (T := T) (φ := φ) (ψ := ψ) hcons
  exact queryStrength_le_of_pointwise_on (T := T) (W := W) (φ := φ) (ψ := ψ) hW himp

/-- Categorical-aligned FOL consequence wrapper:
same multiset strength inequality with explicit endpoint-surface input. -/
theorem multiset_strength_le_of_consequence_categorical {L : Language.{u}}
    (H : WMHyperdoctrine (FOLState L))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ :=
  multiset_strength_le_of_consequence (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons

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

/-- Categorical-aligned packaging of Foundation semantic consequence into
state-indexed WM consequence rules. -/
def wmConsequenceRuleOn_of_consequence_categorical {L : Language.{u}}
    (H : WMHyperdoctrine (FOLState L))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (T : Theory L) (φ ψ : FOLQuery L)
    (hcons : T ⊨[SmallStruc L] (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) :=
  wmConsequenceRuleOn_of_consequence (T := T) (φ := φ) (ψ := ψ) hcons

/-- Provability wrapper via Foundation soundness (`smallSound!`). -/
theorem multiset_strength_le_of_provable_imp {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ := by
  exact
    multiset_strength_le_of_consequence
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW (smallSound! hprov)

/-- Naming alias: soundness transfer from provability to multiset WM
consequence on states satisfying `T`. -/
theorem multiset_consequence_of_provable_imp {L : Language.{u}}
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ :=
  multiset_strength_le_of_provable_imp (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov

/-- Categorical-aligned FOL provability wrapper:
same multiset strength inequality with explicit endpoint-surface input. -/
theorem multiset_strength_le_of_provable_imp_categorical {L : Language.{u}}
    (H : WMHyperdoctrine (FOLState L))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (T : Theory L)
    (W : FOLState L) (φ ψ : FOLQuery L)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W φ ≤
      BinaryWorldModel.queryStrength (State := FOLState L) (Query := FOLQuery L) W ψ :=
  multiset_strength_le_of_provable_imp (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov

/-- Rule packaging for provable implication into WM consequence rules. -/
def wmConsequenceRuleOn_of_provable_imp {L : Language.{u}}
    (T : Theory L) (φ ψ : FOLQuery L)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) :=
  wmConsequenceRuleOn_of_consequence
    (T := T) (φ := φ) (ψ := ψ) (smallSound! hprov)

/-- Categorical-aligned packaging of Foundation provability into state-indexed
WM consequence rules. -/
def wmConsequenceRuleOn_of_provable_imp_categorical {L : Language.{u}}
    (H : WMHyperdoctrine (FOLState L))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (T : Theory L) (φ ψ : FOLQuery L)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn (FOLState L) (FOLQuery L) :=
  wmConsequenceRuleOn_of_provable_imp (T := T) (φ := φ) (ψ := ψ) hprov

end Mettapedia.Logic.PLNWorldModelFOLCompleteness
