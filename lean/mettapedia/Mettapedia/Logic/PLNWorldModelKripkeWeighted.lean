import Mathlib.Data.Multiset.MapFold
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelKripkeCompleteness

/-!
# Weighted / Source-Aware Kripke WM Variant

This module adds a weighted, provenance-labeled Kripke WM state where each
pointed model contributes an integer weight. It proves a weight-1 specialization
bridge back to the unweighted Kripke WM semantics.
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeWeighted

open LO
open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelKripke
open Mettapedia.Logic.PLNWorldModelKripkeCompleteness
open scoped ENNReal

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelKripke.ModalQuery
abbrev PointedKripke := Mettapedia.Logic.PLNWorldModelKripke.PointedKripke

/-- Source-aware weighted pointed Kripke datum. -/
structure WeightedSourcePointedKripke where
  source : String
  weight : Nat
  point : PointedKripke

abbrev WeightedState := Multiset WeightedSourcePointedKripke

instance : EvidenceType WeightedState where

/-- Expand a weighted/source-aware state into a (possibly repeated) multiset of
pointed Kripke states by replicating each point according to its weight. -/
def weightedExpansion (W : WeightedState) : Multiset PointedKripke :=
  W.bind (fun wp => Multiset.replicate wp.weight wp.point)

theorem weightedExpansion_add (W₁ W₂ : WeightedState) :
    weightedExpansion (W₁ + W₂) = weightedExpansion W₁ + weightedExpansion W₂ := by
  unfold weightedExpansion
  simp [Multiset.add_bind]

/-- Weighted count of satisfying points. -/
def weightedCountP (p : PointedKripke → Prop) [DecidablePred p]
    (W : WeightedState) : Nat :=
  Multiset.countP p (weightedExpansion W)

/-- Additivity of weighted counts over multiset revision (`+`). -/
theorem weightedCountP_add
    (p : PointedKripke → Prop) [DecidablePred p]
    (W₁ W₂ : WeightedState) :
    weightedCountP p (W₁ + W₂) = weightedCountP p W₁ + weightedCountP p W₂ := by
  simp [weightedCountP, weightedExpansion_add, Multiset.countP_add]

theorem weightedCountP_singleton
    (p : PointedKripke → Prop) [DecidablePred p]
    (wp : WeightedSourcePointedKripke) :
    weightedCountP p ({wp} : WeightedState) =
      if p wp.point then wp.weight else 0 := by
  have hrep :
      ∀ n : Nat, Multiset.countP p (Multiset.replicate n wp.point) =
        if p wp.point then n else 0 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        by_cases hp : p wp.point
        · simp [Multiset.replicate_succ, Multiset.countP_cons_of_pos, hp, ih]
        · simp [Multiset.replicate_succ, Multiset.countP_cons_of_neg, hp, ih]
  simpa [weightedCountP, weightedExpansion] using hrep wp.weight

/-- One-step unfolding for weighted counts. -/
theorem weightedCountP_cons
    (p : PointedKripke → Prop) [DecidablePred p]
    (wp : WeightedSourcePointedKripke) (W : WeightedState) :
    weightedCountP p (wp ::ₘ W) =
      weightedCountP p W + if p wp.point then wp.weight else 0 := by
  calc
    weightedCountP p (wp ::ₘ W)
        = weightedCountP p (({wp} : WeightedState) + W) := by simp
    _ = weightedCountP p ({wp} : WeightedState) + weightedCountP p W :=
        weightedCountP_add (p := p) ({wp} : WeightedState) W
    _ = weightedCountP p W + if p wp.point then wp.weight else 0 := by
        simp [weightedCountP_singleton, Nat.add_comm]

/-- Weighted evidence extraction for Kripke modal queries. -/
noncomputable def weightedEvidence (W : WeightedState) (φ : ModalQuery) : BinaryEvidence := by
  classical
  let p : PointedKripke → Prop := fun pk => pk.satisfies φ
  let q : PointedKripke → Prop := fun pk => ¬ pk.satisfies φ
  exact ⟨(weightedCountP p W : ℝ≥0∞), (weightedCountP q W : ℝ≥0∞)⟩

theorem weightedEvidence_add
    (W₁ W₂ : WeightedState) (φ : ModalQuery) :
    weightedEvidence (W₁ + W₂) φ =
      weightedEvidence W₁ φ + weightedEvidence W₂ φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [weightedEvidence, weightedCountP_add, BinaryEvidence.hplus_def]
  · simp [weightedEvidence, weightedCountP_add, BinaryEvidence.hplus_def]

/-- Weighted/source-aware `BinaryWorldModel` instance. -/
noncomputable instance : BinaryWorldModel WeightedState ModalQuery where
  evidence := weightedEvidence
  evidence_add := weightedEvidence_add
  evidence_zero q := by
    classical
    simp only [weightedEvidence, weightedCountP, weightedExpansion,
      Multiset.zero_bind, Multiset.countP_zero, Nat.cast_zero]; rfl

/-- Unit source label used by weight-1 specialization map. -/
def unitSource : String := "unit"

/-- Canonical weight-1/source datum for embedding unweighted pointed states. -/
def weightOnePoint (pk : PointedKripke) : WeightedSourcePointedKripke :=
  { source := unitSource, weight := 1, point := pk }

@[simp] theorem weightOnePoint_point (pk : PointedKripke) :
    (weightOnePoint pk).point = pk := rfl

@[simp] theorem weightOnePoint_weight (pk : PointedKripke) :
    (weightOnePoint pk).weight = 1 := rfl

/-- Embed an unweighted state as a weighted/source-aware state with weight = 1. -/
def toWeightOne (W : Multiset PointedKripke) : WeightedState :=
  W.bind (fun pk => ({weightOnePoint pk} : WeightedState))

@[simp] theorem toWeightOne_cons (a : PointedKripke) (s : Multiset PointedKripke) :
    toWeightOne (a ::ₘ s) = weightOnePoint a ::ₘ toWeightOne s := by
  simp [toWeightOne]

/-- Weight-1 specialization of weighted counts recovers ordinary `countP`. -/
theorem weightedCountP_toWeightOne_eq_countP
    (p : PointedKripke → Prop) [DecidablePred p]
    (W : Multiset PointedKripke) :
    weightedCountP p (toWeightOne W) =
      Multiset.countP p W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp [toWeightOne, weightedCountP, weightedExpansion]
  | @cons a s ih =>
      rw [toWeightOne_cons, weightedCountP_cons, ih]
      by_cases hp : p a
      · simp [Multiset.countP_cons_of_pos, hp, weightOnePoint]
      · simp [Multiset.countP_cons_of_neg, hp, weightOnePoint]

/-- Weight-1 specialization of weighted evidence recovers unweighted Kripke evidence. -/
theorem weightedEvidence_toWeightOne_eq_kripkeEvidence
    (W : Multiset PointedKripke) (φ : ModalQuery) :
    weightedEvidence (toWeightOne W) φ = kripkeEvidence W φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [weightedEvidence, kripkeEvidence, weightedCountP_toWeightOne_eq_countP]
  · simp [weightedEvidence, kripkeEvidence, weightedCountP_toWeightOne_eq_countP]

/-- Weight-1 specialization preserves query strength exactly. -/
theorem queryStrength_toWeightOne_eq_kripke
    (W : Multiset PointedKripke) (φ : ModalQuery) :
    BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (toWeightOne W) φ =
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        W φ := by
  change (BinaryWorldModel.evidence (toWeightOne W) φ).toStrength =
      (BinaryWorldModel.evidence W φ).toStrength
  exact congrArg (fun e => e.toStrength)
    (weightedEvidence_toWeightOne_eq_kripkeEvidence (W := W) (φ := φ))

/-- Weighted evidence coincides with Kripke evidence on the weighted expansion. -/
theorem weightedEvidence_eq_kripkeEvidence_expansion
    (W : WeightedState) (φ : ModalQuery) :
    weightedEvidence W φ = kripkeEvidence (weightedExpansion W) φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [weightedEvidence, weightedCountP, kripkeEvidence]
  · simp [weightedEvidence, weightedCountP, kripkeEvidence]

/-- Weighted query strength is exactly Kripke query strength of the weighted expansion. -/
theorem queryStrength_eq_kripkeExpansion
    (W : WeightedState) (φ : ModalQuery) :
    BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery) W φ =
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        (weightedExpansion W) φ := by
  change (BinaryWorldModel.evidence W φ).toStrength =
      (BinaryWorldModel.evidence (weightedExpansion W) φ).toStrength
  exact congrArg (fun e => e.toStrength)
    (weightedEvidence_eq_kripkeEvidence_expansion (W := W) (φ := φ))

/-- Proof-theoretic implication consequence on weighted states, via expansion transfer. -/
theorem weighted_strength_le_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (W : WeightedState) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ weightedExpansion W, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery) W ψ := by
  have hK :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          (weightedExpansion W) φ ≤
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          (weightedExpansion W) ψ :=
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := weightedExpansion W) (φ := φ) (ψ := ψ) hW hprov
  simpa [queryStrength_eq_kripkeExpansion (W := W) (φ := φ),
    queryStrength_eq_kripkeExpansion (W := W) (φ := ψ)] using hK

/-- Any unweighted Kripke strength inequality transfers to the weight-1 embedding. -/
theorem queryStrength_le_toWeightOne_of_kripke
    (W : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hK :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ) :
    BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (toWeightOne W) φ ≤
      BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (toWeightOne W) ψ := by
  simpa [queryStrength_toWeightOne_eq_kripke (W := W) (φ := φ),
    queryStrength_toWeightOne_eq_kripke (W := W) (φ := ψ)] using hK

/-- Proof-theoretic implication consequence transfers to the weight-1 weighted WM state. -/
theorem toWeightOne_strength_le_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (W : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (toWeightOne W) φ ≤
      BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (toWeightOne W) ψ := by
  have hK :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ :=
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := φ) (ψ := ψ) hW hprov
  exact queryStrength_le_toWeightOne_of_kripke (W := W) (φ := φ) (ψ := ψ) hK

/-- Trusted-source gate for weighted states. -/
def trustedGate (trusted : String → Prop) [DecidablePred trusted]
    (W : WeightedState) : WeightedState :=
  W.filter (fun wp => trusted wp.source)

/-- Governance-facing weighted theorem:
after trusted-source gating, a provable `□φ ➝ ◇φ` implication transfers to the
weighted WM inequality `□φ ⪯ ◇φ`. -/
theorem trustedGate_ob_pe_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (trusted : String → Prop) [DecidablePred trusted]
    (W : WeightedState) (φ : ModalQuery)
    (hW : ∀ pk ∈ weightedExpansion (trustedGate trusted W), pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (trustedGate trusted W) (□φ) ≤
      BinaryWorldModel.queryStrength (State := WeightedState) (Query := ModalQuery)
        (trustedGate trusted W) (◇φ) := by
  exact
    weighted_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := trustedGate trusted W) (φ := □φ) (ψ := ◇φ) hW hprov

/-- State-indexed WM consequence rule packaging for trusted-source gated
obligation/permission consequence (`□φ ⪯ ◇φ`). -/
def wmTrustedGateObPeConsequenceRule
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (trusted : String → Prop) [DecidablePred trusted]
    (φ : ModalQuery)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    WMConsequenceRuleOn WeightedState ModalQuery where
  side := fun W =>
    trustedGate trusted W = W ∧
      (∀ pk ∈ weightedExpansion W, pk.model.toFrame ∈ C)
  premise := □φ
  conclusion := ◇φ
  sound := by
    intro W hW
    rcases hW with ⟨hclosed, hFrame⟩
    have hFrameGate :
        ∀ pk ∈ weightedExpansion (trustedGate trusted W), pk.model.toFrame ∈ C := by
      simpa [hclosed] using hFrame
    exact
      (by
        simpa [hclosed] using
          (trustedGate_ob_pe_strength_le_of_provable
            (S := S) (𝓢 := 𝓢) (C := C)
            (trusted := trusted) (W := W) (φ := φ) hFrameGate hprov))

end Mettapedia.Logic.PLNWorldModelKripkeWeighted
