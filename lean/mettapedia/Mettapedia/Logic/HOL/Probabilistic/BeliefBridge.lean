import Mettapedia.Logic.HOL.LogicalInduction.EmpiricalSpecialCase
import Mettapedia.Logic.HOL.LogicalInduction.Calibration
import Mettapedia.Logic.HOL.Probabilistic.Flattening
import Mettapedia.Logic.HOL.Probabilistic.EmpiricalSpecialCase

/-!
# Semantic-vs-Belief Bridge for Probabilistic HOL

This module relates two distinct higher-order probability layers:

- semantic `ProbHOL` sentence/query strength over measurable indexed model spaces,
- and the Logical-Induction-ready day/process layer over coded closed HOL formulas.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the point is not to collapse
belief into truth.  Instead we define exact comparison predicates and prove
small bridge theorems showing when a belief day or belief process *tracks*
semantic probability on selected formulas or finite samples.

This provides the clean interface needed by later benchmark/planner work:
dynamic belief can be compared against semantic probability without becoming the
canonical meaning of higher-order uncertainty.
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.LogicalInduction
open scoped ENNReal

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

local instance instBeliefBridgeEmpiricalMeasurableSpace :
    MeasurableSpace (HenkinModel.{u, v, w} Base Const) := ⊤

/-- A belief day tracks semantic `ProbHOL` on a single closed HOL formula when
its WM-facing strength agrees with semantic probabilistic query strength. -/
def BeliefDayTracksSentenceProb
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (B : BeliefDay Const)
    (φ : ClosedFormula Const) : Prop :=
  dayQueryStrength (Const := Const) B (encodeClosedFormula φ) =
    probQueryStrength S μ φ

/-- A belief day tracks semantic `ProbHOL` on a finite sample of coded formulas. -/
def BeliefDayTracksSentenceProbOn
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (B : BeliefDay Const)
    (sample : Finset (ClosedFormulaCode Const)) : Prop :=
  ∀ ⦃φ : ClosedFormulaCode Const⦄, φ ∈ sample →
    dayQueryStrength (Const := Const) B φ =
      probQueryStrength S μ (decodeClosedFormula φ)

/-- A belief day tracks hierarchical semantic `ProbHOL` on a single formula when
its WM-facing strength agrees with the hierarchical probabilistic query
strength. -/
def BeliefDayTracksHierarchicalProb
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (B : BeliefDay Const)
    (φ : ClosedFormula Const) : Prop :=
  dayQueryStrength (Const := Const) B (encodeClosedFormula φ) =
    hierarchicalProbQueryStrength H φ

/-- A belief day tracks hierarchical semantic `ProbHOL` on a finite sample of
coded formulas. -/
def BeliefDayTracksHierarchicalProbOn
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (B : BeliefDay Const)
    (sample : Finset (ClosedFormulaCode Const)) : Prop :=
  ∀ ⦃φ : ClosedFormulaCode Const⦄, φ ∈ sample →
    dayQueryStrength (Const := Const) B φ =
      hierarchicalProbQueryStrength H (decodeClosedFormula φ)

/-- A belief process eventually tracks semantic `ProbHOL` on a finite sample. -/
def BeliefProcessEventuallyTracksSentenceProbOn
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (sample : Finset (ClosedFormulaCode Const))
    (P : BeliefProcess Const) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n →
    BeliefDayTracksSentenceProbOn (Const := Const) S μ (P n) sample

/-- A belief process eventually tracks hierarchical semantic `ProbHOL` on a
finite sample. -/
def BeliefProcessEventuallyTracksHierarchicalProbOn
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (sample : Finset (ClosedFormulaCode Const))
    (P : BeliefProcess Const) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n →
    BeliefDayTracksHierarchicalProbOn (Const := Const) H (P n) sample

theorem beliefDayTracksSentenceProbOn_singleton
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (B : BeliefDay Const)
    (φ : ClosedFormula Const) :
    BeliefDayTracksSentenceProb (Const := Const) S μ B φ ↔
      BeliefDayTracksSentenceProbOn (Const := Const) S μ B {encodeClosedFormula φ} := by
  constructor
  · intro htrack ψ hψ
    have hψ' : ψ = encodeClosedFormula φ := by
      simpa using hψ
    subst hψ'
    simpa using htrack
  · intro htrack
    exact htrack (by simp)

theorem beliefDayTracksHierarchicalProbOn_singleton
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (B : BeliefDay Const)
    (φ : ClosedFormula Const) :
    BeliefDayTracksHierarchicalProb (Const := Const) H B φ ↔
      BeliefDayTracksHierarchicalProbOn (Const := Const) H B {encodeClosedFormula φ} := by
  constructor
  · intro htrack ψ hψ
    have hψ' : ψ = encodeClosedFormula φ := by
      simpa using hψ
    subst hψ'
    simpa using htrack
  · intro htrack
    exact htrack (by simp)

theorem beliefDayTracksSentenceProbOn_of_subset
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (B : BeliefDay Const)
    {sample₁ sample₂ : Finset (ClosedFormulaCode Const)}
    (hsub : sample₁ ⊆ sample₂)
    (htrack : BeliefDayTracksSentenceProbOn (Const := Const) S μ B sample₂) :
    BeliefDayTracksSentenceProbOn (Const := Const) S μ B sample₁ := by
  intro φ hφ
  exact htrack (hsub hφ)

theorem beliefDayTracksHierarchicalProbOn_of_subset
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (B : BeliefDay Const)
    {sample₁ sample₂ : Finset (ClosedFormulaCode Const)}
    (hsub : sample₁ ⊆ sample₂)
    (htrack : BeliefDayTracksHierarchicalProbOn (Const := Const) H B sample₂) :
    BeliefDayTracksHierarchicalProbOn (Const := Const) H B sample₁ := by
  intro φ hφ
  exact htrack (hsub hφ)

/-- The constant-one day tracks semantic probability on `⊤`. -/
theorem constantOne_tracks_sentenceProb_top
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (hμ : MeasureTheory.IsProbabilityMeasure μ) :
    BeliefDayTracksSentenceProb (Const := Const) S μ
      (constantDay (Const := Const) Price01.one)
      (.top : ClosedFormula Const) := by
  unfold BeliefDayTracksSentenceProb
  rw [dayQueryStrength_eq_price, probQueryStrength_eq_sentenceProb S μ hμ]
  simp [constantDay, Price01.one, sentenceProb_top_eq_one (S := S) (μ := μ) (hμ := hμ)]

/-- The constant-zero day tracks semantic probability on `⊥`. -/
theorem constantZero_tracks_sentenceProb_bot
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (hμ : MeasureTheory.IsProbabilityMeasure μ) :
    BeliefDayTracksSentenceProb (Const := Const) S μ
      (constantDay (Const := Const) Price01.zero)
      (.bot : ClosedFormula Const) := by
  unfold BeliefDayTracksSentenceProb
  rw [dayQueryStrength_eq_price, probQueryStrength_eq_sentenceProb S μ hμ]
  simp [constantDay, Price01.zero, sentenceProb_bot_eq_zero (S := S) (μ := μ)]

/-- The constant-one day tracks hierarchical semantic probability on `⊤`. -/
theorem constantOne_tracks_hierarchicalProb_top
    (H : HierarchicalState.{u, v, w, x} Base Const) :
    BeliefDayTracksHierarchicalProb (Const := Const) H
      (constantDay (Const := Const) Price01.one)
      (.top : ClosedFormula Const) := by
  unfold BeliefDayTracksHierarchicalProb
  rw [dayQueryStrength_eq_price, hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalSentenceProb_top_eq_one]
  simp [constantDay, Price01.one]

/-- The constant-zero day tracks hierarchical semantic probability on `⊥`. -/
theorem constantZero_tracks_hierarchicalProb_bot
    (H : HierarchicalState.{u, v, w, x} Base Const) :
    BeliefDayTracksHierarchicalProb (Const := Const) H
      (constantDay (Const := Const) Price01.zero)
      (.bot : ClosedFormula Const) := by
  unfold BeliefDayTracksHierarchicalProb
  rw [dayQueryStrength_eq_price, hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalSentenceProb_bot_eq_zero]
  simp [constantDay, Price01.zero]

/-- A process that is eventually exact on a finite sample tracks semantic
probability on that sample, provided the target day already matches the semantic
probabilities there. -/
theorem eventuallyExactOnFiniteSample_implies_eventuallyTracksSentenceProbOn
    (S : ModelSpace.{u, v, w, x} Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (target : BeliefDay Const)
    (sample : Finset (ClosedFormulaCode Const))
    (P : BeliefProcess Const)
    (hexact : EventuallyExactOnFiniteSample (Const := Const) target sample P)
    (htarget : BeliefDayTracksSentenceProbOn (Const := Const) S μ target sample) :
    BeliefProcessEventuallyTracksSentenceProbOn (Const := Const) S μ sample P := by
  rcases hexact with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn φ hφ
  have htargetEq : P n φ = target φ := hN n hn hφ
  exact (dayQueryStrength_ext (Const := Const) (P n) target φ htargetEq).trans (htarget hφ)

/-- Hierarchical variant of the previous exactness-to-tracking theorem. -/
theorem eventuallyExactOnFiniteSample_implies_eventuallyTracksHierarchicalProbOn
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (target : BeliefDay Const)
    (sample : Finset (ClosedFormulaCode Const))
    (P : BeliefProcess Const)
    (hexact : EventuallyExactOnFiniteSample (Const := Const) target sample P)
    (htarget : BeliefDayTracksHierarchicalProbOn (Const := Const) H target sample) :
    BeliefProcessEventuallyTracksHierarchicalProbOn (Const := Const) H sample P := by
  rcases hexact with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn φ hφ
  have htargetEq : P n φ = target φ := hN n hn hφ
  exact (dayQueryStrength_ext (Const := Const) (P n) target φ htargetEq).trans (htarget hφ)

/-- The empirical belief-day construction exactly tracks semantic sentence
probability on every closed HOL formula. -/
theorem empiricalBeliefDay_tracks_empiricalSentenceProb
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (φ : ClosedFormula Const) :
    BeliefDayTracksSentenceProb
      (Const := Const)
      (empiricalModelSpace (Base := Base) (Const := Const) W)
      (PMF.ofMultiset W hW).toMeasure
      (empiricalBeliefDay (Base := Base) (Const := Const) W)
      φ := by
  unfold BeliefDayTracksSentenceProb
  rw [empiricalProbQueryStrength_eq_staticQueryStrength
      (Base := Base) (Const := Const) W hW φ]
  simpa using empiricalDayStrength_eq_staticQueryStrength
    (Base := Base) (Const := Const) W (encodeClosedFormula φ)

/-- The empirical belief-day construction exactly tracks hierarchical semantic
probability through the constant-measure embedding of the empirical sample. -/
theorem empiricalBeliefDay_tracks_empiricalHierarchicalProb
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (φ : ClosedFormula Const) :
    BeliefDayTracksHierarchicalProb
      (Const := Const)
      (HierarchicalState.ofConstantMeasure
        (empiricalModelSpace (Base := Base) (Const := Const) W)
        (PMF.ofMultiset W hW).toMeasure)
      (empiricalBeliefDay (Base := Base) (Const := Const) W)
      φ := by
  unfold BeliefDayTracksHierarchicalProb
  rw [hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb]
  rw [empiricalSentenceProb_eq_staticQueryStrength
      (Base := Base) (Const := Const) W hW φ]
  simpa using empiricalDayStrength_eq_staticQueryStrength
    (Base := Base) (Const := Const) W (encodeClosedFormula φ)

theorem empiricalBeliefDay_tracks_empiricalSentenceProbOn
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (sample : Finset (ClosedFormulaCode Const)) :
    BeliefDayTracksSentenceProbOn
      (Const := Const)
      (empiricalModelSpace (Base := Base) (Const := Const) W)
      (PMF.ofMultiset W hW).toMeasure
      (empiricalBeliefDay (Base := Base) (Const := Const) W)
      sample := by
  intro φ hφ
  simpa using empiricalBeliefDay_tracks_empiricalSentenceProb
    (Base := Base) (Const := Const) W hW (decodeClosedFormula φ)

theorem empiricalBeliefDay_tracks_empiricalHierarchicalProbOn
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (sample : Finset (ClosedFormulaCode Const)) :
    BeliefDayTracksHierarchicalProbOn
      (Const := Const)
      (HierarchicalState.ofConstantMeasure
        (empiricalModelSpace (Base := Base) (Const := Const) W)
        (PMF.ofMultiset W hW).toMeasure)
      (empiricalBeliefDay (Base := Base) (Const := Const) W)
      sample := by
  intro φ hφ
  simpa using empiricalBeliefDay_tracks_empiricalHierarchicalProb
    (Base := Base) (Const := Const) W hW (decodeClosedFormula φ)

end Mettapedia.Logic.HOL.Probabilistic
