import Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge
import Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge
import Mettapedia.Logic.PLNIndefiniteTruthBridge
import Mettapedia.Logic.PLNInferenceRules
import Mettapedia.ProbabilityTheory.HigherOrderProbability.GiryMonad
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

/-!
# Credal Higher-Order HOL Predicate Bridge

The probabilistic bridge assigns a precise Kyburg-flattened strength to a HOL
sentence inside one hierarchical model-space state. This file lifts that
readout to a nonempty family of possible hierarchical states by taking the
lower/upper envelope of the precise strengths.

This is the interval-valued layer needed before full higher-order PLN truth
values: a crisp HOL rule sentence first receives a precise ProbHOL readout in
each completion, then a credal interval across completions.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLCredalBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Probabilistic
open Mettapedia.Logic.HOL.Probabilistic.HierarchicalState
open Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
open Mettapedia.Logic.PLNHigherOrderHOLProbabilisticBridge
open Mettapedia.Logic.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.Logic.PLNFirstOrder
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
open Set
open scoped ENNReal

universe u v w x y z

variable {Base : Type u} {Const : Ty Base → Type v}

private theorem interval_eq_of_bounds_eq {I J : Interval}
    (hl : I.lower = J.lower) (hu : I.upper = J.upper) : I = J := by
  cases I with
  | mk il iu iv =>
    cases J with
    | mk jl ju jv =>
      simp only at hl hu
      subst jl
      subst ju
      rfl

/-- Real-valued precise strength of a closed HOL formula in one hierarchical
state. The underlying ProbHOL value is an `ENNReal`; this view is bounded in
`[0,1]` and is the coordinate used by the real-valued credal interval layer. -/
noncomputable def credalHOLFormulaValue
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) : ℝ :=
  (hierarchicalProbQueryStrength H φ).toReal

theorem credalHOLFormulaValue_nonneg
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    0 ≤ credalHOLFormulaValue H φ :=
  ENNReal.toReal_nonneg

theorem credalHOLFormulaValue_le_one
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    credalHOLFormulaValue H φ ≤ 1 := by
  have hle : hierarchicalProbQueryStrength H φ ≤ 1 := by
    rw [hierarchicalProbQueryStrength_eq_sentenceProb]
    simpa [hierarchicalSentenceProb, HierarchicalState.flattenedModelMeasure] using
      sentenceProb_le_one
        (S := H.baseSpace)
        (μ := H.flattenedModelMeasure)
        (hμ := by
          unfold HierarchicalState.flattenedModelMeasure
          infer_instance)
        (φ := φ)
  simpa [credalHOLFormulaValue] using
    (ENNReal.toReal_mono ENNReal.one_ne_top hle)

theorem hierarchicalProbQueryStrength_le_one
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    hierarchicalProbQueryStrength H φ ≤ 1 := by
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  simpa [hierarchicalSentenceProb, HierarchicalState.flattenedModelMeasure] using
    sentenceProb_le_one
      (S := H.baseSpace)
      (μ := H.flattenedModelMeasure)
      (hμ := by
        unfold HierarchicalState.flattenedModelMeasure
        infer_instance)
      (φ := φ)

theorem credalHOLFormulaValue_mono_of_pointwiseImplies
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (himp : H.baseSpace.PointwiseImplies φ ψ) :
    credalHOLFormulaValue H φ ≤ credalHOLFormulaValue H ψ := by
  unfold credalHOLFormulaValue
  exact
    ENNReal.toReal_mono
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (hierarchicalProbQueryStrength_le_one (Base := Base) (Const := Const) H ψ))
      (hierarchicalProbQueryStrength_mono_of_pointwiseImplies (H := H) himp)

theorem credalHOLFormulaValue_eq_of_pointwiseIff
    (H : HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hiff : H.baseSpace.PointwiseIff φ ψ) :
    credalHOLFormulaValue H φ = credalHOLFormulaValue H ψ := by
  unfold credalHOLFormulaValue
  rw [hierarchicalProbQueryStrength_eq_of_pointwiseIff (H := H) hiff]

/-- Real-valued ProbHOL strength of a negated closed HOL formula is the
complement of the original real-valued strength. This is the formula-level
bridge needed before product/noisy-OR De Morgan laws can speak about genuine
HOL negation rather than only numeric complements. -/
theorem credalHOLFormulaValue_not_eq_one_sub
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    credalHOLFormulaValue H (.not φ) = 1 - credalHOLFormulaValue H φ := by
  unfold credalHOLFormulaValue
  rw [hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalProbQueryStrength_eq_sentenceProb,
    hierarchicalSentenceProb_not_eq_one_sub]
  have hle : hierarchicalSentenceProb H φ ≤ 1 := by
    simpa [hierarchicalSentenceProb, HierarchicalState.flattenedModelMeasure] using
      sentenceProb_le_one
        (S := H.baseSpace)
        (μ := H.flattenedModelMeasure)
        (hμ := by
          unfold HierarchicalState.flattenedModelMeasure
          infer_instance)
        (φ := φ)
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]
  simp

theorem credalHOLFormulaValue_bddBelow
    {ι : Type y}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    BddBelow (Set.range fun i => credalHOLFormulaValue (Hs i) φ) :=
  ⟨0, by
    rintro r ⟨i, rfl⟩
    exact credalHOLFormulaValue_nonneg (Hs i) φ⟩

theorem credalHOLFormulaValue_bddAbove
    {ι : Type y}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    BddAbove (Set.range fun i => credalHOLFormulaValue (Hs i) φ) :=
  ⟨1, by
    rintro r ⟨i, rfl⟩
    exact credalHOLFormulaValue_le_one (Hs i) φ⟩

/-- Credal interval for a closed HOL formula over a nonempty family of
hierarchical model-space completions. -/
noncomputable def credalHOLFormulaInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ => credalHOLFormulaValue (Hs i) φ)
    (hBddBelow := fun _ => credalHOLFormulaValue_bddBelow Hs φ)
    (hBddAbove := fun _ => credalHOLFormulaValue_bddAbove Hs φ)
    ()

theorem credalHOLFormulaInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    0 ≤ (credalHOLFormulaInterval Hs φ).lower := by
  unfold credalHOLFormulaInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty (fun i => credalHOLFormulaValue (Hs i) φ)
  · rintro r ⟨i, rfl⟩
    exact credalHOLFormulaValue_nonneg (Hs i) φ

theorem credalHOLFormulaInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    (credalHOLFormulaInterval Hs φ).upper ≤ 1 := by
  unfold credalHOLFormulaInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty (fun i => credalHOLFormulaValue (Hs i) φ)
  · rintro r ⟨i, rfl⟩
    exact credalHOLFormulaValue_le_one (Hs i) φ

/-- Negating a HOL formula reverses the endpoints of its credal interval. The
lower endpoint of `¬φ` is the complement of the upper endpoint of `φ`. -/
theorem credalHOLFormulaInterval_not_lower_eq_one_sub_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    (credalHOLFormulaInterval Hs (.not φ)).lower =
      1 - (credalHOLFormulaInterval Hs φ).upper := by
  unfold credalHOLFormulaInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_antisymm
  · have hsup_le :
        sSup (Set.range fun i => credalHOLFormulaValue (Hs i) φ) ≤
          1 - sInf (Set.range fun i =>
            credalHOLFormulaValue (Hs i) (.not φ)) := by
      apply csSup_le
      · exact Set.range_nonempty (fun i => credalHOLFormulaValue (Hs i) φ)
      · rintro r ⟨i, rfl⟩
        have hnotLower :
            sInf (Set.range fun i =>
              credalHOLFormulaValue (Hs i) (.not φ)) ≤
                credalHOLFormulaValue (Hs i) (.not φ) :=
          csInf_le
            (credalHOLFormulaValue_bddBelow Hs (.not φ)) ⟨i, rfl⟩
        rw [credalHOLFormulaValue_not_eq_one_sub] at hnotLower
        linarith
    linarith
  · apply le_csInf
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaValue (Hs i) (.not φ)
    · rintro r ⟨i, rfl⟩
      have hle :
          credalHOLFormulaValue (Hs i) φ ≤
            sSup (Set.range fun i => credalHOLFormulaValue (Hs i) φ) :=
        le_csSup (credalHOLFormulaValue_bddAbove Hs φ) ⟨i, rfl⟩
      change
        1 - sSup (Set.range fun i => credalHOLFormulaValue (Hs i) φ) ≤
          credalHOLFormulaValue (Hs i) (.not φ)
      rw [credalHOLFormulaValue_not_eq_one_sub]
      linarith

/-- Negating a HOL formula reverses the endpoints of its credal interval. The
upper endpoint of `¬φ` is the complement of the lower endpoint of `φ`. -/
theorem credalHOLFormulaInterval_not_upper_eq_one_sub_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    (credalHOLFormulaInterval Hs (.not φ)).upper =
      1 - (credalHOLFormulaInterval Hs φ).lower := by
  unfold credalHOLFormulaInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaValue (Hs i) (.not φ)
    · rintro r ⟨i, rfl⟩
      have hlow :
          sInf (Set.range fun i => credalHOLFormulaValue (Hs i) φ) ≤
            credalHOLFormulaValue (Hs i) φ :=
        csInf_le (credalHOLFormulaValue_bddBelow Hs φ) ⟨i, rfl⟩
      change
        credalHOLFormulaValue (Hs i) (.not φ) ≤
          1 - sInf (Set.range fun i => credalHOLFormulaValue (Hs i) φ)
      rw [credalHOLFormulaValue_not_eq_one_sub]
      linarith
  · have hle :
        1 - sSup (Set.range fun i =>
          credalHOLFormulaValue (Hs i) (.not φ)) ≤
            sInf (Set.range fun i => credalHOLFormulaValue (Hs i) φ) := by
      apply le_csInf
      · exact Set.range_nonempty fun i => credalHOLFormulaValue (Hs i) φ
      · rintro r ⟨i, rfl⟩
        have hnot_le :
            credalHOLFormulaValue (Hs i) (.not φ) ≤
              sSup (Set.range fun i =>
                credalHOLFormulaValue (Hs i) (.not φ)) :=
          le_csSup (credalHOLFormulaValue_bddAbove Hs (.not φ)) ⟨i, rfl⟩
        rw [credalHOLFormulaValue_not_eq_one_sub] at hnot_le
        linarith
    linarith

/-! ## Packaging HO credal intervals as PLN indefinite truth values -/

/-- Package a higher-order HOL credal interval as the live PLN
`IndefiniteTruthValue` record. The interval endpoints come from the nonempty
family of hierarchical HOL states; the credibility coordinate remains an
explicit evidence-concentration input, as in the rest of the PLN truth tower. -/
noncomputable def credalHOLFormulaITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalHOLFormulaInterval Hs φ
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalHOLFormulaInterval_lower_nonneg Hs φ)
    (credalHOLFormulaInterval_upper_le_one Hs φ)
    hcred

@[simp] theorem credalHOLFormulaITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaITV Hs φ credibility hcred).lower =
      (credalHOLFormulaInterval Hs φ).lower := by
  simp [credalHOLFormulaITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaITV Hs φ credibility hcred).upper =
      (credalHOLFormulaInterval Hs φ).upper := by
  simp [credalHOLFormulaITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaITV_credibility
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaITV Hs φ credibility hcred).credibility =
      credibility := by
  simp [credalHOLFormulaITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaITV_width
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaITV Hs φ credibility hcred).width =
      (credalHOLFormulaInterval Hs φ).width := by
  simp [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    Interval.width]

theorem credalHOLFormulaInterval_lower_mono_of_pointwise_value_le
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hVal :
      ∀ i, credalHOLFormulaValue (Hs i) φ ≤ credalHOLFormulaValue (Hs i) ψ) :
    (credalHOLFormulaInterval Hs φ).lower ≤
      (credalHOLFormulaInterval Hs ψ).lower := by
  unfold credalHOLFormulaInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty (fun i => credalHOLFormulaValue (Hs i) ψ)
  · rintro r ⟨i, rfl⟩
    exact le_trans
      (csInf_le (credalHOLFormulaValue_bddBelow Hs φ) ⟨i, rfl⟩)
      (hVal i)

theorem credalHOLFormulaInterval_upper_mono_of_pointwise_value_le
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hVal :
      ∀ i, credalHOLFormulaValue (Hs i) φ ≤ credalHOLFormulaValue (Hs i) ψ) :
    (credalHOLFormulaInterval Hs φ).upper ≤
      (credalHOLFormulaInterval Hs ψ).upper := by
  unfold credalHOLFormulaInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty (fun i => credalHOLFormulaValue (Hs i) φ)
  · rintro r ⟨i, rfl⟩
    exact le_trans (hVal i)
      (le_csSup (credalHOLFormulaValue_bddAbove Hs ψ) ⟨i, rfl⟩)

theorem credalHOLFormulaInterval_mono_of_pointwise_value_le
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hVal :
      ∀ i, credalHOLFormulaValue (Hs i) φ ≤ credalHOLFormulaValue (Hs i) ψ) :
    (credalHOLFormulaInterval Hs φ).lower ≤
        (credalHOLFormulaInterval Hs ψ).lower ∧
      (credalHOLFormulaInterval Hs φ).upper ≤
        (credalHOLFormulaInterval Hs ψ).upper :=
  ⟨credalHOLFormulaInterval_lower_mono_of_pointwise_value_le Hs hVal,
   credalHOLFormulaInterval_upper_mono_of_pointwise_value_le Hs hVal⟩

theorem credalHOLFormulaInterval_mono_of_pointwiseImplies
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (himp : ∀ i, (Hs i).baseSpace.PointwiseImplies φ ψ) :
    (credalHOLFormulaInterval Hs φ).lower ≤
        (credalHOLFormulaInterval Hs ψ).lower ∧
      (credalHOLFormulaInterval Hs φ).upper ≤
        (credalHOLFormulaInterval Hs ψ).upper :=
  credalHOLFormulaInterval_mono_of_pointwise_value_le Hs
    (fun i => credalHOLFormulaValue_mono_of_pointwiseImplies
      (Base := Base) (Const := Const) (Hs i) (himp i))

theorem credalHOLFormulaITV_mono_of_pointwiseImplies
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (himp : ∀ i, (Hs i).baseSpace.PointwiseImplies φ ψ) :
    (credalHOLFormulaITV Hs φ credibility hcred).lower ≤
        (credalHOLFormulaITV Hs ψ credibility hcred).lower ∧
      (credalHOLFormulaITV Hs φ credibility hcred).upper ≤
        (credalHOLFormulaITV Hs ψ credibility hcred).upper := by
  simpa using
    (credalHOLFormulaInterval_mono_of_pointwiseImplies
      (Base := Base) (Const := Const) Hs himp)

/-! ## Same-completion binary rule envelopes -/

/-- A binary real-valued rule function is monotone on the probability unit
square. This is the right hypothesis for PLN truth functions, whose algebraic
laws are meant on valid strength coordinates rather than all of `ℝ × ℝ`. -/
def BinaryRuleMonotoneOnUnit (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂ : ℝ⦄,
    0 ≤ a₁ → a₂ ≤ 1 → 0 ≤ b₁ → b₂ ≤ 1 →
      a₁ ≤ a₂ → b₁ ≤ b₂ → f a₁ b₁ ≤ f a₂ b₂

/-- Pointwise value of a binary PLN rule function applied to two closed HOL
formula strengths inside one hierarchical state. -/
noncomputable def credalHOLFormulaBinaryRuleValue
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ) : ℝ :=
  f (credalHOLFormulaValue H φ) (credalHOLFormulaValue H ψ)

theorem credalHOLFormulaBinaryRuleValue_bddBelow
    {ι : Type y}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f) :
    BddBelow
      (Set.range fun i =>
        credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f) :=
  ⟨f 0 0, by
    rintro r ⟨i, rfl⟩
    exact hmono
      (by norm_num)
      (credalHOLFormulaValue_le_one (Hs i) φ)
      (by norm_num)
      (credalHOLFormulaValue_le_one (Hs i) ψ)
      (credalHOLFormulaValue_nonneg (Hs i) φ)
      (credalHOLFormulaValue_nonneg (Hs i) ψ)⟩

theorem credalHOLFormulaBinaryRuleValue_bddAbove
    {ι : Type y}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f) :
    BddAbove
      (Set.range fun i =>
        credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f) :=
  ⟨f 1 1, by
    rintro r ⟨i, rfl⟩
    exact hmono
      (credalHOLFormulaValue_nonneg (Hs i) φ)
      (by norm_num)
      (credalHOLFormulaValue_nonneg (Hs i) ψ)
      (by norm_num)
      (credalHOLFormulaValue_le_one (Hs i) φ)
      (credalHOLFormulaValue_le_one (Hs i) ψ)⟩

/-- Same-completion binary-rule interval: apply the rule function to the two
precise strengths inside each hierarchical state, then take the lower/upper
envelope across completions. This is the theorem-level core of the Kyburg-style
"combine after flattening per completion, then envelope" discipline. -/
noncomputable def credalHOLFormulaBinaryRuleInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ => credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f)
    (hBddBelow := fun _ =>
      credalHOLFormulaBinaryRuleValue_bddBelow Hs φ ψ f hmono)
    (hBddAbove := fun _ =>
      credalHOLFormulaBinaryRuleValue_bddAbove Hs φ ψ f hmono)
    ()

/-- Independent-envelope hull of a binary rule: apply the rule to the lower
endpoints and upper endpoints of the two marginal formula intervals. The
same-completion rule interval is contained in this hull. -/
noncomputable def credalHOLFormulaBinaryRuleHull
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f) : Interval where
  lower :=
    f (credalHOLFormulaInterval Hs φ).lower
      (credalHOLFormulaInterval Hs ψ).lower
  upper :=
    f (credalHOLFormulaInterval Hs φ).upper
      (credalHOLFormulaInterval Hs ψ).upper
  valid := by
    exact hmono
      (credalHOLFormulaInterval_lower_nonneg Hs φ)
      (credalHOLFormulaInterval_upper_le_one Hs φ)
      (credalHOLFormulaInterval_lower_nonneg Hs ψ)
      (credalHOLFormulaInterval_upper_le_one Hs ψ)
      (credalHOLFormulaInterval Hs φ).valid
      (credalHOLFormulaInterval Hs ψ).valid

theorem credalHOLFormulaBinaryRuleInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f)
    (h00 : 0 ≤ f 0 0) :
    0 ≤ (credalHOLFormulaBinaryRuleInterval Hs φ ψ f hmono).lower := by
  unfold credalHOLFormulaBinaryRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_trans h00
    (le_csInf
      (Set.range_nonempty fun i =>
        credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f)
      (by
        rintro r ⟨i, rfl⟩
        exact hmono
          (by norm_num)
          (credalHOLFormulaValue_le_one (Hs i) φ)
          (by norm_num)
          (credalHOLFormulaValue_le_one (Hs i) ψ)
          (credalHOLFormulaValue_nonneg (Hs i) φ)
          (credalHOLFormulaValue_nonneg (Hs i) ψ)))

theorem credalHOLFormulaBinaryRuleInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f)
    (h11 : f 1 1 ≤ 1) :
    (credalHOLFormulaBinaryRuleInterval Hs φ ψ f hmono).upper ≤ 1 := by
  unfold credalHOLFormulaBinaryRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_trans
    (csSup_le
      (Set.range_nonempty fun i =>
        credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f)
      (by
        rintro r ⟨i, rfl⟩
        exact hmono
          (credalHOLFormulaValue_nonneg (Hs i) φ)
          (by norm_num)
          (credalHOLFormulaValue_nonneg (Hs i) ψ)
          (by norm_num)
          (credalHOLFormulaValue_le_one (Hs i) φ)
          (credalHOLFormulaValue_le_one (Hs i) ψ)))
    h11

theorem credalHOLFormulaBinaryRuleInterval_containedIn_hull
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f) :
    (credalHOLFormulaBinaryRuleInterval Hs φ ψ f hmono).containedIn
      (credalHOLFormulaBinaryRuleHull Hs φ ψ f hmono) := by
  unfold Interval.containedIn credalHOLFormulaBinaryRuleInterval
    credalHOLFormulaBinaryRuleHull
  dsimp [IntervalAddSemantics.intervalOf]
  constructor
  · apply le_csInf
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f
    · rintro r ⟨i, rfl⟩
      exact hmono
        (credalHOLFormulaInterval_lower_nonneg Hs φ)
        (credalHOLFormulaValue_le_one (Hs i) φ)
        (credalHOLFormulaInterval_lower_nonneg Hs ψ)
        (credalHOLFormulaValue_le_one (Hs i) ψ)
        (csInf_le (credalHOLFormulaValue_bddBelow Hs φ) ⟨i, rfl⟩)
        (csInf_le (credalHOLFormulaValue_bddBelow Hs ψ) ⟨i, rfl⟩)
  · apply csSup_le
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaBinaryRuleValue (Hs i) φ ψ f
    · rintro r ⟨i, rfl⟩
      exact hmono
        (credalHOLFormulaValue_nonneg (Hs i) φ)
        (credalHOLFormulaInterval_upper_le_one Hs φ)
        (credalHOLFormulaValue_nonneg (Hs i) ψ)
        (credalHOLFormulaInterval_upper_le_one Hs ψ)
        (le_csSup (credalHOLFormulaValue_bddAbove Hs φ) ⟨i, rfl⟩)
        (le_csSup (credalHOLFormulaValue_bddAbove Hs ψ) ⟨i, rfl⟩)

/-- PLN `ITV` view of a same-completion binary rule interval. This is a
generic packaging point for later HO rule families: the rule supplies the
pointwise combination formula, and this bridge supplies the model-class
lower/upper envelope plus explicit credibility coordinate. -/
noncomputable def credalHOLFormulaBinaryRuleITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f)
    (h00 : 0 ≤ f 0 0)
    (h11 : f 1 1 ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalHOLFormulaBinaryRuleInterval Hs φ ψ f hmono
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalHOLFormulaBinaryRuleInterval_lower_nonneg Hs φ ψ f hmono h00)
    (credalHOLFormulaBinaryRuleInterval_upper_le_one Hs φ ψ f hmono h11)
    hcred

@[simp] theorem credalHOLFormulaBinaryRuleITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f)
    (h00 : 0 ≤ f 0 0)
    (h11 : f 1 1 ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaBinaryRuleITV Hs φ ψ f hmono h00 h11
      credibility hcred).lower =
      (credalHOLFormulaBinaryRuleInterval Hs φ ψ f hmono).lower := by
  simp [credalHOLFormulaBinaryRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaBinaryRuleITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f)
    (h00 : 0 ≤ f 0 0)
    (h11 : f 1 1 ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaBinaryRuleITV Hs φ ψ f hmono h00 h11
      credibility hcred).upper =
      (credalHOLFormulaBinaryRuleInterval Hs φ ψ f hmono).upper := by
  simp [credalHOLFormulaBinaryRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaBinaryRuleITV_credibility
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ ψ : ClosedFormula Const)
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f)
    (h00 : 0 ≤ f 0 0)
    (h11 : f 1 1 ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaBinaryRuleITV Hs φ ψ f hmono h00 h11
      credibility hcred).credibility = credibility := by
  simp [credalHOLFormulaBinaryRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

/-! ## Same-completion finite rule envelopes -/

/-- A finite real-valued rule function is monotone on the probability unit
cube. This is the indexed version of `BinaryRuleMonotoneOnUnit`, used for
multi-premise PLN rules and Kyburg-style multi-join envelopes. -/
def FiniteRuleMonotoneOnUnit {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ⦃a b : Fin n → ℝ⦄,
    (∀ k, 0 ≤ a k) → (∀ k, b k ≤ 1) →
      (∀ k, a k ≤ b k) → F a ≤ F b

/-- A finite real-valued rule function maps the probability unit cube back
into the probability unit interval. Some PLN rules, notably modus ponens with
a background default, are bounded without being globally monotone in every
coordinate. Those rules can still receive same-completion credal envelopes,
but they do not automatically get independent-endpoint hull theorems. -/
def FiniteRuleMapsUnitToUnit {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ a, (∀ k, 0 ≤ a k) → (∀ k, a k ≤ 1) → F a ∈ Set.Icc (0 : ℝ) 1

/-- A monotone finite rule with valid endpoint values maps the whole
probability unit cube into the probability unit interval. This is the generic
boundedness fact behind product, noisy-OR, and other globally monotone
multi-join operators. -/
theorem finiteRuleMapsUnitToUnit_of_monotone_endpoints {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => (0 : ℝ)))
    (hone : F (fun _ => (1 : ℝ)) ≤ 1) :
    FiniteRuleMapsUnitToUnit F := by
  intro a ha_nonneg ha_le_one
  constructor
  · have hlow : F (fun _ : Fin n => (0 : ℝ)) ≤ F a := by
      exact hmono (by intro _k; norm_num) ha_le_one ha_nonneg
    exact le_trans hzero hlow
  · have hhigh : F a ≤ F (fun _ : Fin n => (1 : ℝ)) := by
      exact hmono ha_nonneg (by intro _k; norm_num) ha_le_one
    exact le_trans hhigh hone

/-- Pointwise value of an indexed PLN rule function applied to finitely many
closed HOL formula strengths inside one hierarchical state. -/
noncomputable def credalHOLFormulaFiniteRuleValue
    {n : ℕ}
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ) : ℝ :=
  F (fun k => credalHOLFormulaValue H (φ k))

/-- The predictive measure inside a hierarchical HOL state is exactly the
Giry/Kyburg join of the state-space measure over component model measures. -/
theorem hierarchicalState_flattenedModelMeasure_eq_kyburg_join
    (H : HierarchicalState.{u, v, w, x} Base Const) :
    H.flattenedModelMeasure =
      MeasureTheory.Measure.join (H.pd.mixingMeasure.map H.pd.kernel) := by
  simpa [HierarchicalState.flattenedModelMeasure] using
    Mettapedia.ProbabilityTheory.HigherOrderProbability.flatten_is_join H.pd

/-- Formula strength in one hierarchical completion is sentence probability
under the Kyburg/Giry joined predictive measure, converted to `ℝ`. -/
theorem credalHOLFormulaValue_eq_toReal_sentenceProb_kyburg_join
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const) :
    credalHOLFormulaValue H φ =
      (sentenceProb H.baseSpace
        (MeasureTheory.Measure.join (H.pd.mixingMeasure.map H.pd.kernel))
        φ).toReal := by
  unfold credalHOLFormulaValue
  rw [hierarchicalProbQueryStrength_eq_sentenceProb]
  unfold hierarchicalSentenceProb
  rw [hierarchicalState_flattenedModelMeasure_eq_kyburg_join]

/-- Same-completion finite HO rule values are ordinary PLN finite-rule
applications to Kyburg/Giry-joined sentence probabilities in that completion.

This is the theoremic bridge between the old Kyburg flattening lane and the
live HO-PLN multi-join surface: product, noisy-OR, and later rule operators all
consume the flattened predictive measure of each hierarchical state before the
credal envelope is taken across states. -/
theorem credalHOLFormulaFiniteRuleValue_eq_rule_on_kyburg_join
    {n : ℕ}
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ) :
    credalHOLFormulaFiniteRuleValue H φ F =
      F (fun k =>
        (sentenceProb H.baseSpace
          (MeasureTheory.Measure.join (H.pd.mixingMeasure.map H.pd.kernel))
          (φ k)).toReal) := by
  simp [credalHOLFormulaFiniteRuleValue,
    credalHOLFormulaValue_eq_toReal_sentenceProb_kyburg_join]

/-- View a binary PLN rule function as a two-input indexed finite rule. -/
noncomputable def binaryRuleAsFinite2
    (f : ℝ → ℝ → ℝ) : (Fin 2 → ℝ) → ℝ :=
  fun xs => f (xs 0) (xs 1)

theorem binaryRuleAsFinite2_monotone_on_unit
    (f : ℝ → ℝ → ℝ)
    (hmono : BinaryRuleMonotoneOnUnit f) :
    FiniteRuleMonotoneOnUnit (binaryRuleAsFinite2 f) := by
  intro a b ha_nonneg hb_le_one hle
  exact hmono
    (ha_nonneg 0)
    (hb_le_one 0)
    (ha_nonneg 1)
    (hb_le_one 1)
    (hle 0)
    (hle 1)

@[simp] theorem credalHOLFormulaFiniteRuleValue_binaryRuleAsFinite2
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin 2 → ClosedFormula Const)
    (f : ℝ → ℝ → ℝ) :
    credalHOLFormulaFiniteRuleValue H φ (binaryRuleAsFinite2 f) =
      credalHOLFormulaBinaryRuleValue H (φ 0) (φ 1) f := rfl

/-- Concrete product multi-join over a finite vector of strength coordinates.

This is the first named n-ary rule operator above the generic finite-rule
surface: it acts like the same-completion product/conjunction fold on
probability-strength inputs. -/
noncomputable def productMultiJoin {n : ℕ} (xs : Fin n → ℝ) : ℝ :=
  ∏ j, xs j

theorem productMultiJoin_monotone_on_unit {n : ℕ} :
    FiniteRuleMonotoneOnUnit (@productMultiJoin n) := by
  intro a b ha_nonneg _hb_le_one hle
  unfold productMultiJoin
  exact Finset.prod_le_prod (fun j _hj => ha_nonneg j) (fun j _hj => hle j)

theorem productMultiJoin_zero_nonneg {n : ℕ} :
    0 ≤ productMultiJoin (n := n) (fun _ => (0 : ℝ)) := by
  unfold productMultiJoin
  exact Finset.prod_nonneg (fun _j _hj => by norm_num)

theorem productMultiJoin_one_le_one {n : ℕ} :
    productMultiJoin (n := n) (fun _ => (1 : ℝ)) ≤ 1 := by
  simp [productMultiJoin]

theorem productMultiJoin_mapsUnitToUnit {n : ℕ} :
    FiniteRuleMapsUnitToUnit (@productMultiJoin n) :=
  finiteRuleMapsUnitToUnit_of_monotone_endpoints
    productMultiJoin_monotone_on_unit
    productMultiJoin_zero_nonneg
    productMultiJoin_one_le_one

@[simp] theorem productMultiJoin_zero_arity
    (xs : Fin 0 → ℝ) :
    productMultiJoin xs = 1 := by
  simp [productMultiJoin]

@[simp] theorem productMultiJoin_one_arity
    (xs : Fin 1 → ℝ) :
    productMultiJoin xs = xs 0 := by
  simp [productMultiJoin]

@[simp] theorem productMultiJoin_two_arity
    (xs : Fin 2 → ℝ) :
    productMultiJoin xs = xs 0 * xs 1 := by
  simp [productMultiJoin]

/-- Concrete noisy-OR multi-join over a finite vector of strength
coordinates.

This is the n-ary independent-cause / fuzzy-OR companion to
`productMultiJoin`: it combines premise strengths as
`1 - ∏ j, (1 - xs j)`. -/
noncomputable def noisyOrMultiJoin {n : ℕ} (xs : Fin n → ℝ) : ℝ :=
  1 - ∏ j, (1 - xs j)

theorem noisyOrMultiJoin_monotone_on_unit {n : ℕ} :
    FiniteRuleMonotoneOnUnit (@noisyOrMultiJoin n) := by
  intro a b _ha_nonneg hb_le_one hle
  unfold noisyOrMultiJoin
  have hprod : ∏ j, (1 - b j) ≤ ∏ j, (1 - a j) := by
    exact Finset.prod_le_prod
      (fun j _hj => sub_nonneg.mpr (hb_le_one j))
      (fun j _hj => sub_le_sub_left (hle j) 1)
  linarith

theorem noisyOrMultiJoin_zero_nonneg {n : ℕ} :
    0 ≤ noisyOrMultiJoin (n := n) (fun _ => (0 : ℝ)) := by
  simp [noisyOrMultiJoin]

theorem noisyOrMultiJoin_one_le_one {n : ℕ} :
    noisyOrMultiJoin (n := n) (fun _ => (1 : ℝ)) ≤ 1 := by
  unfold noisyOrMultiJoin
  have hnonneg : 0 ≤ ∏ j : Fin n, (1 - (1 : ℝ)) := by
    exact Finset.prod_nonneg (fun _j _hj => by norm_num)
  linarith

theorem noisyOrMultiJoin_mapsUnitToUnit {n : ℕ} :
    FiniteRuleMapsUnitToUnit (@noisyOrMultiJoin n) :=
  finiteRuleMapsUnitToUnit_of_monotone_endpoints
    noisyOrMultiJoin_monotone_on_unit
    noisyOrMultiJoin_zero_nonneg
    noisyOrMultiJoin_one_le_one

@[simp] theorem noisyOrMultiJoin_zero_arity
    (xs : Fin 0 → ℝ) :
    noisyOrMultiJoin xs = 0 := by
  simp [noisyOrMultiJoin]

@[simp] theorem noisyOrMultiJoin_one_arity
    (xs : Fin 1 → ℝ) :
    noisyOrMultiJoin xs = xs 0 := by
  simp [noisyOrMultiJoin]

@[simp] theorem noisyOrMultiJoin_two_arity
    (xs : Fin 2 → ℝ) :
    noisyOrMultiJoin xs = xs 0 + xs 1 - xs 0 * xs 1 := by
  simp [noisyOrMultiJoin]
  ring

/-- Noisy-OR is the product multi-join of complement coordinates, followed by
outer complement. This is the basic Boolean duality law for the named finite
multi-join operators. -/
theorem noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl {n : ℕ}
    (xs : Fin n → ℝ) :
    noisyOrMultiJoin xs =
      1 - productMultiJoin (fun j => 1 - xs j) := by
  rfl

/-- Complement of noisy-OR is product of complements. -/
theorem one_sub_noisyOrMultiJoin_eq_productMultiJoin_compl {n : ℕ}
    (xs : Fin n → ℝ) :
    1 - noisyOrMultiJoin xs =
      productMultiJoin (fun j => 1 - xs j) := by
  rw [noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]
  ring

/-- Product of complements and noisy-OR add to certainty. -/
theorem productMultiJoin_compl_add_noisyOrMultiJoin {n : ℕ}
    (xs : Fin n → ℝ) :
    productMultiJoin (fun j => 1 - xs j) + noisyOrMultiJoin xs = 1 := by
  rw [noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]
  ring

/-- Applying noisy-OR to complement coordinates is the outer complement of
product multi-join. -/
theorem noisyOrMultiJoin_compl_eq_one_sub_productMultiJoin {n : ℕ}
    (xs : Fin n → ℝ) :
    noisyOrMultiJoin (fun j => 1 - xs j) =
      1 - productMultiJoin xs := by
  rw [noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]
  simp [productMultiJoin]

theorem credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl
    {n : ℕ}
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    credalHOLFormulaFiniteRuleValue H φ (@noisyOrMultiJoin n) =
      1 - productMultiJoin
        (fun k => 1 - credalHOLFormulaValue H (φ k)) := by
  simp [credalHOLFormulaFiniteRuleValue,
    noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]

/-- Formula-level noisy-OR is the complement of product applied to the actual
negated HOL formulas, not merely to numeric complements. -/
theorem credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_not
    {n : ℕ}
    (H : HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    credalHOLFormulaFiniteRuleValue H φ (@noisyOrMultiJoin n) =
      1 -
        credalHOLFormulaFiniteRuleValue H
          (fun k => (.not (φ k) : ClosedFormula Const))
          (@productMultiJoin n) := by
  rw [credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl]
  simp [credalHOLFormulaFiniteRuleValue, credalHOLFormulaValue_not_eq_one_sub]

/-- PLN's `2inh2sim` rule is a valid monotone binary rule on strength
coordinates. This exposes the first rule-specific consumer of the generic
same-completion HO rule envelope. -/
theorem twoInh2Sim_binaryRuleMonotoneOnUnit :
    BinaryRuleMonotoneOnUnit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim := by
  intro a₁ a₂ b₁ b₂ ha₁_nonneg ha₂_le_one hb₁_nonneg hb₂_le_one ha hb
  exact Mettapedia.Logic.PLNInferenceRules.twoInh2Sim_mono_on_unit
    ha₁_nonneg ha₂_le_one hb₁_nonneg hb₂_le_one ha hb

theorem twoInh2Sim_zero_zero_nonneg :
    0 ≤ Mettapedia.Logic.PLNInferenceRules.twoInh2Sim 0 0 := by
  norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

theorem twoInh2Sim_one_one_le_one :
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim 1 1 ≤ 1 := by
  norm_num [Mettapedia.Logic.PLNInferenceRules.twoInh2Sim]

/-- View PLN modus ponens with a fixed background/default parameter as a
two-input indexed rule: input `0` is the implication strength, input `1` is the
premise strength. -/
noncomputable def modusPonensAsFinite2
    (c : ℝ) : (Fin 2 → ℝ) → ℝ :=
  fun xs => Mettapedia.Logic.PLNInferenceRules.modusPonens (xs 0) (xs 1) c

theorem modusPonensAsFinite2_mapsUnitToUnit
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    FiniteRuleMapsUnitToUnit (modusPonensAsFinite2 c) := by
  intro xs hnonneg hle
  exact
    Mettapedia.Logic.PLNInferenceRules.modusPonens_mem_unit
      (xs 0) (xs 1) c
      ⟨hnonneg 0, hle 0⟩
      ⟨hnonneg 1, hle 1⟩
      hc

/-- View PLN symmetric modus ponens with a fixed background/default parameter
as a two-input indexed rule: input `0` is predicate similarity, input `1` is
the premise strength. -/
noncomputable def symmetricModusPonensAsFinite2
    (c : ℝ) : (Fin 2 → ℝ) → ℝ :=
  fun xs =>
    Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens
      (xs 0) (xs 1) c

theorem symmetricModusPonensAsFinite2_mapsUnitToUnit
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 0.5) :
    FiniteRuleMapsUnitToUnit (symmetricModusPonensAsFinite2 c) := by
  intro xs hnonneg hle
  exact
    Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens_mem_unit
      (xs 0) (xs 1) c
      ⟨hnonneg 0, hle 0⟩
      ⟨hnonneg 1, hle 1⟩
      hc

/-- View PLN `sim2inh` as a three-input indexed rule: input `0` is similarity,
input `1` is the source term strength, and input `2` is the target term
strength. Unlike `2inh2sim`, this rule is not valid on the whole unit cube:
it needs the source strength to be positive and the target strength to be no
larger than the source strength. -/
noncomputable def sim2inhAsFinite3 : (Fin 3 → ℝ) → ℝ :=
  fun xs =>
    Mettapedia.Logic.PLNInferenceRules.sim2inh
      (xs 0) (xs 1) (xs 2)

theorem sim2inhAsFinite3_mapsConstrainedToUnit
    (xs : Fin 3 → ℝ)
    (hnonneg : ∀ j, 0 ≤ xs j)
    (hle : ∀ j, xs j ≤ 1)
    (hSource_pos : 0 < xs 1)
    (hTarget_le_source : xs 2 ≤ xs 1) :
    sim2inhAsFinite3 xs ∈ Set.Icc (0 : ℝ) 1 := by
  exact
    Mettapedia.Logic.PLNInferenceRules.sim2inh_mem_unit
      (xs 0) (xs 1) (xs 2)
      ⟨hnonneg 0, hle 0⟩
      ⟨hSource_pos, hle 1⟩
      ⟨hnonneg 2, hle 2⟩
      hTarget_le_source

theorem credalHOLFormulaFiniteRuleValue_bddBelow
    {ι : Type y} {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) :
    BddBelow
      (Set.range fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ F) :=
  ⟨F (fun _ => 0), by
    rintro r ⟨i, rfl⟩
    exact hmono
      (fun _ => by norm_num)
      (fun k => credalHOLFormulaValue_le_one (Hs i) (φ k))
      (fun k => credalHOLFormulaValue_nonneg (Hs i) (φ k))⟩

theorem credalHOLFormulaFiniteRuleValue_bddAbove
    {ι : Type y} {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) :
    BddAbove
      (Set.range fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ F) :=
  ⟨F (fun _ => 1), by
    rintro r ⟨i, rfl⟩
    exact hmono
      (fun k => credalHOLFormulaValue_nonneg (Hs i) (φ k))
      (fun _ => by norm_num)
      (fun k => credalHOLFormulaValue_le_one (Hs i) (φ k))⟩

/-- Same-completion finite-rule interval: apply the indexed rule to all
premise strengths inside each hierarchical completion, then take the envelope
across completions. This is the finite multi-join skeleton; rule-specific PLN
formulas plug in as concrete monotone `F`s. -/
noncomputable def credalHOLFormulaFiniteRuleInterval
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ => credalHOLFormulaFiniteRuleValue (Hs i) φ F)
    (hBddBelow := fun _ =>
      credalHOLFormulaFiniteRuleValue_bddBelow Hs φ F hmono)
    (hBddAbove := fun _ =>
      credalHOLFormulaFiniteRuleValue_bddAbove Hs φ F hmono)
    ()

/-- Independent-envelope hull of an indexed finite rule. The same-completion
finite-rule interval is contained in this hull. -/
noncomputable def credalHOLFormulaFiniteRuleHull
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) : Interval where
  lower := F (fun k => (credalHOLFormulaInterval Hs (φ k)).lower)
  upper := F (fun k => (credalHOLFormulaInterval Hs (φ k)).upper)
  valid := by
    exact hmono
      (fun k => credalHOLFormulaInterval_lower_nonneg Hs (φ k))
      (fun k => credalHOLFormulaInterval_upper_le_one Hs (φ k))
      (fun k => (credalHOLFormulaInterval Hs (φ k)).valid)

theorem credalHOLFormulaFiniteRuleInterval_lower_nonneg
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0)) :
    0 ≤ (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).lower := by
  unfold credalHOLFormulaFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_trans hzero
    (le_csInf
      (Set.range_nonempty fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ F)
      (by
        rintro r ⟨i, rfl⟩
        exact hmono
          (fun _ => by norm_num)
          (fun k => credalHOLFormulaValue_le_one (Hs i) (φ k))
          (fun k => credalHOLFormulaValue_nonneg (Hs i) (φ k))))

theorem credalHOLFormulaFiniteRuleInterval_upper_le_one
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hone : F (fun _ => 1) ≤ 1) :
    (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).upper ≤ 1 := by
  unfold credalHOLFormulaFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_trans
    (csSup_le
      (Set.range_nonempty fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ F)
      (by
        rintro r ⟨i, rfl⟩
        exact hmono
          (fun k => credalHOLFormulaValue_nonneg (Hs i) (φ k))
          (fun _ => by norm_num)
          (fun k => credalHOLFormulaValue_le_one (Hs i) (φ k))))
    hone

theorem credalHOLFormulaFiniteRuleInterval_containedIn_hull
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) :
    (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).containedIn
      (credalHOLFormulaFiniteRuleHull Hs φ F hmono) := by
  unfold Interval.containedIn credalHOLFormulaFiniteRuleInterval
    credalHOLFormulaFiniteRuleHull
  dsimp [IntervalAddSemantics.intervalOf]
  constructor
  · apply le_csInf
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ F
    · rintro r ⟨i, rfl⟩
      exact hmono
        (fun k => credalHOLFormulaInterval_lower_nonneg Hs (φ k))
        (fun k => credalHOLFormulaValue_le_one (Hs i) (φ k))
        (fun k => csInf_le
          (credalHOLFormulaValue_bddBelow Hs (φ k)) ⟨i, rfl⟩)
  · apply csSup_le
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ F
    · rintro r ⟨i, rfl⟩
      exact hmono
        (fun k => credalHOLFormulaValue_nonneg (Hs i) (φ k))
        (fun k => credalHOLFormulaInterval_upper_le_one Hs (φ k))
        (fun k => le_csSup
          (credalHOLFormulaValue_bddAbove Hs (φ k)) ⟨i, rfl⟩)

/-- Lower endpoint tightness for the independent hull: if one completion
simultaneously realizes every premise lower endpoint, then the same-completion
finite-rule lower endpoint is exactly the hull lower endpoint.

This is the generic joint-realization condition needed before an independent
endpoint hull may be read as tight rather than merely as a safe relaxation. -/
theorem credalHOLFormulaFiniteRuleInterval_lower_eq_hull_lower_of_joint_lower_realizer
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hreal :
      ∃ i0 : ι,
        ∀ k : Fin n,
          credalHOLFormulaValue (Hs i0) (φ k) =
            (credalHOLFormulaInterval Hs (φ k)).lower) :
    (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).lower =
      (credalHOLFormulaFiniteRuleHull Hs φ F hmono).lower := by
  apply le_antisymm
  · obtain ⟨i0, hi0⟩ := hreal
    unfold credalHOLFormulaFiniteRuleInterval credalHOLFormulaFiniteRuleHull
    dsimp [IntervalAddSemantics.intervalOf]
    have hle :
        sInf (Set.range fun i =>
          credalHOLFormulaFiniteRuleValue (Hs i) φ F) ≤
          credalHOLFormulaFiniteRuleValue (Hs i0) φ F :=
      csInf_le
        (credalHOLFormulaFiniteRuleValue_bddBelow Hs φ F hmono) ⟨i0, rfl⟩
    simpa [credalHOLFormulaFiniteRuleValue, hi0] using hle
  · exact
      (credalHOLFormulaFiniteRuleInterval_containedIn_hull
        Hs φ F hmono).1

/-- Upper endpoint tightness for the independent hull: if one completion
simultaneously realizes every premise upper endpoint, then the same-completion
finite-rule upper endpoint is exactly the hull upper endpoint. -/
theorem credalHOLFormulaFiniteRuleInterval_upper_eq_hull_upper_of_joint_upper_realizer
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hreal :
      ∃ i0 : ι,
        ∀ k : Fin n,
          credalHOLFormulaValue (Hs i0) (φ k) =
            (credalHOLFormulaInterval Hs (φ k)).upper) :
    (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).upper =
      (credalHOLFormulaFiniteRuleHull Hs φ F hmono).upper := by
  apply le_antisymm
  · exact
      (credalHOLFormulaFiniteRuleInterval_containedIn_hull
        Hs φ F hmono).2
  · obtain ⟨i0, hi0⟩ := hreal
    unfold credalHOLFormulaFiniteRuleInterval credalHOLFormulaFiniteRuleHull
    dsimp [IntervalAddSemantics.intervalOf]
    have hle :
        credalHOLFormulaFiniteRuleValue (Hs i0) φ F ≤
          sSup (Set.range fun i =>
            credalHOLFormulaFiniteRuleValue (Hs i) φ F) :=
      le_csSup
        (credalHOLFormulaFiniteRuleValue_bddAbove Hs φ F hmono) ⟨i0, rfl⟩
    simpa [credalHOLFormulaFiniteRuleValue, hi0] using hle

theorem credalHOLFormulaFiniteRuleHull_lower_nonneg
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0)) :
    0 ≤ (credalHOLFormulaFiniteRuleHull Hs φ F hmono).lower := by
  unfold credalHOLFormulaFiniteRuleHull
  dsimp
  exact le_trans hzero
    (hmono
      (fun _ => by norm_num)
      (fun k => le_trans
        (credalHOLFormulaInterval Hs (φ k)).valid
        (credalHOLFormulaInterval_upper_le_one Hs (φ k)))
      (fun k => credalHOLFormulaInterval_lower_nonneg Hs (φ k)))

theorem credalHOLFormulaFiniteRuleHull_upper_le_one
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hone : F (fun _ => 1) ≤ 1) :
    (credalHOLFormulaFiniteRuleHull Hs φ F hmono).upper ≤ 1 := by
  unfold credalHOLFormulaFiniteRuleHull
  dsimp
  exact le_trans
    (hmono
      (fun k => le_trans
        (credalHOLFormulaInterval_lower_nonneg Hs (φ k))
        (credalHOLFormulaInterval Hs (φ k)).valid)
      (fun _ => by norm_num)
      (fun k => credalHOLFormulaInterval_upper_le_one Hs (φ k)))
    hone

/-- PLN `ITV` view of a same-completion finite rule interval. This is the
generic indexed packaging point for multi-premise higher-order PLN rules. -/
noncomputable def credalHOLFormulaFiniteRuleITV
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalHOLFormulaFiniteRuleInterval Hs φ F hmono
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalHOLFormulaFiniteRuleInterval_lower_nonneg Hs φ F hmono hzero)
    (credalHOLFormulaFiniteRuleInterval_upper_le_one Hs φ F hmono hone)
    hcred

@[simp] theorem credalHOLFormulaFiniteRuleITV_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaFiniteRuleITV Hs φ F hmono hzero hone
      credibility hcred).lower =
      (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).lower := by
  simp [credalHOLFormulaFiniteRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaFiniteRuleITV_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaFiniteRuleITV Hs φ F hmono hzero hone
      credibility hcred).upper =
      (credalHOLFormulaFiniteRuleInterval Hs φ F hmono).upper := by
  simp [credalHOLFormulaFiniteRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalHOLFormulaFiniteRuleITV_credibility
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaFiniteRuleITV Hs φ F hmono hzero hone
      credibility hcred).credibility = credibility := by
  simp [credalHOLFormulaFiniteRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

/-- Formula-level product multi-join interval: multiply the premise strengths
inside each hierarchical completion, then envelope across completions. -/
noncomputable def credalHOLFormulaProductMultiJoinInterval
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) : Interval :=
  credalHOLFormulaFiniteRuleInterval Hs φ (@productMultiJoin n)
    productMultiJoin_monotone_on_unit

/-- Independent-endpoint hull for formula-level product multi-join. The
same-completion product interval is contained in this hull; equality would
require extra dependence assumptions and is intentionally not claimed. -/
noncomputable def credalHOLFormulaProductMultiJoinHull
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) : Interval :=
  credalHOLFormulaFiniteRuleHull Hs φ (@productMultiJoin n)
    productMultiJoin_monotone_on_unit

@[simp] theorem credalHOLFormulaProductMultiJoinHull_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaProductMultiJoinHull Hs φ).lower =
      productMultiJoin
        (fun k => (credalHOLFormulaInterval Hs (φ k)).lower) := rfl

@[simp] theorem credalHOLFormulaProductMultiJoinHull_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaProductMultiJoinHull Hs φ).upper =
      productMultiJoin
        (fun k => (credalHOLFormulaInterval Hs (φ k)).upper) := rfl

theorem credalHOLFormulaProductMultiJoinInterval_containedIn_hull
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaProductMultiJoinInterval Hs φ).containedIn
      (credalHOLFormulaProductMultiJoinHull Hs φ) := by
  exact
    credalHOLFormulaFiniteRuleInterval_containedIn_hull
      Hs φ (@productMultiJoin n) productMultiJoin_monotone_on_unit

theorem credalHOLFormulaProductMultiJoinHull_lower_nonneg
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    0 ≤ (credalHOLFormulaProductMultiJoinHull Hs φ).lower :=
  credalHOLFormulaFiniteRuleHull_lower_nonneg
    Hs φ (@productMultiJoin n) productMultiJoin_monotone_on_unit
    productMultiJoin_zero_nonneg

theorem credalHOLFormulaProductMultiJoinHull_upper_le_one
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaProductMultiJoinHull Hs φ).upper ≤ 1 :=
  credalHOLFormulaFiniteRuleHull_upper_le_one
    Hs φ (@productMultiJoin n) productMultiJoin_monotone_on_unit
    productMultiJoin_one_le_one

/-- PLN truth-value view of the formula-level product multi-join interval. -/
noncomputable def credalHOLFormulaProductMultiJoinITV
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaFiniteRuleITV Hs φ (@productMultiJoin n)
    productMultiJoin_monotone_on_unit productMultiJoin_zero_nonneg
    productMultiJoin_one_le_one credibility hcred

@[simp] theorem credalHOLFormulaProductMultiJoinITV_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaProductMultiJoinITV Hs φ credibility hcred).lower =
      (credalHOLFormulaProductMultiJoinInterval Hs φ).lower := by
  rfl

@[simp] theorem credalHOLFormulaProductMultiJoinITV_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaProductMultiJoinITV Hs φ credibility hcred).upper =
      (credalHOLFormulaProductMultiJoinInterval Hs φ).upper := by
  rfl

@[simp] theorem credalHOLFormulaProductMultiJoinITV_credibility
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaProductMultiJoinITV Hs φ credibility hcred).credibility =
      credibility := by
  simp [credalHOLFormulaProductMultiJoinITV]

/-- Formula-level noisy-OR multi-join interval: combine premise strengths
inside each hierarchical completion with noisy-OR, then envelope across
completions. -/
noncomputable def credalHOLFormulaNoisyOrMultiJoinInterval
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) : Interval :=
  credalHOLFormulaFiniteRuleInterval Hs φ (@noisyOrMultiJoin n)
    noisyOrMultiJoin_monotone_on_unit

/-- Same-completion De Morgan law for formula-level multi-joins, lower
endpoint. Noisy-OR over a family of HOL formulas is the complement of the
upper endpoint of the product multi-join over the actual negated formulas, with
both envelopes taken over the same hierarchical completions. -/
theorem credalHOLFormulaNoisyOrMultiJoinInterval_lower_eq_one_sub_product_not_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinInterval Hs φ).lower =
      1 -
        (credalHOLFormulaProductMultiJoinInterval Hs
          (fun k => (.not (φ k) : ClosedFormula Const))).upper := by
  unfold credalHOLFormulaNoisyOrMultiJoinInterval
    credalHOLFormulaProductMultiJoinInterval
    credalHOLFormulaFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_antisymm
  · have hsup_le :
        sSup (Set.range fun i =>
          credalHOLFormulaFiniteRuleValue (Hs i)
            (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)) ≤
          1 - sInf (Set.range fun i =>
            credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)) := by
      apply csSup_le
      · exact Set.range_nonempty fun i =>
          credalHOLFormulaFiniteRuleValue (Hs i)
            (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)
      · rintro r ⟨i, rfl⟩
        have hlow :
            sInf (Set.range fun i =>
              credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)) ≤
                credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n) := by
          exact csInf_le
            (credalHOLFormulaFiniteRuleValue_bddBelow
              Hs φ (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit) ⟨i, rfl⟩
        rw [credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_not] at hlow
        change
          credalHOLFormulaFiniteRuleValue (Hs i)
            (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n) ≤
            1 - sInf (Set.range fun i =>
              credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n))
        linarith
    linarith
  · apply le_csInf
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)
    · rintro r ⟨i, rfl⟩
      have hle :
          credalHOLFormulaFiniteRuleValue (Hs i)
            (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n) ≤
            sSup (Set.range fun i =>
              credalHOLFormulaFiniteRuleValue (Hs i)
                (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)) := by
        exact le_csSup
          (credalHOLFormulaFiniteRuleValue_bddAbove
            Hs (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)
            productMultiJoin_monotone_on_unit) ⟨i, rfl⟩
      change
        1 - sSup (Set.range fun i =>
          credalHOLFormulaFiniteRuleValue (Hs i)
            (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)) ≤
          credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)
      rw [credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_not]
      linarith

/-- Same-completion De Morgan law for formula-level multi-joins, upper
endpoint. This is the dual endpoint to
`credalHOLFormulaNoisyOrMultiJoinInterval_lower_eq_one_sub_product_not_upper`. -/
theorem credalHOLFormulaNoisyOrMultiJoinInterval_upper_eq_one_sub_product_not_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinInterval Hs φ).upper =
      1 -
        (credalHOLFormulaProductMultiJoinInterval Hs
          (fun k => (.not (φ k) : ClosedFormula Const))).lower := by
  unfold credalHOLFormulaNoisyOrMultiJoinInterval
    credalHOLFormulaProductMultiJoinInterval
    credalHOLFormulaFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty fun i =>
        credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)
    · rintro r ⟨i, rfl⟩
      have hlow :
          sInf (Set.range fun i =>
            credalHOLFormulaFiniteRuleValue (Hs i)
              (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)) ≤
            credalHOLFormulaFiniteRuleValue (Hs i)
              (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n) := by
        exact csInf_le
          (credalHOLFormulaFiniteRuleValue_bddBelow
            Hs (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)
            productMultiJoin_monotone_on_unit) ⟨i, rfl⟩
      have hNoisy :
          credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n) =
            1 - credalHOLFormulaFiniteRuleValue (Hs i)
              (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n) := by
        exact credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_not
          (Hs i) φ
      dsimp
      rw [hNoisy]
      linarith
  · have hle :
        1 - sSup (Set.range fun i =>
          credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)) ≤
          sInf (Set.range fun i =>
            credalHOLFormulaFiniteRuleValue (Hs i)
              (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)) := by
      apply le_csInf
      · exact Set.range_nonempty fun i =>
          credalHOLFormulaFiniteRuleValue (Hs i)
            (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n)
      · rintro r ⟨i, rfl⟩
        have hnoisy_le :
            credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n) ≤
              sSup (Set.range fun i =>
                credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n)) := by
          exact le_csSup
            (credalHOLFormulaFiniteRuleValue_bddAbove
              Hs φ (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit) ⟨i, rfl⟩
        have hNoisy :
            credalHOLFormulaFiniteRuleValue (Hs i) φ (@noisyOrMultiJoin n) =
              1 - credalHOLFormulaFiniteRuleValue (Hs i)
                (fun k => (.not (φ k) : ClosedFormula Const)) (@productMultiJoin n) := by
          exact credalHOLFormulaFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_not
            (Hs i) φ
        rw [hNoisy] at hnoisy_le
        linarith
    linarith

/-- Independent-endpoint hull for formula-level noisy-OR multi-join. This is
the hull companion to `credalHOLFormulaNoisyOrMultiJoinInterval`, not an
independence assertion. -/
noncomputable def credalHOLFormulaNoisyOrMultiJoinHull
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) : Interval :=
  credalHOLFormulaFiniteRuleHull Hs φ (@noisyOrMultiJoin n)
    noisyOrMultiJoin_monotone_on_unit

@[simp] theorem credalHOLFormulaNoisyOrMultiJoinHull_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).lower =
      noisyOrMultiJoin
        (fun k => (credalHOLFormulaInterval Hs (φ k)).lower) := rfl

@[simp] theorem credalHOLFormulaNoisyOrMultiJoinHull_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).upper =
      noisyOrMultiJoin
        (fun k => (credalHOLFormulaInterval Hs (φ k)).upper) := rfl

theorem credalHOLFormulaNoisyOrMultiJoinHull_lower_eq_one_sub_product_compl
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).lower =
      1 - productMultiJoin
        (fun k => 1 - (credalHOLFormulaInterval Hs (φ k)).lower) := by
  rw [credalHOLFormulaNoisyOrMultiJoinHull_lower,
    noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]

theorem credalHOLFormulaNoisyOrMultiJoinHull_upper_eq_one_sub_product_compl
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).upper =
      1 - productMultiJoin
        (fun k => 1 - (credalHOLFormulaInterval Hs (φ k)).upper) := by
  rw [credalHOLFormulaNoisyOrMultiJoinHull_upper,
    noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]

theorem credalHOLFormulaNoisyOrMultiJoinInterval_containedIn_hull
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinInterval Hs φ).containedIn
      (credalHOLFormulaNoisyOrMultiJoinHull Hs φ) := by
  exact
    credalHOLFormulaFiniteRuleInterval_containedIn_hull
      Hs φ (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit

theorem credalHOLFormulaNoisyOrMultiJoinHull_lower_nonneg
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    0 ≤ (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).lower :=
  credalHOLFormulaFiniteRuleHull_lower_nonneg
    Hs φ (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
    noisyOrMultiJoin_zero_nonneg

theorem credalHOLFormulaNoisyOrMultiJoinHull_upper_le_one
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).upper ≤ 1 :=
  credalHOLFormulaFiniteRuleHull_upper_le_one
    Hs φ (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
    noisyOrMultiJoin_one_le_one

/-- Hull-level De Morgan law for the lower endpoint: noisy-OR over formulas is
the complement of the upper endpoint of product over their actual HOL
negations. This is an independent-endpoint hull law, not a same-completion
interval equality. -/
theorem credalHOLFormulaNoisyOrMultiJoinHull_lower_eq_one_sub_product_not_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).lower =
      1 -
        (credalHOLFormulaProductMultiJoinHull Hs
          (fun k => (.not (φ k) : ClosedFormula Const))).upper := by
  rw [credalHOLFormulaNoisyOrMultiJoinHull_lower_eq_one_sub_product_compl,
    credalHOLFormulaProductMultiJoinHull_upper]
  congr 1
  apply congrArg productMultiJoin
  funext k
  rw [credalHOLFormulaInterval_not_upper_eq_one_sub_lower]

/-- Hull-level De Morgan law for the upper endpoint: noisy-OR over formulas is
the complement of the lower endpoint of product over their actual HOL
negations. -/
theorem credalHOLFormulaNoisyOrMultiJoinHull_upper_eq_one_sub_product_not_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const) :
    (credalHOLFormulaNoisyOrMultiJoinHull Hs φ).upper =
      1 -
        (credalHOLFormulaProductMultiJoinHull Hs
          (fun k => (.not (φ k) : ClosedFormula Const))).lower := by
  rw [credalHOLFormulaNoisyOrMultiJoinHull_upper_eq_one_sub_product_compl,
    credalHOLFormulaProductMultiJoinHull_lower]
  congr 1
  apply congrArg productMultiJoin
  funext k
  rw [credalHOLFormulaInterval_not_lower_eq_one_sub_upper]

/-- PLN truth-value view of the formula-level noisy-OR multi-join interval. -/
noncomputable def credalHOLFormulaNoisyOrMultiJoinITV
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaFiniteRuleITV Hs φ (@noisyOrMultiJoin n)
    noisyOrMultiJoin_monotone_on_unit noisyOrMultiJoin_zero_nonneg
    noisyOrMultiJoin_one_le_one credibility hcred

@[simp] theorem credalHOLFormulaNoisyOrMultiJoinITV_lower
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaNoisyOrMultiJoinITV Hs φ credibility hcred).lower =
      (credalHOLFormulaNoisyOrMultiJoinInterval Hs φ).lower := by
  rfl

@[simp] theorem credalHOLFormulaNoisyOrMultiJoinITV_upper
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaNoisyOrMultiJoinITV Hs φ credibility hcred).upper =
      (credalHOLFormulaNoisyOrMultiJoinInterval Hs φ).upper := by
  rfl

@[simp] theorem credalHOLFormulaNoisyOrMultiJoinITV_credibility
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalHOLFormulaNoisyOrMultiJoinITV Hs φ credibility hcred).credibility =
      credibility := by
  simp [credalHOLFormulaNoisyOrMultiJoinITV]

/-- Kyburg-style finite-rule multi-join collapse: if every hierarchical
completion gives the same value after applying the finite PLN rule, then the
same-completion credal rule interval is exactly that point interval. This is
the precise pole of the HO-PLN credal rule surface. -/
theorem credalHOLFormulaFiniteRuleInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (c : ℝ)
    (hVal :
      ∀ i, credalHOLFormulaFiniteRuleValue (Hs i) φ F = c) :
    credalHOLFormulaFiniteRuleInterval Hs φ F hmono =
      constInterval c := by
  classical
  have hEq :
      Set.range (fun i => credalHOLFormulaFiniteRuleValue (Hs i) φ F) =
        {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        change credalHOLFormulaFiniteRuleValue (Hs i0) φ F = r
        rw [hVal i0, ← hr]⟩
  simp [credalHOLFormulaFiniteRuleInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- Singleton completion families collapse to precise finite-rule multi-joins.
This says the higher-order credal rule layer reduces to ordinary ProbHOL rule
evaluation when there is no completion uncertainty. -/
theorem credalHOLFormulaFiniteRuleInterval_eq_const_of_subsingleton
    {ι : Type y} [Subsingleton ι] [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (i0 : ι)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) :
    credalHOLFormulaFiniteRuleInterval Hs φ F hmono =
      constInterval (credalHOLFormulaFiniteRuleValue (Hs i0) φ F) := by
  exact
    credalHOLFormulaFiniteRuleInterval_eq_const_of_pointwise_value_eq
      Hs φ F hmono (credalHOLFormulaFiniteRuleValue (Hs i0) φ F)
      (fun i => by
        have : i = i0 := Subsingleton.elim i i0
        simp [this])

/-- If a finite-rule multi-join collapses to a point interval, its interval
width is zero. -/
theorem credalHOLFormulaFiniteRuleITV_width_eq_zero_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι] {n : ℕ}
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : Fin n → ClosedFormula Const)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (c credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (hVal :
      ∀ i, credalHOLFormulaFiniteRuleValue (Hs i) φ F = c) :
    (credalHOLFormulaFiniteRuleITV Hs φ F hmono hzero hone
      credibility hcred).width = 0 := by
  have hI :
      credalHOLFormulaFiniteRuleInterval Hs φ F hmono =
        constInterval c :=
    credalHOLFormulaFiniteRuleInterval_eq_const_of_pointwise_value_eq
      Hs φ F hmono c hVal
  simp [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    credalHOLFormulaFiniteRuleITV, hI, constInterval]

theorem credalHOLFormulaInterval_eq_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hVal :
      ∀ i, credalHOLFormulaValue (Hs i) φ = credalHOLFormulaValue (Hs i) ψ) :
    credalHOLFormulaInterval Hs φ = credalHOLFormulaInterval Hs ψ := by
  let I := credalHOLFormulaInterval Hs φ
  let J := credalHOLFormulaInterval Hs ψ
  have hl : I.lower = J.lower :=
    le_antisymm
      (credalHOLFormulaInterval_lower_mono_of_pointwise_value_le Hs
        (fun i => le_of_eq (hVal i)))
      (credalHOLFormulaInterval_lower_mono_of_pointwise_value_le Hs
        (fun i => ge_of_eq (hVal i)))
  have hu : I.upper = J.upper :=
    le_antisymm
      (credalHOLFormulaInterval_upper_mono_of_pointwise_value_le Hs
        (fun i => le_of_eq (hVal i)))
      (credalHOLFormulaInterval_upper_mono_of_pointwise_value_le Hs
        (fun i => ge_of_eq (hVal i)))
  exact interval_eq_of_bounds_eq hl hu

theorem credalHOLFormulaInterval_eq_of_pointwiseIff
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    {φ ψ : ClosedFormula Const}
    (hiff : ∀ i, (Hs i).baseSpace.PointwiseIff φ ψ) :
    credalHOLFormulaInterval Hs φ = credalHOLFormulaInterval Hs ψ :=
  credalHOLFormulaInterval_eq_of_pointwise_value_eq Hs
    (fun i => credalHOLFormulaValue_eq_of_pointwiseIff
      (Base := Base) (Const := Const) (Hs i) (hiff i))

theorem credalHOLFormulaInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (φ : ClosedFormula Const)
    (c : ℝ)
    (hVal : ∀ i, credalHOLFormulaValue (Hs i) φ = c) :
    credalHOLFormulaInterval Hs φ = constInterval c := by
  classical
  have hEq :
      Set.range (fun i => credalHOLFormulaValue (Hs i) φ) = {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        change credalHOLFormulaValue (Hs i0) φ = r
        rw [hVal i0, ← hr]⟩
  simp [credalHOLFormulaInterval, IntervalAddSemantics.intervalOf, hEq,
    constInterval]

/-- Singleton completion families collapse to point intervals. This is the
formal sanity check that a credal HO readout reduces to precise ProbHOL when
there is only one hierarchical state. -/
theorem credalHOLFormulaInterval_eq_const_of_subsingleton
    {ι : Type y} [Subsingleton ι] [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (i0 : ι)
    (φ : ClosedFormula Const) :
    credalHOLFormulaInterval Hs φ =
      constInterval (credalHOLFormulaValue (Hs i0) φ) := by
  classical
  have hEq :
      Set.range (fun i => credalHOLFormulaValue (Hs i) φ) =
        {credalHOLFormulaValue (Hs i0) φ} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      have : i = i0 := Subsingleton.elim i i0
      simp [this]
    · intro hr
      rcases hr with rfl
      exact ⟨i0, rfl⟩
  simp [credalHOLFormulaInterval, IntervalAddSemantics.intervalOf, hEq,
    constInterval]

/-- Credal interval for the predicate-inheritance rule sentence. -/
noncomputable def credalPredicateImplicationInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalHOLFormulaInterval Hs
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)

/-! ## Credal full-strength predicate inheritance over Henkin completions -/

/-- Point value of full extensional/intensional predicate-inheritance strength
in one possible pointed Henkin completion. The object-domain finiteness
instance is explicit because it depends on the chosen model. -/
noncomputable def credalPredicateFullInheritanceFamilyValue
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (i : ι) : ℝ := by
  letI := hObj i
  exact
    predicateFullInheritanceStrength
      (Base := Base) (Const := Const) (Ms i) σ p q

theorem credalPredicateFullInheritanceFamilyValue_nonneg
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (i : ι) :
    0 ≤ credalPredicateFullInheritanceFamilyValue
      (Base := Base) (Const := Const) Ms σ hObj p q i := by
  unfold credalPredicateFullInheritanceFamilyValue
  letI := hObj i
  exact
    predicateFullInheritanceStrength_nonneg
      (Base := Base) (Const := Const) (Ms i) σ p q

theorem credalPredicateFullInheritanceFamilyValue_le_one
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (i : ι) :
    credalPredicateFullInheritanceFamilyValue
      (Base := Base) (Const := Const) Ms σ hObj p q i ≤ 1 := by
  unfold credalPredicateFullInheritanceFamilyValue
  letI := hObj i
  exact
    predicateFullInheritanceStrength_le_one
      (Base := Base) (Const := Const) (Ms i) σ p q

theorem credalPredicateFullInheritanceFamilyValue_bddBelow
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    BddBelow
      (Set.range
        (credalPredicateFullInheritanceFamilyValue
          (Base := Base) (Const := Const) Ms σ hObj p q)) :=
  ⟨0, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateFullInheritanceFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ hObj p q i⟩

theorem credalPredicateFullInheritanceFamilyValue_bddAbove
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    BddAbove
      (Set.range
        (credalPredicateFullInheritanceFamilyValue
          (Base := Base) (Const := Const) Ms σ hObj p q)) :=
  ⟨1, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateFullInheritanceFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ hObj p q i⟩

/-- Credal interval for full extensional/intensional predicate-inheritance
strength over a nonempty family of possible pointed Henkin completions. This is
the graded/intensional sibling of the formula-probability interval above. -/
noncomputable def credalPredicateFullInheritanceInterval
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ =>
      credalPredicateFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ hObj p q i)
    (hBddBelow := fun _ =>
      credalPredicateFullInheritanceFamilyValue_bddBelow
        (Base := Base) (Const := Const) Ms σ hObj p q)
    (hBddAbove := fun _ =>
      credalPredicateFullInheritanceFamilyValue_bddAbove
        (Base := Base) (Const := Const) Ms σ hObj p q)
    ()

theorem credalPredicateFullInheritanceInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    0 ≤ (credalPredicateFullInheritanceInterval Ms σ hObj p q).lower := by
  unfold credalPredicateFullInheritanceInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateFullInheritanceFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ hObj p q i

theorem credalPredicateFullInheritanceInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (credalPredicateFullInheritanceInterval Ms σ hObj p q).upper ≤ 1 := by
  unfold credalPredicateFullInheritanceInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateFullInheritanceFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ hObj p q i

theorem credalPredicateFullInheritanceInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hVal :
      ∀ i, credalPredicateFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ hObj p q i = c) :
    credalPredicateFullInheritanceInterval Ms σ hObj p q = constInterval c := by
  classical
  have hEq :
      Set.range
          (credalPredicateFullInheritanceFamilyValue
            (Base := Base) (Const := Const) Ms σ hObj p q) = {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        rw [hVal i0, ← hr]⟩
  simp [credalPredicateFullInheritanceInterval, IntervalAddSemantics.intervalOf,
    hEq, constInterval]

/-- If each completion has the inherited nonempty supports and validates the
HOL predicate implication, the full-strength inheritance interval collapses to
the certain interval `[1,1]`. -/
theorem credalPredicateFullInheritanceInterval_eq_const_one_of_pointwise_models
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hsubE :
      ∀ i, ((predicateInterpretation
        (Base := Base) (Const := Const) (Ms i) σ).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ∀ i, ((predicateInterpretation
        (Base := Base) (Const := Const) (Ms i) σ).meaning q).intent.ncard ≠ 0)
    (hModels :
      ∀ i, HenkinModel.models (Ms i)
        (predicateImpFormula (Base := Base) (Const := Const) σ p q)) :
    credalPredicateFullInheritanceInterval Ms σ hObj p q = constInterval 1 := by
  exact
    credalPredicateFullInheritanceInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Ms σ hObj p q 1
      (by
        intro i
        unfold credalPredicateFullInheritanceFamilyValue
        letI := hObj i
        exact
          (predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
            (Base := Base) (Const := Const) (Ms i) σ p q
            (hsubE i) (hsuperI i)).2 (hModels i))

/-! ## Credal full-strength inheritance over finite predicate vocabularies -/

/-- Point value of full extensional/intensional inheritance strength for a
finite working predicate vocabulary in one possible pointed Henkin completion. -/
noncomputable def credalPredicateVocabularyFullInheritanceFamilyValue
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (i : ι) : ℝ := by
  letI := hObj i
  exact
    predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyFullInheritanceFamilyValue_nonneg
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (i : ι) :
    0 ≤ credalPredicateVocabularyFullInheritanceFamilyValue
      (Base := Base) (Const := Const) Ms σ decode hObj p q i := by
  unfold credalPredicateVocabularyFullInheritanceFamilyValue
  letI := hObj i
  exact
    predicateVocabularyFullInheritanceStrength_nonneg
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyFullInheritanceFamilyValue_le_one
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (i : ι) :
    credalPredicateVocabularyFullInheritanceFamilyValue
      (Base := Base) (Const := Const) Ms σ decode hObj p q i ≤ 1 := by
  unfold credalPredicateVocabularyFullInheritanceFamilyValue
  letI := hObj i
  exact
    predicateVocabularyFullInheritanceStrength_le_one
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyFullInheritanceFamilyValue_bddBelow
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    BddBelow
      (Set.range
        (credalPredicateVocabularyFullInheritanceFamilyValue
          (Base := Base) (Const := Const) Ms σ decode hObj p q)) :=
  ⟨0, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyFullInheritanceFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode hObj p q i⟩

theorem credalPredicateVocabularyFullInheritanceFamilyValue_bddAbove
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    BddAbove
      (Set.range
        (credalPredicateVocabularyFullInheritanceFamilyValue
          (Base := Base) (Const := Const) Ms σ decode hObj p q)) :=
  ⟨1, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyFullInheritanceFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode hObj p q i⟩

/-- Credal interval for full extensional/intensional predicate-inheritance
strength over a finite active predicate vocabulary and a nonempty family of
pointed Henkin completions. -/
noncomputable def credalPredicateVocabularyFullInheritanceInterval
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ =>
      credalPredicateVocabularyFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q i)
    (hBddBelow := fun _ =>
      credalPredicateVocabularyFullInheritanceFamilyValue_bddBelow
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
    (hBddAbove := fun _ =>
      credalPredicateVocabularyFullInheritanceFamilyValue_bddAbove
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
    ()

theorem credalPredicateVocabularyFullInheritanceInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ (credalPredicateVocabularyFullInheritanceInterval Ms σ decode hObj p q).lower := by
  unfold credalPredicateVocabularyFullInheritanceInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateVocabularyFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyFullInheritanceFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode hObj p q i

theorem credalPredicateVocabularyFullInheritanceInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    (credalPredicateVocabularyFullInheritanceInterval Ms σ decode hObj p q).upper ≤ 1 := by
  unfold credalPredicateVocabularyFullInheritanceInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateVocabularyFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyFullInheritanceFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode hObj p q i

theorem credalPredicateVocabularyFullInheritanceInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (c : ℝ)
    (hVal :
      ∀ i, credalPredicateVocabularyFullInheritanceFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q i = c) :
    credalPredicateVocabularyFullInheritanceInterval Ms σ decode hObj p q =
      constInterval c := by
  classical
  have hEq :
      Set.range
          (credalPredicateVocabularyFullInheritanceFamilyValue
            (Base := Base) (Const := Const) Ms σ decode hObj p q) = {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        rw [hVal i0, ← hr]⟩
  simp [credalPredicateVocabularyFullInheritanceInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- If every completion has the inherited finite-vocabulary supports and
validates the decoded HOL predicate implication, the finite-vocabulary
full-strength interval collapses to `[1,1]`. -/
theorem credalPredicateVocabularyFullInheritanceInterval_eq_const_one_of_pointwise_models
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (hsubE :
      ∀ i, ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) (Ms i) σ decode).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ∀ i, ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) (Ms i) σ decode).meaning q).intent.ncard ≠ 0)
    (hModels :
      ∀ i, HenkinModel.models (Ms i)
        (predicateImpFormula (Base := Base) (Const := Const) σ (decode p) (decode q))) :
    credalPredicateVocabularyFullInheritanceInterval Ms σ decode hObj p q =
      constInterval 1 := by
  exact
    credalPredicateVocabularyFullInheritanceInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Ms σ decode hObj p q 1
      (by
        intro i
        unfold credalPredicateVocabularyFullInheritanceFamilyValue
        letI := hObj i
        exact
          (predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
            (Base := Base) (Const := Const) (Ms i) σ decode p q
            (hsubE i) (hsuperI i)).2 (hModels i))

/-! ## Credal finite-vocabulary predicate similarity -/

/-- Point value of predicate similarity for a finite active predicate
vocabulary in one possible pointed Henkin completion. It reuses the finite
vocabulary full-inheritance bridge and PLN's ordinary `2inh2sim` formula. -/
noncomputable def credalPredicateVocabularySimilarityFamilyValue
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (i : ι) : ℝ := by
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySimilarityStrength
        (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularySimilarityFamilyValue_nonneg
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (i : ι) :
    0 ≤ credalPredicateVocabularySimilarityFamilyValue
      (Base := Base) (Const := Const) Ms σ decode hObj p q i := by
  unfold credalPredicateVocabularySimilarityFamilyValue
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySimilarityStrength_nonneg
        (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularySimilarityFamilyValue_le_one
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (i : ι) :
    credalPredicateVocabularySimilarityFamilyValue
      (Base := Base) (Const := Const) Ms σ decode hObj p q i ≤ 1 := by
  unfold credalPredicateVocabularySimilarityFamilyValue
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySimilarityStrength_le_one
        (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularySimilarityFamilyValue_bddBelow
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    BddBelow
      (Set.range
        (credalPredicateVocabularySimilarityFamilyValue
          (Base := Base) (Const := Const) Ms σ decode hObj p q)) :=
  ⟨0, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularySimilarityFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode hObj p q i⟩

theorem credalPredicateVocabularySimilarityFamilyValue_bddAbove
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    BddAbove
      (Set.range
        (credalPredicateVocabularySimilarityFamilyValue
          (Base := Base) (Const := Const) Ms σ decode hObj p q)) :=
  ⟨1, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularySimilarityFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode hObj p q i⟩

/-- Credal interval for finite-vocabulary predicate similarity across a
nonempty family of possible pointed Henkin completions. -/
noncomputable def credalPredicateVocabularySimilarityInterval
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ =>
      credalPredicateVocabularySimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q i)
    (hBddBelow := fun _ =>
      credalPredicateVocabularySimilarityFamilyValue_bddBelow
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
    (hBddAbove := fun _ =>
      credalPredicateVocabularySimilarityFamilyValue_bddAbove
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
    ()

theorem credalPredicateVocabularySimilarityInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ (credalPredicateVocabularySimilarityInterval Ms σ decode hObj p q).lower := by
  unfold credalPredicateVocabularySimilarityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateVocabularySimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularySimilarityFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode hObj p q i

theorem credalPredicateVocabularySimilarityInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred) :
    (credalPredicateVocabularySimilarityInterval Ms σ decode hObj p q).upper ≤ 1 := by
  unfold credalPredicateVocabularySimilarityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateVocabularySimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularySimilarityFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode hObj p q i

theorem credalPredicateVocabularySimilarityInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (c : ℝ)
    (hVal :
      ∀ i, credalPredicateVocabularySimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q i = c) :
    credalPredicateVocabularySimilarityInterval Ms σ decode hObj p q =
      constInterval c := by
  classical
  have hEq :
      Set.range
          (credalPredicateVocabularySimilarityFamilyValue
            (Base := Base) (Const := Const) Ms σ decode hObj p q) = {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        rw [hVal i0, ← hr]⟩
  simp [credalPredicateVocabularySimilarityInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- If every completion has the inherited finite-vocabulary supports and
validates the decoded HOL predicate equivalence, the finite-vocabulary
similarity interval collapses to `[1,1]`. -/
theorem credalPredicateVocabularySimilarityInterval_eq_const_one_of_pointwise_models
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (hpE :
      ∀ i, ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) (Ms i) σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ i, ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) (Ms i) σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ i, ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) (Ms i) σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ i, ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) (Ms i) σ decode).meaning p).intent.ncard ≠ 0)
    (hModels :
      ∀ i, HenkinModel.models (Ms i)
        (predicateIffFormula (Base := Base) (Const := Const) σ (decode p) (decode q))) :
    credalPredicateVocabularySimilarityInterval Ms σ decode hObj p q =
      constInterval 1 := by
  exact
    credalPredicateVocabularySimilarityInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Ms σ decode hObj p q 1
      (by
        intro i
        unfold credalPredicateVocabularySimilarityFamilyValue
        letI := hObj i
        exact
          Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySimilarityStrength_eq_one_of_models_predicateIffFormula
              (Base := Base) (Const := Const) (Ms i) σ decode p q
              (hpE i) (hqI i) (hqE i) (hpI i) (hModels i))

/-! ## Credal pure extensional/intensional finite-vocabulary similarity -/

/-- Point value of the pure extensional predicate-similarity readout for a
finite active predicate vocabulary in one possible Henkin completion. -/
noncomputable def credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (i : ι) : ℝ := by
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureExtensionalSimilarityStrength
      (Base := Base) (Const := Const) (Ms i) σ decode p q

/-- Point value of the pure intensional predicate-similarity readout for a
finite active predicate vocabulary in one possible Henkin completion. -/
noncomputable def credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (i : ι) : ℝ :=
  Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength
    (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_nonneg
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (i : ι) :
    0 ≤ credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
      (Base := Base) (Const := Const) Ms σ decode hObj p q i := by
  unfold credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureExtensionalSimilarityStrength_nonneg
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_le_one
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (i : ι) :
    credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
      (Base := Base) (Const := Const) Ms σ decode hObj p q i ≤ 1 := by
  unfold credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureExtensionalSimilarityStrength_le_one
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_nonneg
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (i : ι) :
    0 ≤ credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
      (Base := Base) (Const := Const) Ms σ decode p q i := by
  unfold credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength_nonneg
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_le_one
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (i : ι) :
    credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
      (Base := Base) (Const := Const) Ms σ decode p q i ≤ 1 := by
  unfold credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength_le_one
      (Base := Base) (Const := Const) (Ms i) σ decode p q

theorem credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_bddBelow
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred) :
    BddBelow
      (Set.range
        (credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
          (Base := Base) (Const := Const) Ms σ decode hObj p q)) :=
  ⟨0, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode hObj p q i⟩

theorem credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_bddAbove
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred) :
    BddAbove
      (Set.range
        (credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
          (Base := Base) (Const := Const) Ms σ decode hObj p q)) :=
  ⟨1, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode hObj p q i⟩

theorem credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_bddBelow
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    BddBelow
      (Set.range
        (credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
          (Base := Base) (Const := Const) Ms σ decode p q)) :=
  ⟨0, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode p q i⟩

theorem credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_bddAbove
    {ι : Type y}
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    BddAbove
      (Set.range
        (credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
          (Base := Base) (Const := Const) Ms σ decode p q)) :=
  ⟨1, by
    rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode p q i⟩

/-- Credal interval for pure extensional finite-vocabulary predicate
similarity across a nonempty family of possible Henkin completions. -/
noncomputable def credalPredicateVocabularyPureExtensionalSimilarityInterval
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ =>
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q i)
    (hBddBelow := fun _ =>
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_bddBelow
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
    (hBddAbove := fun _ =>
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_bddAbove
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
    ()

/-- Credal interval for pure intensional finite-vocabulary predicate
similarity across a nonempty family of possible Henkin completions. -/
noncomputable def credalPredicateVocabularyPureIntensionalSimilarityInterval
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := ι)
    (Θ := fun i _ =>
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode p q i)
    (hBddBelow := fun _ =>
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_bddBelow
        (Base := Base) (Const := Const) Ms σ decode p q)
    (hBddAbove := fun _ =>
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_bddAbove
        (Base := Base) (Const := Const) Ms σ decode p q)
    ()

theorem credalPredicateVocabularyPureExtensionalSimilarityInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred) :
    0 ≤ (credalPredicateVocabularyPureExtensionalSimilarityInterval
      Ms σ decode hObj p q).lower := by
  unfold credalPredicateVocabularyPureExtensionalSimilarityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode hObj p q i

theorem credalPredicateVocabularyPureExtensionalSimilarityInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred) :
    (credalPredicateVocabularyPureExtensionalSimilarityInterval
      Ms σ decode hObj p q).upper ≤ 1 := by
  unfold credalPredicateVocabularyPureExtensionalSimilarityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureExtensionalSimilarityFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode hObj p q i

theorem credalPredicateVocabularyPureIntensionalSimilarityInterval_lower_nonneg
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ (credalPredicateVocabularyPureIntensionalSimilarityInterval
      Ms σ decode p q).lower := by
  unfold credalPredicateVocabularyPureIntensionalSimilarityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_nonneg
        (Base := Base) (Const := Const) Ms σ decode p q i

theorem credalPredicateVocabularyPureIntensionalSimilarityInterval_upper_le_one
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred) :
    (credalPredicateVocabularyPureIntensionalSimilarityInterval
      Ms σ decode p q).upper ≤ 1 := by
  unfold credalPredicateVocabularyPureIntensionalSimilarityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode p q)
  · rintro r ⟨i, rfl⟩
    exact
      credalPredicateVocabularyPureIntensionalSimilarityFamilyValue_le_one
        (Base := Base) (Const := Const) Ms σ decode p q i

theorem credalPredicateVocabularyPureExtensionalSimilarityInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (c : ℝ)
    (hVal :
      ∀ i, credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode hObj p q i = c) :
    credalPredicateVocabularyPureExtensionalSimilarityInterval
        Ms σ decode hObj p q =
      constInterval c := by
  classical
  have hEq :
      Set.range
          (credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
            (Base := Base) (Const := Const) Ms σ decode hObj p q) = {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        rw [hVal i0, ← hr]⟩
  simp [credalPredicateVocabularyPureExtensionalSimilarityInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

theorem credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_of_pointwise_value_eq
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (c : ℝ)
    (hVal :
      ∀ i, credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
        (Base := Base) (Const := Const) Ms σ decode p q i = c) :
    credalPredicateVocabularyPureIntensionalSimilarityInterval
        Ms σ decode p q =
      constInterval c := by
  classical
  have hEq :
      Set.range
          (credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
            (Base := Base) (Const := Const) Ms σ decode p q) = {c} := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact hVal i
    · intro hr
      rcases (inferInstance : Nonempty ι) with ⟨i0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨i0, by
        rw [hVal i0, ← hr]⟩
  simp [credalPredicateVocabularyPureIntensionalSimilarityInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- If every possible Henkin completion makes `p` and `q` mutually pure
extensionally inheriting, then the pure-extensional predicate-similarity credal
interval collapses to certainty. This is the model-family form of the ordinary
PLN inheritance-to-similarity bridge. -/
theorem credalPredicateVocabularyPureExtensionalSimilarityInterval_eq_const_one_of_pointwise_mutualExtensional
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (hpE :
      ∀ i,
        ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ∀ i,
        ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).meaning q).extent.ncard ≠ 0)
    (hMutual :
      ∀ i,
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).ExtensionalInherits p q ∧
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).ExtensionalInherits q p) :
    credalPredicateVocabularyPureExtensionalSimilarityInterval
        (Base := Base) (Const := Const) Ms σ decode hObj p q =
      constInterval 1 := by
  apply
    credalPredicateVocabularyPureExtensionalSimilarityInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Ms σ decode hObj p q 1
  intro i
  unfold credalPredicateVocabularyPureExtensionalSimilarityFamilyValue
  letI := hObj i
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureExtensionalSimilarityStrength_eq_one_of_mutualExtensional
        (Base := Base) (Const := Const) (Ms i) σ decode p q
        (hpE i) (hqE i) (hMutual i).1 (hMutual i).2

/-- If every possible Henkin completion makes `p` and `q` mutually pure
intensionally inheriting, then the pure-intensional predicate-similarity credal
interval collapses to certainty. PAT/ASSOC-style pattern evidence should feed
this theorem by proving the mutual intensional hypotheses model-by-model. -/
theorem credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_one_of_pointwise_mutualIntensional
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hpI :
      ∀ i,
        ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).meaning p).intent.ncard ≠ 0)
    (hqI :
      ∀ i,
        ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).meaning q).intent.ncard ≠ 0)
    (hMutual :
      ∀ i,
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).IntensionalInherits p q ∧
          (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).IntensionalInherits q p) :
    credalPredicateVocabularyPureIntensionalSimilarityInterval
        (Base := Base) (Const := Const) Ms σ decode p q =
      constInterval 1 := by
  apply
    credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Ms σ decode p q 1
  intro i
  unfold credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength_eq_one_of_mutualIntensional
        (Base := Base) (Const := Const) (Ms i) σ decode p q
        (hpI i) (hqI i) (hMutual i).1 (hMutual i).2

/-- Pointwise same-intent evidence across every possible Henkin completion
collapses the pure-intensional predicate-similarity interval to certainty.
This is the model-family form of the PAT/ASSOC target: establish equality of
the pattern/intension attribute sets, then reuse the common HO-PLN similarity
surface. -/
theorem credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_one_of_pointwise_sameIntent
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (hpI :
      ∀ i,
        ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).meaning p).intent.ncard ≠ 0)
    (hqI :
      ∀ i,
        ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
            (Base := Base) (Const := Const) (Ms i) σ decode).meaning q).intent.ncard ≠ 0)
    (hSame :
      ∀ i,
        Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
          (Base := Base) (Const := Const) (Ms i) σ decode p q) :
    credalPredicateVocabularyPureIntensionalSimilarityInterval
        (Base := Base) (Const := Const) Ms σ decode p q =
      constInterval 1 := by
  apply
    credalPredicateVocabularyPureIntensionalSimilarityInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Ms σ decode p q 1
  intro i
  unfold credalPredicateVocabularyPureIntensionalSimilarityFamilyValue
  exact
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularyPureIntensionalSimilarityStrength_eq_one_of_sameIntent
      (Base := Base) (Const := Const) (Ms i) σ decode p q
      (hpI i) (hqI i) (hSame i)

/-- Credal interval for predicate similarity/equivalence. -/
noncomputable def credalPredicateSimilarityInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalHOLFormulaInterval Hs
    (predicateIffFormula (Base := Base) (Const := Const) σ p q)

/-- Credal interval obtained by applying PLN's `2inh2sim` rule to the two
directed predicate-implication strengths inside each hierarchical completion.
This is distinct from the HOL equivalence-sentence interval above: it is the
PLN rule-level reconstruction of similarity from two directed inheritance
queries. -/
noncomputable def credalPredicateTwoInh2SimInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalHOLFormulaBinaryRuleInterval Hs
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)
    (predicateImpFormula (Base := Base) (Const := Const) σ q p)
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    twoInh2Sim_binaryRuleMonotoneOnUnit

/-- Independent endpoint hull for the `2inh2sim` predicate-similarity rule. The
same-completion rule interval is contained in this hull, but need not equal it
when the two directed implications are completion-correlated. -/
noncomputable def credalPredicateTwoInh2SimHull
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalHOLFormulaBinaryRuleHull Hs
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)
    (predicateImpFormula (Base := Base) (Const := Const) σ q p)
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    twoInh2Sim_binaryRuleMonotoneOnUnit

theorem credalPredicateTwoInh2SimInterval_containedIn_hull
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (credalPredicateTwoInh2SimInterval Hs σ p q).containedIn
      (credalPredicateTwoInh2SimHull Hs σ p q) := by
  unfold credalPredicateTwoInh2SimInterval credalPredicateTwoInh2SimHull
  exact credalHOLFormulaBinaryRuleInterval_containedIn_hull
    (Base := Base) (Const := Const) Hs
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)
    (predicateImpFormula (Base := Base) (Const := Const) σ q p)
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    twoInh2Sim_binaryRuleMonotoneOnUnit

/-- Credal interval for universal predicate truth. -/
noncomputable def credalPredicateForAllInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalHOLFormulaInterval Hs
    (predicateForAllFormula (Base := Base) (Const := Const) σ p)

/-- Credal interval for existential predicate truth. -/
noncomputable def credalPredicateExistsInterval
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalHOLFormulaInterval Hs
    (predicateExistsFormula (Base := Base) (Const := Const) σ p)

/-! ## Credal arbitrary-capacity QFM endpoint intervals -/

/-- Point value of the arbitrary-capacity QFM universal endpoint for one
capacity completion. At zero tolerance, the QFM near-one mass of the
HOL-induced crisp profile is exactly the capacity of the predicate extension,
so a family of such capacities is the first interval-valued lift of the
satisfying-set reduction. -/
noncomputable def credalPredicateQFMForAllCapacityValue
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) : ℝ :=
  (νs k (predicateExtension (Base := Base) (Const := Const) M σ p) : ℝ)

theorem credalPredicateQFMForAllCapacityValue_eq_nearOneMassInf_of_epsilon_zero
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) :
    credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs p k =
      (nearOneMassInf params (νs k)
        (predicateCrispProfileInf
          (Base := Base) (Const := Const) M σ p) : ℝ) := by
  unfold credalPredicateQFMForAllCapacityValue
  rw [predicateNearOneMassInf_eq_capacity_extension_of_epsilon_zero
    (Base := Base) (Const := Const) M σ params hε (νs k) p]

theorem credalPredicateQFMForAllCapacityValue_nonneg
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) :
    0 ≤ credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs p k := by
  exact
    FuzzyCapacity.cap_nonneg (νs k)
      (predicateExtension (Base := Base) (Const := Const) M σ p)

theorem credalPredicateQFMForAllCapacityValue_le_one
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) :
    credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs p k ≤ 1 := by
  exact
    FuzzyCapacity.cap_le_one (νs k)
      (predicateExtension (Base := Base) (Const := Const) M σ p)

/-- Point value of the arbitrary-capacity QFM existential endpoint for one
capacity completion. This is the PLN/QFM existential score
`1 - capacity(complement(extension(P)))`, not ordinary nonempty existence. -/
noncomputable def credalPredicateQFMThereExistsCapacityValue
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) : ℝ :=
  1 -
    (νs k
      (predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ : ℝ)

theorem credalPredicateQFMThereExistsCapacityValue_eq_nearZeroMassInf_of_epsilon_zero
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (params : FuzzyQuantifierParamsInf) (hε : params.ε = 0)
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) :
    credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs p k =
      1 -
        (nearZeroMassInf params (νs k)
          (predicateCrispProfileInf
            (Base := Base) (Const := Const) M σ p) : ℝ) := by
  unfold credalPredicateQFMThereExistsCapacityValue
  rw [predicateNearZeroMassInf_eq_capacity_compl_extension_of_epsilon_zero
    (Base := Base) (Const := Const) M σ params hε (νs k) p]

theorem credalPredicateQFMThereExistsCapacityValue_nonneg
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) :
    0 ≤ credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs p k := by
  exact sub_nonneg.mpr
    (FuzzyCapacity.cap_le_one (νs k)
      (predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ)

theorem credalPredicateQFMThereExistsCapacityValue_le_one
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (k : κ) :
    credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs p k ≤ 1 := by
  exact sub_le_self 1
    (FuzzyCapacity.cap_nonneg (νs k)
      (predicateExtension (Base := Base) (Const := Const) M σ p)ᶜ)

theorem credalPredicateQFMForAllCapacityValue_bddBelow
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    BddBelow
      (Set.range
        (credalPredicateQFMForAllCapacityValue
          (Base := Base) (Const := Const) M σ νs p)) :=
  ⟨0, by
    rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs p k⟩

theorem credalPredicateQFMForAllCapacityValue_bddAbove
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    BddAbove
      (Set.range
        (credalPredicateQFMForAllCapacityValue
          (Base := Base) (Const := Const) M σ νs p)) :=
  ⟨1, by
    rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs p k⟩

theorem credalPredicateQFMThereExistsCapacityValue_bddBelow
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    BddBelow
      (Set.range
        (credalPredicateQFMThereExistsCapacityValue
          (Base := Base) (Const := Const) M σ νs p)) :=
  ⟨0, by
    rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs p k⟩

theorem credalPredicateQFMThereExistsCapacityValue_bddAbove
    {κ : Type x}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    BddAbove
      (Set.range
        (credalPredicateQFMThereExistsCapacityValue
          (Base := Base) (Const := Const) M σ νs p)) :=
  ⟨1, by
    rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs p k⟩

/-- Credal interval over a family of arbitrary capacities for the QFM
universal endpoint of one HOL predicate extension. -/
noncomputable def credalPredicateQFMForAllCapacityInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := κ)
    (Θ := fun k _ =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs p k)
    (hBddBelow := fun _ =>
      credalPredicateQFMForAllCapacityValue_bddBelow
        (Base := Base) (Const := Const) M σ νs p)
    (hBddAbove := fun _ =>
      credalPredicateQFMForAllCapacityValue_bddAbove
        (Base := Base) (Const := Const) M σ νs p)
    ()

/-- Credal interval over a family of arbitrary capacities for the QFM
existential endpoint of one HOL predicate extension. -/
noncomputable def credalPredicateQFMThereExistsCapacityInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := κ)
    (Θ := fun k _ =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs p k)
    (hBddBelow := fun _ =>
      credalPredicateQFMThereExistsCapacityValue_bddBelow
        (Base := Base) (Const := Const) M σ νs p)
    (hBddAbove := fun _ =>
      credalPredicateQFMThereExistsCapacityValue_bddAbove
        (Base := Base) (Const := Const) M σ νs p)
    ()

theorem credalPredicateQFMForAllCapacityInterval_lower_nonneg
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    0 ≤
      (credalPredicateQFMForAllCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).lower := by
  unfold credalPredicateQFMForAllCapacityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs p)
  · rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs p k

theorem credalPredicateQFMForAllCapacityInterval_upper_le_one
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (credalPredicateQFMForAllCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).upper ≤ 1 := by
  unfold credalPredicateQFMForAllCapacityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs p)
  · rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs p k

theorem credalPredicateQFMThereExistsCapacityInterval_lower_nonneg
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    0 ≤
      (credalPredicateQFMThereExistsCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).lower := by
  unfold credalPredicateQFMThereExistsCapacityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty
      (credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs p)
  · rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs p k

theorem credalPredicateQFMThereExistsCapacityInterval_upper_le_one
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (credalPredicateQFMThereExistsCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).upper ≤ 1 := by
  unfold credalPredicateQFMThereExistsCapacityInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty
      (credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs p)
  · rintro r ⟨k, rfl⟩
    exact
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs p k

/-! ## Finite QFM capacity-rule envelopes -/

/-- Pointwise application of a finite PLN rule function to a family of QFM
capacity endpoint values inside one capacity/reference-class completion. This
is the capacity-side analogue of `credalHOLFormulaFiniteRuleValue`. -/
noncomputable def credalQFMCapacityFiniteRuleValue
    {κ : Type x} {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (k : κ) : ℝ :=
  F (endpoint k)

theorem credalQFMCapacityFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl
    {κ : Type x} {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (k : κ) :
    credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k =
      1 - productMultiJoin (fun j => 1 - endpoint k j) := by
  simp [credalQFMCapacityFiniteRuleValue,
    noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]

theorem credalQFMCapacityFiniteBoundedRuleValue_bddBelow
    {κ : Type x} {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    BddBelow
      (Set.range fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k) :=
  ⟨0, by
    rintro r ⟨k, rfl⟩
    exact (hunit (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)).1⟩

theorem credalQFMCapacityFiniteBoundedRuleValue_bddAbove
    {κ : Type x} {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    BddAbove
      (Set.range fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k) :=
  ⟨1, by
    rintro r ⟨k, rfl⟩
    exact (hunit (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)).2⟩

theorem credalQFMCapacityFiniteRuleValue_bddBelow
    {κ : Type x} {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    BddBelow
      (Set.range fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k) :=
  ⟨F (fun _ => 0), by
    rintro r ⟨k, rfl⟩
    exact hmono
      (fun _ => by norm_num)
      (fun j => hEndpoint_le_one k j)
      (fun j => hEndpoint_nonneg k j)⟩

theorem credalQFMCapacityFiniteRuleValue_bddAbove
    {κ : Type x} {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    BddAbove
      (Set.range fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k) :=
  ⟨F (fun _ => 1), by
    rintro r ⟨k, rfl⟩
    exact hmono
      (fun j => hEndpoint_nonneg k j)
      (fun _ => by norm_num)
      (fun j => hEndpoint_le_one k j)⟩

/-- Marginal interval for one indexed QFM capacity endpoint across a nonempty
family of capacity/reference-class completions. -/
noncomputable def credalQFMCapacityEndpointInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (j : Fin n) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := κ)
    (Θ := fun k _ => endpoint k j)
    (hBddBelow := fun _ =>
      ⟨0, by
        rintro r ⟨k, rfl⟩
        exact hEndpoint_nonneg k j⟩)
    (hBddAbove := fun _ =>
      ⟨1, by
        rintro r ⟨k, rfl⟩
        exact hEndpoint_le_one k j⟩)
    ()

theorem credalQFMCapacityEndpointInterval_lower_nonneg
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (j : Fin n) :
    0 ≤
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one j).lower := by
  unfold credalQFMCapacityEndpointInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty (fun k => endpoint k j)
  · rintro r ⟨k, rfl⟩
    exact hEndpoint_nonneg k j

theorem credalQFMCapacityEndpointInterval_upper_le_one
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (j : Fin n) :
    (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one j).upper ≤ 1 := by
  unfold credalQFMCapacityEndpointInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty (fun k => endpoint k j)
  · rintro r ⟨k, rfl⟩
    exact hEndpoint_le_one k j

theorem credalQFMCapacityEndpointInterval_lower_le_value
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (j : Fin n) (k : κ) :
    (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one j).lower ≤
      endpoint k j := by
  unfold credalQFMCapacityEndpointInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact csInf_le
    (⟨0, by
      rintro r ⟨k, rfl⟩
      exact hEndpoint_nonneg k j⟩)
    ⟨k, rfl⟩

theorem credalQFMCapacityEndpointInterval_value_le_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (j : Fin n) (k : κ) :
    endpoint k j ≤
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one j).upper := by
  unfold credalQFMCapacityEndpointInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_csSup
    (⟨1, by
      rintro r ⟨k, rfl⟩
      exact hEndpoint_le_one k j⟩)
    ⟨k, rfl⟩

/-- Same-completion finite-rule interval for QFM capacity endpoints: apply the
indexed rule inside each capacity/reference-class completion, then take the
credal envelope. This is the concrete QFM-side multi-join skeleton. -/
noncomputable def credalQFMCapacityFiniteRuleInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := κ)
    (Θ := fun k _ => credalQFMCapacityFiniteRuleValue endpoint F k)
    (hBddBelow := fun _ =>
      credalQFMCapacityFiniteRuleValue_bddBelow
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one)
    (hBddAbove := fun _ =>
      credalQFMCapacityFiniteRuleValue_bddAbove
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one)
    ()

/-- Same-completion interval for bounded finite QFM capacity rules. This is
the safe envelope for PLN rules that map unit inputs to unit outputs but are
not globally monotone in every coordinate. Because no monotonicity is assumed,
no independent-endpoint hull theorem is claimed here. -/
noncomputable def credalQFMCapacityFiniteBoundedRuleInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := κ)
    (Θ := fun k _ => credalQFMCapacityFiniteRuleValue endpoint F k)
    (hBddBelow := fun _ =>
      credalQFMCapacityFiniteBoundedRuleValue_bddBelow
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one)
    (hBddAbove := fun _ =>
      credalQFMCapacityFiniteBoundedRuleValue_bddAbove
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one)
    ()

theorem credalQFMCapacityFiniteBoundedRuleInterval_lower_nonneg
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    0 ≤
      (credalQFMCapacityFiniteBoundedRuleInterval
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one).lower := by
  unfold credalQFMCapacityFiniteBoundedRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty fun k =>
      credalQFMCapacityFiniteRuleValue endpoint F k
  · rintro r ⟨k, rfl⟩
    exact (hunit (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)).1

theorem credalQFMCapacityFiniteBoundedRuleInterval_upper_le_one
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityFiniteBoundedRuleInterval
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one).upper ≤ 1 := by
  unfold credalQFMCapacityFiniteBoundedRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty fun k =>
      credalQFMCapacityFiniteRuleValue endpoint F k
  · rintro r ⟨k, rfl⟩
    exact (hunit (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)).2

/-- PLN truth-value view of a bounded same-completion finite QFM capacity-rule
interval. -/
noncomputable def credalQFMCapacityFiniteBoundedRuleITV
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I :=
    credalQFMCapacityFiniteBoundedRuleInterval
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalQFMCapacityFiniteBoundedRuleInterval_lower_nonneg
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one)
    (credalQFMCapacityFiniteBoundedRuleInterval_upper_le_one
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one)
    hcred

@[simp] theorem credalQFMCapacityFiniteBoundedRuleITV_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityFiniteBoundedRuleITV
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one
      credibility hcred).lower =
      (credalQFMCapacityFiniteBoundedRuleInterval
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one).lower := by
  simp [credalQFMCapacityFiniteBoundedRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalQFMCapacityFiniteBoundedRuleITV_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityFiniteBoundedRuleITV
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one
      credibility hcred).upper =
      (credalQFMCapacityFiniteBoundedRuleInterval
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one).upper := by
  simp [credalQFMCapacityFiniteBoundedRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalQFMCapacityFiniteBoundedRuleITV_credibility
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityFiniteBoundedRuleITV
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one
      credibility hcred).credibility = credibility := by
  simp [credalQFMCapacityFiniteBoundedRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

/-- Bounded finite-rule multi-join collapse for QFM capacity endpoints: if all
capacity/reference-class completions agree after the rule is applied, the
bounded same-completion interval is exactly the corresponding point interval. -/
theorem credalQFMCapacityFiniteBoundedRuleInterval_eq_const_of_pointwise_value_eq
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (c : ℝ)
    (hVal :
      ∀ k, credalQFMCapacityFiniteRuleValue endpoint F k = c) :
    credalQFMCapacityFiniteBoundedRuleInterval
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one =
      constInterval c := by
  classical
  have hEq :
      Set.range (fun k => credalQFMCapacityFiniteRuleValue endpoint F k) =
        {c} := by
    ext r
    constructor
    · rintro ⟨k, rfl⟩
      exact hVal k
    · intro hr
      rcases (inferInstance : Nonempty κ) with ⟨k0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨k0, by
        change credalQFMCapacityFiniteRuleValue endpoint F k0 = r
        rw [hVal k0, ← hr]⟩
  simp [credalQFMCapacityFiniteBoundedRuleInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- Singleton capacity/reference-class families collapse to point-valued
bounded finite-rule QFM multi-joins. -/
theorem credalQFMCapacityFiniteBoundedRuleInterval_eq_const_of_subsingleton
    {κ : Type x} [Subsingleton κ] [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (k0 : κ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    credalQFMCapacityFiniteBoundedRuleInterval
        endpoint F hunit hEndpoint_nonneg hEndpoint_le_one =
      constInterval (credalQFMCapacityFiniteRuleValue endpoint F k0) := by
  exact
    credalQFMCapacityFiniteBoundedRuleInterval_eq_const_of_pointwise_value_eq
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one
      (credalQFMCapacityFiniteRuleValue endpoint F k0)
      (fun k => by
        have : k = k0 := Subsingleton.elim k k0
        simp [this])

/-- When a bounded finite-rule QFM multi-join collapses to a point interval,
its PLN truth-value width is zero. -/
theorem credalQFMCapacityFiniteBoundedRuleITV_width_eq_zero_of_pointwise_value_eq
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hunit : FiniteRuleMapsUnitToUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (c credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (hVal :
      ∀ k, credalQFMCapacityFiniteRuleValue endpoint F k = c) :
    (credalQFMCapacityFiniteBoundedRuleITV
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one
      credibility hcred).width = 0 := by
  have hI :
      credalQFMCapacityFiniteBoundedRuleInterval
          endpoint F hunit hEndpoint_nonneg hEndpoint_le_one =
        constInterval c :=
    credalQFMCapacityFiniteBoundedRuleInterval_eq_const_of_pointwise_value_eq
      endpoint F hunit hEndpoint_nonneg hEndpoint_le_one c hVal
  simp [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    credalQFMCapacityFiniteBoundedRuleITV, hI, constInterval]

theorem credalQFMCapacitySim2InhRuleValue_bddBelow
    {κ : Type x}
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1) :
    BddBelow
      (Set.range fun k =>
        credalQFMCapacityFiniteRuleValue endpoint sim2inhAsFinite3 k) :=
  ⟨0, by
    rintro r ⟨k, rfl⟩
    exact (sim2inhAsFinite3_mapsConstrainedToUnit
      (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)
      (hSource_pos k)
      (hTarget_le_source k)).1⟩

theorem credalQFMCapacitySim2InhRuleValue_bddAbove
    {κ : Type x}
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1) :
    BddAbove
      (Set.range fun k =>
        credalQFMCapacityFiniteRuleValue endpoint sim2inhAsFinite3 k) :=
  ⟨1, by
    rintro r ⟨k, rfl⟩
    exact (sim2inhAsFinite3_mapsConstrainedToUnit
      (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)
      (hSource_pos k)
      (hTarget_le_source k)).2⟩

/-- Same-completion interval for QFM `sim2inh` endpoints. This is the
constrained-rule envelope: each completion must satisfy the real PLN side
conditions (`s_A > 0` and `s_B <= s_A`) before `sim2inh` is allowed to
contribute to the credal family. -/
noncomputable def credalQFMCapacitySim2InhInterval
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1) : Interval :=
  IntervalAddSemantics.intervalOf (α := Unit) (ι := κ)
    (Θ := fun k _ =>
      credalQFMCapacityFiniteRuleValue endpoint sim2inhAsFinite3 k)
    (hBddBelow := fun _ =>
      credalQFMCapacitySim2InhRuleValue_bddBelow
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSource_pos hTarget_le_source)
    (hBddAbove := fun _ =>
      credalQFMCapacitySim2InhRuleValue_bddAbove
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSource_pos hTarget_le_source)
    ()

theorem credalQFMCapacitySim2InhInterval_lower_nonneg
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1) :
    0 ≤
      (credalQFMCapacitySim2InhInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSource_pos hTarget_le_source).lower := by
  unfold credalQFMCapacitySim2InhInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_csInf
  · exact Set.range_nonempty fun k =>
      credalQFMCapacityFiniteRuleValue endpoint sim2inhAsFinite3 k
  · rintro r ⟨k, rfl⟩
    exact (sim2inhAsFinite3_mapsConstrainedToUnit
      (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)
      (hSource_pos k)
      (hTarget_le_source k)).1

theorem credalQFMCapacitySim2InhInterval_upper_le_one
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1) :
    (credalQFMCapacitySim2InhInterval
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source).upper ≤ 1 := by
  unfold credalQFMCapacitySim2InhInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply csSup_le
  · exact Set.range_nonempty fun k =>
      credalQFMCapacityFiniteRuleValue endpoint sim2inhAsFinite3 k
  · rintro r ⟨k, rfl⟩
    exact (sim2inhAsFinite3_mapsConstrainedToUnit
      (endpoint k)
      (fun j => hEndpoint_nonneg k j)
      (fun j => hEndpoint_le_one k j)
      (hSource_pos k)
      (hTarget_le_source k)).2

/-- PLN truth-value view of a constrained same-completion QFM `sim2inh`
interval. -/
noncomputable def credalQFMCapacitySim2InhITV
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I :=
    credalQFMCapacitySim2InhInterval
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalQFMCapacitySim2InhInterval_lower_nonneg
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source)
    (credalQFMCapacitySim2InhInterval_upper_le_one
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source)
    hcred

@[simp] theorem credalQFMCapacitySim2InhITV_lower
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacitySim2InhITV
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source credibility hcred).lower =
      (credalQFMCapacitySim2InhInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSource_pos hTarget_le_source).lower := by
  simp [credalQFMCapacitySim2InhITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalQFMCapacitySim2InhITV_upper
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacitySim2InhITV
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source credibility hcred).upper =
      (credalQFMCapacitySim2InhInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSource_pos hTarget_le_source).upper := by
  simp [credalQFMCapacitySim2InhITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalQFMCapacitySim2InhITV_credibility
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacitySim2InhITV
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSource_pos hTarget_le_source credibility hcred).credibility =
      credibility := by
  simp [credalQFMCapacitySim2InhITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

/-- Independent-endpoint hull for QFM `sim2inh`. The lower endpoint uses
lower similarity, upper source strength, and lower target strength; the upper
endpoint uses upper similarity, lower source strength, and upper target
strength. This mixed polarity is forced by `sim2inh`: it is monotone in
similarity and target strength, but antitone in source strength. -/
noncomputable def credalQFMCapacitySim2InhHull
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSourceLower_pos :
      0 <
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower) :
    Interval where
  lower :=
    Mettapedia.Logic.PLNInferenceRules.sim2inh
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).upper
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 2).lower
  upper :=
    Mettapedia.Logic.PLNInferenceRules.sim2inh
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).upper
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 2).upper
  valid := by
    have hSourceUpper_pos :
        0 <
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 1).upper :=
      lt_of_lt_of_le hSourceLower_pos
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid
    exact
      Mettapedia.Logic.PLNInferenceRules.sim2inh_mixed_mono
        (credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one 0)
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).valid
        hSourceLower_pos
        hSourceUpper_pos
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid
        (credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one 2)
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 2).valid

theorem credalQFMCapacitySim2InhHull_lower_nonneg
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSourceLower_pos :
      0 <
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower)
    (hTargetUpper_le_sourceLower :
      (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 2).upper ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower) :
    0 ≤
      (credalQFMCapacitySim2InhHull
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSourceLower_pos).lower := by
  unfold credalQFMCapacitySim2InhHull
  exact
    (Mettapedia.Logic.PLNInferenceRules.sim2inh_mem_unit
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).upper
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 2).lower
      ⟨credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one 0,
        le_trans
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 0).valid
          (credalQFMCapacityEndpointInterval_upper_le_one
            endpoint hEndpoint_nonneg hEndpoint_le_one 0)⟩
      ⟨lt_of_lt_of_le hSourceLower_pos
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid,
        credalQFMCapacityEndpointInterval_upper_le_one
          endpoint hEndpoint_nonneg hEndpoint_le_one 1⟩
      ⟨credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one 2,
        le_trans
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 2).valid
          (credalQFMCapacityEndpointInterval_upper_le_one
            endpoint hEndpoint_nonneg hEndpoint_le_one 2)⟩
      (le_trans
        (le_trans
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 2).valid
          hTargetUpper_le_sourceLower)
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid)).1

theorem credalQFMCapacitySim2InhHull_upper_le_one
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSourceLower_pos :
      0 <
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower)
    (hTargetUpper_le_sourceLower :
      (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 2).upper ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower) :
    (credalQFMCapacitySim2InhHull
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSourceLower_pos).upper ≤ 1 := by
  unfold credalQFMCapacitySim2InhHull
  exact
    (Mettapedia.Logic.PLNInferenceRules.sim2inh_mem_unit
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).upper
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 2).upper
      ⟨le_trans
          (credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one 0)
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 0).valid,
        credalQFMCapacityEndpointInterval_upper_le_one
          endpoint hEndpoint_nonneg hEndpoint_le_one 0⟩
      ⟨hSourceLower_pos,
        le_trans
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid
          (credalQFMCapacityEndpointInterval_upper_le_one
            endpoint hEndpoint_nonneg hEndpoint_le_one 1)⟩
      ⟨le_trans
          (credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one 2)
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 2).valid,
        credalQFMCapacityEndpointInterval_upper_le_one
          endpoint hEndpoint_nonneg hEndpoint_le_one 2⟩
      hTargetUpper_le_sourceLower).2

theorem credalQFMCapacitySim2InhInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSource_pos : ∀ k, 0 < endpoint k 1)
    (hTarget_le_source : ∀ k, endpoint k 2 ≤ endpoint k 1)
    (hSourceLower_pos :
      0 <
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower) :
    (credalQFMCapacitySim2InhInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSource_pos hTarget_le_source).containedIn
      (credalQFMCapacitySim2InhHull
        endpoint hEndpoint_nonneg hEndpoint_le_one
        hSourceLower_pos) := by
  unfold Interval.containedIn
    credalQFMCapacitySim2InhInterval
    credalQFMCapacitySim2InhHull
  dsimp [IntervalAddSemantics.intervalOf, credalQFMCapacityFiniteRuleValue,
    sim2inhAsFinite3]
  constructor
  · apply le_csInf
    · exact Set.range_nonempty fun k =>
        Mettapedia.Logic.PLNInferenceRules.sim2inh
          (endpoint k 0) (endpoint k 1) (endpoint k 2)
    · rintro r ⟨k, rfl⟩
      have hSourceUpper_pos :
          0 <
            (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one 1).upper :=
        lt_of_lt_of_le (hSource_pos k)
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)
      exact
        Mettapedia.Logic.PLNInferenceRules.sim2inh_mixed_mono
          (credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one 0)
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
          (hSource_pos k)
          hSourceUpper_pos
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)
          (credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one 2)
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 2 k)
  · apply csSup_le
    · exact Set.range_nonempty fun k =>
        Mettapedia.Logic.PLNInferenceRules.sim2inh
          (endpoint k 0) (endpoint k 1) (endpoint k 2)
    · rintro r ⟨k, rfl⟩
      exact
        Mettapedia.Logic.PLNInferenceRules.sim2inh_mixed_mono
          (hEndpoint_nonneg k 0)
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
          hSourceLower_pos
          (hSource_pos k)
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)
          (hEndpoint_nonneg k 2)
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 2 k)

/-- PLN truth-value packaging for the independent-endpoint `sim2inh` hull.
The cross-endpoint side condition is intentionally explicit: without
`target.upper <= source.lower`, the upper hull endpoint can exceed `1`. -/
noncomputable def credalQFMCapacitySim2InhHullITV
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 3 → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hSourceLower_pos :
      0 <
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower)
    (hTargetUpper_le_sourceLower :
      (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 2).upper ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I :=
    credalQFMCapacitySim2InhHull
      endpoint hEndpoint_nonneg hEndpoint_le_one hSourceLower_pos
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalQFMCapacitySim2InhHull_lower_nonneg
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSourceLower_pos hTargetUpper_le_sourceLower)
    (credalQFMCapacitySim2InhHull_upper_le_one
      endpoint hEndpoint_nonneg hEndpoint_le_one
      hSourceLower_pos hTargetUpper_le_sourceLower)
    hcred

/-- Independent-endpoint hull for QFM modus ponens under the honest side
condition that the implication-strength lower endpoint is at least the
background/default `c`. Under that condition, modus ponens is monotone on the
relevant endpoint rectangle even though it is not globally monotone on the
entire unit square. -/
noncomputable def credalQFMCapacityModusPonensHull
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 2 → ℝ)
    (c : ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hcLower :
      c ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower) :
    Interval where
  lower :=
    Mettapedia.Logic.PLNInferenceRules.modusPonens
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower
      c
  upper :=
    Mettapedia.Logic.PLNInferenceRules.modusPonens
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).upper
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).upper
      c
  valid := by
    exact
      Mettapedia.Logic.PLNInferenceRules.modusPonens_mono_of_background_le
        (credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one 1)
        hcLower
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).valid
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid

theorem credalQFMCapacityModusPonensBoundedRuleInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 2 → ℝ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hcLower :
      c ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower) :
    (credalQFMCapacityFiniteBoundedRuleInterval
        endpoint (modusPonensAsFinite2 c)
        (modusPonensAsFinite2_mapsUnitToUnit c hc)
        hEndpoint_nonneg hEndpoint_le_one).containedIn
      (credalQFMCapacityModusPonensHull
        endpoint c hEndpoint_nonneg hEndpoint_le_one hcLower) := by
  unfold Interval.containedIn
    credalQFMCapacityFiniteBoundedRuleInterval
    credalQFMCapacityModusPonensHull
  dsimp [IntervalAddSemantics.intervalOf, credalQFMCapacityFiniteRuleValue,
    modusPonensAsFinite2]
  constructor
  · apply le_csInf
    · exact Set.range_nonempty fun k =>
        Mettapedia.Logic.PLNInferenceRules.modusPonens
          (endpoint k 0) (endpoint k 1) c
    · rintro r ⟨k, rfl⟩
      exact
        Mettapedia.Logic.PLNInferenceRules.modusPonens_mono_of_background_le
          (credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one 1)
          hcLower
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)
  · apply csSup_le
    · exact Set.range_nonempty fun k =>
        Mettapedia.Logic.PLNInferenceRules.modusPonens
          (endpoint k 0) (endpoint k 1) c
    · rintro r ⟨k, rfl⟩
      have hcValue : c ≤ endpoint k 0 :=
        le_trans hcLower
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
      exact
        Mettapedia.Logic.PLNInferenceRules.modusPonens_mono_of_background_le
          (hEndpoint_nonneg k 1)
          hcValue
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)

/-- Independent-endpoint hull for QFM symmetric modus ponens under the honest
side condition that the similarity-strength lower endpoint is high enough
relative to the background/default `c`. Symmetric MP is not globally monotone
in the premise coordinate; this threshold is what makes the endpoint hull
sound. -/
noncomputable def credalQFMCapacitySymmetricModusPonensHull
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 2 → ℝ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hcLower :
      c * (1 +
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower) ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower) :
    Interval where
  lower :=
    Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower
      c
  upper :=
    Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 0).upper
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one 1).upper
      c
  valid := by
    have hPremiseLower :
        (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower ∈
          Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact
          credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one 1
      · exact le_trans
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid
          (credalQFMCapacityEndpointInterval_upper_le_one
            endpoint hEndpoint_nonneg hEndpoint_le_one 1)
    exact
      Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens_mono_of_background_le
        hPremiseLower
        hc.1
        (by linarith [hc.2])
        hcLower
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).valid
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid

theorem credalQFMCapacitySymmetricModusPonensBoundedRuleInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (endpoint : κ → Fin 2 → ℝ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hcLower :
      c * (1 +
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower) ≤
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one 0).lower) :
    (credalQFMCapacityFiniteBoundedRuleInterval
        endpoint (symmetricModusPonensAsFinite2 c)
        (symmetricModusPonensAsFinite2_mapsUnitToUnit c hc)
        hEndpoint_nonneg hEndpoint_le_one).containedIn
      (credalQFMCapacitySymmetricModusPonensHull
        endpoint c hc hEndpoint_nonneg hEndpoint_le_one hcLower) := by
  unfold Interval.containedIn
    credalQFMCapacityFiniteBoundedRuleInterval
    credalQFMCapacitySymmetricModusPonensHull
  dsimp [IntervalAddSemantics.intervalOf, credalQFMCapacityFiniteRuleValue,
    symmetricModusPonensAsFinite2]
  constructor
  · apply le_csInf
    · exact Set.range_nonempty fun k =>
        Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens
          (endpoint k 0) (endpoint k 1) c
    · rintro r ⟨k, rfl⟩
      have hPremiseLower :
          (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one 1).lower ∈
            Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact
            credalQFMCapacityEndpointInterval_lower_nonneg
              endpoint hEndpoint_nonneg hEndpoint_le_one 1
        · exact le_trans
            (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one 1).valid
            (credalQFMCapacityEndpointInterval_upper_le_one
              endpoint hEndpoint_nonneg hEndpoint_le_one 1)
      exact
        Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens_mono_of_background_le
          hPremiseLower
          hc.1
          (by linarith [hc.2])
          hcLower
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)
  · apply csSup_le
    · exact Set.range_nonempty fun k =>
        Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens
          (endpoint k 0) (endpoint k 1) c
    · rintro r ⟨k, rfl⟩
      have hcValue :
          c * (1 + endpoint k 0) ≤ endpoint k 0 :=
        Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens_background_le_of_le
          (by linarith [hc.2])
          hcLower
          (credalQFMCapacityEndpointInterval_lower_le_value
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
      exact
        Mettapedia.Logic.PLNInferenceRules.symmetricModusPonens_mono_of_background_le
          ⟨hEndpoint_nonneg k 1, hEndpoint_le_one k 1⟩
          hc.1
          (by linarith [hc.2])
          hcValue
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 0 k)
          (credalQFMCapacityEndpointInterval_value_le_upper
            endpoint hEndpoint_nonneg hEndpoint_le_one 1 k)

/-- Independent-endpoint hull for a finite QFM capacity rule. The
same-completion rule interval is contained in this hull; equality would require
extra independence/correlation assumptions and is intentionally not claimed. -/
noncomputable def credalQFMCapacityFiniteRuleHull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval where
  lower :=
    F (fun j =>
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one j).lower)
  upper :=
    F (fun j =>
      (credalQFMCapacityEndpointInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one j).upper)
  valid := by
    exact hmono
      (fun j =>
        credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one j)
      (fun j =>
        credalQFMCapacityEndpointInterval_upper_le_one
          endpoint hEndpoint_nonneg hEndpoint_le_one j)
      (fun j =>
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one j).valid)

theorem credalQFMCapacityFiniteRuleInterval_containedIn_hull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityFiniteRuleInterval
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).containedIn
      (credalQFMCapacityFiniteRuleHull
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one) := by
  unfold Interval.containedIn credalQFMCapacityFiniteRuleInterval
    credalQFMCapacityFiniteRuleHull
  dsimp [IntervalAddSemantics.intervalOf]
  constructor
  · apply le_csInf
    · exact Set.range_nonempty fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k
    · rintro r ⟨k, rfl⟩
      exact hmono
        (fun j =>
          credalQFMCapacityEndpointInterval_lower_nonneg
            endpoint hEndpoint_nonneg hEndpoint_le_one j)
        (fun j => hEndpoint_le_one k j)
        (fun j => by
          unfold credalQFMCapacityEndpointInterval
          dsimp [IntervalAddSemantics.intervalOf]
          exact csInf_le
            (⟨0, by
              rintro r ⟨k, rfl⟩
              exact hEndpoint_nonneg k j⟩)
            ⟨k, rfl⟩)
  · apply csSup_le
    · exact Set.range_nonempty fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k
    · rintro r ⟨k, rfl⟩
      exact hmono
        (fun j => hEndpoint_nonneg k j)
        (fun j =>
          credalQFMCapacityEndpointInterval_upper_le_one
            endpoint hEndpoint_nonneg hEndpoint_le_one j)
        (fun j => by
          unfold credalQFMCapacityEndpointInterval
          dsimp [IntervalAddSemantics.intervalOf]
          exact le_csSup
            (⟨1, by
              rintro r ⟨k, rfl⟩
              exact hEndpoint_le_one k j⟩)
            ⟨k, rfl⟩)

/-- Lower endpoint tightness for the QFM/capacity independent hull: if one
capacity/reference-class completion simultaneously realizes every marginal
lower endpoint, then the same-completion finite-rule lower endpoint is exactly
the hull lower endpoint. -/
theorem credalQFMCapacityFiniteRuleInterval_lower_eq_hull_lower_of_joint_lower_realizer
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hreal :
      ∃ k0 : κ,
        ∀ j : Fin n,
          endpoint k0 j =
            (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one j).lower) :
    (credalQFMCapacityFiniteRuleInterval
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).lower =
      (credalQFMCapacityFiniteRuleHull
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).lower := by
  apply le_antisymm
  · obtain ⟨k0, hk0⟩ := hreal
    unfold credalQFMCapacityFiniteRuleInterval
      credalQFMCapacityFiniteRuleHull
    dsimp [IntervalAddSemantics.intervalOf]
    have hle :
        sInf (Set.range fun k =>
          credalQFMCapacityFiniteRuleValue endpoint F k) ≤
          credalQFMCapacityFiniteRuleValue endpoint F k0 :=
      csInf_le
        (credalQFMCapacityFiniteRuleValue_bddBelow
          endpoint F hmono hEndpoint_nonneg hEndpoint_le_one) ⟨k0, rfl⟩
    have hpoint :
        endpoint k0 =
          fun j : Fin n =>
            (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one j).lower :=
      funext hk0
    simpa [credalQFMCapacityFiniteRuleValue, hpoint] using hle
  · exact
      (credalQFMCapacityFiniteRuleInterval_containedIn_hull
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).1

/-- Upper endpoint tightness for the QFM/capacity independent hull: if one
capacity/reference-class completion simultaneously realizes every marginal
upper endpoint, then the same-completion finite-rule upper endpoint is exactly
the hull upper endpoint. -/
theorem credalQFMCapacityFiniteRuleInterval_upper_eq_hull_upper_of_joint_upper_realizer
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hreal :
      ∃ k0 : κ,
        ∀ j : Fin n,
          endpoint k0 j =
            (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one j).upper) :
    (credalQFMCapacityFiniteRuleInterval
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).upper =
      (credalQFMCapacityFiniteRuleHull
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).upper := by
  apply le_antisymm
  · exact
      (credalQFMCapacityFiniteRuleInterval_containedIn_hull
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).2
  · obtain ⟨k0, hk0⟩ := hreal
    unfold credalQFMCapacityFiniteRuleInterval
      credalQFMCapacityFiniteRuleHull
    dsimp [IntervalAddSemantics.intervalOf]
    have hle :
        credalQFMCapacityFiniteRuleValue endpoint F k0 ≤
          sSup (Set.range fun k =>
            credalQFMCapacityFiniteRuleValue endpoint F k) :=
      le_csSup
        (credalQFMCapacityFiniteRuleValue_bddAbove
          endpoint F hmono hEndpoint_nonneg hEndpoint_le_one) ⟨k0, rfl⟩
    have hpoint :
        endpoint k0 =
          fun j : Fin n =>
            (credalQFMCapacityEndpointInterval
              endpoint hEndpoint_nonneg hEndpoint_le_one j).upper :=
      funext hk0
    simpa [credalQFMCapacityFiniteRuleValue, hpoint] using hle

theorem credalQFMCapacityFiniteRuleHull_lower_nonneg
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0)) :
    0 ≤
      (credalQFMCapacityFiniteRuleHull
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).lower := by
  unfold credalQFMCapacityFiniteRuleHull
  dsimp
  exact le_trans hzero
    (hmono
      (fun _ => by norm_num)
      (fun j => le_trans
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one j).valid
        (credalQFMCapacityEndpointInterval_upper_le_one
          endpoint hEndpoint_nonneg hEndpoint_le_one j))
      (fun j =>
        credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one j))

theorem credalQFMCapacityFiniteRuleHull_upper_le_one
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hone : F (fun _ => 1) ≤ 1) :
    (credalQFMCapacityFiniteRuleHull
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).upper ≤ 1 := by
  unfold credalQFMCapacityFiniteRuleHull
  dsimp
  exact le_trans
    (hmono
      (fun j => le_trans
        (credalQFMCapacityEndpointInterval_lower_nonneg
          endpoint hEndpoint_nonneg hEndpoint_le_one j)
        (credalQFMCapacityEndpointInterval
          endpoint hEndpoint_nonneg hEndpoint_le_one j).valid)
      (fun _ => by norm_num)
      (fun j =>
        credalQFMCapacityEndpointInterval_upper_le_one
          endpoint hEndpoint_nonneg hEndpoint_le_one j))
    hone

theorem credalQFMCapacityFiniteRuleInterval_lower_nonneg
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0)) :
    0 ≤
      (credalQFMCapacityFiniteRuleInterval
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).lower := by
  unfold credalQFMCapacityFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_trans hzero
    (le_csInf
      (Set.range_nonempty fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k)
      (by
        rintro r ⟨k, rfl⟩
        exact hmono
          (fun _ => by norm_num)
          (fun j => hEndpoint_le_one k j)
          (fun j => hEndpoint_nonneg k j)))

theorem credalQFMCapacityFiniteRuleInterval_upper_le_one
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hone : F (fun _ => 1) ≤ 1) :
    (credalQFMCapacityFiniteRuleInterval
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).upper ≤ 1 := by
  unfold credalQFMCapacityFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  exact le_trans
    (csSup_le
      (Set.range_nonempty fun k =>
        credalQFMCapacityFiniteRuleValue endpoint F k)
      (by
        rintro r ⟨k, rfl⟩
        exact hmono
          (fun j => hEndpoint_nonneg k j)
          (fun _ => by norm_num)
          (fun j => hEndpoint_le_one k j)))
    hone

/-- PLN truth-value view of a same-completion finite QFM capacity-rule
interval. This is the generic ITV packaging point for QFM-side multi-premise
rules over capacity/reference-class completions. -/
noncomputable def credalQFMCapacityFiniteRuleITV
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I :=
    credalQFMCapacityFiniteRuleInterval
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalQFMCapacityFiniteRuleInterval_lower_nonneg
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one hzero)
    (credalQFMCapacityFiniteRuleInterval_upper_le_one
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one hone)
    hcred

@[simp] theorem credalQFMCapacityFiniteRuleITV_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityFiniteRuleITV
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one hzero hone
      credibility hcred).lower =
      (credalQFMCapacityFiniteRuleInterval
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).lower := by
  simp [credalQFMCapacityFiniteRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalQFMCapacityFiniteRuleITV_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityFiniteRuleITV
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one hzero hone
      credibility hcred).upper =
      (credalQFMCapacityFiniteRuleInterval
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one).upper := by
  simp [credalQFMCapacityFiniteRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalQFMCapacityFiniteRuleITV_credibility
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityFiniteRuleITV
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one hzero hone
      credibility hcred).credibility = credibility := by
  simp [credalQFMCapacityFiniteRuleITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

/-- Product multi-join interval for QFM capacity endpoints: multiply the
endpoint values inside each capacity/reference-class completion, then envelope
across completions. -/
noncomputable def credalQFMCapacityProductMultiJoinInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval :=
  credalQFMCapacityFiniteRuleInterval endpoint (@productMultiJoin n)
    productMultiJoin_monotone_on_unit hEndpoint_nonneg hEndpoint_le_one

/-- Independent-endpoint hull for QFM/capacity product multi-join. -/
noncomputable def credalQFMCapacityProductMultiJoinHull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval :=
  credalQFMCapacityFiniteRuleHull endpoint (@productMultiJoin n)
    productMultiJoin_monotone_on_unit hEndpoint_nonneg hEndpoint_le_one

@[simp] theorem credalQFMCapacityProductMultiJoinHull_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityProductMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).lower =
      productMultiJoin
        (fun j =>
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one j).lower) := rfl

@[simp] theorem credalQFMCapacityProductMultiJoinHull_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityProductMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).upper =
      productMultiJoin
        (fun j =>
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one j).upper) := rfl

theorem credalQFMCapacityProductMultiJoinInterval_containedIn_hull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityProductMultiJoinInterval
      endpoint hEndpoint_nonneg hEndpoint_le_one).containedIn
      (credalQFMCapacityProductMultiJoinHull
        endpoint hEndpoint_nonneg hEndpoint_le_one) := by
  exact
    credalQFMCapacityFiniteRuleInterval_containedIn_hull
      endpoint (@productMultiJoin n) productMultiJoin_monotone_on_unit
      hEndpoint_nonneg hEndpoint_le_one

theorem credalQFMCapacityProductMultiJoinHull_lower_nonneg
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    0 ≤
      (credalQFMCapacityProductMultiJoinHull
        endpoint hEndpoint_nonneg hEndpoint_le_one).lower :=
  credalQFMCapacityFiniteRuleHull_lower_nonneg
    endpoint (@productMultiJoin n) productMultiJoin_monotone_on_unit
    hEndpoint_nonneg hEndpoint_le_one productMultiJoin_zero_nonneg

theorem credalQFMCapacityProductMultiJoinHull_upper_le_one
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityProductMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).upper ≤ 1 :=
  credalQFMCapacityFiniteRuleHull_upper_le_one
    endpoint (@productMultiJoin n) productMultiJoin_monotone_on_unit
    hEndpoint_nonneg hEndpoint_le_one productMultiJoin_one_le_one

/-- PLN truth-value view of the QFM capacity product multi-join interval. -/
noncomputable def credalQFMCapacityProductMultiJoinITV
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteRuleITV endpoint (@productMultiJoin n)
    productMultiJoin_monotone_on_unit hEndpoint_nonneg hEndpoint_le_one
    productMultiJoin_zero_nonneg productMultiJoin_one_le_one
    credibility hcred

@[simp] theorem credalQFMCapacityProductMultiJoinITV_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityProductMultiJoinITV
      endpoint hEndpoint_nonneg hEndpoint_le_one credibility hcred).lower =
      (credalQFMCapacityProductMultiJoinInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one).lower := by
  rfl

@[simp] theorem credalQFMCapacityProductMultiJoinITV_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityProductMultiJoinITV
      endpoint hEndpoint_nonneg hEndpoint_le_one credibility hcred).upper =
      (credalQFMCapacityProductMultiJoinInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one).upper := by
  rfl

@[simp] theorem credalQFMCapacityProductMultiJoinITV_credibility
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityProductMultiJoinITV
      endpoint hEndpoint_nonneg hEndpoint_le_one credibility hcred).credibility =
      credibility := by
  simp [credalQFMCapacityProductMultiJoinITV]

/-- Noisy-OR multi-join interval for QFM capacity endpoints: combine endpoint
values inside each capacity/reference-class completion, then envelope across
completions. -/
noncomputable def credalQFMCapacityNoisyOrMultiJoinInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval :=
  credalQFMCapacityFiniteRuleInterval endpoint (@noisyOrMultiJoin n)
    noisyOrMultiJoin_monotone_on_unit hEndpoint_nonneg hEndpoint_le_one

/-- Same-completion De Morgan law for QFM/capacity multi-joins, lower
endpoint. Noisy-OR over the endpoint family is the complement of the upper
endpoint of product over the pointwise-complement endpoint family, with both
intervals ranging over the same capacity/reference-class completions. -/
theorem credalQFMCapacityNoisyOrMultiJoinInterval_lower_eq_one_sub_product_compl_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinInterval
      endpoint hEndpoint_nonneg hEndpoint_le_one).lower =
      1 -
        (credalQFMCapacityProductMultiJoinInterval
          (fun k j => 1 - endpoint k j)
          (fun k j => sub_nonneg.mpr (hEndpoint_le_one k j))
          (fun k j => by linarith [hEndpoint_nonneg k j])).upper := by
  unfold credalQFMCapacityNoisyOrMultiJoinInterval
    credalQFMCapacityProductMultiJoinInterval
    credalQFMCapacityFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_antisymm
  · have hsup_le :
        sSup (Set.range fun k =>
          credalQFMCapacityFiniteRuleValue
            (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) ≤
          1 - sInf (Set.range fun k =>
            credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k) := by
      apply csSup_le
      · exact Set.range_nonempty fun k =>
          credalQFMCapacityFiniteRuleValue
            (fun k j => 1 - endpoint k j) (@productMultiJoin n) k
      · rintro r ⟨k, rfl⟩
        have hlower :
            sInf (Set.range fun k =>
              credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k) ≤
                credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k := by
          exact csInf_le
            (credalQFMCapacityFiniteRuleValue_bddBelow
              endpoint (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
              hEndpoint_nonneg hEndpoint_le_one) ⟨k, rfl⟩
        rw [credalQFMCapacityFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl] at hlower
        change
          productMultiJoin (fun j => 1 - endpoint k j) ≤
            1 - sInf (Set.range fun k =>
              credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k)
        linarith
    linarith
  · apply le_csInf
    · exact Set.range_nonempty fun k =>
        credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k
    · rintro r ⟨k, rfl⟩
      have hle :
          credalQFMCapacityFiniteRuleValue
            (fun k j => 1 - endpoint k j) (@productMultiJoin n) k ≤
            sSup (Set.range fun k =>
              credalQFMCapacityFiniteRuleValue
                (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) := by
        exact le_csSup
          (credalQFMCapacityFiniteRuleValue_bddAbove
            (fun k j => 1 - endpoint k j) (@productMultiJoin n)
            productMultiJoin_monotone_on_unit
            (fun k j => sub_nonneg.mpr (hEndpoint_le_one k j))
            (fun k j => by linarith [hEndpoint_nonneg k j])) ⟨k, rfl⟩
      have hle' :
          productMultiJoin (fun j => 1 - endpoint k j) ≤
            sSup (Set.range fun k =>
              credalQFMCapacityFiniteRuleValue
                (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) := by
        simpa [credalQFMCapacityFiniteRuleValue] using hle
      change
        1 - sSup (Set.range fun k =>
          credalQFMCapacityFiniteRuleValue
            (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) ≤
          credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k
      rw [credalQFMCapacityFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl]
      linarith

/-- Same-completion De Morgan law for QFM/capacity multi-joins, upper
endpoint. This is the dual endpoint to
`credalQFMCapacityNoisyOrMultiJoinInterval_lower_eq_one_sub_product_compl_upper`. -/
theorem credalQFMCapacityNoisyOrMultiJoinInterval_upper_eq_one_sub_product_compl_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinInterval
      endpoint hEndpoint_nonneg hEndpoint_le_one).upper =
      1 -
        (credalQFMCapacityProductMultiJoinInterval
          (fun k j => 1 - endpoint k j)
          (fun k j => sub_nonneg.mpr (hEndpoint_le_one k j))
          (fun k j => by linarith [hEndpoint_nonneg k j])).lower := by
  unfold credalQFMCapacityNoisyOrMultiJoinInterval
    credalQFMCapacityProductMultiJoinInterval
    credalQFMCapacityFiniteRuleInterval
  dsimp [IntervalAddSemantics.intervalOf]
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty fun k =>
        credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k
    · rintro r ⟨k, rfl⟩
      have hlow :
          sInf (Set.range fun k =>
            credalQFMCapacityFiniteRuleValue
              (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) ≤
            credalQFMCapacityFiniteRuleValue
              (fun k j => 1 - endpoint k j) (@productMultiJoin n) k := by
        exact csInf_le
          (credalQFMCapacityFiniteRuleValue_bddBelow
            (fun k j => 1 - endpoint k j) (@productMultiJoin n)
            productMultiJoin_monotone_on_unit
            (fun k j => sub_nonneg.mpr (hEndpoint_le_one k j))
            (fun k j => by linarith [hEndpoint_nonneg k j])) ⟨k, rfl⟩
      have hlow' :
          sInf (Set.range fun k =>
            credalQFMCapacityFiniteRuleValue
              (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) ≤
            productMultiJoin (fun j => 1 - endpoint k j) := by
        simpa [credalQFMCapacityFiniteRuleValue] using hlow
      have hNoisy :
          credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k =
            1 - productMultiJoin (fun j => 1 - endpoint k j) := by
        exact credalQFMCapacityFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl
          endpoint k
      dsimp
      rw [hNoisy]
      linarith
  · have hle :
        1 - sSup (Set.range fun k =>
          credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k) ≤
          sInf (Set.range fun k =>
            credalQFMCapacityFiniteRuleValue
              (fun k j => 1 - endpoint k j) (@productMultiJoin n) k) := by
      apply le_csInf
      · exact Set.range_nonempty fun k =>
          credalQFMCapacityFiniteRuleValue
            (fun k j => 1 - endpoint k j) (@productMultiJoin n) k
      · rintro r ⟨k, rfl⟩
        have hnoisy_le :
            credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k ≤
              sSup (Set.range fun k =>
                credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k) := by
          exact le_csSup
            (credalQFMCapacityFiniteRuleValue_bddAbove
              endpoint (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
              hEndpoint_nonneg hEndpoint_le_one) ⟨k, rfl⟩
        have hNoisy :
            credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k =
              1 - productMultiJoin (fun j => 1 - endpoint k j) := by
          exact credalQFMCapacityFiniteRuleValue_noisyOr_eq_one_sub_productMultiJoin_compl
            endpoint k
        rw [hNoisy] at hnoisy_le
        change
          1 - sSup (Set.range fun k =>
            credalQFMCapacityFiniteRuleValue endpoint (@noisyOrMultiJoin n) k) ≤
            productMultiJoin (fun j => 1 - endpoint k j)
        linarith
    linarith

/-- Independent-endpoint hull for QFM/capacity noisy-OR multi-join. -/
noncomputable def credalQFMCapacityNoisyOrMultiJoinHull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) : Interval :=
  credalQFMCapacityFiniteRuleHull endpoint (@noisyOrMultiJoin n)
    noisyOrMultiJoin_monotone_on_unit hEndpoint_nonneg hEndpoint_le_one

@[simp] theorem credalQFMCapacityNoisyOrMultiJoinHull_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).lower =
      noisyOrMultiJoin
        (fun j =>
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one j).lower) := rfl

@[simp] theorem credalQFMCapacityNoisyOrMultiJoinHull_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).upper =
      noisyOrMultiJoin
        (fun j =>
          (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one j).upper) := rfl

theorem credalQFMCapacityNoisyOrMultiJoinHull_lower_eq_one_sub_product_compl
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).lower =
      1 - productMultiJoin
        (fun j =>
          1 - (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one j).lower) := by
  rw [credalQFMCapacityNoisyOrMultiJoinHull_lower,
    noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]

theorem credalQFMCapacityNoisyOrMultiJoinHull_upper_eq_one_sub_product_compl
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).upper =
      1 - productMultiJoin
        (fun j =>
          1 - (credalQFMCapacityEndpointInterval
            endpoint hEndpoint_nonneg hEndpoint_le_one j).upper) := by
  rw [credalQFMCapacityNoisyOrMultiJoinHull_upper,
    noisyOrMultiJoin_eq_one_sub_productMultiJoin_compl]

theorem credalQFMCapacityNoisyOrMultiJoinInterval_containedIn_hull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinInterval
      endpoint hEndpoint_nonneg hEndpoint_le_one).containedIn
      (credalQFMCapacityNoisyOrMultiJoinHull
        endpoint hEndpoint_nonneg hEndpoint_le_one) := by
  exact
    credalQFMCapacityFiniteRuleInterval_containedIn_hull
      endpoint (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
      hEndpoint_nonneg hEndpoint_le_one

theorem credalQFMCapacityNoisyOrMultiJoinHull_lower_nonneg
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    0 ≤
      (credalQFMCapacityNoisyOrMultiJoinHull
        endpoint hEndpoint_nonneg hEndpoint_le_one).lower :=
  credalQFMCapacityFiniteRuleHull_lower_nonneg
    endpoint (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
    hEndpoint_nonneg hEndpoint_le_one noisyOrMultiJoin_zero_nonneg

theorem credalQFMCapacityNoisyOrMultiJoinHull_upper_le_one
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    (credalQFMCapacityNoisyOrMultiJoinHull
      endpoint hEndpoint_nonneg hEndpoint_le_one).upper ≤ 1 :=
  credalQFMCapacityFiniteRuleHull_upper_le_one
    endpoint (@noisyOrMultiJoin n) noisyOrMultiJoin_monotone_on_unit
    hEndpoint_nonneg hEndpoint_le_one noisyOrMultiJoin_one_le_one

/-- PLN truth-value view of the QFM capacity noisy-OR multi-join interval. -/
noncomputable def credalQFMCapacityNoisyOrMultiJoinITV
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteRuleITV endpoint (@noisyOrMultiJoin n)
    noisyOrMultiJoin_monotone_on_unit hEndpoint_nonneg hEndpoint_le_one
    noisyOrMultiJoin_zero_nonneg noisyOrMultiJoin_one_le_one
    credibility hcred

@[simp] theorem credalQFMCapacityNoisyOrMultiJoinITV_lower
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityNoisyOrMultiJoinITV
      endpoint hEndpoint_nonneg hEndpoint_le_one credibility hcred).lower =
      (credalQFMCapacityNoisyOrMultiJoinInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one).lower := by
  rfl

@[simp] theorem credalQFMCapacityNoisyOrMultiJoinITV_upper
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityNoisyOrMultiJoinITV
      endpoint hEndpoint_nonneg hEndpoint_le_one credibility hcred).upper =
      (credalQFMCapacityNoisyOrMultiJoinInterval
        endpoint hEndpoint_nonneg hEndpoint_le_one).upper := by
  rfl

@[simp] theorem credalQFMCapacityNoisyOrMultiJoinITV_credibility
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalQFMCapacityNoisyOrMultiJoinITV
      endpoint hEndpoint_nonneg hEndpoint_le_one credibility hcred).credibility =
      credibility := by
  simp [credalQFMCapacityNoisyOrMultiJoinITV]

/-- Finite-rule multi-join collapse for QFM capacity endpoints: if all
capacity/reference-class completions agree after the monotone rule is applied,
the same-completion interval is exactly the corresponding point interval. -/
theorem credalQFMCapacityFiniteRuleInterval_eq_const_of_pointwise_value_eq
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (c : ℝ)
    (hVal :
      ∀ k, credalQFMCapacityFiniteRuleValue endpoint F k = c) :
    credalQFMCapacityFiniteRuleInterval
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one =
      constInterval c := by
  classical
  have hEq :
      Set.range (fun k => credalQFMCapacityFiniteRuleValue endpoint F k) =
        {c} := by
    ext r
    constructor
    · rintro ⟨k, rfl⟩
      exact hVal k
    · intro hr
      rcases (inferInstance : Nonempty κ) with ⟨k0⟩
      rw [Set.mem_singleton_iff] at hr
      exact ⟨k0, by
        change credalQFMCapacityFiniteRuleValue endpoint F k0 = r
        rw [hVal k0, ← hr]⟩
  simp [credalQFMCapacityFiniteRuleInterval,
    IntervalAddSemantics.intervalOf, hEq, constInterval]

/-- Singleton capacity/reference-class families collapse to point-valued
monotone finite-rule QFM multi-joins. -/
theorem credalQFMCapacityFiniteRuleInterval_eq_const_of_subsingleton
    {κ : Type x} [Subsingleton κ] [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (k0 : κ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1) :
    credalQFMCapacityFiniteRuleInterval
        endpoint F hmono hEndpoint_nonneg hEndpoint_le_one =
      constInterval (credalQFMCapacityFiniteRuleValue endpoint F k0) := by
  exact
    credalQFMCapacityFiniteRuleInterval_eq_const_of_pointwise_value_eq
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one
      (credalQFMCapacityFiniteRuleValue endpoint F k0)
      (fun k => by
        have : k = k0 := Subsingleton.elim k k0
        simp [this])

/-- When a monotone finite-rule QFM multi-join collapses to a point interval,
its PLN truth-value width is zero. -/
theorem credalQFMCapacityFiniteRuleITV_width_eq_zero_of_pointwise_value_eq
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (endpoint : κ → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hEndpoint_nonneg : ∀ k j, 0 ≤ endpoint k j)
    (hEndpoint_le_one : ∀ k j, endpoint k j ≤ 1)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (c credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (hVal :
      ∀ k, credalQFMCapacityFiniteRuleValue endpoint F k = c) :
    (credalQFMCapacityFiniteRuleITV
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one hzero hone
      credibility hcred).width = 0 := by
  have hI :
      credalQFMCapacityFiniteRuleInterval
          endpoint F hmono hEndpoint_nonneg hEndpoint_le_one =
        constInterval c :=
    credalQFMCapacityFiniteRuleInterval_eq_const_of_pointwise_value_eq
      endpoint F hmono hEndpoint_nonneg hEndpoint_le_one c hVal
  simp [Mettapedia.Logic.PLNIndefiniteTruth.ITV.width,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    credalQFMCapacityFiniteRuleITV, hI, constInterval]

/-- Same-completion finite-rule interval for the QFM universal endpoint of a
finite family of HOL predicates. -/
noncomputable def credalPredicateQFMForAllFiniteRuleInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) : Interval :=
  credalQFMCapacityFiniteRuleInterval
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    F hmono
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs (ps j) k)

/-- Independent-endpoint hull for finite QFM universal endpoint rules. -/
noncomputable def credalPredicateQFMForAllFiniteRuleHull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) : Interval :=
  credalQFMCapacityFiniteRuleHull
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    F hmono
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs (ps j) k)

theorem credalPredicateQFMForAllFiniteRuleInterval_containedIn_hull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) :
    (credalPredicateQFMForAllFiniteRuleInterval
        (Base := Base) (Const := Const) M σ νs ps F hmono).containedIn
      (credalPredicateQFMForAllFiniteRuleHull
        (Base := Base) (Const := Const) M σ νs ps F hmono) := by
  exact
    credalQFMCapacityFiniteRuleInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMForAllCapacityValue
          (Base := Base) (Const := Const) M σ νs (ps j) k)
      F hmono
      (fun k j =>
        credalPredicateQFMForAllCapacityValue_nonneg
          (Base := Base) (Const := Const) M σ νs (ps j) k)
      (fun k j =>
        credalPredicateQFMForAllCapacityValue_le_one
          (Base := Base) (Const := Const) M σ νs (ps j) k)

/-- PLN truth-value view of same-completion finite rules over QFM universal
endpoint capacities. -/
noncomputable def credalPredicateQFMForAllFiniteRuleITV
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteRuleITV
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    F hmono
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    hzero hone credibility hcred

/-- Same-completion finite-rule interval for the QFM existential endpoint of a
finite family of HOL predicates. -/
noncomputable def credalPredicateQFMThereExistsFiniteRuleInterval
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) : Interval :=
  credalQFMCapacityFiniteRuleInterval
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    F hmono
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs (ps j) k)

/-- Independent-endpoint hull for finite QFM existential endpoint rules. -/
noncomputable def credalPredicateQFMThereExistsFiniteRuleHull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) : Interval :=
  credalQFMCapacityFiniteRuleHull
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    F hmono
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs (ps j) k)

theorem credalPredicateQFMThereExistsFiniteRuleInterval_containedIn_hull
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F) :
    (credalPredicateQFMThereExistsFiniteRuleInterval
        (Base := Base) (Const := Const) M σ νs ps F hmono).containedIn
      (credalPredicateQFMThereExistsFiniteRuleHull
        (Base := Base) (Const := Const) M σ νs ps F hmono) := by
  exact
    credalQFMCapacityFiniteRuleInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMThereExistsCapacityValue
          (Base := Base) (Const := Const) M σ νs (ps j) k)
      F hmono
      (fun k j =>
        credalPredicateQFMThereExistsCapacityValue_nonneg
          (Base := Base) (Const := Const) M σ νs (ps j) k)
      (fun k j =>
        credalPredicateQFMThereExistsCapacityValue_le_one
          (Base := Base) (Const := Const) M σ νs (ps j) k)

/-- PLN truth-value view of same-completion finite rules over QFM existential
endpoint capacities. -/
noncomputable def credalPredicateQFMThereExistsFiniteRuleITV
    {κ : Type x} [Nonempty κ] {n : ℕ}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (ps : Fin n → UnaryPredicate (Base := Base) (Const := Const) σ)
    (F : (Fin n → ℝ) → ℝ)
    (hmono : FiniteRuleMonotoneOnUnit F)
    (hzero : 0 ≤ F (fun _ => 0))
    (hone : F (fun _ => 1) ≤ 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteRuleITV
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    F hmono
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs (ps j) k)
    hzero hone credibility hcred

/-! ## Concrete QFM consumers of PLN rule formulas -/

/-- Package two directed QFM endpoint predicates as the two inputs expected by
binary PLN rule formulas such as `2inh2sim`. In similarity applications these
are the forward and reverse directed inheritance/evidence predicates. -/
def directedPredicateEndpointPair
    (σ : Ty Base)
    (forward reverse : UnaryPredicate (Base := Base) (Const := Const) σ) :
    Fin 2 → UnaryPredicate (Base := Base) (Const := Const) σ :=
  fun j => if j = 0 then forward else reverse

/-- Package the three endpoint predicates expected by ternary PLN rule
formulas such as `sim2inh`: similarity, source term strength, target term
strength. -/
def predicateEndpointTriple
    (σ : Ty Base)
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ) :
    Fin 3 → UnaryPredicate (Base := Base) (Const := Const) σ :=
  fun j => if j = 0 then similarity else if j = 1 then source else target

/-- Same-completion QFM universal-endpoint interval for PLN modus ponens with
a fixed background/default parameter. Input `implication` is the conditional
strength endpoint and `premise` is the premise-strength endpoint. Since modus
ponens is bounded but not globally monotone in all coordinates, this gives a
same-completion interval but intentionally no independent-endpoint hull. -/
noncomputable def credalPredicateQFMForAllModusPonensInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : Interval :=
  credalQFMCapacityFiniteBoundedRuleInterval
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (modusPonensAsFinite2 c)
    (modusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)

/-- Independent-endpoint hull for QFM universal modus ponens under the side
condition that the implication endpoint's lower bound is at least the
background/default `c`. -/
noncomputable def credalPredicateQFMForAllModusPonensHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hcLower :
      c ≤
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs implication).lower) :
    Interval :=
  credalQFMCapacityModusPonensHull
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    c
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (by
      simpa [credalPredicateQFMForAllCapacityInterval,
        credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
        using hcLower)

theorem credalPredicateQFMForAllModusPonensInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hcLower :
      c ≤
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs implication).lower) :
    (credalPredicateQFMForAllModusPonensInterval
        (Base := Base) (Const := Const) M σ νs implication premise c hc).containedIn
      (credalPredicateQFMForAllModusPonensHull
        (Base := Base) (Const := Const) M σ νs implication premise
        c hcLower) := by
  exact
    credalQFMCapacityModusPonensBoundedRuleInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMForAllCapacityValue
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ implication premise) j) k)
      c hc
      (fun k j =>
        credalPredicateQFMForAllCapacityValue_nonneg
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ implication premise) j) k)
      (fun k j =>
        credalPredicateQFMForAllCapacityValue_le_one
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ implication premise) j) k)
      (by
        simpa [credalPredicateQFMForAllCapacityInterval,
          credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
          using hcLower)

/-- ITV packaging for QFM universal modus ponens. -/
noncomputable def credalPredicateQFMForAllModusPonensITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteBoundedRuleITV
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (modusPonensAsFinite2 c)
    (modusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    credibility hcred

/-- Same-completion QFM existential-endpoint interval for PLN modus ponens with
a fixed background/default parameter. -/
noncomputable def credalPredicateQFMThereExistsModusPonensInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : Interval :=
  credalQFMCapacityFiniteBoundedRuleInterval
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (modusPonensAsFinite2 c)
    (modusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)

/-- Independent-endpoint hull for QFM existential modus ponens under the side
condition that the implication endpoint's lower bound is at least the
background/default `c`. -/
noncomputable def credalPredicateQFMThereExistsModusPonensHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hcLower :
      c ≤
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs implication).lower) :
    Interval :=
  credalQFMCapacityModusPonensHull
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    c
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (by
      simpa [credalPredicateQFMThereExistsCapacityInterval,
        credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
        using hcLower)

theorem credalPredicateQFMThereExistsModusPonensInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hcLower :
      c ≤
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs implication).lower) :
    (credalPredicateQFMThereExistsModusPonensInterval
        (Base := Base) (Const := Const) M σ νs implication premise c hc).containedIn
      (credalPredicateQFMThereExistsModusPonensHull
        (Base := Base) (Const := Const) M σ νs implication premise
        c hcLower) := by
  exact
    credalQFMCapacityModusPonensBoundedRuleInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMThereExistsCapacityValue
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ implication premise) j) k)
      c hc
      (fun k j =>
        credalPredicateQFMThereExistsCapacityValue_nonneg
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ implication premise) j) k)
      (fun k j =>
        credalPredicateQFMThereExistsCapacityValue_le_one
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ implication premise) j) k)
      (by
        simpa [credalPredicateQFMThereExistsCapacityInterval,
          credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
          using hcLower)

/-- ITV packaging for QFM existential modus ponens. -/
noncomputable def credalPredicateQFMThereExistsModusPonensITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (implication premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteBoundedRuleITV
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (modusPonensAsFinite2 c)
    (modusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ implication premise) j) k)
    credibility hcred

/-- Same-completion QFM universal-endpoint interval for PLN symmetric modus
ponens with a fixed background/default parameter. Input `similarity` is the
predicate-level similarity endpoint and `premise` is the premise-strength
endpoint. -/
noncomputable def credalPredicateQFMForAllSymmetricModusPonensInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5) : Interval :=
  credalQFMCapacityFiniteBoundedRuleInterval
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (symmetricModusPonensAsFinite2 c)
    (symmetricModusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)

/-- Independent-endpoint hull for QFM universal symmetric modus ponens under
the side condition that the similarity endpoint is high enough relative to
the background/default `c`. -/
noncomputable def credalPredicateQFMForAllSymmetricModusPonensHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (hcLower :
      c * (1 +
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) ≤
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) :
    Interval :=
  credalQFMCapacitySymmetricModusPonensHull
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    c hc
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (by
      simpa [credalPredicateQFMForAllCapacityInterval,
        credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
        using hcLower)

theorem credalPredicateQFMForAllSymmetricModusPonensInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (hcLower :
      c * (1 +
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) ≤
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) :
    (credalPredicateQFMForAllSymmetricModusPonensInterval
        (Base := Base) (Const := Const) M σ νs similarity premise c hc).containedIn
      (credalPredicateQFMForAllSymmetricModusPonensHull
        (Base := Base) (Const := Const) M σ νs similarity premise
        c hc hcLower) := by
  exact
    credalQFMCapacitySymmetricModusPonensBoundedRuleInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMForAllCapacityValue
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ similarity premise) j) k)
      c hc
      (fun k j =>
        credalPredicateQFMForAllCapacityValue_nonneg
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ similarity premise) j) k)
      (fun k j =>
        credalPredicateQFMForAllCapacityValue_le_one
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ similarity premise) j) k)
      (by
        simpa [credalPredicateQFMForAllCapacityInterval,
          credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
          using hcLower)

/-- ITV packaging for QFM universal symmetric modus ponens. -/
noncomputable def credalPredicateQFMForAllSymmetricModusPonensITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteBoundedRuleITV
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (symmetricModusPonensAsFinite2 c)
    (symmetricModusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (fun k j =>
      credalPredicateQFMForAllCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    credibility hcred

/-- Same-completion QFM existential-endpoint interval for PLN symmetric modus
ponens with a fixed background/default parameter. -/
noncomputable def credalPredicateQFMThereExistsSymmetricModusPonensInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5) : Interval :=
  credalQFMCapacityFiniteBoundedRuleInterval
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (symmetricModusPonensAsFinite2 c)
    (symmetricModusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)

/-- Independent-endpoint hull for QFM existential symmetric modus ponens under
the side condition that the similarity endpoint is high enough relative to
the background/default `c`. -/
noncomputable def credalPredicateQFMThereExistsSymmetricModusPonensHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (hcLower :
      c * (1 +
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) ≤
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) :
    Interval :=
  credalQFMCapacitySymmetricModusPonensHull
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    c hc
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (by
      simpa [credalPredicateQFMThereExistsCapacityInterval,
        credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
        using hcLower)

theorem credalPredicateQFMThereExistsSymmetricModusPonensInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (hcLower :
      c * (1 +
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) ≤
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs similarity).lower) :
    (credalPredicateQFMThereExistsSymmetricModusPonensInterval
        (Base := Base) (Const := Const) M σ νs similarity premise c hc).containedIn
      (credalPredicateQFMThereExistsSymmetricModusPonensHull
        (Base := Base) (Const := Const) M σ νs similarity premise
        c hc hcLower) := by
  exact
    credalQFMCapacitySymmetricModusPonensBoundedRuleInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMThereExistsCapacityValue
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ similarity premise) j) k)
      c hc
      (fun k j =>
        credalPredicateQFMThereExistsCapacityValue_nonneg
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ similarity premise) j) k)
      (fun k j =>
        credalPredicateQFMThereExistsCapacityValue_le_one
          (Base := Base) (Const := Const) M σ νs
          ((directedPredicateEndpointPair (Base := Base) (Const := Const)
            σ similarity premise) j) k)
      (by
        simpa [credalPredicateQFMThereExistsCapacityInterval,
          credalQFMCapacityEndpointInterval, directedPredicateEndpointPair]
          using hcLower)

/-- ITV packaging for QFM existential symmetric modus ponens. -/
noncomputable def credalPredicateQFMThereExistsSymmetricModusPonensITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity premise :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 0.5)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacityFiniteBoundedRuleITV
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (symmetricModusPonensAsFinite2 c)
    (symmetricModusPonensAsFinite2_mapsUnitToUnit c hc)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_nonneg
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    (fun k j =>
      credalPredicateQFMThereExistsCapacityValue_le_one
        (Base := Base) (Const := Const) M σ νs
        ((directedPredicateEndpointPair (Base := Base) (Const := Const)
          σ similarity premise) j) k)
    credibility hcred

/-- Same-completion QFM universal-endpoint interval for PLN `sim2inh`. This
is a constrained rule surface: each capacity/reference-class completion must
have a positive source-strength endpoint and a target-strength endpoint no
larger than the source-strength endpoint. -/
noncomputable def credalPredicateQFMForAllSim2InhInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSource_pos :
      ∀ k,
        0 <
          credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hTarget_le_source :
      ∀ k,
        credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs target k ≤
          credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs source k) :
    Interval :=
  credalQFMCapacitySim2InhInterval
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_le_one])
    (by
      intro k
      simpa [predicateEndpointTriple] using hSource_pos k)
    (by
      intro k
      simpa [predicateEndpointTriple] using hTarget_le_source k)

/-- ITV packaging for constrained QFM universal `sim2inh`. -/
noncomputable def credalPredicateQFMForAllSim2InhITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSource_pos :
      ∀ k,
        0 <
          credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hTarget_le_source :
      ∀ k,
        credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs target k ≤
          credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacitySim2InhITV
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_le_one])
    (by
      intro k
      simpa [predicateEndpointTriple] using hSource_pos k)
    (by
      intro k
      simpa [predicateEndpointTriple] using hTarget_le_source k)
    credibility hcred

/-- Same-completion QFM existential-endpoint interval for PLN `sim2inh`. -/
noncomputable def credalPredicateQFMThereExistsSim2InhInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSource_pos :
      ∀ k,
        0 <
          credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hTarget_le_source :
      ∀ k,
        credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs target k ≤
          credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs source k) :
    Interval :=
  credalQFMCapacitySim2InhInterval
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one])
    (by
      intro k
      simpa [predicateEndpointTriple] using hSource_pos k)
    (by
      intro k
      simpa [predicateEndpointTriple] using hTarget_le_source k)

/-- ITV packaging for constrained QFM existential `sim2inh`. -/
noncomputable def credalPredicateQFMThereExistsSim2InhITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSource_pos :
      ∀ k,
        0 <
          credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hTarget_le_source :
      ∀ k,
        credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs target k ≤
          credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacitySim2InhITV
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one])
    (by
      intro k
      simpa [predicateEndpointTriple] using hSource_pos k)
    (by
      intro k
      simpa [predicateEndpointTriple] using hTarget_le_source k)
    credibility hcred

/-- Independent-endpoint QFM universal hull for PLN `sim2inh`. -/
noncomputable def credalPredicateQFMForAllSim2InhHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSourceLower_pos :
      0 <
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower) :
    Interval :=
  credalQFMCapacitySim2InhHull
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_le_one])
    (by
      simpa [credalPredicateQFMForAllCapacityInterval,
        credalQFMCapacityEndpointInterval, predicateEndpointTriple]
        using hSourceLower_pos)

theorem credalPredicateQFMForAllSim2InhInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSource_pos :
      ∀ k,
        0 <
          credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hTarget_le_source :
      ∀ k,
        credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs target k ≤
          credalPredicateQFMForAllCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hSourceLower_pos :
      0 <
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower) :
    (credalPredicateQFMForAllSim2InhInterval
        (Base := Base) (Const := Const) M σ νs
        similarity source target hSource_pos hTarget_le_source).containedIn
      (credalPredicateQFMForAllSim2InhHull
        (Base := Base) (Const := Const) M σ νs
        similarity source target hSourceLower_pos) := by
  exact
    credalQFMCapacitySim2InhInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMForAllCapacityValue
          (Base := Base) (Const := Const) M σ νs
          ((predicateEndpointTriple (Base := Base) (Const := Const)
            σ similarity source target) j) k)
      (fun k j => by
        by_cases h0 : j = 0
        · simp [predicateEndpointTriple, h0,
            credalPredicateQFMForAllCapacityValue_nonneg]
        · by_cases h1 : j = 1
          · simp [predicateEndpointTriple, h1,
              credalPredicateQFMForAllCapacityValue_nonneg]
          · simp [predicateEndpointTriple, h0, h1,
              credalPredicateQFMForAllCapacityValue_nonneg])
      (fun k j => by
        by_cases h0 : j = 0
        · simp [predicateEndpointTriple, h0,
            credalPredicateQFMForAllCapacityValue_le_one]
        · by_cases h1 : j = 1
          · simp [predicateEndpointTriple, h1,
              credalPredicateQFMForAllCapacityValue_le_one]
          · simp [predicateEndpointTriple, h0, h1,
              credalPredicateQFMForAllCapacityValue_le_one])
      (by
        intro k
        simpa [predicateEndpointTriple] using hSource_pos k)
      (by
        intro k
        simpa [predicateEndpointTriple] using hTarget_le_source k)
      (by
        simpa [credalPredicateQFMForAllCapacityInterval,
          credalQFMCapacityEndpointInterval, predicateEndpointTriple]
          using hSourceLower_pos)

/-- ITV packaging for the independent-endpoint universal `sim2inh` hull. -/
noncomputable def credalPredicateQFMForAllSim2InhHullITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSourceLower_pos :
      0 <
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower)
    (hTargetUpper_le_sourceLower :
      (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs target).upper ≤
        (credalPredicateQFMForAllCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacitySim2InhHullITV
    (endpoint := fun k j =>
      credalPredicateQFMForAllCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMForAllCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMForAllCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMForAllCapacityValue_le_one])
    (by
      simpa [credalPredicateQFMForAllCapacityInterval,
        credalQFMCapacityEndpointInterval, predicateEndpointTriple]
        using hSourceLower_pos)
    (by
      simpa [credalPredicateQFMForAllCapacityInterval,
        credalQFMCapacityEndpointInterval, predicateEndpointTriple]
        using hTargetUpper_le_sourceLower)
    credibility hcred

/-- Independent-endpoint QFM existential hull for PLN `sim2inh`. -/
noncomputable def credalPredicateQFMThereExistsSim2InhHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSourceLower_pos :
      0 <
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower) :
    Interval :=
  credalQFMCapacitySim2InhHull
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one])
    (by
      simpa [credalPredicateQFMThereExistsCapacityInterval,
        credalQFMCapacityEndpointInterval, predicateEndpointTriple]
        using hSourceLower_pos)

theorem credalPredicateQFMThereExistsSim2InhInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSource_pos :
      ∀ k,
        0 <
          credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hTarget_le_source :
      ∀ k,
        credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs target k ≤
          credalPredicateQFMThereExistsCapacityValue
            (Base := Base) (Const := Const) M σ νs source k)
    (hSourceLower_pos :
      0 <
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower) :
    (credalPredicateQFMThereExistsSim2InhInterval
        (Base := Base) (Const := Const) M σ νs
        similarity source target hSource_pos hTarget_le_source).containedIn
      (credalPredicateQFMThereExistsSim2InhHull
        (Base := Base) (Const := Const) M σ νs
        similarity source target hSourceLower_pos) := by
  exact
    credalQFMCapacitySim2InhInterval_containedIn_hull
      (endpoint := fun k j =>
        credalPredicateQFMThereExistsCapacityValue
          (Base := Base) (Const := Const) M σ νs
          ((predicateEndpointTriple (Base := Base) (Const := Const)
            σ similarity source target) j) k)
      (fun k j => by
        by_cases h0 : j = 0
        · simp [predicateEndpointTriple, h0,
            credalPredicateQFMThereExistsCapacityValue_nonneg]
        · by_cases h1 : j = 1
          · simp [predicateEndpointTriple, h1,
              credalPredicateQFMThereExistsCapacityValue_nonneg]
          · simp [predicateEndpointTriple, h0, h1,
              credalPredicateQFMThereExistsCapacityValue_nonneg])
      (fun k j => by
        by_cases h0 : j = 0
        · simp [predicateEndpointTriple, h0,
            credalPredicateQFMThereExistsCapacityValue_le_one]
        · by_cases h1 : j = 1
          · simp [predicateEndpointTriple, h1,
              credalPredicateQFMThereExistsCapacityValue_le_one]
          · simp [predicateEndpointTriple, h0, h1,
              credalPredicateQFMThereExistsCapacityValue_le_one])
      (by
        intro k
        simpa [predicateEndpointTriple] using hSource_pos k)
      (by
        intro k
        simpa [predicateEndpointTriple] using hTarget_le_source k)
      (by
        simpa [credalPredicateQFMThereExistsCapacityInterval,
          credalQFMCapacityEndpointInterval, predicateEndpointTriple]
          using hSourceLower_pos)

/-- ITV packaging for the independent-endpoint existential `sim2inh` hull. -/
noncomputable def credalPredicateQFMThereExistsSim2InhHullITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (similarity source target :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (hSourceLower_pos :
      0 <
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower)
    (hTargetUpper_le_sourceLower :
      (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs target).upper ≤
        (credalPredicateQFMThereExistsCapacityInterval
          (Base := Base) (Const := Const) M σ νs source).lower)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalQFMCapacitySim2InhHullITV
    (endpoint := fun k j =>
      credalPredicateQFMThereExistsCapacityValue
        (Base := Base) (Const := Const) M σ νs
        ((predicateEndpointTriple (Base := Base) (Const := Const)
          σ similarity source target) j) k)
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_nonneg]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_nonneg])
    (fun k j => by
      by_cases h0 : j = 0
      · simp [predicateEndpointTriple, h0,
          credalPredicateQFMThereExistsCapacityValue_le_one]
      · by_cases h1 : j = 1
        · simp [predicateEndpointTriple, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one]
        · simp [predicateEndpointTriple, h0, h1,
            credalPredicateQFMThereExistsCapacityValue_le_one])
    (by
      simpa [credalPredicateQFMThereExistsCapacityInterval,
        credalQFMCapacityEndpointInterval, predicateEndpointTriple]
        using hSourceLower_pos)
    (by
      simpa [credalPredicateQFMThereExistsCapacityInterval,
        credalQFMCapacityEndpointInterval, predicateEndpointTriple]
        using hTargetUpper_le_sourceLower)
    credibility hcred

/-- Same-completion QFM universal-endpoint interval for PLN's `2inh2sim`
formula. This is the capacity-side consumer of the concrete similarity rule:
apply `2inh2sim` to the two directed QFM endpoint strengths inside each
capacity/reference-class completion, then envelope across completions. -/
noncomputable def credalPredicateQFMForAllTwoInh2SimInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalPredicateQFMForAllFiniteRuleInterval
    (Base := Base) (Const := Const) M σ νs
    (directedPredicateEndpointPair (Base := Base) (Const := Const)
      σ forward reverse)
    (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
    (binaryRuleAsFinite2_monotone_on_unit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
      twoInh2Sim_binaryRuleMonotoneOnUnit)

/-- Independent-endpoint hull for QFM universal `2inh2sim`. The same-completion
interval is contained in this hull; equality would require extra assumptions
about how the two directed endpoints co-vary across completions. -/
noncomputable def credalPredicateQFMForAllTwoInh2SimHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalPredicateQFMForAllFiniteRuleHull
    (Base := Base) (Const := Const) M σ νs
    (directedPredicateEndpointPair (Base := Base) (Const := Const)
      σ forward reverse)
    (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
    (binaryRuleAsFinite2_monotone_on_unit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
      twoInh2Sim_binaryRuleMonotoneOnUnit)

theorem credalPredicateQFMForAllTwoInh2SimInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ) :
    (credalPredicateQFMForAllTwoInh2SimInterval
        (Base := Base) (Const := Const) M σ νs forward reverse).containedIn
      (credalPredicateQFMForAllTwoInh2SimHull
        (Base := Base) (Const := Const) M σ νs forward reverse) := by
  exact
    credalPredicateQFMForAllFiniteRuleInterval_containedIn_hull
      (Base := Base) (Const := Const) M σ νs
      (directedPredicateEndpointPair (Base := Base) (Const := Const)
        σ forward reverse)
      (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
      (binaryRuleAsFinite2_monotone_on_unit
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
        twoInh2Sim_binaryRuleMonotoneOnUnit)

/-- ITV packaging for QFM universal `2inh2sim`. -/
noncomputable def credalPredicateQFMForAllTwoInh2SimITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalPredicateQFMForAllFiniteRuleITV
    (Base := Base) (Const := Const) M σ νs
    (directedPredicateEndpointPair (Base := Base) (Const := Const)
      σ forward reverse)
    (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
    (binaryRuleAsFinite2_monotone_on_unit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
      twoInh2Sim_binaryRuleMonotoneOnUnit)
    (by simpa [binaryRuleAsFinite2] using twoInh2Sim_zero_zero_nonneg)
    (by simpa [binaryRuleAsFinite2] using twoInh2Sim_one_one_le_one)
    credibility hcred

/-- Same-completion QFM existential-endpoint interval for PLN's `2inh2sim`
formula. -/
noncomputable def credalPredicateQFMThereExistsTwoInh2SimInterval
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalPredicateQFMThereExistsFiniteRuleInterval
    (Base := Base) (Const := Const) M σ νs
    (directedPredicateEndpointPair (Base := Base) (Const := Const)
      σ forward reverse)
    (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
    (binaryRuleAsFinite2_monotone_on_unit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
      twoInh2Sim_binaryRuleMonotoneOnUnit)

/-- Independent-endpoint hull for QFM existential `2inh2sim`. -/
noncomputable def credalPredicateQFMThereExistsTwoInh2SimHull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ) : Interval :=
  credalPredicateQFMThereExistsFiniteRuleHull
    (Base := Base) (Const := Const) M σ νs
    (directedPredicateEndpointPair (Base := Base) (Const := Const)
      σ forward reverse)
    (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
    (binaryRuleAsFinite2_monotone_on_unit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
      twoInh2Sim_binaryRuleMonotoneOnUnit)

theorem credalPredicateQFMThereExistsTwoInh2SimInterval_containedIn_hull
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ) :
    (credalPredicateQFMThereExistsTwoInh2SimInterval
        (Base := Base) (Const := Const) M σ νs forward reverse).containedIn
      (credalPredicateQFMThereExistsTwoInh2SimHull
        (Base := Base) (Const := Const) M σ νs forward reverse) := by
  exact
    credalPredicateQFMThereExistsFiniteRuleInterval_containedIn_hull
      (Base := Base) (Const := Const) M σ νs
      (directedPredicateEndpointPair (Base := Base) (Const := Const)
        σ forward reverse)
      (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
      (binaryRuleAsFinite2_monotone_on_unit
        Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
        twoInh2Sim_binaryRuleMonotoneOnUnit)

/-- ITV packaging for QFM existential `2inh2sim`. -/
noncomputable def credalPredicateQFMThereExistsTwoInh2SimITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (forward reverse :
      UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalPredicateQFMThereExistsFiniteRuleITV
    (Base := Base) (Const := Const) M σ νs
    (directedPredicateEndpointPair (Base := Base) (Const := Const)
      σ forward reverse)
    (binaryRuleAsFinite2 Mettapedia.Logic.PLNInferenceRules.twoInh2Sim)
    (binaryRuleAsFinite2_monotone_on_unit
      Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
      twoInh2Sim_binaryRuleMonotoneOnUnit)
    (by simpa [binaryRuleAsFinite2] using twoInh2Sim_zero_zero_nonneg)
    (by simpa [binaryRuleAsFinite2] using twoInh2Sim_one_one_le_one)
    credibility hcred

/-! ## Predicate-facing PLN indefinite truth values -/

/-- PLN truth-value view of the arbitrary-capacity QFM universal endpoint over
a nonempty family of capacity completions. -/
noncomputable def credalPredicateQFMForAllCapacityITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I :=
    credalPredicateQFMForAllCapacityInterval
      (Base := Base) (Const := Const) M σ νs p
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateQFMForAllCapacityInterval_lower_nonneg
      (Base := Base) (Const := Const) M σ νs p)
    (credalPredicateQFMForAllCapacityInterval_upper_le_one
      (Base := Base) (Const := Const) M σ νs p)
    hcred

/-- PLN truth-value view of the arbitrary-capacity QFM existential endpoint
over a nonempty family of capacity completions. -/
noncomputable def credalPredicateQFMThereExistsCapacityITV
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I :=
    credalPredicateQFMThereExistsCapacityInterval
      (Base := Base) (Const := Const) M σ νs p
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateQFMThereExistsCapacityInterval_lower_nonneg
      (Base := Base) (Const := Const) M σ νs p)
    (credalPredicateQFMThereExistsCapacityInterval_upper_le_one
      (Base := Base) (Const := Const) M σ νs p)
    hcred

@[simp] theorem credalPredicateQFMForAllCapacityITV_lower
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateQFMForAllCapacityITV
      (Base := Base) (Const := Const) M σ νs p
      credibility hcred).lower =
      (credalPredicateQFMForAllCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).lower := by
  simp [credalPredicateQFMForAllCapacityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateQFMForAllCapacityITV_upper
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateQFMForAllCapacityITV
      (Base := Base) (Const := Const) M σ νs p
      credibility hcred).upper =
      (credalPredicateQFMForAllCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).upper := by
  simp [credalPredicateQFMForAllCapacityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateQFMForAllCapacityITV_credibility
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateQFMForAllCapacityITV
      (Base := Base) (Const := Const) M σ νs p
      credibility hcred).credibility = credibility := by
  simp [credalPredicateQFMForAllCapacityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateQFMThereExistsCapacityITV_lower
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateQFMThereExistsCapacityITV
      (Base := Base) (Const := Const) M σ νs p
      credibility hcred).lower =
      (credalPredicateQFMThereExistsCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).lower := by
  simp [credalPredicateQFMThereExistsCapacityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateQFMThereExistsCapacityITV_upper
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateQFMThereExistsCapacityITV
      (Base := Base) (Const := Const) M σ νs p
      credibility hcred).upper =
      (credalPredicateQFMThereExistsCapacityInterval
        (Base := Base) (Const := Const) M σ νs p).upper := by
  simp [credalPredicateQFMThereExistsCapacityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateQFMThereExistsCapacityITV_credibility
    {κ : Type x} [Nonempty κ]
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M σ)]
    (νs :
      κ →
        FuzzyCapacity
          (PredicateObject (Base := Base) (Const := Const) M σ))
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateQFMThereExistsCapacityITV
      (Base := Base) (Const := Const) M σ νs p
      credibility hcred).credibility = credibility := by
  simp [credalPredicateQFMThereExistsCapacityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

/-- PLN truth-value view of the predicate-inheritance rule sentence. -/
noncomputable def credalPredicateImplicationITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaITV Hs
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)
    credibility hcred

/-- PLN truth-value view of full extensional/intensional predicate-inheritance
strength over a nonempty family of pointed Henkin completions. -/
noncomputable def credalPredicateFullInheritanceITV
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalPredicateFullInheritanceInterval
    (Base := Base) (Const := Const) Ms σ hObj p q
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateFullInheritanceInterval_lower_nonneg
      (Base := Base) (Const := Const) Ms σ hObj p q)
    (credalPredicateFullInheritanceInterval_upper_le_one
      (Base := Base) (Const := Const) Ms σ hObj p q)
    hcred

/-- PLN truth-value view of full extensional/intensional inheritance strength
over a finite active predicate vocabulary and a nonempty family of pointed
Henkin completions. -/
noncomputable def credalPredicateVocabularyFullInheritanceITV
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalPredicateVocabularyFullInheritanceInterval
    (Base := Base) (Const := Const) Ms σ decode hObj p q
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateVocabularyFullInheritanceInterval_lower_nonneg
      (Base := Base) (Const := Const) Ms σ decode hObj p q)
    (credalPredicateVocabularyFullInheritanceInterval_upper_le_one
      (Base := Base) (Const := Const) Ms σ decode hObj p q)
    hcred

/-- PLN truth-value view of finite-vocabulary predicate similarity over a
nonempty family of pointed Henkin completions. This is the interval-valued
`Equivalence`/`Similarity` sibling of finite-vocabulary full inheritance. -/
noncomputable def credalPredicateVocabularySimilarityITV
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalPredicateVocabularySimilarityInterval
    (Base := Base) (Const := Const) Ms σ decode hObj p q
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateVocabularySimilarityInterval_lower_nonneg
      (Base := Base) (Const := Const) Ms σ decode hObj p q)
    (credalPredicateVocabularySimilarityInterval_upper_le_one
      (Base := Base) (Const := Const) Ms σ decode hObj p q)
    hcred

/-- PLN truth-value view of pure extensional finite-vocabulary predicate
similarity over a nonempty family of pointed Henkin completions. -/
noncomputable def credalPredicateVocabularyPureExtensionalSimilarityITV
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalPredicateVocabularyPureExtensionalSimilarityInterval
    (Base := Base) (Const := Const) Ms σ decode hObj p q
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateVocabularyPureExtensionalSimilarityInterval_lower_nonneg
      (Base := Base) (Const := Const) Ms σ decode hObj p q)
    (credalPredicateVocabularyPureExtensionalSimilarityInterval_upper_le_one
      (Base := Base) (Const := Const) Ms σ decode hObj p q)
    hcred

/-- PLN truth-value view of pure intensional finite-vocabulary predicate
similarity over a nonempty family of pointed Henkin completions. -/
noncomputable def credalPredicateVocabularyPureIntensionalSimilarityITV
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  let I := credalPredicateVocabularyPureIntensionalSimilarityInterval
    (Base := Base) (Const := Const) Ms σ decode p q
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    I.lower I.upper credibility I.valid
    (credalPredicateVocabularyPureIntensionalSimilarityInterval_lower_nonneg
      (Base := Base) (Const := Const) Ms σ decode p q)
    (credalPredicateVocabularyPureIntensionalSimilarityInterval_upper_le_one
      (Base := Base) (Const := Const) Ms σ decode p q)
    hcred

/-- PLN truth-value view of predicate similarity/equivalence. -/
noncomputable def credalPredicateSimilarityITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaITV Hs
    (predicateIffFormula (Base := Base) (Const := Const) σ p q)
    credibility hcred

/-- PLN truth-value view of predicate similarity reconstructed from the two
directed predicate-inheritance strengths by the `2inh2sim` rule. -/
noncomputable def credalPredicateTwoInh2SimITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaBinaryRuleITV Hs
    (predicateImpFormula (Base := Base) (Const := Const) σ p q)
    (predicateImpFormula (Base := Base) (Const := Const) σ q p)
    Mettapedia.Logic.PLNInferenceRules.twoInh2Sim
    twoInh2Sim_binaryRuleMonotoneOnUnit
    twoInh2Sim_zero_zero_nonneg
    twoInh2Sim_one_one_le_one
    credibility hcred

/-- PLN truth-value view of universal predicate truth. -/
noncomputable def credalPredicateForAllITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaITV Hs
    (predicateForAllFormula (Base := Base) (Const := Const) σ p)
    credibility hcred

/-- PLN truth-value view of existential predicate truth. -/
noncomputable def credalPredicateExistsITV
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  credalHOLFormulaITV Hs
    (predicateExistsFormula (Base := Base) (Const := Const) σ p)
    credibility hcred

@[simp] theorem credalPredicateImplicationITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateImplicationITV Hs σ p q credibility hcred).lower =
      (credalPredicateImplicationInterval Hs σ p q).lower := by
  simp [credalPredicateImplicationITV, credalPredicateImplicationInterval]

@[simp] theorem credalPredicateImplicationITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateImplicationITV Hs σ p q credibility hcred).upper =
      (credalPredicateImplicationInterval Hs σ p q).upper := by
  simp [credalPredicateImplicationITV, credalPredicateImplicationInterval]

@[simp] theorem credalPredicateFullInheritanceITV_lower
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateFullInheritanceITV Ms σ hObj p q credibility hcred).lower =
      (credalPredicateFullInheritanceInterval Ms σ hObj p q).lower := by
  simp [credalPredicateFullInheritanceITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateFullInheritanceITV_upper
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateFullInheritanceITV Ms σ hObj p q credibility hcred).upper =
      (credalPredicateFullInheritanceInterval Ms σ hObj p q).upper := by
  simp [credalPredicateFullInheritanceITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateFullInheritanceITV_credibility
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateFullInheritanceITV Ms σ hObj p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateFullInheritanceITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyFullInheritanceITV_lower
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyFullInheritanceITV
      Ms σ decode hObj p q credibility hcred).lower =
      (credalPredicateVocabularyFullInheritanceInterval
        Ms σ decode hObj p q).lower := by
  simp [credalPredicateVocabularyFullInheritanceITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyFullInheritanceITV_upper
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyFullInheritanceITV
      Ms σ decode hObj p q credibility hcred).upper =
      (credalPredicateVocabularyFullInheritanceInterval
        Ms σ decode hObj p q).upper := by
  simp [credalPredicateVocabularyFullInheritanceITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyFullInheritanceITV_credibility
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyFullInheritanceITV
      Ms σ decode hObj p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateVocabularyFullInheritanceITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularySimilarityITV_lower
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularySimilarityITV
      Ms σ decode hObj p q credibility hcred).lower =
      (credalPredicateVocabularySimilarityInterval
        Ms σ decode hObj p q).lower := by
  simp [credalPredicateVocabularySimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularySimilarityITV_upper
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularySimilarityITV
      Ms σ decode hObj p q credibility hcred).upper =
      (credalPredicateVocabularySimilarityInterval
        Ms σ decode hObj p q).upper := by
  simp [credalPredicateVocabularySimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularySimilarityITV_credibility
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularySimilarityITV
      Ms σ decode hObj p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateVocabularySimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyPureExtensionalSimilarityITV_lower
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyPureExtensionalSimilarityITV
      Ms σ decode hObj p q credibility hcred).lower =
      (credalPredicateVocabularyPureExtensionalSimilarityInterval
        Ms σ decode hObj p q).lower := by
  simp [credalPredicateVocabularyPureExtensionalSimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyPureExtensionalSimilarityITV_upper
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyPureExtensionalSimilarityITV
      Ms σ decode hObj p q credibility hcred).upper =
      (credalPredicateVocabularyPureExtensionalSimilarityInterval
        Ms σ decode hObj p q).upper := by
  simp [credalPredicateVocabularyPureExtensionalSimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyPureExtensionalSimilarityITV_credibility
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (hObj : ∀ i : ι, Fintype (PredicateObject (Base := Base) (Const := Const) (Ms i) σ))
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyPureExtensionalSimilarityITV
      Ms σ decode hObj p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateVocabularyPureExtensionalSimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyPureIntensionalSimilarityITV_lower
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyPureIntensionalSimilarityITV
      Ms σ decode p q credibility hcred).lower =
      (credalPredicateVocabularyPureIntensionalSimilarityInterval
        Ms σ decode p q).lower := by
  simp [credalPredicateVocabularyPureIntensionalSimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyPureIntensionalSimilarityITV_upper
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyPureIntensionalSimilarityITV
      Ms σ decode p q credibility hcred).upper =
      (credalPredicateVocabularyPureIntensionalSimilarityInterval
        Ms σ decode p q).upper := by
  simp [credalPredicateVocabularyPureIntensionalSimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateVocabularyPureIntensionalSimilarityITV_credibility
    {ι : Type y} [Nonempty ι]
    (Ms : ι → HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type z}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p q : Pred)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateVocabularyPureIntensionalSimilarityITV
      Ms σ decode p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateVocabularyPureIntensionalSimilarityITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility]

@[simp] theorem credalPredicateSimilarityITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateSimilarityITV Hs σ p q credibility hcred).lower =
      (credalPredicateSimilarityInterval Hs σ p q).lower := by
  simp [credalPredicateSimilarityITV, credalPredicateSimilarityInterval]

@[simp] theorem credalPredicateSimilarityITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateSimilarityITV Hs σ p q credibility hcred).upper =
      (credalPredicateSimilarityInterval Hs σ p q).upper := by
  simp [credalPredicateSimilarityITV, credalPredicateSimilarityInterval]

@[simp] theorem credalPredicateSimilarityITV_credibility
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateSimilarityITV Hs σ p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateSimilarityITV]

@[simp] theorem credalPredicateTwoInh2SimITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateTwoInh2SimITV Hs σ p q credibility hcred).lower =
      (credalPredicateTwoInh2SimInterval Hs σ p q).lower := by
  simp [credalPredicateTwoInh2SimITV, credalPredicateTwoInh2SimInterval]

@[simp] theorem credalPredicateTwoInh2SimITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateTwoInh2SimITV Hs σ p q credibility hcred).upper =
      (credalPredicateTwoInh2SimInterval Hs σ p q).upper := by
  simp [credalPredicateTwoInh2SimITV, credalPredicateTwoInh2SimInterval]

@[simp] theorem credalPredicateTwoInh2SimITV_credibility
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateTwoInh2SimITV Hs σ p q credibility hcred).credibility =
      credibility := by
  simp [credalPredicateTwoInh2SimITV]

@[simp] theorem credalPredicateForAllITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateForAllITV Hs σ p credibility hcred).lower =
      (credalPredicateForAllInterval Hs σ p).lower := by
  simp [credalPredicateForAllITV, credalPredicateForAllInterval]

@[simp] theorem credalPredicateForAllITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateForAllITV Hs σ p credibility hcred).upper =
      (credalPredicateForAllInterval Hs σ p).upper := by
  simp [credalPredicateForAllITV, credalPredicateForAllInterval]

@[simp] theorem credalPredicateForAllITV_credibility
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateForAllITV Hs σ p credibility hcred).credibility =
      credibility := by
  simp [credalPredicateForAllITV]

@[simp] theorem credalPredicateExistsITV_lower
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateExistsITV Hs σ p credibility hcred).lower =
      (credalPredicateExistsInterval Hs σ p).lower := by
  simp [credalPredicateExistsITV, credalPredicateExistsInterval]

@[simp] theorem credalPredicateExistsITV_upper
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateExistsITV Hs σ p credibility hcred).upper =
      (credalPredicateExistsInterval Hs σ p).upper := by
  simp [credalPredicateExistsITV, credalPredicateExistsInterval]

@[simp] theorem credalPredicateExistsITV_credibility
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateExistsITV Hs σ p credibility hcred).credibility =
      credibility := by
  simp [credalPredicateExistsITV]

theorem credalPredicateSimilarityInterval_eq_const_of_subsingleton
    {ι : Type y} [Subsingleton ι] [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (i0 : ι)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    credalPredicateSimilarityInterval Hs σ p q =
      constInterval
        (credalHOLFormulaValue (Hs i0)
          (predicateIffFormula (Base := Base) (Const := Const) σ p q)) := by
  exact
    credalHOLFormulaInterval_eq_const_of_subsingleton
      (Base := Base) (Const := Const) Hs i0
      (predicateIffFormula (Base := Base) (Const := Const) σ p q)

theorem credalPredicateSimilarityInterval_comm
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    credalPredicateSimilarityInterval Hs σ p q =
      credalPredicateSimilarityInterval Hs σ q p := by
  unfold credalPredicateSimilarityInterval
  exact
    credalHOLFormulaInterval_eq_of_pointwiseIff
      (Base := Base) (Const := Const) Hs
      (fun i =>
        pointwiseIff_predicateIffFormula_comm
          (Base := Base) (Const := Const) (Hs i).baseSpace σ p q)

theorem credalPredicateSimilarityITV_comm_endpoints
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    (credalPredicateSimilarityITV Hs σ p q credibility hcred).lower =
        (credalPredicateSimilarityITV Hs σ q p credibility hcred).lower ∧
      (credalPredicateSimilarityITV Hs σ p q credibility hcred).upper =
        (credalPredicateSimilarityITV Hs σ q p credibility hcred).upper := by
  constructor
  · simpa using
      congrArg Interval.lower
        (credalPredicateSimilarityInterval_comm
          (Base := Base) (Const := Const) Hs σ p q)
  · simpa using
      congrArg Interval.upper
        (credalPredicateSimilarityInterval_comm
          (Base := Base) (Const := Const) Hs σ p q)

theorem credalPredicateSimilarityInterval_eq_const_one_of_pointwiseMutualInherits
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hMutual :
      ∀ j : ι, ∀ i : (Hs j).baseSpace.Idx,
        predicateMutualInheritsAt (Base := Base) (Const := Const)
          ((Hs j).baseSpace.model i) σ p q) :
    credalPredicateSimilarityInterval Hs σ p q = constInterval 1 := by
  unfold credalPredicateSimilarityInterval
  exact
    credalHOLFormulaInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Hs
      (predicateIffFormula (Base := Base) (Const := Const) σ p q) 1
      (by
        intro j
        unfold credalHOLFormulaValue
        change
          (hierarchicalPredicateSimilarityStrength
            (Base := Base) (Const := Const) (Hs j) σ p q).toReal = 1
        rw [hierarchicalPredicateSimilarityStrength_eq_one_of_pointwiseMutualInherits
          (Base := Base) (Const := Const) (Hs j) σ p q (hMutual j)]
        simp)

theorem credalPredicateSimilarityInterval_eq_const_zero_of_pointwiseNotMutualInherits
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hNotMutual :
      ∀ j : ι, ∀ i : (Hs j).baseSpace.Idx,
        ¬ predicateMutualInheritsAt (Base := Base) (Const := Const)
          ((Hs j).baseSpace.model i) σ p q) :
    credalPredicateSimilarityInterval Hs σ p q = constInterval 0 := by
  unfold credalPredicateSimilarityInterval
  exact
    credalHOLFormulaInterval_eq_const_of_pointwise_value_eq
      (Base := Base) (Const := Const) Hs
      (predicateIffFormula (Base := Base) (Const := Const) σ p q) 0
      (by
        intro j
        unfold credalHOLFormulaValue
        change
          (hierarchicalPredicateSimilarityStrength
            (Base := Base) (Const := Const) (Hs j) σ p q).toReal = 0
        rw [hierarchicalPredicateSimilarityStrength_eq_zero_of_pointwiseNotMutualInherits
          (Base := Base) (Const := Const) (Hs j) σ p q (hNotMutual j)]
        simp)

theorem credalPredicateForAllInterval_mono_of_pointwiseInherits
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      ∀ j : ι, ∀ i : (Hs j).baseSpace.Idx,
        (predicateInterpretation (Base := Base) (Const := Const)
          ((Hs j).baseSpace.model i) σ).Inherits p q) :
    (credalPredicateForAllInterval Hs σ p).lower ≤
        (credalPredicateForAllInterval Hs σ q).lower ∧
      (credalPredicateForAllInterval Hs σ p).upper ≤
        (credalPredicateForAllInterval Hs σ q).upper := by
  unfold credalPredicateForAllInterval
  exact
    credalHOLFormulaInterval_mono_of_pointwiseImplies
      (Base := Base) (Const := Const) Hs
      (by
        intro j i hAll
        exact
          predicateForAll_mono_of_inherits
            (Base := Base) (Const := Const)
            ((Hs j).baseSpace.model i) σ p q (hInh j i) hAll)

theorem credalPredicateExistsInterval_mono_of_pointwiseInherits
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      ∀ j : ι, ∀ i : (Hs j).baseSpace.Idx,
        (predicateInterpretation (Base := Base) (Const := Const)
          ((Hs j).baseSpace.model i) σ).Inherits p q) :
    (credalPredicateExistsInterval Hs σ p).lower ≤
        (credalPredicateExistsInterval Hs σ q).lower ∧
      (credalPredicateExistsInterval Hs σ p).upper ≤
        (credalPredicateExistsInterval Hs σ q).upper := by
  unfold credalPredicateExistsInterval
  exact
    credalHOLFormulaInterval_mono_of_pointwiseImplies
      (Base := Base) (Const := Const) Hs
      (by
        intro j i hExists
        exact
          predicateExists_mono_of_inherits
            (Base := Base) (Const := Const)
            ((Hs j).baseSpace.model i) σ p q (hInh j i) hExists)

theorem credalPredicateForAllITV_mono_of_pointwiseInherits
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (hInh :
      ∀ j : ι, ∀ i : (Hs j).baseSpace.Idx,
        (predicateInterpretation (Base := Base) (Const := Const)
          ((Hs j).baseSpace.model i) σ).Inherits p q) :
    (credalPredicateForAllITV Hs σ p credibility hcred).lower ≤
        (credalPredicateForAllITV Hs σ q credibility hcred).lower ∧
      (credalPredicateForAllITV Hs σ p credibility hcred).upper ≤
        (credalPredicateForAllITV Hs σ q credibility hcred).upper := by
  simpa using
    (credalPredicateForAllInterval_mono_of_pointwiseInherits
      (Base := Base) (Const := Const) Hs σ p q hInh)

theorem credalPredicateExistsITV_mono_of_pointwiseInherits
    {ι : Type y} [Nonempty ι]
    (Hs : ι → HierarchicalState.{u, v, w, x} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1)
    (hInh :
      ∀ j : ι, ∀ i : (Hs j).baseSpace.Idx,
        (predicateInterpretation (Base := Base) (Const := Const)
          ((Hs j).baseSpace.model i) σ).Inherits p q) :
    (credalPredicateExistsITV Hs σ p credibility hcred).lower ≤
        (credalPredicateExistsITV Hs σ q credibility hcred).lower ∧
      (credalPredicateExistsITV Hs σ p credibility hcred).upper ≤
        (credalPredicateExistsITV Hs σ q credibility hcred).upper := by
  simpa using
    (credalPredicateExistsInterval_mono_of_pointwiseInherits
      (Base := Base) (Const := Const) Hs σ p q hInh)

end Mettapedia.Logic.PLNHigherOrderHOLCredalBridge
