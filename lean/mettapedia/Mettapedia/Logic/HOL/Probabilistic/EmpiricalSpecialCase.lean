import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Probability.Distributions.Uniform
import Mettapedia.Logic.HOL.Probabilistic.WorldModelBridge
import Mettapedia.Logic.HOL.WorldModel

/-!
# Empirical Special Case of Probabilistic HOL

This module proves that the existing multiset-counting HOL↔WM semantics is a
genuine special case of the new infinitary-first `ProbHOL` semantics.

The construction preserves multiplicity exactly by using the uniform `PMF`
induced by a nonempty multiset of pointed Henkin models. Duplicate models
contribute repeated mass, matching the current empirical PLN interpretation.

This semantic probability layer stays distinct from the dynamic belief-process
layer motivated by Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020).
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

noncomputable section

local instance instEmpiricalMeasurableSpace :
    MeasurableSpace (HenkinModel.{u, v, w} Base Const) := ⊤

local instance instEmpiricalDecidableHolSatisfies (φ : ClosedFormula Const) :
    DecidablePred (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) :=
  Classical.decPred _

/-- Empirical `ProbHOL` model space induced by the raw model type itself, equipped
with the discrete measurable structure in which every set is measurable. -/
noncomputable def empiricalModelSpace
    (_W : Multiset (HenkinModel.{u, v, w} Base Const)) :
    ModelSpace Base Const where
  Idx := HenkinModel.{u, v, w} Base Const
  instMeasurableSpace := inferInstance
  model := id
  measurable_sentence_event := by
    intro φ
    trivial

private theorem holEvidence_total_eq_card
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ : ClosedFormula Const) :
    (holEvidence (Base := Base) (Const := Const) W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W +
          Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const => ¬ holSatisfies M φ) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP
        (p := fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W : ℝ≥0∞) +
          (Multiset.countP
            (fun M : HenkinModel.{u, v, w} Base Const => ¬ holSatisfies M φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold holEvidence Evidence.total
  simpa using hcard.symm

private theorem staticQueryStrength_eq_count_ratio
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (φ : ClosedFormula Const) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W φ =
      (Multiset.countP
          (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W : ℝ≥0∞) /
        (W.card : ℝ≥0∞) := by
  let p : HenkinModel.{u, v, w} Base Const → Prop := fun M => holSatisfies M φ
  letI : DecidablePred p := Classical.decPred p
  have hcardNat : W.card ≠ 0 := by
    intro hcard
    exact hW (Multiset.card_eq_zero.mp hcard)
  have hcardENN : (W.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hcardNat
  unfold WorldModel.queryStrength Evidence.toStrength
  change
    (if (holEvidence (Base := Base) (Const := Const) W φ).total = 0 then 0
      else (holEvidence (Base := Base) (Const := Const) W φ).pos /
        (holEvidence (Base := Base) (Const := Const) W φ).total) =
      (Multiset.countP p W : ℝ≥0∞) / (W.card : ℝ≥0∞)
  rw [holEvidence_total_eq_card (Base := Base) (Const := Const) W φ, if_neg hcardENN]
  simp [holEvidence, p]

/-- Semantic `ProbHOL` sentence probability of the empirical multiset sample. -/
theorem empiricalSentenceProb_eq_count_ratio
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (φ : ClosedFormula Const) :
    sentenceProb
        (empiricalModelSpace (Base := Base) (Const := Const) W)
        (PMF.ofMultiset W hW).toMeasure
        φ =
      (Multiset.countP
          (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W : ℝ≥0∞) /
        (W.card : ℝ≥0∞) := by
  classical
  let p : HenkinModel.{u, v, w} Base Const → Prop := fun M => holSatisfies M φ
  letI : DecidablePred p := Classical.decPred p
  have hmeas :
      MeasurableSet
        ((empiricalModelSpace (Base := Base) (Const := Const) W).sentenceEvent φ) := by
    simp [empiricalModelSpace, ModelSpace.sentenceEvent]
  have hmeasure' :
      (PMF.ofMultiset W hW).toMeasure
          ((empiricalModelSpace (Base := Base) (Const := Const) W).sentenceEvent φ) =
        (∑' x : HenkinModel.{u, v, w} Base Const, ((W.filter p).count x : ℝ≥0∞)) /
          (W.card : ℝ≥0∞) := by
    have htmp :=
      (PMF.toMeasure_ofMultiset_apply (s := W) (hs := hW)
        (t := (empiricalModelSpace (Base := Base) (Const := Const) W).sentenceEvent φ) hmeas)
    simp [empiricalModelSpace, ModelSpace.sentenceEvent, p] at htmp ⊢
  have hsum :
      (∑' x : HenkinModel.{u, v, w} Base Const, ((W.filter p).count x : ℝ≥0∞)) =
        ((W.filter p).card : ℝ≥0∞) := by
    calc
      (∑' x : HenkinModel.{u, v, w} Base Const, ((W.filter p).count x : ℝ≥0∞))
          = ∑ x ∈ (W.filter p).toFinset, ((W.filter p).count x : ℝ≥0∞) := by
              exact tsum_eq_sum fun a ha =>
                Nat.cast_eq_zero.2 <| by
                  rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]
      _ = ((W.filter p).card : ℝ≥0∞) := by
          rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
  calc
    sentenceProb
        (empiricalModelSpace (Base := Base) (Const := Const) W)
        (PMF.ofMultiset W hW).toMeasure
        φ
        =
          (PMF.ofMultiset W hW).toMeasure
            ((empiricalModelSpace (Base := Base) (Const := Const) W).sentenceEvent φ) := by
              rfl
    _ = (∑' x : HenkinModel.{u, v, w} Base Const, ((W.filter p).count x : ℝ≥0∞)) /
          (W.card : ℝ≥0∞) := hmeasure'
    _ = ((W.filter p).card : ℝ≥0∞) / (W.card : ℝ≥0∞) := by rw [hsum]
    _ = (Multiset.countP p W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
          rw [Multiset.countP_eq_card_filter]
    _ =
        (Multiset.countP
          (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W : ℝ≥0∞) /
          (W.card : ℝ≥0∞) := by
            simp [p]

/-- The old static HOL-WM strength is the empirical special case of semantic
sentence probability over multisets of pointed Henkin models. -/
theorem empiricalSentenceProb_eq_staticQueryStrength
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (φ : ClosedFormula Const) :
    sentenceProb
        (empiricalModelSpace (Base := Base) (Const := Const) W)
        (PMF.ofMultiset W hW).toMeasure
        φ =
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W φ := by
  rw [empiricalSentenceProb_eq_count_ratio (Base := Base) (Const := Const) W hW φ,
    staticQueryStrength_eq_count_ratio (Base := Base) (Const := Const) W hW φ]

/-- The probabilistic WM-facing strength induced by the empirical measure agrees
with the existing static HOL-WM query strength. -/
theorem empiricalProbQueryStrength_eq_staticQueryStrength
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (hW : W ≠ 0)
    (φ : ClosedFormula Const) :
    probQueryStrength
        (empiricalModelSpace (Base := Base) (Const := Const) W)
        (PMF.ofMultiset W hW).toMeasure
        φ =
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W φ := by
  rw [probQueryStrength_eq_sentenceProb
      (S := empiricalModelSpace (Base := Base) (Const := Const) W)
      (μ := (PMF.ofMultiset W hW).toMeasure)
      (hμ := PMF.toMeasure.isProbabilityMeasure _)]
  exact empiricalSentenceProb_eq_staticQueryStrength (Base := Base) (Const := Const) W hW φ

/-- Singleton empirical semantic probability agrees with the old singleton
adequacy theorem on satisfying queries. -/
theorem empiricalSentenceProb_singleton_of_satisfies
    (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormula Const)
    (hφ : holSatisfies M φ) :
    sentenceProb
        (empiricalModelSpace (Base := Base) (Const := Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)))
        (PMF.ofMultiset ({M} : Multiset (HenkinModel.{u, v, w} Base Const))
          (by simp)).toMeasure
        φ = 1 := by
  rw [empiricalSentenceProb_eq_staticQueryStrength
      (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const))
      (by simp) φ]
  exact queryStrength_singleton_of_satisfies (Base := Base) (Const := Const) M φ hφ

/-- Singleton empirical semantic probability agrees with the old singleton
adequacy theorem on non-satisfying queries. -/
theorem empiricalSentenceProb_singleton_of_not_satisfies
    (M : HenkinModel.{u, v, w} Base Const)
    (φ : ClosedFormula Const)
    (hφ : ¬ holSatisfies M φ) :
    sentenceProb
        (empiricalModelSpace (Base := Base) (Const := Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)))
        (PMF.ofMultiset ({M} : Multiset (HenkinModel.{u, v, w} Base Const))
          (by simp)).toMeasure
        φ = 0 := by
  rw [empiricalSentenceProb_eq_staticQueryStrength
      (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const))
      (by simp) φ]
  exact queryStrength_singleton_of_not_satisfies (Base := Base) (Const := Const) M φ hφ

end

end Mettapedia.Logic.HOL.Probabilistic
