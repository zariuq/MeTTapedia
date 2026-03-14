import Mettapedia.Logic.PLNWorldModelPredCodeCompleteness

/-!
# Predicate-Code WM Consequence API

Compatibility and naming-clean module over `PLNWorldModelPredCodeCompleteness`.
-/

namespace Mettapedia.Logic.PLNWorldModelPredCodeConsequence

open Mettapedia.Logic.PLNWorldModelPredCodeCompleteness
open Mettapedia.Logic.PLNWorldModelPredCode
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.HigherOrder

abbrev PredCodeQuery (U : Type*) := Mettapedia.Logic.PLNWorldModelPredCode.PredCodeQuery U
abbrev PointedPredCode (U : Type*) :=
  Mettapedia.Logic.PLNWorldModelPredCode.PointedPredCode U
abbrev PredCodeState (U : Type*) := Mettapedia.Logic.PLNWorldModelPredCode.PredCodeState U

abbrev pointwiseImplies {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.pointwiseImplies q₁ q₂

abbrev singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.singletonStrengthLE q₁ q₂

abbrev singletonConsequence {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.singletonConsequence q₁ q₂

theorem pointwiseImplies_iff_singletonConsequence {U : Type*}
    (q₁ q₂ : PredCodeQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonConsequence q₁ q₂ :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.pointwiseImplies_iff_singletonConsequence
    (q₁ := q₁) (q₂ := q₂)

theorem multiset_strength_le_of_pointwise {U : Type*}
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.multiset_strength_le_of_pointwise
    (W := W) (q₁ := q₁) (q₂ := q₂) himp

def wmConsequenceRuleOn_of_pointwise {U : Type*} (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRuleOn (PredCodeState U) (PredCodeQuery U) :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.wmConsequenceRuleOn_of_pointwise
    (q₁ := q₁) (q₂ := q₂)

theorem externalImplication_iff_singletonConsequence_of_sound_complete {U : Type*}
    (ProvImp : PredCodeQuery U → PredCodeQuery U → Prop)
    (hSound : ∀ {q₁ q₂}, ProvImp q₁ q₂ → pointwiseImplies q₁ q₂)
    (hComplete : ∀ {q₁ q₂}, pointwiseImplies q₁ q₂ → ProvImp q₁ q₂)
    (q₁ q₂ : PredCodeQuery U) :
    ProvImp q₁ q₂ ↔ singletonConsequence q₁ q₂ :=
  Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.externalImplication_iff_singletonConsequence_of_sound_complete
    (ProvImp := ProvImp) hSound hComplete q₁ q₂

/-! ## Negative-scope theorem pack -/

/-- If there is a pointed counterexample (`q₁` true and `q₂` false), singleton
predicate-code consequence fails. -/
theorem singletonStrengthLE_not_of_counterexample {U : Type*}
    (q₁ q₂ : PredCodeQuery U) (pw : PointedPredCode U)
    (hq₁ : pw.satisfies q₁)
    (hnq₂ : ¬ pw.satisfies q₂) :
    ¬ singletonStrengthLE q₁ q₂ := by
  intro hsing
  have himp : pointwiseImplies q₁ q₂ :=
    (Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂)).2 hsing
  exact hnq₂ (himp pw hq₁)

/-- Incompleteness witness: if an external implication relation misses a
singleton consequence case, it cannot be equivalent to WM singleton consequence. -/
theorem externalImplication_not_equiv_singletonConsequence_of_incomplete_witness {U : Type*}
    (ProvImp : PredCodeQuery U → PredCodeQuery U → Prop)
    {q₁ q₂ : PredCodeQuery U}
    (hsing : singletonConsequence q₁ q₂)
    (hnot : ¬ ProvImp q₁ q₂) :
    ¬ (∀ r₁ r₂ : PredCodeQuery U, ProvImp r₁ r₂ ↔ singletonConsequence r₁ r₂) := by
  intro hall
  exact hnot ((hall q₁ q₂).2 hsing)

/-- Unsoundness witness: if an external implication relation proves a formula pair
with a pointed counterexample, it cannot be equivalent to WM singleton consequence. -/
theorem externalImplication_not_equiv_singletonConsequence_of_unsound_witness {U : Type*}
    (ProvImp : PredCodeQuery U → PredCodeQuery U → Prop)
    {q₁ q₂ : PredCodeQuery U}
    (hprov : ProvImp q₁ q₂)
    (hcounter : ∃ pw : PointedPredCode U, pw.satisfies q₁ ∧ ¬ pw.satisfies q₂) :
    ¬ (∀ r₁ r₂ : PredCodeQuery U, ProvImp r₁ r₂ ↔ singletonConsequence r₁ r₂) := by
  intro hall
  have hsing : singletonConsequence q₁ q₂ := (hall q₁ q₂).1 hprov
  rcases hcounter with ⟨pw, hq₁, hnq₂⟩
  exact (singletonStrengthLE_not_of_counterexample
    (q₁ := q₁) (q₂ := q₂) (pw := pw) hq₁ hnq₂) hsing

/-- Concrete negative fixture for Bool predicate-code queries:
`true` does not imply `¬true` at singleton consequence level. -/
theorem bool_not_trivial_counterexample :
    ¬ singletonConsequence (U := Bool) (.trivial) (.comp_not .trivial) := by
  refine singletonStrengthLE_not_of_counterexample
    (q₁ := (.trivial : PredCodeQuery Bool))
    (q₂ := (.comp_not .trivial : PredCodeQuery Bool))
    (pw := ⟨true⟩) ?_ ?_
  · simp [Mettapedia.Logic.PLNWorldModelPredCode.PointedPredCode.satisfies,
      Mettapedia.Logic.HigherOrder.evalPred]
  · simp [Mettapedia.Logic.PLNWorldModelPredCode.PointedPredCode.satisfies,
      Mettapedia.Logic.HigherOrder.evalPred]

end Mettapedia.Logic.PLNWorldModelPredCodeConsequence
