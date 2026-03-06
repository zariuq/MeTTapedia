import Mettapedia.Logic.PLNWorldModelHOLCompleteness

/-!
# HOL WM Consequence API (Preferred Name)

Compatibility and naming-clean module over `PLNWorldModelHOLCompleteness`.

- Keep historical module available for downstream imports.
- Expose the same consequence surface under `...HOLConsequence`.
- Add explicit negative-scope theorem families so "closure" claims are
  accompanied by counterexample criteria.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLConsequence

open Mettapedia.Logic.PLNWorldModelHOLCompleteness
open Mettapedia.Logic.PLNWorldModelHOL
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.HigherOrder

abbrev HOLQuery (U : Type*) := Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLQuery U
abbrev PointedHOL (U : Type*) := Mettapedia.Logic.PLNWorldModelHOLCompleteness.PointedHOL U
abbrev HOLState (U : Type*) := Mettapedia.Logic.PLNWorldModelHOLCompleteness.HOLState U

abbrev pointwiseImplies {U : Type*} (q₁ q₂ : HOLQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.pointwiseImplies q₁ q₂

abbrev singletonStrengthLE {U : Type*} (q₁ q₂ : HOLQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.singletonStrengthLE q₁ q₂

abbrev singletonConsequence {U : Type*} (q₁ q₂ : HOLQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.singletonConsequence q₁ q₂

theorem pointwiseImplies_iff_singletonConsequence {U : Type*}
    (q₁ q₂ : HOLQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonConsequence q₁ q₂ :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.pointwiseImplies_iff_singletonConsequence
    (q₁ := q₁) (q₂ := q₂)

theorem multiset_strength_le_of_pointwise {U : Type*}
    (W : HOLState U) (q₁ q₂ : HOLQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := HOLState U) (Query := HOLQuery U) W q₁ ≤
      WorldModel.queryStrength (State := HOLState U) (Query := HOLQuery U) W q₂ :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.multiset_strength_le_of_pointwise
    (W := W) (q₁ := q₁) (q₂ := q₂) himp

def wmConsequenceRuleOn_of_pointwise {U : Type*} (q₁ q₂ : HOLQuery U) :
    WMConsequenceRuleOn (HOLState U) (HOLQuery U) :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.wmConsequenceRuleOn_of_pointwise
    (q₁ := q₁) (q₂ := q₂)

theorem externalImplication_iff_singletonConsequence_of_sound_complete {U : Type*}
    (ProvImp : HOLQuery U → HOLQuery U → Prop)
    (hSound : ∀ {q₁ q₂}, ProvImp q₁ q₂ → pointwiseImplies q₁ q₂)
    (hComplete : ∀ {q₁ q₂}, pointwiseImplies q₁ q₂ → ProvImp q₁ q₂)
    (q₁ q₂ : HOLQuery U) :
    ProvImp q₁ q₂ ↔ singletonConsequence q₁ q₂ :=
  Mettapedia.Logic.PLNWorldModelHOLCompleteness.externalImplication_iff_singletonConsequence_of_sound_complete
    (ProvImp := ProvImp) hSound hComplete q₁ q₂

/-! ## Negative-scope theorem pack -/

/-- If there is a pointed counterexample (`q₁` true and `q₂` false), singleton
HOL consequence fails. -/
theorem singletonStrengthLE_not_of_counterexample {U : Type*}
    (q₁ q₂ : HOLQuery U) (pw : PointedHOL U)
    (hq₁ : pw.satisfies q₁)
    (hnq₂ : ¬ pw.satisfies q₂) :
    ¬ singletonStrengthLE q₁ q₂ := by
  intro hsing
  have himp : pointwiseImplies q₁ q₂ :=
    (Mettapedia.Logic.PLNWorldModelHOLCompleteness.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂)).2 hsing
  exact hnq₂ (himp pw hq₁)

/-- Incompleteness witness: if an external implication relation misses a
singleton consequence case, it cannot be equivalent to WM singleton consequence. -/
theorem externalImplication_not_equiv_singletonConsequence_of_incomplete_witness {U : Type*}
    (ProvImp : HOLQuery U → HOLQuery U → Prop)
    {q₁ q₂ : HOLQuery U}
    (hsing : singletonConsequence q₁ q₂)
    (hnot : ¬ ProvImp q₁ q₂) :
    ¬ (∀ r₁ r₂ : HOLQuery U, ProvImp r₁ r₂ ↔ singletonConsequence r₁ r₂) := by
  intro hall
  exact hnot ((hall q₁ q₂).2 hsing)

/-- Unsoundness witness: if an external implication relation proves a formula pair
with a pointed counterexample, it cannot be equivalent to WM singleton consequence. -/
theorem externalImplication_not_equiv_singletonConsequence_of_unsound_witness {U : Type*}
    (ProvImp : HOLQuery U → HOLQuery U → Prop)
    {q₁ q₂ : HOLQuery U}
    (hprov : ProvImp q₁ q₂)
    (hcounter : ∃ pw : PointedHOL U, pw.satisfies q₁ ∧ ¬ pw.satisfies q₂) :
    ¬ (∀ r₁ r₂ : HOLQuery U, ProvImp r₁ r₂ ↔ singletonConsequence r₁ r₂) := by
  intro hall
  have hsing : singletonConsequence q₁ q₂ := (hall q₁ q₂).1 hprov
  rcases hcounter with ⟨pw, hq₁, hnq₂⟩
  exact (singletonStrengthLE_not_of_counterexample
    (q₁ := q₁) (q₂ := q₂) (pw := pw) hq₁ hnq₂) hsing

/-- Concrete negative fixture for Bool HOL queries:
`true` does not imply `¬true` at singleton consequence level. -/
theorem bool_not_trivial_counterexample :
    ¬ singletonConsequence (U := Bool) (.trivial) (.comp_not .trivial) := by
  refine singletonStrengthLE_not_of_counterexample
    (q₁ := (.trivial : HOLQuery Bool))
    (q₂ := (.comp_not .trivial : HOLQuery Bool))
    (pw := ⟨true⟩) ?_ ?_
  · simp [Mettapedia.Logic.PLNWorldModelHOL.PointedHOL.satisfies,
      Mettapedia.Logic.HigherOrder.evalPred]
  · simp [Mettapedia.Logic.PLNWorldModelHOL.PointedHOL.satisfies,
      Mettapedia.Logic.HigherOrder.evalPred]

end Mettapedia.Logic.PLNWorldModelHOLConsequence
