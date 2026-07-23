import Mettapedia.Languages.MeTTa.PrimeCellCausalSemantics
import Mettapedia.PLN.WorldModel.WorldModelOverlap

/-!
# Prime cell-causal explanations to overlap-aware world-model evidence

Prime supplies occurrence identity and causal receipts.  A world-model
interpretation supplies weights.  This bridge isolates the smallest example
where retaining shared cause identity changes the answer: two rule
occurrences supported by the same fair producer outcome have probability
`1/2`, while incorrectly treating the explanations as independent gives
`3/4`.
-/

namespace Mettapedia.PLN.Bridges.PrimeCellCausalProbability

open Mettapedia.Languages.MeTTa.PrimeCellCausalSemantics
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WorldModelOverlap

local instance : EvidenceType ℚ := {}

local instance rationalWorldModel : AdditiveWorldModel ℚ Unit ℚ where
  extract state _ := state
  extract_add _ _ _ := rfl

/-- A small overlap model for nested evidence events.  The overlap of two
weights is their minimum; merging uses inclusion-exclusion.  This model is
appropriate for the discriminator below, where both explanations denote the
same event. -/
def nestedCauseOverlapLayer : SubtractiveOverlapLayer ℚ Unit ℚ where
  merge left right := left + right - min left right
  overlap left right _ := min left right
  combine left right overlap := left + right - overlap
  independent left right _ := min left right = 0
  evidence_merge _ _ _ := rfl
  additive_of_independent left right _ independent := by
    change left + right - min left right = left + right
    rw [independent]
    simp
  combine_eq_sub _ _ _ := rfl
  independent_iff_zero_overlap _ _ _ := Iff.rfl

def sharedExplanationLeft : PublicationOccurrence Nat Nat Nat Nat :=
  { occurrence := 0, rule := 10, answer := 1, receipt := {100} }

def sharedExplanationRight : PublicationOccurrence Nat Nat Nat Nat :=
  { occurrence := 1, rule := 11, answer := 1, receipt := {100} }

/-- Prime retains two rule occurrences while revealing that their causal
support is the same producer event. -/
theorem two_rules_one_shared_cause :
    sharedExplanationLeft.occurrence ≠ sharedExplanationRight.occurrence ∧
    sharedExplanationLeft.rule ≠ sharedExplanationRight.rule ∧
    sharedExplanationLeft.answer = sharedExplanationRight.answer ∧
    sharedExplanationLeft.receipt = sharedExplanationRight.receipt := by
  decide

def fairOutcome : ℚ := 1 / 2

/-- Applying the WM overlap law to the two shared explanations counts their
one causal event once. -/
theorem dependence_aware_probability_is_half :
    AdditiveWorldModel.extract
      (State := ℚ) (Query := Unit) (Ev := ℚ)
      (nestedCauseOverlapLayer.merge fairOutcome fairOutcome) () = 1 / 2 := by
  calc
    AdditiveWorldModel.extract
        (State := ℚ) (Query := Unit) (Ev := ℚ)
        (nestedCauseOverlapLayer.merge fairOutcome fairOutcome) () =
      AdditiveWorldModel.extract
          (State := ℚ) (Query := Unit) (Ev := ℚ) fairOutcome () +
        AdditiveWorldModel.extract
          (State := ℚ) (Query := Unit) (Ev := ℚ) fairOutcome () -
        nestedCauseOverlapLayer.overlap fairOutcome fairOutcome () :=
      SubtractiveOverlapLayer.inclusionExclusion
        nestedCauseOverlapLayer fairOutcome fairOutcome ()
    _ = 1 / 2 := by
      change fairOutcome + fairOutcome - min fairOutcome fairOutcome = 1 / 2
      norm_num [fairOutcome]

def independentOr (left right : ℚ) : ℚ :=
  1 - (1 - left) * (1 - right)

/-- Negative discriminator: assuming independence between the two syntactic
explanations double-counts their shared cause. -/
theorem naive_independent_explanations_give_three_quarters :
    independentOr fairOutcome fairOutcome = 3 / 4 := by
  norm_num [independentOr, fairOutcome]

theorem shared_cause_discriminates_aggregation :
    AdditiveWorldModel.extract
      (State := ℚ) (Query := Unit) (Ev := ℚ)
      (nestedCauseOverlapLayer.merge fairOutcome fairOutcome) () ≠
      independentOr fairOutcome fairOutcome := by
  rw [dependence_aware_probability_is_half,
    naive_independent_explanations_give_three_quarters]
  norm_num

end Mettapedia.PLN.Bridges.PrimeCellCausalProbability
