import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Expert-choice routing invariants

Expert-choice routing gives every expert a fixed number of selection slots.
This balances expert-side work by construction while allowing heterogeneous
token-side load.  The two properties must not be conflated: equal expert load
does not imply that every token is selected.

This module proves fixed distinct load, conservation of total assignments, and
an explicit token-starvation boundary.  It is independent of the learned score
or top-k implementation that produces the assignment.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace ExpertChoiceRouting

open scoped BigOperators

/-- An expert-choice assignment with `capacity` distinct tokens per expert. -/
structure Assignment
    (Expert Token : Type*) (capacity : ℕ) where
  selected : Expert → Fin capacity → Token
  selected_injective : ∀ expert, Function.Injective (selected expert)

variable {Expert Token : Type*} {capacity : ℕ}

/-- The distinct tokens selected by one expert. -/
def selectedTokens
    [Fintype (Fin capacity)] [DecidableEq Token]
    (assignment : Assignment Expert Token capacity)
    (expert : Expert) : Finset Token :=
  Finset.univ.image (assignment.selected expert)

/-- Every expert receives exactly the declared distinct-token capacity. -/
theorem selectedTokens_card
    [DecidableEq Token]
    (assignment : Assignment Expert Token capacity)
    (expert : Expert) :
    (selectedTokens assignment expert).card = capacity := by
  rw [selectedTokens,
    Finset.card_image_of_injective _ (assignment.selected_injective expert),
    Finset.card_univ, Fintype.card_fin]

/-- Number of expert slots routed to one token. -/
def tokenLoad
    [Fintype Expert] [Fintype Token] [DecidableEq Token]
    (assignment : Assignment Expert Token capacity)
    (token : Token) : ℕ :=
  ∑ expert : Expert, ∑ slot : Fin capacity,
    if assignment.selected expert slot = token then 1 else 0

/-- The sum of token-side loads is exactly expert count times capacity. -/
theorem total_tokenLoad
    [Fintype Expert] [Fintype Token] [DecidableEq Token]
    (assignment : Assignment Expert Token capacity) :
    ∑ token : Token, tokenLoad assignment token =
      Fintype.card Expert * capacity := by
  simp only [tokenLoad]
  calc
    (∑ token : Token, ∑ expert : Expert, ∑ slot : Fin capacity,
        if assignment.selected expert slot = token then 1 else 0) =
        ∑ expert : Expert, ∑ token : Token, ∑ slot : Fin capacity,
          if assignment.selected expert slot = token then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ expert : Expert, ∑ slot : Fin capacity, ∑ token : Token,
          if assignment.selected expert slot = token then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro expert _
      exact Finset.sum_comm
    _ = ∑ _expert : Expert, ∑ _slot : Fin capacity, 1 := by
      apply Finset.sum_congr rfl
      intro expert _
      apply Finset.sum_congr rfl
      intro slot _
      simp
    _ = Fintype.card Expert * capacity := by
      simp [Fintype.card_fin]

/-- If no token is starved, the number of tokens cannot exceed total expert
capacity. -/
theorem token_count_le_total_capacity_of_positive_load
    [Fintype Expert] [Fintype Token] [DecidableEq Token]
    (assignment : Assignment Expert Token capacity)
    (covered : ∀ token, 0 < tokenLoad assignment token) :
    Fintype.card Token ≤ Fintype.card Expert * capacity := by
  rw [← total_tokenLoad assignment]
  calc
    Fintype.card Token = ∑ _token : Token, 1 := by simp
    _ ≤ ∑ token : Token, tokenLoad assignment token := by
      apply Finset.sum_le_sum
      intro token _
      exact covered token

/-! ## Positive and negative fixtures -/

def balancedAssignment : Assignment (Fin 2) (Fin 2) 1 where
  selected expert _slot := expert
  selected_injective _expert := by
    intro left right _
    exact Subsingleton.elim left right

theorem balancedAssignment_each_expert_load :
    ∀ expert, (selectedTokens balancedAssignment expert).card = 1 :=
  selectedTokens_card balancedAssignment

theorem balancedAssignment_each_token_load :
    tokenLoad balancedAssignment 0 = 1 ∧
      tokenLoad balancedAssignment 1 = 1 := by
  decide

def starvingAssignment : Assignment (Fin 2) (Fin 3) 1 where
  selected _expert _slot := 0
  selected_injective _expert := by
    intro left right _
    exact Subsingleton.elim left right

theorem starvingAssignment_expert_load_balanced :
    ∀ expert, (selectedTokens starvingAssignment expert).card = 1 :=
  selectedTokens_card starvingAssignment

/-- Perfect expert load can coexist with two completely unselected tokens. -/
theorem expert_balance_does_not_imply_token_coverage :
    tokenLoad starvingAssignment 0 = 2 ∧
      tokenLoad starvingAssignment 1 = 0 ∧
      tokenLoad starvingAssignment 2 = 0 := by
  decide

/-- The coverage theorem detects the fixture's insufficient total capacity. -/
theorem starvingAssignment_cannot_have_positive_load_everywhere :
    ¬ (∀ token, 0 < tokenLoad starvingAssignment token) := by
  intro covered
  have capacityBound :=
    token_count_le_total_capacity_of_positive_load starvingAssignment covered
  norm_num at capacityBound

#print axioms selectedTokens_card
#print axioms total_tokenLoad
#print axioms token_count_le_total_capacity_of_positive_load
#print axioms expert_balance_does_not_imply_token_coverage
#print axioms starvingAssignment_cannot_have_positive_load_everywhere

end ExpertChoiceRouting

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
