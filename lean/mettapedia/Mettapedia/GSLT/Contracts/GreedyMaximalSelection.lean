import Mathlib.Data.Finset.Card

/-!
# Lexicographic choice on a finite hereditary family

Given a fixed word of candidates, inclusion of an earlier candidate
has priority over later decisions. If admissibility is hereditary, one
pass chooses the best admissible decision word and a maximal set.
Pairwise compatibility is one such family, not a hypothesis that all
legal parallel firings reduce to pairwise tests.

An order on the *resulting states* is a different policy. The theorem
does not license the greedy selector for that order unless a separate
correspondence is established.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.GreedyMaximalSelection

variable {Candidate : Type*} [DecidableEq Candidate]

def Hereditary (legal : Finset Candidate → Prop) : Prop :=
  ∀ ⦃small large⦄, small ⊆ large → legal large → legal small

variable (legal : Finset Candidate → Prop) [DecidablePred legal]

def choose (prior : Finset Candidate) : List Candidate → Finset Candidate
  | [] => prior
  | first :: rest =>
      if legal (insert first prior) then choose (insert first prior) rest
      else choose prior rest

theorem prefix_subset (prior : Finset Candidate) (priority : List Candidate) :
    prior ⊆ choose legal prior priority := by
  induction priority generalizing prior with
  | nil => exact Finset.Subset.refl _
  | cons first rest ih =>
      rw [choose]
      split
      · exact Finset.subset_insert _ _ |>.trans (ih _)
      · exact ih _

theorem choose_legal {prior : Finset Candidate} (prefixLegal : legal prior)
    (priority : List Candidate) : legal (choose legal prior priority) := by
  induction priority generalizing prior with
  | nil => exact prefixLegal
  | cons first rest ih =>
      rw [choose]
      split
      · rename_i good
        exact ih good
      · exact ih prefixLegal

theorem choose_subset (prior : Finset Candidate) (priority : List Candidate) :
    choose legal prior priority ⊆ prior ∪ priority.toFinset := by
  induction priority generalizing prior with
  | nil => simp [choose]
  | cons first rest ih =>
      rw [choose]
      split
      · intro value owned
        have fromEarlier := Finset.mem_union.mp (ih _ owned)
        simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at fromEarlier ⊢
        tauto
      · simpa only [List.toFinset_cons] using
          (ih prior).trans (Finset.union_subset_union_right (Finset.subset_insert first rest.toFinset))

theorem omitted_insert_illegal (hereditary : Hereditary legal) (priority : List Candidate)
    (prior : Finset Candidate) {value : Candidate} (listed : value ∈ priority)
    (omitted : value ∉ choose legal prior priority) :
    ¬ legal (insert value (choose legal prior priority)) := by
  induction priority generalizing prior with
  | nil => simp at listed
  | cons first rest ih =>
      by_cases addFirst : legal (insert first prior)
      · rw [choose, if_pos addFirst] at omitted ⊢
        rcases List.mem_cons.mp listed with rfl | later
        · exact (omitted (prefix_subset legal _ _ (Finset.mem_insert_self ..))).elim
        · exact ih _ later omitted
      · rw [choose, if_neg addFirst] at omitted ⊢
        rcases List.mem_cons.mp listed with rfl | later
        · intro enlarged
          exact addFirst (hereditary (Finset.insert_subset_insert _ (prefix_subset legal _ _)) enlarged)
        · exact ih _ later omitted

theorem choose_maximal (hereditary : Hereditary legal) (prior : Finset Candidate)
    (priority : List Candidate) {other : Finset Candidate}
    (available : other ⊆ prior ∪ priority.toFinset) (allowed : legal other)
    (extendsChoice : choose legal prior priority ⊆ other) :
    other = choose legal prior priority := by
  refine Finset.Subset.antisymm (fun value inOther => ?_) extendsChoice
  by_contra omitted
  have notPrefix : value ∉ prior := fun member => omitted (prefix_subset legal _ _ member)
  have listed : value ∈ priority := by
    rcases Finset.mem_union.mp (available inOther) with initial | inWord
    · exact (notPrefix initial).elim
    · exact List.mem_toFinset.mp inWord
  exact omitted_insert_illegal legal hereditary priority prior listed omitted
    (hereditary (Finset.insert_subset inOther extendsChoice) allowed)

/-- Membership decisions in the declared order. The comparison prefers
true (take) to false (skip) at the first unequal position. -/
def decisions (selection : Finset Candidate) (priority : List Candidate) : List Bool :=
  priority.map (fun c => decide (c ∈ selection))

def FirstPreference (chosen alternative : Bool) : Prop :=
  chosen = true ∧ alternative = false

/-- The greedy answer is lexicographically preferred even to feasible
contenders that are not maximal. Whole-set scans are not needed to
construct the preferred answer. -/
theorem choose_preferred (hereditary : Hereditary legal) (priority : List Candidate)
    (prior : Finset Candidate) (prefixLegal : legal prior)
    (other : Finset Candidate) (containsPrefix : prior ⊆ other) (otherLegal : legal other) :
    decisions (choose legal prior priority) priority = decisions other priority ∨
      List.Lex FirstPreference (decisions (choose legal prior priority) priority)
        (decisions other priority) := by
  induction priority generalizing prior with
  | nil => exact Or.inl rfl
  | cons first rest ih =>
      by_cases addFirst : legal (insert first prior)
      · rw [choose, if_pos addFirst]
        have taken : first ∈ choose legal (insert first prior) rest :=
          prefix_subset legal _ _ (Finset.mem_insert_self ..)
        simp only [decisions, List.map_cons, taken, decide_true]
        by_cases kept : first ∈ other
        · simp only [kept, decide_true]
          rcases ih (insert first prior) addFirst (Finset.insert_subset kept containsPrefix)
            with same | preferred
          · exact Or.inl (congrArg (List.cons true) same)
          · exact Or.inr (.cons preferred)
        · simp only [kept, decide_false]
          exact Or.inr (.rel ⟨rfl, rfl⟩)
      · rw [choose, if_neg addFirst]
        have notTaken : first ∉ choose legal prior rest := fun member => addFirst
          (hereditary (Finset.insert_subset member (prefix_subset legal _ _))
            (choose_legal legal prefixLegal rest))
        have notKept : first ∉ other := fun member => addFirst
          (hereditary (Finset.insert_subset member containsPrefix) otherLegal)
        simp only [decisions, List.map_cons, notTaken, notKept, decide_false]
        rcases ih prior prefixLegal containsPrefix with same | preferred
        · exact Or.inl (congrArg (List.cons false) same)
        · exact Or.inr (.cons preferred)

namespace Controls

private def atMostOne (xs : Finset Nat) : Prop := xs.card ≤ 1
private instance (xs : Finset Nat) : Decidable (atMostOne xs) := inferInstanceAs (Decidable (_ ≤ _))

theorem atMostOne_hereditary : Hereditary atMostOne := by
  intro small large inclusion allowed
  exact (Finset.card_le_card inclusion).trans allowed

/-- Same conflict family, two declared priorities. For example, if
candidate 0 emits 9 and candidate 1 emits 1, priority [0,1] does not
choose the numerically least emitted state. -/
theorem priority_is_not_state_order :
    choose atMostOne ∅ [0, 1] = {0} ∧ choose atMostOne ∅ [1, 0] = {1} := by
  decide

private def inPairs (xs : Finset Nat) : Prop := xs = ∅ ∨ xs = {0, 1}
private instance (xs : Finset Nat) : Decidable (inPairs xs) := inferInstanceAs (Decidable (_ ∨ _))

theorem nonhereditary_test_can_block_the_better_bag :
    choose inPairs ∅ [0, 1] = ∅ ∧ inPairs {0, 1} ∧ {0, 1} ≠ (∅ : Finset Nat) := by
  decide

end Controls

#print axioms choose_maximal
#print axioms choose_preferred
#print axioms Controls.priority_is_not_state_order
#print axioms Controls.nonhereditary_test_can_block_the_better_bag

end Mettapedia.GSLT.Contracts.GreedyMaximalSelection
