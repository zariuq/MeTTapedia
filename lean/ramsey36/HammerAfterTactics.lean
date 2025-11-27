-- Break down with tactics FIRST, then hammer on small sub-goals
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Use tactics to break down, then hammer the pieces
theorem double_counting_with_tactics {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  -- Define the edge set explicitly
  let E := (A ×ˢ B).filter (fun p => R p.1 p.2)

  -- Break down: LHS = |E|
  suffices h1 : (∑ a ∈ A, (B.filter (R a)).card) = E.card by
    -- And: RHS = |E|
    suffices h2 : (∑ b ∈ B, (A.filter (fun a => R a b)).card) = E.card by
      omega
    sorry -- Hammer sub-goal 2
  sorry -- Hammer sub-goal 1

-- Now let's prove sub-goal 1 with maximum tactic breakdown
lemma count_edges_by_first {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (∑ a ∈ A, (B.filter (R a)).card) = E.card := by
  intro E
  -- Use card_eq_sum_ones: |S| = ∑ x ∈ S, 1
  rw [card_eq_sum_ones]
  -- Now we need: ∑ a ∈ A, |{b ∈ B | R a b}| = ∑ (a,b) ∈ E, 1
  rw [sum_comm_finset]
  -- After swapping, we need to show sums are equal
  congr 1
  ext ab
  simp only [E, mem_filter, mem_product]
  -- At this point, try hammer on the simplified goal
  sorry

-- Sub-goal 2: count by second coordinate
lemma count_edges_by_second {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) = E.card := by
  intro E
  rw [card_eq_sum_ones]
  rw [sum_comm_finset]
  congr 1
  ext ab
  simp only [E, mem_filter, mem_product]
  sorry

-- Try an even MORE broken-down version
lemma edges_eq_sum_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    E.card = ∑ a ∈ A, (E.filter (fun p => p.1 = a)).card := by
  intro E
  -- This should follow from partitioning E by first coordinate
  -- Try with minimal rewriting
  have : E = E.biUnion (fun a => E.filter (fun p => p.1 = a)) := by
    hammer (config := { aesopPremises := 64, autoPremises := 32 })
  sorry

-- Most basic sub-goal: prove fiber equals filter
lemma fiber_eq_filter_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] (a : α) (ha : a ∈ A) :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (E.filter (fun p => p.1 = a)) = (B.filter (R a)).map ⟨fun b => (a, b), fun b1 b2 h => by simp at h; exact h⟩ := by
  intro E
  ext ⟨a', b⟩
  simp only [E, mem_filter, mem_product, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨⟨⟨ha', hb⟩, hr⟩, heq⟩
    use b
    simp [heq] at hr ⊢
    exact ⟨hb, hr⟩
  · intro ⟨b', ⟨hb', hr'⟩, heq⟩
    simp at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨⟨⟨ha, hb'⟩, hr'⟩, rfl⟩

-- Now try hammer on the fiber equality after simplification
lemma fiber_card_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] (a : α) (ha : a ∈ A) :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (E.filter (fun p => p.1 = a)).card = (B.filter (R a)).card := by
  intro E
  rw [fiber_eq_filter_product A B R a ha]
  simp only [card_map]
