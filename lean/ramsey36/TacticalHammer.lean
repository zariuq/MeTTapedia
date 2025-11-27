-- Maximum tactical breakdown, then hammer on small pieces
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Step 1: Prove fiber equals mapped filter (NO HAMMER, pure tactics)
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

-- Step 2: Cardinality of fiber equals cardinality of filter (NO HAMMER, uses step 1)
lemma fiber_card_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] (a : α) (ha : a ∈ A) :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (E.filter (fun p => p.1 = a)).card = (B.filter (R a)).card := by
  intro E
  rw [fiber_eq_filter_product A B R a ha]
  simp only [card_map]

-- Step 3: Sum of fiber cardinalities (try HAMMER here on the sum rewriting)
lemma sum_fiber_cards {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (∑ a ∈ A, (E.filter (fun p => p.1 = a)).card) = E.card := by
  intro E
  classical
  -- This is card_eq_sum_card_fiberwise applied to E with f = Prod.fst
  -- But simplified for this specific case
  -- The key: E partitions into fibers by first coordinate
  have key : ∀ p ∈ E, p.1 ∈ A := by
    intros ⟨a, b⟩ hp
    simp [E, mem_filter, mem_product] at hp
    exact hp.1.1
  -- Now E = ⋃ a ∈ A, {p ∈ E | p.1 = a}
  -- Use card_eq_sum_card_fiberwise with f = Prod.fst
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)]
  · simp only [mem_filter]
  · exact key

-- Step 4: Combine steps to get LHS = |E|
lemma count_edges_by_first {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (∑ a ∈ A, (B.filter (R a)).card) = E.card := by
  intro E
  classical
  -- Rewrite each term using fiber_card_eq
  have h_fibers : ∑ a ∈ A, (B.filter (R a)).card = ∑ a ∈ A, (E.filter (fun p => p.1 = a)).card := by
    congr 1
    ext a
    by_cases ha : a ∈ A
    · rw [fiber_card_eq A B R a ha]
    · -- If a ∉ A, both sides are 0 (since we're summing over A)
      simp [ha]
  rw [h_fibers]
  -- Now apply sum_fiber_cards
  exact sum_fiber_cards A B R

-- Step 5: Same for RHS (symmetric to step 4)
lemma count_edges_by_second {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) = E.card := by
  intro E
  classical
  -- Symmetric to count_edges_by_first, but partition by second coordinate
  sorry -- TODO: same structure as above but with Prod.snd

-- Step 6: Main theorem (trivial once we have steps 4 and 5)
theorem double_counting_tactical {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)]
    [∀ b, DecidablePred (fun a => R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
    (∑ b ∈ B, (A.filter (fun a => R a b)).card) := by
  let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
  have h1 := count_edges_by_first A B R
  have h2 := count_edges_by_second A B R
  omega

-- Now let's try HAMMER on the key lemma: sum of fibers equals card
-- Break it down even MORE
lemma disjiUnion_fiber_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [∀ a, DecidablePred (R a)] :
    let E := (A ×ˢ B).filter (fun p => R p.1 p.2)
    ∀ a1 ∈ A, ∀ a2 ∈ A, a1 ≠ a2 →
      Disjoint (E.filter (fun p => p.1 = a1)) (E.filter (fun p => p.1 = a2)) := by
  intro E a1 ha1 a2 ha2 hne
  rw [disjoint_left]
  intro ⟨x1, x2⟩ h1 h2
  simp only [E, mem_filter, mem_product] at h1 h2
  -- p.1 = a1 and p.1 = a2, but a1 ≠ a2
  have eq1 : x1 = a1 := h1.2
  have eq2 : x1 = a2 := h2.2
  -- Apply hammer's suggestion
  subst eq2 eq1
  simp_all
