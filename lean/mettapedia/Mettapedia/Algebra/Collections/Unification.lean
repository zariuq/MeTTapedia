import Mettapedia.Algebra.Collections.Rest
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Abel

/-!
# Unifying collection patterns with a rest on each side

Matching (`Rest`) solves a collection equation whose right side is a
ground value. Unification solves an equation with an unknown rest on both
sides: `named₁ ⊕ rest₁ = named₂ ⊕ rest₂`, where `⊕` is the operation of the
collection's free structure.

* **Lists.** `A ++ r = B ++ s` is solvable exactly when one named prefix extends
  the other, and then it has one most general solution (`list_unify_iff`).
* **Bags.** `A + r = B + s` always has one most general solution with a fresh
  rest `t`: `r = (B - A) + t` and `s = (A - B) + t` (`bag_unify_iff`). Every
  solution is exactly one instance of it: the solutions are in bijection with
  the bags `t` (`bagUnifiers`). Bag unification with named elements and one
  rest per side is unitary.
* **Sets, disjoint rests.** `A ∪ r = B ∪ s` with `r` disjoint from `A` and `s`
  from `B` has the solutions `r = (B \ A) ∪ t`, `s = (A \ B) ∪ t` with `t`
  disjoint from `A ∪ B` (`set_unify_iff`), in bijection with those `t`
  (`setUnifiers`): unitary up to a freshness constraint. Without disjointness
  one rest does not determine the other (`Controls.set_rests_undetermined`).
* **Element variables.** `x :: r = y :: s` has two families of solutions,
  `x = y, r = s` and `r = y :: t, s = x :: t` (`cons_unify_iff`), and neither
  family contains the other (`Controls.both_families_needed`): unification with
  element variables on both sides is finitary, not unitary. Against named
  values, `x :: r = B + s` has one family per position of `x`: inside the named
  part or inside the other rest (`cons_unify_named_iff`).
* **Decomposition.** Every solution of `A + r = B + s` splits the named parts
  into a matched part and unmatched parts with no common element, and each rest
  is the other side's unmatched part plus one fresh part
  (`bag_decompose_iff`). With element variables, this is one family of
  solutions per partial matching of the two sides' variables, and identifying
  variables keeps a family's instances solutions
  (`Controls.bag_needs_no_disequality`).
* **Sets with element variables.** `{x | r} = {y | s}` with disjoint rests has
  the families `x = y, r = s` and `x ≠ y, r = {y} ∪ t, s = {x} ∪ t`
  (`set_cons_unify_iff`). The second needs the disequality `x ≠ y`: set
  unification with element variables leaves constraints, not only
  substitutions.
* **Several element variables against a value.** Choosing `k` ordered
  occurrences of a bag (`selections`) gives `n (n - 1) ⋯ (n - k + 1)` results
  for a bag of size `n` (`card_selections`), each a solution
  (`mem_selections`). On a duplicate-free bag every solution is returned once
  (`nodup_selections`); on a bag with a repeated element a solution is returned
  more than once, and the set of its distinct elements may have no solution at
  all (`Controls.repeated_element_repeats_answers`).
* **Unification types.** A complete set of solutions covers every solution
  by an instance of a member (`IsComplete`); a problem is unitary, finitary
  or infinitary as such sets have at most one, finitely many, or only
  infinitely many members (`Unitary`, `Finitary`, `Infinitary`).
* **Associative unification is infinitary.** Over the free monoid with
  sequence variables, `x a = a x` has the solutions `x ↦ aⁿ`, a minimal
  complete set, and no finite complete set exists (`plotkin_infinitary`).
* **Flat bag patterns are finitary.** `{xs | r} = {ys | s}`, with element terms
  and optional rests, holds exactly for the instances of one family per
  partial matching of the two sides' elements: matched pairs are equations
  between element terms, and the rests are the unmatched elements plus one
  common fresh part (`flat_bag_unify_iff`, `flat_bag_closed_iff`).
* **Flat set patterns with disjoint rests are finitary with constraints.**
  Their solutions are the bag families on representatives of each side's
  distinct values, with disequalities that no substitution expresses
  (`flat_set_unify_iff`, `set_disjoint_unify_iff_bag`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Unification

open Mettapedia.Algebra.Collections.Rest

variable {α : Type*}

/-! ## Lists -/

/-- Two list patterns with a trailing rest each unify exactly when one named
prefix extends the other; the extra part is then forced into the other rest. -/
theorem list_unify_iff (named₁ named₂ rest₁ rest₂ : List α) :
    named₁ ++ rest₁ = named₂ ++ rest₂ ↔
      (∃ extra, named₂ = named₁ ++ extra ∧ rest₁ = extra ++ rest₂) ∨
        ∃ extra, named₁ = named₂ ++ extra ∧ rest₂ = extra ++ rest₁ :=
  List.append_eq_append_iff

/-! ## Bags -/

section Bags

variable [DecidableEq α]

/-- **Bag unification is unitary.** `named₁ + rest₁ = named₂ + rest₂` holds
exactly for the instances of one most general solution with a fresh rest. -/
theorem bag_unify_iff (named₁ named₂ rest₁ rest₂ : Multiset α) :
    named₁ + rest₁ = named₂ + rest₂ ↔
      ∃ fresh, rest₁ = (named₂ - named₁) + fresh ∧ rest₂ = (named₁ - named₂) + fresh := by
  constructor
  · intro solves
    have counts : ∀ a, named₁.count a + rest₁.count a = named₂.count a + rest₂.count a :=
      fun a => by simpa only [Multiset.count_add] using congrArg (Multiset.count a) solves
    refine ⟨rest₁ - (named₂ - named₁), ?_, ?_⟩
    · ext a
      have := counts a
      simp only [Multiset.count_add, Multiset.count_sub]
      omega
    · ext a
      have := counts a
      simp only [Multiset.count_add, Multiset.count_sub]
      omega
  · rintro ⟨fresh, rfl, rfl⟩
    ext a
    simp only [Multiset.count_add, Multiset.count_sub]
    omega

/-- The solutions of `named₁ + rest₁ = named₂ + rest₂`. -/
def BagUnifier (named₁ named₂ : Multiset α) : Type _ :=
  {rests : Multiset α × Multiset α // named₁ + rests.1 = named₂ + rests.2}

/-- **Every solution is exactly one instance of the most general solution**:
the solutions correspond one to one to the values of the fresh rest. -/
def bagUnifiers (named₁ named₂ : Multiset α) : BagUnifier named₁ named₂ ≃ Multiset α where
  toFun solution := solution.1.1 - (named₂ - named₁)
  invFun fresh := ⟨((named₂ - named₁) + fresh, (named₁ - named₂) + fresh),
    (bag_unify_iff named₁ named₂ _ _).mpr ⟨fresh, rfl, rfl⟩⟩
  left_inv solution := by
    obtain ⟨⟨rest₁, rest₂⟩, solves⟩ := solution
    obtain ⟨fresh, rfl, rfl⟩ := (bag_unify_iff named₁ named₂ rest₁ rest₂).mp solves
    apply Subtype.ext
    simp only [add_tsub_cancel_left]
  right_inv fresh := by
    simp only [add_tsub_cancel_left]

omit [DecidableEq α] in
/-- In the unitary case each rest determines the other. -/
theorem bag_rest_determines (named₁ named₂ rest₁ rest₂ rest₂' : Multiset α)
    (first : named₁ + rest₁ = named₂ + rest₂) (second : named₁ + rest₁ = named₂ + rest₂') :
    rest₂ = rest₂' :=
  add_left_cancel (first.symm.trans second)

/-- One element variable on each side: the two families of solutions. -/
theorem cons_unify_iff (x y : α) (rest₁ rest₂ : Multiset α) :
    x ::ₘ rest₁ = y ::ₘ rest₂ ↔
      (x = y ∧ rest₁ = rest₂) ∨ ∃ fresh, rest₁ = y ::ₘ fresh ∧ rest₂ = x ::ₘ fresh := by
  rw [Multiset.cons_eq_cons]
  constructor
  · rintro (same | ⟨_, fresh, first, second⟩)
    · exact Or.inl same
    · exact Or.inr ⟨fresh, first, second⟩
  · rintro (same | ⟨fresh, rfl, rfl⟩)
    · exact Or.inl same
    · by_cases same : x = y
      · subst same
        exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨same, fresh, rfl, rfl⟩

/-- An element variable against named values and a rest: the variable is one of
the named values, or it lies in the other rest. -/
theorem cons_unify_named_iff (x : α) (rest₁ named rest₂ : Multiset α) :
    x ::ₘ rest₁ = named + rest₂ ↔
      (x ∈ named ∧ rest₁ = named.erase x + rest₂) ∨
        ∃ fresh, rest₂ = x ::ₘ fresh ∧ rest₁ = named + fresh := by
  constructor
  · intro solves
    have member : x ∈ named + rest₂ := solves ▸ Multiset.mem_cons_self x rest₁
    have rest : rest₁ = (named + rest₂).erase x := by
      rw [← solves, Multiset.erase_cons_head]
    by_cases inNamed : x ∈ named
    · exact Or.inl ⟨inNamed, rest.trans (Multiset.erase_add_left_pos rest₂ inNamed)⟩
    · have inRest : x ∈ rest₂ := (Multiset.mem_add.mp member).resolve_left inNamed
      refine Or.inr ⟨rest₂.erase x, (Multiset.cons_erase inRest).symm, ?_⟩
      exact rest.trans (Multiset.erase_add_right_pos named inRest)
  · rintro (⟨inNamed, rfl⟩ | ⟨fresh, rfl, rfl⟩)
    · rw [← Multiset.cons_add, Multiset.cons_erase inNamed]
    · rw [Multiset.add_cons]

/-- **Every solution of a bag equation decomposes.** The named parts share a
matched part, their unmatched parts have no element in common, and each rest
holds the other side's unmatched part and one common fresh part. With element
variables, the variables of the two sides are matched by a partial matching of
positions, so the solutions form finitely many families. -/
theorem bag_decompose_iff (named₁ named₂ rest₁ rest₂ : Multiset α) :
    named₁ + rest₁ = named₂ + rest₂ ↔
      ∃ matched unmatched₁ unmatched₂ fresh : Multiset α,
        named₁ = matched + unmatched₁ ∧ named₂ = matched + unmatched₂ ∧
          (∀ a ∈ unmatched₁, a ∉ unmatched₂) ∧
            rest₁ = unmatched₂ + fresh ∧ rest₂ = unmatched₁ + fresh := by
  constructor
  · intro solves
    obtain ⟨fresh, first, second⟩ := (bag_unify_iff named₁ named₂ rest₁ rest₂).mp solves
    refine ⟨named₁ ∩ named₂, named₁ - named₂, named₂ - named₁, fresh, ?_, ?_, ?_, first, second⟩
    · ext a
      simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
      omega
    · ext a
      simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
      omega
    · intro a inFirst inSecond
      rw [← Multiset.count_pos, Multiset.count_sub] at inFirst inSecond
      omega
  · rintro ⟨matched, unmatched₁, unmatched₂, fresh, rfl, rfl, -, rfl, rfl⟩
    ext a
    simp only [Multiset.count_add]
    omega

/-! ### Several element variables against a value -/

/-- Ordered choices of `k` occurrences of a bag, each with the bag that is
left; one element variable is `selectOccurrences`. -/
def selections : ℕ → Multiset α → Multiset (List α × Multiset α)
  | 0, value => {([], value)}
  | k + 1, value => (selectOccurrences value).bind fun choice =>
      (selections k choice.2).map fun picked => (choice.1 :: picked.1, picked.2)

/-- The selections are exactly the solutions of `x₁ :: … :: xₖ :: rest = value`. -/
theorem mem_selections (k : ℕ) (value : Multiset α) (solution : List α × Multiset α) :
    solution ∈ selections k value ↔
      solution.1.length = k ∧ (solution.1 : Multiset α) + solution.2 = value := by
  induction k generalizing value solution with
  | zero =>
      obtain ⟨picked, rest⟩ := solution
      simp only [selections, Multiset.mem_singleton, Prod.mk.injEq, List.length_eq_zero_iff]
      constructor
      · rintro ⟨rfl, rfl⟩
        simp
      · rintro ⟨rfl, solves⟩
        simpa using solves
  | succ k ih =>
      obtain ⟨picked, rest⟩ := solution
      simp only [selections, Multiset.mem_bind, Multiset.mem_map, selectOccurrences]
      constructor
      · rintro ⟨_, ⟨element, member, rfl⟩, ⟨picked', rest'⟩, chosen, same⟩
        obtain ⟨length, solves⟩ := (ih _ _).mp chosen
        simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        refine ⟨by simp [length], ?_⟩
        rw [← Multiset.cons_coe, Multiset.cons_add, solves, Multiset.cons_erase member]
      · rintro ⟨length, solves⟩
        cases picked with
        | nil => simp at length
        | cons element picked' =>
            simp only [List.length_cons, add_left_inj] at length
            rw [← Multiset.cons_coe, Multiset.cons_add] at solves
            obtain ⟨member, restEq⟩ := (bag_select_iff element _ value).mp solves
            refine ⟨(element, value.erase element), ⟨element, member, rfl⟩, (picked', rest),
              (ih _ _).mpr ⟨length, restEq⟩, rfl⟩

/-- `k` ordered choices among `n` occurrences: `n (n - 1) ⋯ (n - k + 1)`. -/
theorem card_selections (k : ℕ) (value : Multiset α) :
    (selections k value).card = value.card.descFactorial k := by
  induction k generalizing value with
  | zero => simp [selections]
  | succ k ih =>
      simp only [selections, Multiset.card_bind, selectOccurrences, Multiset.map_map]
      rw [Multiset.map_congr rfl (g := fun _ => (value.card - 1).descFactorial k) ?_]
      · rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
        cases size : value.card with
        | zero => simp
        | succ n => rw [Nat.succ_descFactorial_succ, Nat.add_sub_cancel]
      · intro element member
        simp only [Function.comp_apply, Multiset.card_map, ih,
          Multiset.card_erase_of_mem member, Nat.pred_eq_sub_one]

/-- **On a duplicate-free bag every solution is returned once.** -/
theorem nodup_selections (k : ℕ) {value : Multiset α} (nodup : value.Nodup) :
    (selections k value).Nodup := by
  induction k generalizing value with
  | zero => exact Multiset.nodup_singleton _
  | succ k ih =>
      have occurrencesNodup : (selectOccurrences value).Nodup := by
        unfold selectOccurrences
        exact Multiset.Nodup.map (fun first second same => (Prod.mk.inj same).1) nodup
      rw [selections, Multiset.nodup_bind]
      constructor
      · intro choice member
        obtain ⟨element, _, rfl⟩ := Multiset.mem_map.mp member
        refine Multiset.Nodup.map (fun first second same => ?_) (ih (nodup.erase _))
        simp only [Prod.mk.injEq, List.cons.injEq, true_and] at same
        exact Prod.ext same.1 same.2
      · refine Multiset.Nodup.pairwise ?_ occurrencesNodup
        intro firstChoice firstMember secondChoice secondMember different
        obtain ⟨first, _, rfl⟩ := Multiset.mem_map.mp firstMember
        obtain ⟨second, _, rfl⟩ := Multiset.mem_map.mp secondMember
        have distinct : first ≠ second := fun same => different (by rw [same])
        simp only [Function.onFun]
        rw [Multiset.disjoint_left]
        intro answer inFirst inSecond
        obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp inFirst
        obtain ⟨_, _, same⟩ := Multiset.mem_map.mp inSecond
        simp only [Prod.mk.injEq, List.cons.injEq] at same
        exact distinct same.1.1.symm

end Bags

/-! ## Sets with disjoint rests -/

section Sets

variable [DecidableEq α]

/-- **Set unification with disjoint rests is unitary up to freshness.** -/
theorem set_unify_iff (named₁ named₂ rest₁ rest₂ : Finset α) :
    (named₁ ∪ rest₁ = named₂ ∪ rest₂ ∧ Disjoint named₁ rest₁ ∧ Disjoint named₂ rest₂) ↔
      ∃ fresh, Disjoint fresh (named₁ ∪ named₂) ∧
        rest₁ = (named₂ \ named₁) ∪ fresh ∧ rest₂ = (named₁ \ named₂) ∪ fresh := by
  constructor
  · rintro ⟨solves, apart₁, apart₂⟩
    refine ⟨rest₁ \ named₂, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x inFresh inNamed
      rw [Finset.mem_sdiff] at inFresh
      rcases Finset.mem_union.mp inNamed with inFirst | inSecond
      · exact Finset.disjoint_left.mp apart₁ inFirst inFresh.1
      · exact inFresh.2 inSecond
    · ext x
      have member := congrArg (x ∈ ·) solves
      have outside₁ : x ∈ named₁ → x ∉ rest₁ := fun h => Finset.disjoint_left.mp apart₁ h
      have outside₂ : x ∈ named₂ → x ∉ rest₂ := fun h => Finset.disjoint_left.mp apart₂ h
      simp only [Finset.mem_union, Finset.mem_sdiff, eq_iff_iff] at member ⊢
      tauto
    · ext x
      have member := congrArg (x ∈ ·) solves
      have outside₁ : x ∈ named₁ → x ∉ rest₁ := fun h => Finset.disjoint_left.mp apart₁ h
      have outside₂ : x ∈ named₂ → x ∉ rest₂ := fun h => Finset.disjoint_left.mp apart₂ h
      simp only [Finset.mem_union, Finset.mem_sdiff, eq_iff_iff] at member ⊢
      tauto
  · rintro ⟨fresh, apart, rfl, rfl⟩
    have outside : ∀ x, x ∈ fresh → x ∉ named₁ ∧ x ∉ named₂ := by
      intro x inFresh
      have := Finset.disjoint_left.mp apart inFresh
      simpa only [Finset.mem_union, not_or] using this
    refine ⟨?_, ?_, ?_⟩
    · ext x
      have := outside x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    · rw [Finset.disjoint_left]
      intro x inNamed inRest
      have := outside x
      simp only [Finset.mem_union, Finset.mem_sdiff] at inRest
      tauto
    · rw [Finset.disjoint_left]
      intro x inNamed inRest
      have := outside x
      simp only [Finset.mem_union, Finset.mem_sdiff] at inRest
      tauto

/-- The solutions of set unification with disjoint rests. -/
def SetUnifier (named₁ named₂ : Finset α) : Type _ :=
  {rests : Finset α × Finset α //
    named₁ ∪ rests.1 = named₂ ∪ rests.2 ∧ Disjoint named₁ rests.1 ∧ Disjoint named₂ rests.2}

/-- The solutions correspond one to one to the fresh rests, the sets disjoint
from every named value. -/
def setUnifiers (named₁ named₂ : Finset α) :
    SetUnifier named₁ named₂ ≃ {fresh : Finset α // Disjoint fresh (named₁ ∪ named₂)} where
  toFun solution :=
    ⟨solution.1.1 \ named₂, by
      obtain ⟨fresh, apart, restEq, _⟩ :=
        (set_unify_iff named₁ named₂ solution.1.1 solution.1.2).mp solution.2
      rw [Finset.disjoint_left]
      intro x inFresh inNamed
      rw [restEq, Finset.mem_sdiff, Finset.mem_union, Finset.mem_sdiff] at inFresh
      rcases inFresh with ⟨inner | inner, outsideSecond⟩
      · exact outsideSecond inner.1
      · exact Finset.disjoint_left.mp apart inner inNamed⟩
  invFun fresh := ⟨((named₂ \ named₁) ∪ fresh.1, (named₁ \ named₂) ∪ fresh.1),
    (set_unify_iff named₁ named₂ _ _).mpr ⟨fresh.1, fresh.2, rfl, rfl⟩⟩
  left_inv solution := by
    obtain ⟨⟨rest₁, rest₂⟩, solves⟩ := solution
    obtain ⟨fresh, apart, rfl, rfl⟩ := (set_unify_iff named₁ named₂ rest₁ rest₂).mp solves
    apply Subtype.ext
    have outside : ∀ x, x ∈ fresh → x ∉ named₁ ∧ x ∉ named₂ := by
      intro x inFresh
      simpa only [Finset.mem_union, not_or] using Finset.disjoint_left.mp apart inFresh
    refine Prod.ext ?_ ?_ <;>
    · ext x
      have := outside x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
  right_inv fresh := by
    obtain ⟨fresh, apart⟩ := fresh
    apply Subtype.ext
    have outside : ∀ x, x ∈ fresh → x ∉ named₁ ∧ x ∉ named₂ := by
      intro x inFresh
      simpa only [Finset.mem_union, not_or] using Finset.disjoint_left.mp apart inFresh
    ext x
    have := outside x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- **One element variable on each side of a set equation with disjoint
rests.** Either the variables are equal and the rests are equal, or they are
different and each lies in the other side's rest. The second family carries a
disequality, which no substitution expresses. -/
theorem set_cons_unify_iff (x y : α) (rest₁ rest₂ : Finset α) :
    (insert x rest₁ = insert y rest₂ ∧ x ∉ rest₁ ∧ y ∉ rest₂) ↔
      (x = y ∧ rest₁ = rest₂ ∧ x ∉ rest₁) ∨
        (x ≠ y ∧ ∃ fresh, x ∉ fresh ∧ y ∉ fresh ∧
          rest₁ = insert y fresh ∧ rest₂ = insert x fresh) := by
  constructor
  · rintro ⟨solves, xOut, yOut⟩
    have member : ∀ z, z = x ∨ z ∈ rest₁ ↔ z = y ∨ z ∈ rest₂ := fun z => by
      simpa only [Finset.mem_insert] using Iff.of_eq (congrArg (z ∈ ·) solves)
    by_cases same : x = y
    · subst same
      refine Or.inl ⟨rfl, ?_, xOut⟩
      ext z
      have := member z
      by_cases zx : z = x
      · subst zx; tauto
      · tauto
    · refine Or.inr ⟨same, rest₁.erase y, ?_, ?_, ?_, ?_⟩
      · exact fun inside => xOut (Finset.mem_of_mem_erase inside)
      · exact Finset.notMem_erase y rest₁
      · have yIn : y ∈ rest₁ := ((member y).mpr (Or.inl rfl)).resolve_left (Ne.symm same)
        exact (Finset.insert_erase yIn).symm
      · ext z
        have := member z
        simp only [Finset.mem_insert, Finset.mem_erase]
        by_cases zx : z = x
        · subst zx; tauto
        · by_cases zy : z = y
          · subst zy; tauto
          · tauto
  · rintro (⟨rfl, rfl, xOut⟩ | ⟨different, fresh, xOut, yOut, rfl, rfl⟩)
    · exact ⟨rfl, xOut, xOut⟩
    · refine ⟨Finset.insert_comm _ _ _, ?_, ?_⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨different, xOut⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨Ne.symm different, yOut⟩

end Sets

/-! ## Complete sets of solutions and unification types -/

section Types

variable {S : Type*}

/-- `C` is a complete set of solutions: its members solve the problem, and
every solution is an instance of a member. `instanceOf θ δ` says that `δ` is
an instance of `θ`. -/
structure IsComplete (solves : S → Prop) (instanceOf : S → S → Prop) (C : Set S) : Prop where
  sound : ∀ θ ∈ C, solves θ
  covers : ∀ δ, solves δ → ∃ θ ∈ C, instanceOf θ δ

/-- A complete set none of whose members is an instance of another. -/
structure IsMinimalComplete (solves : S → Prop) (instanceOf : S → S → Prop) (C : Set S) : Prop
    extends IsComplete solves instanceOf C where
  minimal : ∀ θ ∈ C, ∀ θ' ∈ C, instanceOf θ θ' → θ = θ'

/-- At most one most general solution is needed. -/
def Unitary (solves : S → Prop) (instanceOf : S → S → Prop) : Prop :=
  ∃ C, IsComplete solves instanceOf C ∧ C.Subsingleton

/-- Finitely many solutions suffice. -/
def Finitary (solves : S → Prop) (instanceOf : S → S → Prop) : Prop :=
  ∃ C, IsComplete solves instanceOf C ∧ C.Finite

/-- A minimal complete set exists, and none is finite. -/
def Infinitary (solves : S → Prop) (instanceOf : S → S → Prop) : Prop :=
  (∃ C, IsMinimalComplete solves instanceOf C) ∧ ¬ Finitary solves instanceOf

theorem Unitary.finitary {solves : S → Prop} {instanceOf : S → S → Prop}
    (unitary : Unitary solves instanceOf) : Finitary solves instanceOf := by
  obtain ⟨C, complete, single⟩ := unitary
  exact ⟨C, complete, single.finite⟩

end Types

/-! ## Associative unification is infinitary -/

section Associative

variable {A X : Type*}

/-- Words over constants `A` and sequence variables `X`: the terms of the free
monoid, in which a variable stands for any finite word. -/
abbrev Word (A X : Type*) := List (A ⊕ X)

/-- Replace each variable by a word. -/
def substWord (σ : X → Word A X) (w : Word A X) : Word A X :=
  w.flatMap (Sum.elim (fun a => [Sum.inl a]) σ)

@[simp] theorem substWord_nil (σ : X → Word A X) : substWord σ [] = [] := rfl

@[simp] theorem substWord_cons_inl (σ : X → Word A X) (a : A) (w : Word A X) :
    substWord σ (.inl a :: w) = .inl a :: substWord σ w := rfl

@[simp] theorem substWord_cons_inr (σ : X → Word A X) (x : X) (w : Word A X) :
    substWord σ (.inr x :: w) = σ x ++ substWord σ w := rfl

theorem substWord_append (σ : X → Word A X) (u v : Word A X) :
    substWord σ (u ++ v) = substWord σ u ++ substWord σ v :=
  List.flatMap_append

@[simp] theorem substWord_replicate (σ : X → Word A X) (a : A) (n : ℕ) :
    substWord σ (List.replicate n (.inl a)) = List.replicate n (.inl a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, substWord_cons_inl, ih]

/-- `δ` is an instance of `θ` on the variables `V`. -/
def InstanceOn (V : Set X) (θ δ : X → Word A X) : Prop :=
  ∃ τ : X → Word A X, ∀ x ∈ V, δ x = substWord τ (θ x)

/-- A word that commutes with a letter is a power of that letter. -/
theorem eq_replicate_of_append_singleton {c : A ⊕ X} :
    ∀ {w : Word A X}, w ++ [c] = c :: w → w = List.replicate w.length c
  | [], _ => rfl
  | d :: w, commutes => by
      simp only [List.cons_append, List.cons.injEq] at commutes
      obtain ⟨rfl, rest⟩ := commutes
      have power := eq_replicate_of_append_singleton rest
      calc d :: w = d :: List.replicate w.length d := by rw [← power]
        _ = List.replicate (d :: w).length d := by rw [List.length_cons, List.replicate_succ]

/-- Plotkin's equation `x a = a x`, a variable against a constant. -/
def PlotkinSolves (a : A) (x : X) (σ : X → Word A X) : Prop :=
  substWord σ [.inr x, .inl a] = substWord σ [.inl a, .inr x]

/-- Its solutions are the substitutions sending `x` to a power of `a`. -/
theorem plotkinSolves_iff (a : A) (x : X) (σ : X → Word A X) :
    PlotkinSolves a x σ ↔ ∃ n, σ x = List.replicate n (.inl a) := by
  unfold PlotkinSolves
  simp only [substWord_cons_inr, substWord_cons_inl, substWord_nil, List.append_nil]
  constructor
  · intro commutes
    exact ⟨_, eq_replicate_of_append_singleton commutes⟩
  · rintro ⟨n, power⟩
    rw [power, ← List.replicate_succ', List.replicate_succ]

variable [DecidableEq X]

/-- The solution `x ↦ aⁿ`, other variables unchanged. -/
def plotkinPower (a : A) (x : X) (n : ℕ) : X → Word A X :=
  fun y => if y = x then List.replicate n (.inl a) else [.inr y]

theorem plotkinPower_solves (a : A) (x : X) (n : ℕ) : PlotkinSolves a x (plotkinPower a x n) :=
  (plotkinSolves_iff a x _).mpr ⟨n, by simp [plotkinPower]⟩

/-- **No finite complete set of unifiers exists** for `x a = a x`: an instance
of a power of `a` is that same power, so a complete set needs one member per
power. -/
theorem plotkin_not_finitary (a : A) (x : X) :
    ¬ Finitary (PlotkinSolves a x) (InstanceOn {x}) := by
  rintro ⟨C, complete, finite⟩
  have every : ∀ n, n ∈ (fun θ : X → Word A X => (θ x).length) '' C := by
    intro n
    obtain ⟨θ, member, τ, covered⟩ := complete.covers _ (plotkinPower_solves a x n)
    obtain ⟨m, power⟩ := (plotkinSolves_iff a x θ).mp (complete.sound θ member)
    have same := congrArg List.length (covered x rfl)
    simp only [plotkinPower, if_pos, power, substWord_replicate, List.length_replicate] at same
    exact ⟨θ, member, by simp [power, same]⟩
  obtain ⟨bound, isBound⟩ :=
    Set.Finite.bddAbove (Set.Finite.image (fun θ : X → Word A X => (θ x).length) finite)
  have := isBound (every (bound + 1))
  omega

/-- The powers of `a` form a minimal complete set. -/
theorem plotkin_minimal (a : A) (x : X) :
    IsMinimalComplete (PlotkinSolves a x) (InstanceOn {x}) (Set.range (plotkinPower a x)) where
  sound := by
    rintro _ ⟨n, rfl⟩
    exact plotkinPower_solves a x n
  covers := by
    intro δ solves
    obtain ⟨n, power⟩ := (plotkinSolves_iff a x δ).mp solves
    refine ⟨plotkinPower a x n, ⟨n, rfl⟩, δ, ?_⟩
    intro y member
    rw [Set.mem_singleton_iff] at member
    subst member
    simp [plotkinPower, power]
  minimal := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ ⟨τ, covered⟩
    have same := congrArg List.length (covered x rfl)
    simp only [plotkinPower, if_pos, substWord_replicate, List.length_replicate] at same
    rw [same]

/-- **Associative unification is infinitary** (Plotkin): `x a = a x` has a
minimal complete set of unifiers, and every complete set is infinite. -/
theorem plotkin_infinitary (a : A) (x : X) :
    Infinitary (PlotkinSolves a x) (InstanceOn {x}) :=
  ⟨⟨_, plotkin_minimal a x⟩, plotkin_not_finitary a x⟩

end Associative

/-! ## Flat bag patterns: one family of solutions per partial matching -/

section FlatBags

variable {α β A : Type*}

/-- The partial matchings of two lists of element terms: each left element is
paired with one right element, which is removed, or left unmatched. Each
result lists the pairs, the unmatched left elements and the unmatched right
elements. -/
def matchings : List α → List β → List (List (α × β) × List α × List β)
  | [], ys => [([], [], ys)]
  | x :: xs, ys =>
      (matchings xs ys).map (fun r => (r.1, x :: r.2.1, r.2.2)) ++
        (List.finRange ys.length).flatMap fun j : Fin ys.length =>
          (matchings xs (ys.eraseIdx j)).map fun r => ((x, ys.get j) :: r.1, r.2.1, r.2.2)

/-- A partial matching uses every element once. -/
theorem perm_of_mem_matchings :
    ∀ {xs : List α} {ys : List β} {r : List (α × β) × List α × List β},
      r ∈ matchings xs ys →
        (r.1.map Prod.fst ++ r.2.1).Perm xs ∧ (r.1.map Prod.snd ++ r.2.2).Perm ys
  | [], ys, r, member => by
      simp only [matchings, List.mem_singleton] at member
      subst member
      simp
  | x :: xs, ys, r, member => by
      rw [matchings, List.mem_append] at member
      rcases member with unmatched | matched
      · obtain ⟨r', inner, rfl⟩ := List.mem_map.mp unmatched
        obtain ⟨left, right⟩ := perm_of_mem_matchings inner
        exact ⟨List.perm_middle.trans (left.cons x), right⟩
      · obtain ⟨j, -, chosen⟩ := List.mem_flatMap.mp matched
        obtain ⟨r', inner, rfl⟩ := List.mem_map.mp chosen
        obtain ⟨left, right⟩ := perm_of_mem_matchings inner
        refine ⟨left.cons x, ?_⟩
        exact (right.cons _).trans (List.getElem_cons_eraseIdx_perm j.isLt)

variable [DecidableEq A]

/-- **Flat bag unification is finitary.** With element terms read by `v`,
`{xs | r} = {ys | s}` holds exactly when some partial matching pairs equal
elements, and each rest is the other side's unmatched elements plus one
common fresh part. The matchings are finitely many; in each family the pairs
are syntactic equations between element terms and the rests are in solved
form. A side with no rest has `0` for its rest, which forces the other side's
unmatched elements to be absent. -/
theorem flat_bag_unify_iff (v : α → A) :
    ∀ (xs ys : List α) (r s : Multiset A),
      ((xs.map v : List A) : Multiset A) + r = (ys.map v : List A) + s ↔
        ∃ m ∈ matchings xs ys, (∀ p ∈ m.1, v p.1 = v p.2) ∧
          ∃ t, r = ((m.2.2.map v : List A) : Multiset A) + t ∧
            s = ((m.2.1.map v : List A) : Multiset A) + t := by
  intro xs
  induction xs with
  | nil =>
      intro ys r s
      constructor
      · intro solves
        refine ⟨([], [], ys), by simp [matchings], by simp, s, ?_, by simp⟩
        simpa using solves
      · rintro ⟨m, member, -, t, rfl, rfl⟩
        simp only [matchings, List.mem_singleton] at member
        subst member
        simp
  | cons x xs ih =>
      intro ys r s
      constructor
      · intro solves
        rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add] at solves
        by_cases found : ∃ j : Fin ys.length, v (ys.get j) = v x
        · obtain ⟨j, same⟩ := found
          have split : ((ys.map v : List A) : Multiset A) =
              v x ::ₘ (((ys.eraseIdx j).map v : List A) : Multiset A) := by
            rw [← same, Multiset.cons_coe, ← List.map_cons]
            exact Multiset.coe_eq_coe.mpr ((List.getElem_cons_eraseIdx_perm j.isLt).symm.map v)
          rw [split, Multiset.cons_add, Multiset.cons_inj_right] at solves
          obtain ⟨m, member, pairs, t, rest₁, rest₂⟩ := (ih _ r s).mp solves
          refine ⟨((x, ys.get j) :: m.1, m.2.1, m.2.2), ?_, ?_, t, rest₁, rest₂⟩
          · rw [matchings, List.mem_append]
            exact Or.inr (List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
              List.mem_map.mpr ⟨m, member, rfl⟩⟩)
          · intro p inPairs
            rcases List.mem_cons.mp inPairs with rfl | later
            · exact same.symm
            · exact pairs p later
        · simp only [not_exists] at found
          have absent : v x ∉ ((ys.map v : List A) : Multiset A) := by
            intro inside
            obtain ⟨y, inYs, same⟩ := List.mem_map.mp (Multiset.mem_coe.mp inside)
            obtain ⟨j, rfl⟩ := List.get_of_mem inYs
            exact found j same
          have inRest : v x ∈ s := by
            have : v x ∈ ((ys.map v : List A) : Multiset A) + s :=
              solves ▸ Multiset.mem_cons_self _ _
            exact (Multiset.mem_add.mp this).resolve_left absent
          rw [← Multiset.cons_erase inRest, Multiset.add_cons, Multiset.cons_inj_right] at solves
          obtain ⟨m, member, pairs, t, rest₁, rest₂⟩ := (ih ys r (s.erase (v x))).mp solves
          refine ⟨(m.1, x :: m.2.1, m.2.2), ?_, pairs, t, rest₁, ?_⟩
          · rw [matchings, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨m, member, rfl⟩)
          · rw [← Multiset.cons_erase inRest, rest₂, List.map_cons, ← Multiset.cons_coe,
              Multiset.cons_add]
      · rintro ⟨m, member, pairs, t, rfl, rfl⟩
        obtain ⟨left, right⟩ := perm_of_mem_matchings member
        rw [← Multiset.coe_eq_coe.mpr (left.map v), ← Multiset.coe_eq_coe.mpr (right.map v)]
        have matched : m.1.map (v ∘ Prod.fst) = m.1.map (v ∘ Prod.snd) :=
          List.map_congr_left fun p inPairs => pairs p inPairs
        simp only [List.map_append, List.map_map, ← Multiset.coe_add, matched]
        abel

/-- With no rest on either side, the solutions are the perfect matchings of
equal elements. -/
theorem flat_bag_closed_iff (v : α → A) (xs ys : List α) :
    ((xs.map v : List A) : Multiset A) = (ys.map v : List A) ↔
      ∃ m ∈ matchings xs ys, (∀ p ∈ m.1, v p.1 = v p.2) ∧ m.2.1 = [] ∧ m.2.2 = [] := by
  have := flat_bag_unify_iff v xs ys 0 0
  simp only [add_zero] at this
  rw [this]
  constructor
  · rintro ⟨m, member, pairs, t, rest₁, rest₂⟩
    have left_zero {a t : Multiset A} (sum : 0 = a + t) : a = 0 := by
      have count := congrArg Multiset.card sum
      rw [Multiset.card_add, Multiset.card_zero] at count
      exact Multiset.card_eq_zero.mp (by omega)
    have empty₁ := left_zero rest₁
    have empty₂ := left_zero rest₂
    simp only [Multiset.coe_eq_zero, List.map_eq_nil_iff] at empty₁ empty₂
    exact ⟨m, member, pairs, empty₂, empty₁⟩
  · rintro ⟨m, member, pairs, empty₁, empty₂⟩
    exact ⟨m, member, pairs, 0, by simp [empty₂], by simp [empty₁]⟩

end FlatBags

/-! ## Flat set patterns with disjoint rests -/

section FlatSets

variable {α A : Type*} [DecidableEq A]

/-- Sets with rests disjoint from their named elements are equal exactly when
their duplicate-free bags are. -/
theorem set_disjoint_unify_iff_bag (X Y r s : Finset A) :
    (X ∪ r = Y ∪ s ∧ Disjoint X r ∧ Disjoint Y s) ↔
      (X.val + r.val = Y.val + s.val ∧ Disjoint X r ∧ Disjoint Y s) := by
  constructor
  · rintro ⟨solves, apart₁, apart₂⟩
    refine ⟨?_, apart₁, apart₂⟩
    rw [← Finset.disjUnion_eq_union _ _ apart₁, ← Finset.disjUnion_eq_union _ _ apart₂] at solves
    exact congrArg Finset.val solves
  · rintro ⟨solves, apart₁, apart₂⟩
    refine ⟨?_, apart₁, apart₂⟩
    rw [← Finset.disjUnion_eq_union _ _ apart₁, ← Finset.disjUnion_eq_union _ _ apart₂]
    exact Finset.val_injective solves

/-- Every list of element terms has a sublist that reads every value once. -/
theorem exists_representatives (v : α → A) :
    ∀ xs : List α, ∃ xs' : List α, xs'.Sublist xs ∧ (xs'.map v).Nodup ∧
      (xs'.map v).toFinset = (xs.map v).toFinset
  | [] => ⟨[], List.Sublist.slnil, List.nodup_nil, rfl⟩
  | x :: xs => by
      obtain ⟨xs', sub, nodup, same⟩ := exists_representatives v xs
      by_cases seen : v x ∈ xs.map v
      · refine ⟨xs', sub.cons x, nodup, ?_⟩
        rw [same, List.map_cons, List.toFinset_cons, Finset.insert_eq_of_mem]
        exact List.mem_toFinset.mpr seen
      · refine ⟨x :: xs', sub.cons_cons x, ?_, ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun inside => seen ?_, nodup⟩
          rw [← List.mem_toFinset, ← same]
          exact List.mem_toFinset.mpr inside
        · rw [List.map_cons, List.map_cons, List.toFinset_cons, List.toFinset_cons, same]

/-- **Flat set unification with disjoint rests is finitary with constraints.**
`{xs | r} = {ys | s}`, with each rest disjoint from its side's elements,
holds exactly when representatives chosen among each side's element terms
(finitely many choices: sublists) have pairwise different values covering the
side, and the flat bag equation on the representatives holds. Beyond
equations between element terms, a family carries disequalities: distinct
representatives and disjoint rests. No substitution expresses those. -/
theorem flat_set_unify_iff (v : α → A) (xs ys : List α) (r s : Finset A) :
    ((xs.map v).toFinset ∪ r = (ys.map v).toFinset ∪ s ∧
        Disjoint (xs.map v).toFinset r ∧ Disjoint (ys.map v).toFinset s) ↔
      ∃ xs' ys' : List α, xs'.Sublist xs ∧ ys'.Sublist ys ∧
        (xs'.map v).Nodup ∧ (ys'.map v).Nodup ∧
        (xs'.map v).toFinset = (xs.map v).toFinset ∧ (ys'.map v).toFinset = (ys.map v).toFinset ∧
        Disjoint (xs.map v).toFinset r ∧ Disjoint (ys.map v).toFinset s ∧
        ∃ m ∈ matchings xs' ys', (∀ p ∈ m.1, v p.1 = v p.2) ∧
          ∃ t, r.val = ((m.2.2.map v : List A) : Multiset A) + t ∧
            s.val = ((m.2.1.map v : List A) : Multiset A) + t := by
  have val_of {zs : List α} (nodup : (zs.map v).Nodup) :
      ((zs.map v).toFinset).val = ((zs.map v : List A) : Multiset A) := by
    rw [List.toFinset_val, List.Nodup.dedup nodup]
  constructor
  · intro solves
    obtain ⟨xs', subX, nodupX, sameX⟩ := exists_representatives v xs
    obtain ⟨ys', subY, nodupY, sameY⟩ := exists_representatives v ys
    obtain ⟨bags, apart₁, apart₂⟩ := (set_disjoint_unify_iff_bag _ _ _ _).mp solves
    rw [← sameX, ← sameY, val_of nodupX, val_of nodupY] at bags
    exact ⟨xs', ys', subX, subY, nodupX, nodupY, sameX, sameY, apart₁, apart₂,
      (flat_bag_unify_iff v xs' ys' r.val s.val).mp bags⟩
  · rintro ⟨xs', ys', -, -, nodupX, nodupY, sameX, sameY, apart₁, apart₂, family⟩
    have bags := (flat_bag_unify_iff v xs' ys' r.val s.val).mpr family
    rw [← val_of nodupX, ← val_of nodupY, sameX, sameY] at bags
    exact (set_disjoint_unify_iff_bag _ _ _ _).mpr ⟨bags, apart₁, apart₂⟩

end FlatSets

/-! ## Controls -/

namespace Controls

/-- Without disjointness one rest does not determine the other: against the
rest `∅`, both `∅` and `{1}` solve `{1} ∪ r = {1} ∪ s`. -/
theorem set_rests_undetermined :
    ({1} : Finset ℕ) ∪ ∅ = {1} ∪ ∅ ∧ ({1} : Finset ℕ) ∪ ∅ = {1} ∪ {1} ∧
      (∅ : Finset ℕ) ≠ {1} := by
  decide

/-- With an element variable on each side, neither family of solutions
contains the other: `x = y = 1` with empty rests is only in the first, and
`x = 1, y = 2` with rests `{2}` and `{1}` only in the second. -/
theorem both_families_needed :
    ((1 : ℕ) = 1 ∧ (0 : Multiset ℕ) = 0) ∧
      (¬ ∃ fresh : Multiset ℕ, (0 : Multiset ℕ) = 1 ::ₘ fresh ∧ (0 : Multiset ℕ) = 1 ::ₘ fresh) ∧
      (∃ fresh : Multiset ℕ, ({2} : Multiset ℕ) = 2 ::ₘ fresh ∧ ({1} : Multiset ℕ) = 1 ::ₘ fresh) ∧
      ¬ ((1 : ℕ) = 2 ∧ ({2} : Multiset ℕ) = {1}) := by
  refine ⟨⟨rfl, rfl⟩, ?_, ⟨0, rfl, rfl⟩, by decide⟩
  rintro ⟨fresh, empty, -⟩
  exact Multiset.cons_ne_zero empty.symm

/-- Two element variables against a bag with a repeated element: the solution
`(1, 1)` is chosen twice, by its two orders of occurrences, while the set of
distinct elements has no two distinct elements to choose. On a duplicate-free
value the two readings agree: every solution once. -/
theorem repeated_element_repeats_answers :
    (selections 2 ({1, 1} : Multiset ℕ)).count ([1, 1], 0) = 2 ∧
      selections 2 (({1, 1} : Multiset ℕ).dedup) = 0 ∧
      (selections 2 ({1, 2} : Multiset ℕ)).Nodup := by
  refine ⟨by decide, ?_, nodup_selections 2 (by decide)⟩
  rw [← Multiset.card_eq_zero, card_selections]
  decide

/-- Bag families are closed under identifying the variables: instantiating
both element variables of the second family by one value is still a solution.
The set family is not: with both variables `1` the rests `{1}` are no longer
disjoint from the named element. -/
theorem bag_needs_no_disequality :
    (1 ::ₘ ((1 : ℕ) ::ₘ (0 : Multiset ℕ)) = 1 ::ₘ (1 ::ₘ 0)) ∧
      ¬ ((1 : ℕ) ∉ (insert 1 ∅ : Finset ℕ)) := by
  decide

/-- A bag equation whose named parts overlap: `{1, 2} + r = {2, 3} + s` has the
matched part `{2}`, and `r = {3} + t`, `s = {1} + t`. -/
theorem decompose_example :
    ({1, 2} : Multiset ℕ) + ({3} + {7}) = ({2, 3} : Multiset ℕ) + ({1} + {7}) ∧
      ({1, 2} : Multiset ℕ) ∩ {2, 3} = {2} := by
  decide

/-- **A bag equation with two unifiers.** `{x | r} = {1, 2}` holds exactly
for `x = 1, r = {2}` and for `x = 2, r = {1}`: neither is an instance of the
other. -/
theorem bag_two_unifiers (x : ℕ) (r : Multiset ℕ) :
    x ::ₘ r = {1, 2} ↔ (x = 1 ∧ r = {2}) ∨ (x = 2 ∧ r = {1}) := by
  rw [bag_select_iff]
  constructor
  · rintro ⟨member, rfl⟩
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact Or.inl ⟨rfl, by decide⟩
    · exact Or.inr ⟨rfl, by decide⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨by decide, by decide⟩

/-- **An associative problem with infinitely many unifiers.** Every power of
the letter solves `x a = a x`, and different powers are different solutions. -/
theorem plotkin_every_power (n : ℕ) :
    PlotkinSolves (X := Unit) 0 () (plotkinPower 0 () n) ∧
      plotkinPower (A := ℕ) 0 () n () ≠ plotkinPower 0 () (n + 1) () := by
  refine ⟨plotkinPower_solves 0 () n, ?_⟩
  intro same
  have := congrArg List.length same
  simp [plotkinPower] at this

end Controls

end Mettapedia.Algebra.Collections.Unification
