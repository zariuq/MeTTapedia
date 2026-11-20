import Mettapedia.Languages.MeTTa.GradedWhere
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Grades where matches consume: coefficient and selector

When several candidate firings want the same stored row, only one of them fires. A grade can
then play two different parts, and this module separates them.

## Coefficient

The graded meaning of a race is the sum over which candidate wins: each alternative outcome
with the grade of the firing that leads to it. One run of the race is one term of that sum
(`annotate_eq_winner_add_rest`). Nothing is selected; a reading is applied at the end.
Normalising to a distribution is such a reading; a candidate's share needs the total of its
race (`GSLT.Core.normalizedShare_not_candidatewise`).

Firing every match in one commit multiplies grades where alternatives add them, and the two
are related by distributivity: a commit over rows that each have graded alternatives is the
sum over the joint choices of the products (`all_of_alternatives`).

## Selector

A grade can instead decide the winner: the candidate of greatest grade fires. Picking the
best is not a clause on one candidate
(`GSLT.Core.not_pointwiseSelection_of_isMaxSelection`), an arriving
candidate can change it, and with a complete query of the candidates it is a test of the
firing's own data (`AnnotatedRunsGrades.argmax_changed_by_arrival`, `argmax_iff_seen`).
This module adds:

* The winner does not depend on the order in which the candidates are met exactly when the
  best candidate is unique: then every order selects it (`argmax_perm`), and when two
  different candidates are both best, two orders select differently
  (`argmax_order_decides_of_tie`, `argmax_tie_depends_on_order`). A tie below the best does
  not matter.
* When each firing takes one row, firing the best candidate of each row is optimal among all
  sets of firings that can fire together (`best_per_row_optimal`,
  `best_per_row_attained`).
* When a firing may take several rows, firing the best candidate first is not optimal
  (`best_first_not_optimal`): a firing of grade 3 that takes two rows excludes two firings of
  grade 2 that take one row each.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.GradedWhere.Selection

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.GradedWhere

universe u

variable {K : Type u} {ι Occ M W Y : Type*}

/-! ## Coefficient -/

/-- **One run of a race is one term of its graded meaning.** For candidates given with the
outcome and the grade of each, the graded meaning is the winner's outcome with its grade,
plus the graded meaning of the others. -/
theorem annotate_eq_winner_add_rest [Semiring K] [DecidableEq (W × K)]
    (cs : Multiset (W × K)) {e : W × K} (h : e ∈ cs) :
    annotate cs = Finsupp.single e.1 e.2 + annotate (cs.erase e) := by
  rw [← annotate_cons, Multiset.cons_erase h]

/-- **Every match in one commit, over rows with alternatives.** The product over the rows of
the summed grades of each row's alternatives is the sum, over the joint choices of one
alternative per row, of the product of their grades. -/
theorem all_of_alternatives [CommSemiring K] {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    {κ : ρ → Type*} (alts : ∀ r, Finset (κ r)) (g : ∀ r, κ r → K) :
    ∏ r, ∑ j ∈ alts r, g r j = ∑ c ∈ Fintype.piFinset alts, ∏ r, g r (c r) :=
  Finset.prod_univ_sum alts g

/-! ## Selector -/

/-- A candidate that no later candidate beats is the one selected. -/
theorem argmax_cons_of_best [LinearOrder M] (g : ι → M) (a : ι) (l : List ι)
    (best : ∀ c ∈ l, g c ≤ g a) : (a :: l).argmax g = some a := by
  rw [List.argmax_cons]
  cases h : l.argmax g with
  | none => rfl
  | some c => simp [not_lt.mpr (best c (List.argmax_mem h))]

/-- **Where the best candidate is unique, selection does not depend on the order of the
candidates.** -/
theorem argmax_perm [LinearOrder M] (g : ι → M) {l₁ l₂ : List ι} (p : l₁.Perm l₂)
    (unique_best : ∀ a ∈ l₁, ∀ b ∈ l₁,
      (∀ c ∈ l₁, g c ≤ g a) → (∀ c ∈ l₁, g c ≤ g b) → a = b) :
    l₁.argmax g = l₂.argmax g := by
  cases h₁ : l₁.argmax g with
  | none =>
      rw [List.argmax_eq_none] at h₁
      subst h₁
      rw [List.nil_perm.mp p]
      simp
  | some m =>
      cases h₂ : l₂.argmax g with
      | none =>
          rw [List.argmax_eq_none] at h₂
          subst h₂
          rw [List.perm_nil.mp p] at h₁
          simp at h₁
      | some m' =>
          have hm : m ∈ l₁ := List.argmax_mem h₁
          have hm' : m' ∈ l₁ := p.mem_iff.mpr (List.argmax_mem h₂)
          have best : ∀ c ∈ l₁, g c ≤ g m := fun c hc => List.le_of_mem_argmax hc h₁
          have best' : ∀ c ∈ l₁, g c ≤ g m' := fun c hc =>
            List.le_of_mem_argmax (p.mem_iff.mp hc) h₂
          rw [unique_best m hm m' hm' best best']

/-- **Where two different candidates are both best, the order of the candidates decides.**
Two orders of the same candidates select differently. -/
theorem argmax_order_decides_of_tie [LinearOrder M] [DecidableEq ι] (g : ι → M) {l : List ι}
    {a b : ι} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) (best_a : ∀ c ∈ l, g c ≤ g a)
    (best_b : ∀ c ∈ l, g c ≤ g b) :
    ∃ l₁ l₂ : List ι, l₁.Perm l ∧ l₂.Perm l ∧ l₁.argmax g ≠ l₂.argmax g := by
  refine ⟨a :: l.erase a, b :: l.erase b, (List.perm_cons_erase ha).symm,
    (List.perm_cons_erase hb).symm, ?_⟩
  rw [argmax_cons_of_best g a _ fun c hc => best_a c (List.mem_of_mem_erase hc),
    argmax_cons_of_best g b _ fun c hc => best_b c (List.mem_of_mem_erase hc)]
  exact fun h => ne (Option.some.inj h)

/-- A tie of two candidates, run: each order selects its first. -/
theorem argmax_tie_depends_on_order :
    [true, false].argmax (fun _ : Bool => (0 : ℕ)) ≠
      [false, true].argmax (fun _ : Bool => (0 : ℕ)) := by
  decide

section SingleTake

variable [AddCommMonoid M] [DecidableEq Occ]

/-- **When each firing takes one row, the best firing of each row is optimal.** Let `row i`
be the row the firing `i` takes and `pick o` a firing of greatest grade among those that take
`o`. Every set of firings that take distinct rows weighs at most the picked firings. -/
theorem best_per_row_optimal [PartialOrder M] [IsOrderedAddMonoid M] [CanonicallyOrderedAdd M]
    (c : Finset ι) (row : ι → Occ) (g : ι → M) (pick : Occ → ι)
    (pick_best : ∀ i ∈ c, g i ≤ g (pick (row i))) {s : Finset ι} (sub : s ⊆ c)
    (compatible : Set.InjOn row s) :
    ∑ i ∈ s, g i ≤ ∑ o ∈ c.image row, g (pick o) :=
  calc ∑ i ∈ s, g i ≤ ∑ i ∈ s, g (pick (row i)) :=
        Finset.sum_le_sum fun i hi => pick_best i (sub hi)
    _ = ∑ o ∈ s.image row, g (pick o) := (Finset.sum_image (f := fun o => g (pick o)) compatible).symm
    _ ≤ ∑ o ∈ c.image row, g (pick o) :=
        Finset.sum_le_sum_of_subset (Finset.image_subset_image sub)

/-- The picked firings take distinct rows, and weigh the bound of `best_per_row_optimal`. -/
theorem best_per_row_attained [DecidableEq ι] (c : Finset ι) (row : ι → Occ) (g : ι → M) (pick : Occ → ι)
    (pick_row : ∀ o ∈ c.image row, row (pick o) = o) :
    Set.InjOn row ((c.image row).image pick : Finset ι) ∧
      ∑ i ∈ (c.image row).image pick, g i = ∑ o ∈ c.image row, g (pick o) := by
  have inj : Set.InjOn pick (c.image row : Finset Occ) := by
    intro o ho o' ho' h
    calc o = row (pick o) := (pick_row o (Finset.mem_coe.mp ho)).symm
      _ = row (pick o') := by rw [h]
      _ = o' := pick_row o' (Finset.mem_coe.mp ho')
  refine ⟨?_, Finset.sum_image inj⟩
  intro i hi j hj h
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi)
  obtain ⟨o', ho', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hj)
  rw [pick_row o ho, pick_row o' ho'] at h
  rw [h]

end SingleTake

/-- **When a firing may take several rows, the best firing first is not optimal.** Firing `0`
has the greatest grade and shares a row with each of the others, so once it fires nothing
else can; firings `1` and `2` take different rows and together weigh more. -/
theorem best_first_not_optimal :
    ∃ (taken : Fin 3 → Finset (Fin 2)) (g : Fin 3 → ℕ),
      (∀ j, g j ≤ g 0) ∧ (∀ j, j ≠ 0 → ¬ Disjoint (taken 0) (taken j)) ∧
        Disjoint (taken 1) (taken 2) ∧ g 0 < g 1 + g 2 := by
  refine ⟨![{0, 1}, {0}, {1}], ![3, 2, 2], ?_, ?_, ?_, ?_⟩ <;> decide

end Mettapedia.Languages.MeTTa.GradedWhere.Selection
