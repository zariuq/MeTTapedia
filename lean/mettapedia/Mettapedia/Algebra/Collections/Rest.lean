import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.List
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Set.Finite.Basic

/-!
# Rest patterns over lists, bags and sets

A collection pattern with a rest names some elements and binds the remainder.
Its matches against a value are the solutions of one equation in the
collection's free structure: `named ++ rest = value` for lists,
`named + rest = value` for bags, and `named ∪ rest = value` for sets.

* **Lists.** A prefix and a trailing rest have at most one solution, the drop
  (`list_rest_iff`). Two rests in one list pattern have one solution per split
  point (`list_split_iff`).
* **Bags, named values.** At most one solution, the truncated difference
  (`bag_rest_iff`).
* **Bags, element variables.** `x ::ₘ rest = value` has one solution per
  distinct element of the value (`mem_bagSelections`, `card_bagSelections`),
  and every decomposition into a list of named elements and a rest is one of
  finitely many (`bag_decompositions_finite`). A matcher that chooses by
  position on a stored list returns each solution once per occurrence of its
  chosen element (`count_selectOccurrences`, `indexSelections_eq`).
* **Sets.** With idempotence the rest is not determined: it may or may not
  repeat each named element, so `k` named elements that occur give `2 ^ k`
  rests (`set_rest_iff`, `card_setRests`). Requiring the rest to be disjoint
  from the named elements restores uniqueness (`set_disjoint_rest_iff`), and
  on the duplicate-free representative it is exactly bag selection
  (`set_select_iff_bag_select`; several variables, which must choose distinct
  elements: `set_selections_iff_bag_selections`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Rest

variable {α : Type*}

/-! ## Lists -/

/-- A list pattern `[named… | rest]` matches by prefix; the rest is the drop. -/
theorem list_rest_iff (named rest value : List α) :
    named ++ rest = value ↔ named <+: value ∧ rest = value.drop named.length := by
  constructor
  · rintro rfl
    exact ⟨List.prefix_append named rest, List.drop_left.symm⟩
  · rintro ⟨⟨tail, appended⟩, rfl⟩
    subst appended
    rw [List.drop_left]

/-- Two rests in one list pattern: every split point is a solution. -/
theorem list_split_iff (first second value : List α) :
    first ++ second = value ↔
      ∃ point ≤ value.length, first = value.take point ∧ second = value.drop point := by
  constructor
  · rintro rfl
    exact ⟨first.length, by simp, by simp, by simp⟩
  · rintro ⟨point, _, rfl, rfl⟩
    exact List.take_append_drop point value

/-! ## Bags -/

section Bags

variable [DecidableEq α]

/-- A bag pattern with named values and a rest: the rest is the truncated
difference, and the match exists exactly when the named values are contained
with multiplicity. -/
theorem bag_rest_iff (named rest value : Multiset α) :
    named + rest = value ↔ named ≤ value ∧ rest = value - named := by
  constructor
  · rintro rfl
    exact ⟨Multiset.le_add_right named rest, (add_tsub_cancel_left named rest).symm⟩
  · rintro ⟨contained, rfl⟩
    exact add_tsub_cancel_of_le contained

/-- One element variable and a rest. -/
theorem bag_select_iff (element : α) (rest value : Multiset α) :
    element ::ₘ rest = value ↔ element ∈ value ∧ rest = value.erase element := by
  constructor
  · rintro rfl
    exact ⟨Multiset.mem_cons_self element rest, (Multiset.erase_cons_head element rest).symm⟩
  · rintro ⟨member, rfl⟩
    exact Multiset.cons_erase member

/-- The distinct solutions of `x ::ₘ rest = value`. -/
def bagSelections (value : Multiset α) : Finset (α × Multiset α) :=
  value.toFinset.image fun element => (element, value.erase element)

theorem mem_bagSelections (value : Multiset α) (solution : α × Multiset α) :
    solution ∈ bagSelections value ↔ solution.1 ::ₘ solution.2 = value := by
  obtain ⟨element, rest⟩ := solution
  rw [bag_select_iff]
  simp only [bagSelections, Finset.mem_image, Multiset.mem_toFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨chosen, member, rfl, rfl⟩
    exact ⟨member, rfl⟩
  · rintro ⟨member, rfl⟩
    exact ⟨element, member, rfl, rfl⟩

/-- One solution per distinct element. -/
theorem card_bagSelections (value : Multiset α) :
    (bagSelections value).card = value.toFinset.card :=
  Finset.card_image_of_injective _ (fun _ _ same => (Prod.mk.inj same).1)

/-- Every decomposition of a bag into a list of named elements and a rest is
one of finitely many. -/
theorem bag_decompositions_finite (value : Multiset α) :
    {solution : List α × Multiset α |
      (solution.1 : Multiset α) + solution.2 = value}.Finite := by
  refine (((value.powerset.bind Multiset.lists).map
    (fun named : List α => (named, value - (named : Multiset α)))).toFinset.finite_toSet).subset ?_
  rintro ⟨named, rest⟩ solves
  simp only [Set.mem_ofPred_eq] at solves
  obtain ⟨contained, restEq⟩ := (bag_rest_iff _ _ _).mp solves
  subst restEq
  simp only [Multiset.mem_toFinset, Multiset.mem_map,
    Multiset.mem_bind, Multiset.mem_powerset, Prod.mk.injEq, Finset.mem_coe]
  exact ⟨named, ⟨named, contained, (Multiset.mem_lists_iff _ _).mpr rfl⟩, rfl, rfl⟩

/-- Selection by occurrence: each element of the bag, with the rest left by
removing that occurrence. -/
def selectOccurrences (value : Multiset α) : Multiset (α × Multiset α) :=
  value.map fun element => (element, value.erase element)

/-- Occurrence selection returns exactly the solutions, each as many times as
its chosen element occurs. -/
theorem count_selectOccurrences (value : Multiset α) (element : α) (rest : Multiset α) :
    (selectOccurrences value).count (element, rest) =
      if rest = value.erase element then value.count element else 0 := by
  unfold selectOccurrences
  rw [Multiset.count_map]
  split_ifs with same
  · subst same
    rw [Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro chosen _
    constructor
    · intro equal
      exact (Prod.mk.inj equal).1
    · rintro rfl
      rfl
  · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro chosen _ equal
    obtain ⟨sameElement, sameRest⟩ := Prod.mk.inj equal
    subst sameElement
    exact same sameRest

theorem toFinset_selectOccurrences (value : Multiset α) :
    (selectOccurrences value).toFinset = bagSelections value := by
  unfold selectOccurrences bagSelections
  rw [Multiset.toFinset_map]

/-- Removing the element at a position of a stored list leaves the bag with
one occurrence of that element removed. -/
theorem eraseIdx_coe (stored : List α) (position : Fin stored.length) :
    ((stored.eraseIdx position : List α) : Multiset α) =
      (stored : Multiset α).erase (stored.get position) := by
  induction stored with
  | nil => exact position.elim0
  | cons head tail ih =>
    cases position using Fin.cases with
    | zero => simp
    | succ position =>
      have erased : (head :: tail).eraseIdx (position.succ : ℕ) =
          head :: tail.eraseIdx position := by
        simp [Fin.val_succ]
      have chosen : (head :: tail).get position.succ = tail.get position := rfl
      rw [erased, chosen, ← Multiset.cons_coe, ← Multiset.cons_coe, ih]
      by_cases same : tail.get position = head
      · rw [same, Multiset.erase_cons_head, Multiset.cons_erase]
        rw [← same]
        exact Multiset.mem_coe.mpr (List.get_mem tail position)
      · rw [Multiset.erase_cons_tail _ (Ne.symm same)]

/-- Choosing by position on a stored list, the way a matcher enumerates the
stored elements, is occurrence selection on the stored bag. -/
theorem indexSelections_eq (stored : List α) :
    (((List.finRange stored.length).map fun position =>
        (stored.get position, ((stored.eraseIdx position : List α) : Multiset α))) :
      Multiset (α × Multiset α)) = selectOccurrences stored := by
  unfold selectOccurrences
  have : ((stored : Multiset α).map fun element =>
      (element, (stored : Multiset α).erase element)) =
      (((List.finRange stored.length).map stored.get).map fun element =>
        (element, (stored : Multiset α).erase element) : List (α × Multiset α)) := by
    rw [← List.ofFn_eq_map, List.ofFn_get, Multiset.map_coe]
  rw [this, List.map_map]
  congr 1
  apply List.map_congr_left
  intro position _
  simp [eraseIdx_coe]

end Bags

/-! ## Sets -/

section Sets

variable [DecidableEq α]

/-- One element variable and a rest, modulo idempotence: the rest may or may
not contain the chosen element again. -/
theorem set_select_iff (element : α) (rest value : Finset α) :
    insert element rest = value ↔
      element ∈ value ∧ value.erase element ⊆ rest ∧ rest ⊆ value := by
  constructor
  · rintro rfl
    refine ⟨Finset.mem_insert_self element rest, ?_, Finset.subset_insert element rest⟩
    intro chosen member
    rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase member) with same | kept
    · exact absurd same (Finset.ne_of_mem_erase member)
    · exact kept
  · rintro ⟨member, lower, upper⟩
    apply Finset.Subset.antisymm
    · exact Finset.insert_subset member upper
    · intro chosen chosenMember
      by_cases same : chosen = element
      · rw [same]; exact Finset.mem_insert_self element rest
      · exact Finset.mem_insert_of_mem (lower (Finset.mem_erase.mpr ⟨same, chosenMember⟩))

/-- Named values and a rest, modulo idempotence: every rest between the
unnamed part and the whole value solves. -/
theorem set_rest_iff (named rest value : Finset α) :
    named ∪ rest = value ↔ named ⊆ value ∧ value \ named ⊆ rest ∧ rest ⊆ value := by
  constructor
  · rintro rfl
    refine ⟨Finset.subset_union_left, ?_, Finset.subset_union_right⟩
    intro chosen member
    rw [Finset.mem_sdiff, Finset.mem_union] at member
    exact member.1.resolve_left member.2
  · rintro ⟨contained, lower, upper⟩
    apply Finset.Subset.antisymm (Finset.union_subset contained upper)
    intro chosen member
    by_cases named_member : chosen ∈ named
    · exact Finset.mem_union_left _ named_member
    · exact Finset.mem_union_right _ (lower (Finset.mem_sdiff.mpr ⟨member, named_member⟩))

/-- All rests solving `named ∪ rest = value`. -/
def setRests (named value : Finset α) : Finset (Finset α) :=
  named.powerset.image fun repeated => (value \ named) ∪ repeated

theorem mem_setRests (named value rest : Finset α) (contained : named ⊆ value) :
    rest ∈ setRests named value ↔ named ∪ rest = value := by
  rw [set_rest_iff]
  simp only [setRests, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨repeated, inside, rfl⟩
    exact ⟨contained, Finset.subset_union_left,
      Finset.union_subset Finset.sdiff_subset (inside.trans contained)⟩
  · rintro ⟨_, lower, upper⟩
    refine ⟨rest ∩ named, Finset.inter_subset_right, ?_⟩
    apply Finset.Subset.antisymm
    · exact Finset.union_subset lower Finset.inter_subset_left
    · intro chosen member
      by_cases named_member : chosen ∈ named
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨member, named_member⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨upper member, named_member⟩)

/-- `k` named elements that occur leave `2 ^ k` possible rests. -/
theorem card_setRests (named value : Finset α) :
    (setRests named value).card = 2 ^ named.card := by
  rw [setRests, Finset.card_image_of_injOn, Finset.card_powerset]
  intro first firstInside second secondInside same
  have firstSub : first ⊆ named := Finset.mem_powerset.mp firstInside
  have secondSub : second ⊆ named := Finset.mem_powerset.mp secondInside
  have restrict : ∀ repeated ⊆ named, ((value \ named) ∪ repeated) ∩ named = repeated := by
    intro repeated inside
    ext chosen
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨_, outside⟩ | kept, inNamed⟩
      · exact absurd inNamed outside
      · exact kept
    · intro kept
      exact ⟨Or.inr kept, inside kept⟩
  rw [← restrict first firstSub, ← restrict second secondSub]
  exact congrArg (· ∩ named) same

/-- A rest disjoint from the named values is unique: the set difference. -/
theorem set_disjoint_rest_iff (named rest value : Finset α) :
    named ∪ rest = value ∧ Disjoint named rest ↔ named ⊆ value ∧ rest = value \ named := by
  constructor
  · rintro ⟨rfl, disjoint⟩
    exact ⟨Finset.subset_union_left, (Finset.union_sdiff_cancel_left disjoint).symm⟩
  · rintro ⟨contained, rfl⟩
    exact ⟨Finset.union_sdiff_of_subset contained, Finset.disjoint_sdiff⟩

/-- Disjoint selection on a set is bag selection on its duplicate-free
representative. -/
theorem set_select_iff_bag_select (element : α) (rest value : Finset α) :
    element ::ₘ rest.val = value.val ↔ insert element rest = value ∧ element ∉ rest := by
  constructor
  · intro solves
    have fresh : element ∉ rest := by
      intro member
      have nodup := value.nodup
      rw [← solves, Multiset.nodup_cons] at nodup
      exact nodup.1 member
    refine ⟨?_, fresh⟩
    apply Finset.val_injective
    rw [Finset.insert_val_of_notMem fresh, solves]
  · rintro ⟨rfl, fresh⟩
    rw [Finset.insert_val_of_notMem fresh]

/-- Several element variables and a disjoint rest on a set are bag selection
on its duplicate-free representative: the chosen elements are distinct and the
rest is disjoint from them. -/
theorem set_selections_iff_bag_selections (named : List α) (rest value : Finset α) :
    (named : Multiset α) + rest.val = value.val ↔
      named.toFinset ∪ rest = value ∧ named.Nodup ∧ Disjoint named.toFinset rest := by
  constructor
  · intro solves
    have nodup := value.nodup
    rw [← solves, Multiset.nodup_add] at nodup
    obtain ⟨namedNodup, -, apart⟩ := nodup
    refine ⟨?_, Multiset.coe_nodup.mp namedNodup, ?_⟩
    · ext element
      have member := congrArg (element ∈ ·) solves
      simp only [Multiset.mem_add, Multiset.mem_coe, Finset.mem_val, eq_iff_iff] at member
      simpa [Finset.mem_union, List.mem_toFinset] using member
    · rw [Finset.disjoint_left]
      intro element inNamed inRest
      exact Multiset.disjoint_left.mp apart (Multiset.mem_coe.mpr (List.mem_toFinset.mp inNamed))
        (Finset.mem_val.mpr inRest)
  · rintro ⟨rfl, namedNodup, apart⟩
    rw [← Finset.disjUnion_eq_union _ _ apart]
    change _ = named.toFinset.val + rest.val
    rw [List.toFinset_val, List.Nodup.dedup namedNodup]

end Sets

/-! ## Controls -/

namespace Controls

/-- A list pattern with two rests is not determined. -/
theorem list_two_rests_ambiguous :
    ([] : List ℕ) ++ [1] = [1] ∧ ([1] : List ℕ) ++ [] = [1] ∧ ([] : List ℕ) ≠ [1] :=
  ⟨rfl, rfl, by simp⟩

/-- A list prefix that is not a prefix does not match, even when its elements
occur. -/
theorem list_prefix_is_ordered : ¬ ∃ rest : List ℕ, [2] ++ rest = [1, 2] := by
  rintro ⟨rest, solves⟩
  simp at solves

/-- A bag element variable has one solution per distinct element, and
occurrence selection repeats a solution for a repeated element. -/
theorem bag_variable_two_solutions :
    (1, ({1, 2} : Multiset ℕ)) ∈ bagSelections ({1, 1, 2} : Multiset ℕ) ∧
      (2, ({1, 1} : Multiset ℕ)) ∈ bagSelections ({1, 1, 2} : Multiset ℕ) ∧
      (selectOccurrences ({1, 1, 2} : Multiset ℕ)).count (1, {1, 2}) = 2 := by
  refine ⟨(mem_bagSelections _ _).mpr (by decide), (mem_bagSelections _ _).mpr (by decide), ?_⟩
  rw [count_selectOccurrences, if_pos (by decide)]
  decide

/-- Named bag values must occur with multiplicity. -/
theorem bag_rest_needs_multiplicity :
    ¬ ∃ rest : Multiset ℕ, ({1, 1} : Multiset ℕ) + rest = {1, 2} := by
  rintro ⟨rest, solves⟩
  have := ((bag_rest_iff _ _ _).mp solves).1
  have count := Multiset.count_le_of_le 1 this
  simp at count

/-- Without disjointness a set rest is not unique: `{1 | rest}` against `{1}`
has the rests `∅` and `{1}`. -/
theorem set_rest_not_unique :
    ({1} : Finset ℕ) ∪ ∅ = {1} ∧ ({1} : Finset ℕ) ∪ {1} = {1} ∧
      setRests ({1} : Finset ℕ) {1} = {∅, {1}} := by
  refine ⟨by decide, by decide, by decide⟩

/-- Two element variables cannot choose the same element of a set. -/
theorem set_variables_choose_distinct :
    ((([1, 2] : List ℕ) : Multiset ℕ) + (∅ : Finset ℕ).val = ({1, 2} : Finset ℕ).val) ∧
      ¬ ((([1, 1] : List ℕ) : Multiset ℕ) + ({2} : Finset ℕ).val = ({1, 2} : Finset ℕ).val) := by
  refine ⟨(set_selections_iff_bag_selections _ _ _).mpr ⟨by decide, by decide, by decide⟩, ?_⟩
  rw [set_selections_iff_bag_selections]
  rintro ⟨-, nodup, -⟩
  exact absurd nodup (by decide)

/-- The disjoint rest is the unique one. -/
theorem set_disjoint_rest_control :
    ∀ rest : Finset ℕ, ({1} : Finset ℕ) ∪ rest = {1, 2} ∧ Disjoint {1} rest ↔ rest = {2} := by
  intro rest
  rw [set_disjoint_rest_iff]
  constructor
  · rintro ⟨_, rfl⟩
    decide
  · rintro rfl
    decide

end Controls

end Mettapedia.Algebra.Collections.Rest
