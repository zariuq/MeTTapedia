import Mettapedia.GSLT.Dynamics.GenericJoinRegions
import Mettapedia.Machines.Cursor.PrefixProjectionIndex
import Mathlib.Data.List.Sublists

/-!
# Source-derived layouts for conditioned factor projections

A layout places exactly the currently constrained physical columns before
the output column. Constants are always constrained; variables are constrained
only when the captured environment supplies a value. Repeated variables keep
all their column tests. A prefix index prepared for this layout returns the
same conditioned projection as the independent source-row filter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.FactorProjectionLayout

open ConjunctiveRegionProvenance GenericJoinRegions
open Mettapedia.Machines.Cursor

variable {n : Nat} {Value Id : Type} [LinearOrder Value]

abbrev Row (factor : Factor (Fin n) Value Id) := Id × (Fin factor.arity → Value)

def binding (environment : Environment n Value) : Cell (Fin n) Value → Option Value
  | .constant value => some value
  | .variable name => environment name

omit [LinearOrder Value] in
theorem compatible_binding (environment : Environment n Value) (cell : Cell (Fin n) Value)
    (value outside : Value) :
    compatible environment cell value ↔ (binding environment cell).isSome →
      value = (binding environment cell).getD outside := by
  cases cell with
  | constant literal => simp [compatible, binding]
  | «variable» name => cases present : environment name <;> simp [compatible, binding, present]

def conditions (environment : Environment n Value) (factor : Factor (Fin n) Value Id) : List (Fin factor.arity) :=
  (List.finRange factor.arity).filter (fun column => (binding environment (factor.pattern column)).isSome)

def keys (factor : Factor (Fin n) Value Id) (selected : List (Fin factor.arity)) : List (Row factor → Value) :=
  selected.map (fun column row => row.2 column)

def target (factor : Factor (Fin n) Value Id) (selected : List (Fin factor.arity))
    (environment : Environment n Value) (outside : Value) (i : Fin (keys factor selected).length) : Value :=
  (binding environment (factor.pattern (selected[i.val]'(by simpa [keys] using i.isLt)))).getD outside

omit [LinearOrder Value] in
theorem keys_get (factor : Factor (Fin n) Value Id) (selected : List (Fin factor.arity))
    (i : Fin (keys factor selected).length) (row : Row factor) :
    (keys factor selected)[i] row = row.2 (selected[i.val]'(by simpa [keys] using i.isLt)) := by
  change (selected.map (fun (column : Fin factor.arity) (value : Row factor) => value.2 column))[i.val] row = _
  rw [List.getElem_map]

omit [LinearOrder Value] in
theorem selected_tests (factor : Factor (Fin n) Value Id) (environment : Environment n Value)
    (outside : Value) (row : Row factor) :
    (∀ i : Fin (keys factor (conditions environment factor)).length,
      (keys factor (conditions environment factor))[i] row =
        target factor (conditions environment factor) environment outside i) ↔
      rowMatches environment factor row := by
  have listTests : (∀ i : Fin (keys factor (conditions environment factor)).length,
      (keys factor (conditions environment factor))[i] row =
        target factor (conditions environment factor) environment outside i) ↔
      ∀ column ∈ conditions environment factor,
        row.2 column = (binding environment (factor.pattern column)).getD outside := by
    constructor
    · intro all column member
      obtain ⟨i, inside, atColumn⟩ := List.mem_iff_getElem.mp member
      let index : Fin (keys factor (conditions environment factor)).length := ⟨i, by simpa [keys] using inside⟩
      have test := all index
      rw [keys_get] at test
      simpa only [target, index, atColumn] using test
    · intro all index
      have inside : index.val < (conditions environment factor).length := by simpa [keys] using index.isLt
      have test := all ((conditions environment factor)[index.val]) (List.getElem_mem inside)
      rw [keys_get]
      exact test
  rw [listTests]
  constructor
  · intro all column
    apply (compatible_binding environment (factor.pattern column) (row.2 column) outside).mpr
    intro present
    exact all column (by simp [conditions, present])
  · intro matched column member
    apply (compatible_binding environment (factor.pattern column) (row.2 column) outside).mp (matched column)
    simpa [conditions] using member

theorem reference_projection (factor : Factor (Fin n) Value Id) (environment : Environment n Value)
    (outside : Value) (column : Fin factor.arity) :
    PrefixProjectionIndex.reference (keys factor (conditions environment factor))
      (target factor (conditions environment factor) environment outside) (fun row => row.2 column) factor.rows =
      projection environment factor column := by
  unfold PrefixProjectionIndex.reference
  rw [PrefixRunIndex.reference_eq_filter]
  have filtered : factor.rows.filter (fun row => decide (∀ i : Fin (keys factor (conditions environment factor)).length,
      (keys factor (conditions environment factor))[i] row =
        target factor (conditions environment factor) environment outside i)) =
      factor.rows.filter (fun row => decide (rowMatches environment factor row)) := by
    congr 1
    funext row
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using selected_tests factor environment outside row
  rw [filtered]
  rfl

structure Layout (arity : Nat) where
  conditions : List (Fin arity)
  output : Fin arity
  deriving DecidableEq, Repr

def sourceLayout (factor : Factor (Fin n) Value Id) (environment : Environment n Value)
    (column : Fin factor.arity) : Layout factor.arity := ⟨conditions environment factor, column⟩

def Layout.columns (factor : Factor (Fin n) Value Id) (layout : Layout factor.arity) : List (Row factor → Value) :=
  keys factor layout.conditions ++ [fun row => row.2 layout.output]

def layouts (arity : Nat) : List (Layout arity) :=
  (List.finRange arity).sublists.flatMap (fun selected =>
    (List.finRange arity).map (fun column => ⟨selected, column⟩))

omit [LinearOrder Value] in
theorem sourceLayout_present (factor : Factor (Fin n) Value Id) (environment : Environment n Value)
    (column : Fin factor.arity) : sourceLayout factor environment column ∈ layouts factor.arity := by
  apply List.mem_flatMap.mpr
  refine ⟨conditions environment factor, List.mem_sublists.mpr (List.filter_sublist), ?_⟩
  exact List.mem_map.mpr ⟨column, List.mem_finRange column, rfl⟩

theorem layouts_count (arity : Nat) : (layouts arity).length = 2 ^ arity * arity := by
  simp [layouts, List.length_flatMap, List.map_const', List.sum_replicate, List.length_sublists]

structure Entry (factor : Factor (Fin n) Value Id) where
  layout : Layout factor.arity
  built : PrefixRunIndex.Built (Row factor) Value (layout.columns factor).length

def prepare (factor : Factor (Fin n) Value Id) (layout : Layout factor.arity) : Entry factor :=
  ⟨layout, PrefixRunIndex.build (layout.columns factor) factor.rows⟩

def catalogue (factor : Factor (Fin n) Value Id) : List (Entry factor) :=
  (layouts factor.arity).map (prepare factor)

def lookup {factor : Factor (Fin n) Value Id} (entries : List (Entry factor))
    (requested : Layout factor.arity) : Option (Entry factor) :=
  entries.find? (fun entry => decide (entry.layout = requested))

/-- Count the layout-equality tests in the same left-to-right selection.
The cost of comparing the two finite layouts is a separate scalar ledger. -/
def selectionTests {factor : Factor (Fin n) Value Id} : List (Entry factor) → Layout factor.arity → Nat
  | [], _ => 0
  | entry :: rest, requested =>
      if entry.layout = requested then 1 else 1 + selectionTests rest requested

theorem selectionTests_bound {factor : Factor (Fin n) Value Id} (entries : List (Entry factor))
    (requested : Layout factor.arity) : selectionTests entries requested ≤ entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [selectionTests]
      split <;> simp only [List.length_cons] <;> omega

theorem lookup_catalogue (factor : Factor (Fin n) Value Id) (requested : Layout factor.arity)
    (present : requested ∈ layouts factor.arity) :
    lookup (catalogue factor) requested = some (prepare factor requested) := by
  unfold lookup catalogue
  rw [List.find?_map]
  have found : (layouts factor.arity).find? (fun layout => decide (layout = requested)) = some requested := by
    have any : ((layouts factor.arity).find? (fun layout => decide (layout = requested))).isSome := by
      rw [List.find?_isSome]
      exact ⟨requested, present, by simp⟩
    cases answer : (layouts factor.arity).find? (fun layout => decide (layout = requested)) with
    | none => simp [answer] at any
    | some result =>
        have same : result = requested := by simpa only [decide_eq_true_eq] using List.find?_some answer
        subst result
        rfl
  change ((layouts factor.arity).find? (fun layout => decide (layout = requested))).map (prepare factor) = _
  rw [found]
  rfl

def Entry.read (factor : Factor (Fin n) Value Id) (entry : Entry factor)
    (environment : Environment n Value) (outside : Value) : IndexedIntersection.Range Value × Nat :=
  PrefixProjectionIndex.descend (keys factor entry.layout.conditions) (fun row => row.2 entry.layout.output)
    entry.built.index outside (target factor entry.layout.conditions environment outside)

theorem prepared_source_exact (factor : Factor (Fin n) Value Id) (environment : Environment n Value)
    (outside : Value) (column : Fin factor.arity) :
    let result := (prepare factor (sourceLayout factor environment column)).read factor environment outside
    result.1.view.toFinset = projection environment factor column ∧
      result.1.Sorted ∧ result.1.width ≤ factor.rows.length ∧
      result.2 ≤ factor.arity * (IndexedIntersection.seekBudget factor.rows.length + 1) := by
  have spec := PrefixProjectionIndex.descend_spec (keys factor (conditions environment factor))
    (fun row => row.2 column) factor.rows outside
    (target factor (conditions environment factor) environment outside) factor.rows.length le_rfl
  rw [reference_projection] at spec
  refine ⟨spec.1, spec.2.1, spec.2.2.1, ?_⟩
  have length : (keys factor (conditions environment factor)).length ≤ factor.arity := by
    simpa [keys, conditions] using List.length_filter_le
      (fun column => (binding environment (factor.pattern column)).isSome) (List.finRange factor.arity)
  exact spec.2.2.2.trans (Nat.mul_le_mul_right _ length)

def read {factor : Factor (Fin n) Value Id} (entries : List (Entry factor))
    (environment : Environment n Value) (outside : Value) (column : Fin factor.arity) :
    Option (IndexedIntersection.Range Value × Nat) :=
  (lookup entries (sourceLayout factor environment column)).map
    (fun entry => entry.read factor environment outside)

theorem read_catalogue (factor : Factor (Fin n) Value Id) (environment : Environment n Value)
    (outside : Value) (column : Fin factor.arity) :
    read (catalogue factor) environment outside column =
      some ((prepare factor (sourceLayout factor environment column)).read factor environment outside) := by
  rw [read, lookup_catalogue factor _ (sourceLayout_present factor environment column)]
  rfl

/-- The catalogue is retained data. Its proof is established by preparation;
queries use the stored entries, not a rebuilding environment-to-index function. -/
structure Store (factor : Factor (Fin n) Value Id) where
  entries : List (Entry factor)
  lookup_exact : ∀ environment column, lookup entries (sourceLayout factor environment column) =
    some (prepare factor (sourceLayout factor environment column))

def prepareStore (factor : Factor (Fin n) Value Id) : Store factor where
  entries := catalogue factor
  lookup_exact environment column := lookup_catalogue factor _ (sourceLayout_present factor environment column)

theorem Store.read_success {factor : Factor (Fin n) Value Id} (store : Store factor)
    (environment : Environment n Value) (outside : Value) (column : Fin factor.arity) :
    read store.entries environment outside column =
      some ((prepare factor (sourceLayout factor environment column)).read factor environment outside) := by
  rw [read, store.lookup_exact]
  rfl

def Store.projection {factor : Factor (Fin n) Value Id} (store : Store factor)
    (environment : Environment n Value) (outside : Value) (column : Fin factor.arity) :
    IndexedIntersection.Range Value × Nat :=
  (read store.entries environment outside column).get (by rw [store.read_success]; rfl)

theorem Store.projection_spec {factor : Factor (Fin n) Value Id} (store : Store factor)
    (environment : Environment n Value) (outside : Value) (column : Fin factor.arity) :
    let result := store.projection environment outside column
    result.1.view.toFinset = GenericJoinRegions.projection environment factor column ∧
      result.1.Sorted ∧ result.1.width ≤ factor.rows.length ∧
      result.2 ≤ factor.arity * (IndexedIntersection.seekBudget factor.rows.length + 1) := by
  dsimp only [Store.projection]
  simp only [store.read_success, Option.get_some]
  exact prepared_source_exact factor environment outside column

theorem catalogue_count (factor : Factor (Fin n) Value Id) :
    (catalogue factor).length = 2 ^ factor.arity * factor.arity := by
  rw [catalogue, List.length_map, layouts_count]

theorem layout_length (arity : Nat) (layout : Layout arity) (member : layout ∈ layouts arity) :
    layout.conditions.length ≤ arity := by
  obtain ⟨selected, selectedMember, outputMember⟩ := List.mem_flatMap.mp member
  obtain ⟨column, _, same⟩ := List.mem_map.mp outputMember
  cases same
  simpa using (List.mem_sublists.mp selectedMember).length_le

theorem catalogue_preparation_bound (factor : Factor (Fin n) Value Id) :
    ((catalogue factor).map (fun entry => entry.built.comparisons)).sum ≤
      (2 ^ factor.arity * factor.arity) * ((factor.arity + 1) * factor.rows.length *
        (Mettapedia.Algorithms.CountedKeySort.depth factor.rows.length + 1)) := by
  have perLayout : ∀ layout ∈ layouts factor.arity,
      (prepare factor layout).built.comparisons ≤ (factor.arity + 1) * factor.rows.length *
        (Mettapedia.Algorithms.CountedKeySort.depth factor.rows.length + 1) := by
    intro layout member
    have bound := PrefixRunIndex.build_comparisons (layout.columns factor) factor.rows
    have size := layout_length factor.arity layout member
    have length : (layout.columns factor).length ≤ factor.arity + 1 := by
      simp only [Layout.columns, keys, List.length_append, List.length_map, List.length_singleton]
      omega
    exact bound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ length))
  have summed := List.sum_le_sum (l := layouts factor.arity) perLayout
  simpa [catalogue, List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
    layouts_count, smul_eq_mul] using summed

namespace Controls

abbrev fixture : Factor (Fin 2) Nat Nat :=
  ⟨3, fun column => if column = 0 then .constant 9 else .variable (if column = 1 then 0 else 1),
    [(10, fun i => if i = 0 then 9 else if i = 1 then 1 else 3),
     (11, fun i => if i = 0 then 9 else if i = 1 then 1 else 4),
     (12, fun i => if i = 0 then 8 else if i = 1 then 1 else 5)]⟩

def captured : Environment 2 Nat := fun i => if i = 0 then some 1 else none

theorem constants_and_captures_select_layout : (sourceLayout fixture captured 2).conditions = [0, 1] := by decide +kernel

theorem missing_catalogue_is_refusal : read ([] : List (Entry fixture)) captured 0 2 = none := by decide +kernel

theorem captured_projection_exact :
    ((prepare fixture (sourceLayout fixture captured 2)).read fixture captured 0).1.view = [3, 4] := by decide +kernel

theorem full_catalogue_has_all_twenty_four_layouts : (catalogue fixture).length = 24 := by
  rw [catalogue_count]
  decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.FactorProjectionLayout
