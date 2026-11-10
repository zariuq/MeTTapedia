import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits

/-!
# Store effects at the dialect adapter boundary

Selection and publication have different contracts. `removeAll` takes a completed
per-row selection; it does not unify all selected rows with one shared substitution.
The selector can describe open terms, scoped unification or ground equality. This
module neither replaces those selectors nor treats an interrupted selector as false.
`removeOne` preserves the order of the surviving occurrences and removes at most one.

The list laws are connected to the existing occurrence commit and transform footprint
laws below. They are semantic acceptance contracts, not a C-correspondence theorem.
In particular the Boolean returned here is the changed-store policy of CeTTa's
PeTTa expression-removal path; other source-language return policies are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v
variable {Row : Type u}

/-- Publication of an already selected atom; a comma-shaped atom is still one row. -/
def add (rows : List Row) (row : Row) : List Row := rows ++ [row]

/-- Every matched occurrence is removed, without exporting a row's match bindings. -/
def removeAll (select : Row → Bool) (rows : List Row) : List Row × Bool :=
  (rows.filter fun row => !select row, rows.any select)

/-- One selected occurrence; the remaining equal occurrences are retained. -/
def removeOne (select : Row → Bool) (rows : List Row) : List Row := rows.eraseP select

/-- Routing stores the already split instances in their prescribed order. -/
def route (rows instances : List Row) : List Row × Nat :=
  (rows ++ instances, instances.length)

theorem add_preserves_occurrences (rows : List Row) (row : Row) :
    rows <+: add rows row := by simp [add]

theorem add_length (rows : List Row) (row : Row) :
    (add rows row).length = rows.length + 1 := by simp [add]

theorem removeAll_retains_iff (select : Row → Bool) (rows : List Row) (row : Row) :
    row ∈ (removeAll select rows).1 ↔ row ∈ rows ∧ select row = false := by
  simp [removeAll]

theorem removeAll_reports_change_iff (select : Row → Bool) (rows : List Row) :
    (removeAll select rows).2 = true ↔ ∃ row ∈ rows, select row = true :=
  List.any_eq_true

/-- The removed and surviving occurrences partition the input, including duplicates. -/
theorem removeAll_partition_length (select : Row → Bool) (rows : List Row) :
    (removeAll select rows).1.length + (rows.filter select).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases found : select row <;> simp [removeAll, found] at ih ⊢ <;> omega

theorem removeAll_false_iff_unchanged (select : Row → Bool) (rows : List Row) :
    (removeAll select rows).2 = false ↔ (removeAll select rows).1 = rows := by
  induction rows with
  | nil => simp [removeAll]
  | cons row rest ih =>
      cases found : select row with
      | false => simp_all [removeAll]
      | true =>
          have shorter := (List.filter_sublist (p := fun row => !select row) (l := rest)).length_le
          simp only [removeAll, List.any_cons, found, Bool.true_or, Bool.true_eq_false,
            List.filter_cons, Bool.not_true, Bool.false_eq_true, if_false, false_iff]
          intro same
          have lengths := congrArg List.length same
          simp only [List.length_cons] at lengths
          omega

theorem removeAll_idempotent (select : Row → Bool) (rows : List Row) :
    removeAll select (removeAll select rows).1 = ((removeAll select rows).1, false) := by
  have none : ((removeAll select rows).1).any select = false := by
    apply Bool.eq_false_iff.mpr
    intro someMatch
    obtain ⟨row, member, selected⟩ := List.any_eq_true.mp someMatch
    have absent := (removeAll_retains_iff select rows row).mp member
    simp [absent.2] at selected
  have unchanged := (removeAll_false_iff_unchanged select (removeAll select rows).1).mp none
  exact Prod.ext unchanged none

theorem removeOne_length (select : Row → Bool) (rows : List Row) :
    (removeOne select rows).length =
      if rows.any select then rows.length - 1 else rows.length := List.length_eraseP

/-- The chosen occurrence is the first matching occurrence, not every equal row. -/
theorem removeOne_at_first (select : Row → Bool) (before after : List Row) (row : Row)
    (noEarlier : before.any select = false) (selected : select row = true) :
    removeOne select (before ++ row :: after) = before ++ after := by
  simp [removeOne, List.eraseP_append, noEarlier, selected]

theorem removeOne_keeps_later_copy (select : Row → Bool) (row : Row) (rest : List Row)
    (selected : select row = true) :
    removeOne select (row :: row :: rest) = row :: rest := by
  simp [removeOne, selected]

theorem route_count_is_growth (rows instances : List Row) :
    (route rows instances).1.length = rows.length + (route rows instances).2 := by
  simp [route]

theorem route_composes (rows first second : List Row) :
    route (route rows first).1 second =
      ((route rows (first ++ second)).1, second.length) ∧
    (route rows (first ++ second)).2 = (route rows first).2 + (route rows second).2 := by
  simp [route, List.append_assoc]

section Occurrences

variable {Occurrence : Type u} [DecidableEq Occurrence] {Label : Type v}

/-- Completed selection produces a take-only occurrence effect. -/
def selectedRemoval (label : Occurrence → Label) (select : Label → Bool)
    (store : Finset Occurrence) : Commit Occurrence Label :=
  ⟨regionOf label store select, ∅, ∅, []⟩

omit [DecidableEq Occurrence] in
theorem selectedRemoval_enabled (label : Occurrence → Label) (select : Label → Bool)
    (store : Finset Occurrence) : Enabled label store (selectedRemoval label select store) := by
  refine ⟨Finset.filter_subset _ _, by simp [selectedRemoval], ?_, ?_, ?_⟩
  · simp [selectedRemoval]
  · simp [selectedRemoval]
  · simp [selectedRemoval]

/-- Exact survivor membership, not merely equality of store sizes. -/
theorem selectedRemoval_fire (label : Occurrence → Label) (select : Label → Bool)
    (store : Finset Occurrence) :
    fire store (selectedRemoval label select store) =
      store.filter (fun occurrence => select (label occurrence) = false) := by
  ext occurrence
  simp [fire, selectedRemoval, regionOf]
  tauto

/-- List publication and occurrence publication agree on the retained identities. -/
theorem removeAll_occurrence_projection (label : Occurrence → Label) (select : Label → Bool)
    (rows : List Occurrence) :
    (removeAll (fun occurrence => select (label occurrence)) rows).1.toFinset =
      fire rows.toFinset (selectedRemoval label select rows.toFinset) := by
  rw [selectedRemoval_fire]
  ext occurrence
  simp [removeAll]

/-- One-occurrence deletion realizes `takeOne`; equal labels may still have distinct identities. -/
theorem removeOne_occurrence_projection (label : Occurrence → Label) (select : Label → Bool)
    (before after : List Occurrence) (chosen : Occurrence)
    (identities : (before ++ chosen :: after).Nodup)
    (noEarlier : before.any (fun o => select (label o)) = false)
    (selected : select (label chosen) = true) :
    Enabled label (before ++ chosen :: after).toFinset (Commit.takeOne chosen) ∧
      (removeOne (fun o => select (label o)) (before ++ chosen :: after)).toFinset =
        fire (before ++ chosen :: after).toFinset (Commit.takeOne chosen : Commit Occurrence Label) := by
  have absent := (List.nodup_cons.mp (List.nodup_middle.mp identities)).1
  constructor
  · refine ⟨?_, by simp, by simp, by simp, by simp⟩
    simp
  · rw [removeOne_at_first _ _ _ _ noEarlier selected]
    ext occurrence
    simp only [List.mem_toFinset, fire, Commit.takeOne_taken, Commit.takeOne_made,
      Finset.union_empty, Finset.mem_sdiff, Finset.mem_singleton, List.mem_append, List.mem_cons]
    constructor
    · intro member
      refine ⟨?_, ?_⟩
      · rcases member with member | member
        · exact Or.inl member
        · exact Or.inr (Or.inr member)
      · intro same
        subst occurrence
        exact absent (List.mem_append.mpr member)
    · rintro ⟨member | same | member, different⟩
      · exact Or.inl member
      · exact False.elim (different same)
      · exact Or.inr member

theorem add_is_make (label : Occurrence → Label) (store : Finset Occurrence)
    (fresh : Occurrence) (absent : fresh ∉ store) :
    Enabled label store (Commit.makeOne fresh) ∧
      fire store (Commit.makeOne fresh : Commit Occurrence Label) = insert fresh store := by
  constructor
  · refine ⟨by simp, by simp, by simp, ?_, by simp⟩
    simpa using absent
  · ext occurrence
    simp [fire]

theorem add_occurrence_projection (rows : List Occurrence) (fresh : Occurrence) :
    (add rows fresh).toFinset =
      fire rows.toFinset (Commit.makeOne fresh : Commit Occurrence Label) := by
  ext occurrence
  simp [add, fire]

/-- Routing a completed instance list is a make-only occurrence effect. -/
def routedMakes (instances : Finset Occurrence) : Commit Occurrence Label :=
  ⟨∅, ∅, instances, []⟩

theorem route_occurrence_projection (label : Occurrence → Label)
    (rows instances : List Occurrence) (fresh : Disjoint instances.toFinset rows.toFinset) :
    Enabled label rows.toFinset (routedMakes instances.toFinset) ∧
      (route rows instances).1.toFinset =
        fire rows.toFinset (routedMakes (Label := Label) instances.toFinset) := by
  constructor
  · exact ⟨by simp [routedMakes], by simp [routedMakes], by simp [routedMakes],
      fresh, by simp [routedMakes]⟩
  · ext occurrence
    simp [route, routedMakes, fire]

end Occurrences

section TransformFootprints

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A repeated take consumes two copies; a single stored copy does not license it. -/
theorem double_take_iff (store : PeTTa.LibTransform.Store) (atom : Atom) :
    PeTTa.LibTransform.valid store [(.take, atom), (.take, atom)] = true ↔ 2 ≤ store.count atom := by
  simp [PeTTa.LibTransform.valid]

/-- Sharing a read and a take requires two copies even though the values agree. -/
theorem read_take_iff (store : PeTTa.LibTransform.Store) (atom : Atom) :
    PeTTa.LibTransform.valid store [(.read, atom), (.take, atom)] = true ↔ 2 ≤ store.count atom := by
  simp [PeTTa.LibTransform.valid]

theorem take_count_conservation (store : PeTTa.LibTransform.Store) (footprint : PeTTa.LibTransform.Footprint)
    (valid : PeTTa.LibTransform.valid store footprint = true) (atom : Atom) :
    (PeTTa.LibTransform.commit footprint store).count atom + (PeTTa.LibTransform.takes footprint).count atom =
      store.count atom := by
  rw [PeTTa.LibTransform.count_commit]
  apply Nat.sub_add_cancel
  by_cases present : atom ∈ PeTTa.LibTransform.takes footprint
  · have bound := (PeTTa.LibTransform.valid_iff store footprint).mp valid atom present
    omega
  · simp [List.count_eq_zero.mpr present]

end TransformFootprints

end Mettapedia.Languages.MeTTa.StoreAndDemand.StoreEffects
