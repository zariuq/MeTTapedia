import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Exact and general buckets as a complete candidate index

The builder partitions occurrences, not values. A general bucket covers every
row whose semantic view does not certify a single query key. Subtype and other
global dependencies can use that bucket or a separate dependency region.

Candidate extraction preserves the full answer bag after the real matcher is
applied. This theorem does not license changing effectful branch order or a
declared search strategy. Ordered clients need a stable merge and a residual
cursor refinement in addition to this bag law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.RegionalCandidates

variable {Key Row Answer : Type} [DecidableEq Key]

structure Index (Key Row : Type) where
  named : Key → List Row
  general : List Row

def empty : Index Key Row := ⟨fun _ => [], []⟩

def insert (route : Row → Option Key) (index : Index Key Row) (row : Row) : Index Key Row :=
  match route row with
  | none => { index with general := row :: index.general }
  | some key => { index with named := Function.update index.named key (row :: index.named key) }

/-- Independent bucket construction; a row occurs once in exactly one bucket. -/
def build (route : Row → Option Key) : List Row → Index Key Row
  | [] => empty
  | row :: rest => insert route (build route rest) row

def candidates (index : Index Key Row) (key : Key) : List Row :=
  index.named key ++ index.general

def eligible (route : Row → Option Key) (key : Key) (row : Row) : Bool :=
  decide (route row = some key ∨ route row = none)

theorem named_exact (route : Row → Option Key) (rows : List Row) (key : Key) :
    (build route rows).named key = rows.filter (fun row => decide (route row = some key)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases classified : route row with
    | none => simp [build, insert, classified, ih]
    | some target =>
      by_cases same : key = target
      · subst key
        simp [build, insert, classified, ih]
      · simp [build, insert, classified, ih, Function.update_of_ne same, Ne.symm same]

theorem general_exact (route : Row → Option Key) (rows : List Row) :
    (build route rows).general = rows.filter (fun row => decide (route row = none)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases classified : route row <;> simp [build, insert, classified, ih]

theorem candidates_bag (route : Row → Option Key) (rows : List Row) (key : Key) :
    (candidates (build route rows) key).Perm (rows.filter (eligible route key)) := by
  rw [candidates, named_exact, general_exact]
  induction rows with
  | nil => exact List.Perm.refl _
  | cons row rest ih =>
    cases classified : route row with
    | none =>
      have moved :
          ((rest.filter fun row => decide (route row = some key)) ++
            row :: (rest.filter fun row => decide (route row = none))).Perm
          (row :: ((rest.filter fun row => decide (route row = some key)) ++
            (rest.filter fun row => decide (route row = none)))) := List.perm_middle
      simpa [eligible, classified] using moved.trans (List.Perm.cons row ih)
    | some target =>
      by_cases same : target = key
      · subst target
        simpa [eligible, classified] using List.Perm.cons row ih
      · simpa [eligible, classified, same] using ih

/-- Coverage is a semantic obligation on the classifier, not on hash tags. -/
def Covers (route : Row → Option Key) (matchRow : Key → Row → Option Answer) : Prop :=
  ∀ key row answer, matchRow key row = some answer → eligible route key row = true

theorem filter_before_match (route : Row → Option Key) (matchRow : Key → Row → Option Answer)
    (coverage : Covers route matchRow) (rows : List Row) (key : Key) :
    (rows.filter (eligible route key)).filterMap (matchRow key) = rows.filterMap (matchRow key) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases matched : matchRow key row with
    | none =>
      by_cases inside : eligible route key row = true <;> simp [inside, matched, ih]
    | some answer =>
      simp [coverage key row answer matched, matched, ih]

/-- Full answer multiplicity follows from candidate coverage and real matching. -/
theorem indexed_answers_bag (route : Row → Option Key) (matchRow : Key → Row → Option Answer)
    (coverage : Covers route matchRow) (rows : List Row) (key : Key) :
    ((candidates (build route rows) key).filterMap (matchRow key)).Perm
      (rows.filterMap (matchRow key)) := by
  have perm := (candidates_bag route rows key).filterMap (matchRow key)
  rw [filter_before_match route matchRow coverage rows key] at perm
  exact perm

namespace Controls

/-- Distinct occurrences can carry equal payloads. -/
structure Occurrence where
  id : Nat
  key : Option Nat
  value : Nat
  deriving DecidableEq, Repr

def route (row : Occurrence) := row.key
def matchRow (key : Nat) (row : Occurrence) : Option (Nat × Nat) :=
  if row.key = none ∨ row.key = some key then some (row.id, row.value) else none

theorem coverage : Covers route matchRow := by
  intro key row answer matched
  simp only [matchRow] at matched
  split at matched
  · rename_i selected
    exact by simpa [eligible, route, or_comm] using selected
  · contradiction

def rows : List Occurrence :=
  [⟨10, some 1, 7⟩, ⟨11, none, 8⟩, ⟨12, some 1, 7⟩, ⟨13, some 2, 9⟩]

theorem general_subject_and_duplicate_occurrences_are_retained :
    (candidates (build route rows) 1).map Occurrence.id = [10, 12, 11] ∧
      ((candidates (build route rows) 1).filterMap (matchRow 1)) =
        [(10, 7), (12, 7), (11, 8)] := by decide

theorem exact_bucket_alone_is_incomplete :
    ((build route rows).named 1).filterMap (matchRow 1) ≠ rows.filterMap (matchRow 1) := by decide

/-- An internal representation tag is not a semantic discriminator. -/
def badRoute (row : Occurrence) : Option Nat :=
  if row.id = 11 then some 999 else row.key

theorem misclassified_general_subject_breaks_coverage : ¬ Covers badRoute matchRow := by
  intro covered
  have impossible := covered 1 ⟨11, none, 8⟩ (11, 8) (by decide)
  contradiction

theorem candidate_order_is_not_preserved_by_partition :
    (candidates (build route rows) 1).filterMap (matchRow 1) ≠ rows.filterMap (matchRow 1) := by decide

end Controls

end Mettapedia.Machines.RuntimePlumbing.RegionalCandidates
