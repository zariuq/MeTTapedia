import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutFinite
import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutMaterial
import Mathlib.Data.List.Basic

/-!
# Validated finite presentations and qualified material operations

Rows retain successor occurrences in their authored order. Validation
checks every endpoint and the root. The Aczel equality and membership
readings use support adjacency; they may forget order, multiplicity and
occurrence positions. Those data remain present in the presentation.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Presentations

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ConstructiveFinite

structure Raw where
  root : Nat
  rows : List (List Nat)
  deriving DecidableEq

def Valid (raw : Raw) : Prop :=
  raw.root < raw.rows.length ∧
    ∀ row ∈ raw.rows, ∀ child ∈ row, child < raw.rows.length

def validateBool (raw : Raw) : Bool :=
  decide (raw.root < raw.rows.length) &&
    raw.rows.all (fun row => row.all (fun child => decide (child < raw.rows.length)))

theorem validateBool_eq_true (raw : Raw) : validateBool raw = true ↔ Valid raw := by
  simp [validateBool, Valid, List.all_eq_true]

instance validDecidable (raw : Raw) : Decidable (Valid raw) :=
  decidable_of_iff (validateBool raw = true) (validateBool_eq_true raw)

abbrev Checked := {raw : Raw // Valid raw}

def validate (raw : Raw) : Option Checked :=
  if available : validateBool raw = true then
    some ⟨raw, (validateBool_eq_true raw).mp available⟩
  else none

theorem validate_some (raw : Raw) (checked : Checked) :
    validate raw = some checked ↔ checked.val = raw := by
  constructor
  · intro same
    unfold validate at same
    split at same
    · exact congrArg Subtype.val (Option.some.inj same).symm
    · cases same
  · intro same
    subst raw
    simp [validate, (validateBool_eq_true checked.val).mpr checked.property]

theorem validate_none (raw : Raw) : validate raw = none ↔ ¬ Valid raw := by
  simp [validate, validateBool_eq_true]

abbrev Node (presentation : Checked) := Fin presentation.val.rows.length

instance nodeEnumeration (presentation : Checked) : Enumeration (Node presentation) :=
  inferInstanceAs (Enumeration (Fin _))

instance nodeDecidableEq (presentation : Checked) : DecidableEq (Node presentation) :=
  inferInstanceAs (DecidableEq (Fin _))

def root (presentation : Checked) : Node presentation :=
  ⟨presentation.val.root, presentation.property.1⟩

def row (presentation : Checked) (parent : Node presentation) : List Nat :=
  presentation.val.rows[parent.val]

def edge (presentation : Checked) (parent child : Node presentation) : Prop :=
  child.val ∈ row presentation parent

instance edgeDecidable (presentation : Checked) : DecidableRel (edge presentation) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List Nat)))

def material (presentation : Checked) : HSet :=
  HSet.decorate (edge presentation) (root presentation)

def equality (first second : Checked) : Bool :=
  Finite.equivalent (edge first) (edge second) (root first) (root second)

theorem equality_eq_true (first second : Checked) :
    equality first second = true ↔ material first = material second :=
  Finite.equivalent_material_kernel _ _ _ _

def membership (child parent : Checked) : Bool :=
  decide (∃ node : Node parent, edge parent (root parent) node ∧
    Finite.equivalent (edge child) (edge parent) (root child) node = true)

theorem membership_eq_true (child parent : Checked) :
    membership child parent = true ↔ material child ∈ material parent := by
  simp only [membership, decide_eq_true_eq, Finite.equivalent_material_kernel]
  change (∃ node, edge parent (root parent) node ∧
    HSet.decorate (edge child) (root child) = HSet.decorate (edge parent) node) ↔
      HSet.decorate (edge child) (root child) ∈ HSet.decorate (edge parent) (root parent)
  simpa only [eq_comm] using (HSet.mem_decorate
    (r := edge parent) (a := root parent) (y := HSet.decorate (edge child) (root child))).symm

/-- An occurrence is a position in an authored successor row. Its
identity is deliberately separate from its material target. -/
abbrev Occurrence (presentation : Checked) (parent : Node presentation) :=
  Fin (row presentation parent).length

def occurrenceTarget (presentation : Checked) (parent : Node presentation)
    (occurrence : Occurrence presentation parent) : Node presentation :=
  ⟨(row presentation parent)[occurrence.val], presentation.property.2 _
    (List.getElem_mem parent.isLt) _ (List.getElem_mem occurrence.isLt)⟩

def childSupport (presentation : Checked) : List (Node presentation) :=
  elements.filter (fun child => decide (edge presentation (root presentation) child))

theorem occurrence_edge (presentation : Checked) (parent : Node presentation)
    (occurrence : Occurrence presentation parent) :
    edge presentation parent (occurrenceTarget presentation parent occurrence) :=
  List.getElem_mem occurrence.isLt

theorem edge_iff_occurrence (presentation : Checked) (parent child : Node presentation) :
    edge presentation parent child ↔
      ∃ occurrence : Occurrence presentation parent,
        occurrenceTarget presentation parent occurrence = child := by
  constructor
  · intro available
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp available
    exact ⟨⟨index, bound⟩, Fin.ext same⟩
  · rintro ⟨occurrence, rfl⟩
    exact occurrence_edge presentation parent occurrence

namespace Controls

def empty : Checked := ⟨⟨0, [[]]⟩, by decide⟩
def loop : Checked := ⟨⟨0, [[0]]⟩, by decide⟩
def twoCycle : Checked := ⟨⟨0, [[1], [0]]⟩, by decide⟩
def chain : Checked := ⟨⟨0, [[1], []]⟩, by decide⟩
def duplicate : Checked := ⟨⟨0, [[1, 1], []]⟩, by decide⟩
def twoEmptyTargets : Checked := ⟨⟨0, [[1, 2], [], []]⟩, by decide⟩
def wrongRoot : Raw := ⟨1, [[]]⟩
def wrongEndpoint : Raw := ⟨0, [[1]]⟩

theorem malformed_root_rejected : validate wrongRoot = none := by decide +kernel
theorem malformed_endpoint_rejected : validate wrongEndpoint = none := by decide +kernel

theorem loop_twoCycle_equal : equality loop twoCycle = true := by decide +kernel
theorem loop_empty_distinct : equality loop empty = false := by decide +kernel
theorem chain_empty_distinct : equality chain empty = false := by decide +kernel
theorem repeated_members_same_material : equality duplicate chain = true := by decide +kernel

theorem distinct_empty_targets_same_material : equality twoEmptyTargets chain = true := by decide +kernel

theorem repeated_slots_do_not_add_adjacency_children : (childSupport duplicate).length = 1 := by decide +kernel

theorem distinct_target_nodes_count_separately : (childSupport twoEmptyTargets).length = 2 := by decide +kernel

theorem child_count_does_not_descend :
    ¬ ∃ consumer : HSet → Nat,
      ∀ presentation : Checked, consumer (material presentation) = (childSupport presentation).length := by
  rintro ⟨consumer, computes⟩
  have same := congrArg consumer ((equality_eq_true twoEmptyTargets chain).mp
    distinct_empty_targets_same_material)
  have first : consumer (material twoEmptyTargets) = 2 := computes twoEmptyTargets
  have second : consumer (material chain) = 1 := computes chain
  exact Nat.zero_ne_one (Nat.succ.inj (first.symm.trans (same.trans second)).symm)

theorem loop_self_member : membership loop loop = true := by decide +kernel
theorem empty_in_chain : membership empty chain = true := by decide +kernel
theorem chain_not_in_empty : membership chain empty = false := by decide +kernel

theorem repeated_occurrences_distinct :
    (⟨0, by decide⟩ : Occurrence duplicate (root duplicate)) ≠ ⟨1, by decide⟩ := by decide

theorem repeated_occurrence_targets_agree :
    occurrenceTarget duplicate (root duplicate) ⟨0, by decide⟩ =
      occurrenceTarget duplicate (root duplicate) ⟨1, by decide⟩ := rfl

theorem occurrence_consumer_does_not_descend :
    ¬ ∃ consumer : HSet → Nat,
      ∀ occurrence : Occurrence duplicate (root duplicate),
        consumer (HSet.decorate (edge duplicate)
          (occurrenceTarget duplicate (root duplicate) occurrence)) = occurrence.val := by
  rintro ⟨consumer, computes⟩
  have first := computes ⟨0, by decide⟩
  have second := computes ⟨1, by decide⟩
  rw [← repeated_occurrence_targets_agree] at second
  exact Nat.zero_ne_one (first.symm.trans second)

end Controls

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Presentations
