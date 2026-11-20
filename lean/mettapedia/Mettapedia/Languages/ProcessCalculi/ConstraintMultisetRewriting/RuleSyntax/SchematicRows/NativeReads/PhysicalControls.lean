import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SourceStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls

/-! # Actual physical cells, retained captures and distinct equal occurrences -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.PhysicalControls

open Mettapedia.Logic.LP
open Mettapedia.Machines.ResourceOwnership
open RuleSyntax.Controls (atoms)

abbrev RowTerms := OneFrame.Terms (Term atoms)

def datum : Row RowTerms PUnit.unit := .schematic (Closure.captured (.var 0))

def source : State RowTerms (Fin 2) := ⟨PUnit.unit, [], Finset.univ, fun _ => datum⟩

def heap : Heap (Fin 2) (Row RowTerms PUnit.unit) where
  lookup _ := some ⟨datum, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

def pins : Roots Nat (Fin 2) := {(0, 0), (1, 1)}

theorem physically_represented : SourceStorage.RepresentsOn source [0, 1] heap id := by
  intro occurrence _
  exact ⟨⟨datum, ∅, 8⟩, rfl, rfl⟩

theorem actual_retention_check : RequestBorrow.retentionCheck heap pins [0, 1] = true := by
  apply (RequestBorrow.retentionCheck_iff heap pins [0, 1]).mpr
  refine ⟨fun _ _ => Finset.mem_univ _, ?_⟩
  intro start member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact live_of_root heap pins (owner := 0) (by decide) (by simp [heap])
  · exact live_of_root heap pins (owner := 1) (by decide) (by simp [heap])

theorem full_captured_row_survives_collection (occurrence : Fin 2) :
    SourceStorage.load (collect heap pins) id occurrence = some datum := by
  have listed : occurrence ∈ ([0, 1] : List (Fin 2)) := by fin_cases occurrence <;> decide
  exact SourceStorage.retained_load_exact source [0, 1] heap id physically_represented
    pins actual_retention_check occurrence listed

theorem no_pin_means_no_physical_read (occurrence : Fin 2) :
    (collect heap (∅ : Roots Nat (Fin 2))).lookup occurrence = none :=
  lookup_collect_of_not_live heap ∅ (not_live_empty heap occurrence)

theorem one_clone_can_retain_its_equal_row :
    (collect heap ({(1, 1)} : Roots Nat (Fin 2))).lookup 1 = heap.lookup 1 :=
  lookup_collect_of_live heap {(1, 1)}
    (live_of_root heap {(1, 1)} (owner := 1) (by simp) (by simp [heap]))

theorem equal_payloads_do_not_prove_equal_addresses :
    heap.lookup 0 = heap.lookup 1 ∧ (0 : Fin 2) ≠ 1 := ⟨rfl, by decide⟩

theorem immutable_payload_may_be_shared_by_occurrences :
    SourceStorage.RepresentsOn source [0, 1] heap (fun _ => 0) := by
  intro occurrence _
  exact ⟨⟨datum, ∅, 8⟩, rfl, rfl⟩

#print axioms actual_retention_check
#print axioms full_captured_row_survives_collection
#print axioms no_pin_means_no_physical_read

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.PhysicalControls
