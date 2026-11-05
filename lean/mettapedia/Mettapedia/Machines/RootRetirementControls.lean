import Mettapedia.Machines.RootRetirementLedger

/-!
# Root-retirement separating controls

The concrete graph has a shared two-node cycle. Equal old mark bitmaps and
equal retired-root bitmaps can have different current liveness: the missing
information is overlap with other owners. An exact support ledger handles
that overlap without counting infinitely many paths around the cycle.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RootRetirementLedger.Controls

open ResourceOwnership

abbrev graph := ResourceOwnership.Examples.cyclicHeap

def first : Roots Bool (Fin 3) := {(false, 1)}
def both : Roots Bool (Fin 3) := {(false, 1), (true, 1)}

theorem roots_valid (roots : Roots Bool (Fin 3)) : ValidRoots graph roots := by
  intro pair _
  exact Finset.mem_univ pair.2

theorem first_census : census graph first = {1, 2} := by decide +kernel
theorem both_census : census graph both = {1, 2} := by decide +kernel
theorem retired_first_census : census graph (first \ first) = (∅ : Finset (Fin 3)) := by
  decide +kernel
theorem retired_both_census : census graph (both \ first) = {1, 2} := by decide +kernel

/-- Subtracting a retired provider's reachable bitmap from the old union
would erase a cycle that is still independently rooted. No function of just
those two bitmaps can always recover the exact current bitmap. -/
theorem old_and_retired_bitmaps_insufficient :
    ¬ ∃ update : Finset (Fin 3) → Finset (Fin 3) → Finset (Fin 3),
      ∀ roots removed : Roots Bool (Fin 3), removed ⊆ roots →
        update (census graph roots) (census graph removed) = census graph (roots \ removed) := by
  rintro ⟨update, correct⟩
  have only := correct first first (Finset.Subset.refl _)
  have shared := correct both first (by decide)
  rw [first_census, retired_first_census] at only
  rw [both_census, first_census, retired_both_census] at shared
  have impossible : (∅ : Finset (Fin 3)) = {1, 2} := only.symm.trans shared
  have notEmpty : (∅ : Finset (Fin 3)) ≠ {1, 2} := by decide
  exact notEmpty impossible

theorem final_retirement_clears_count :
    (retire (Heap.begin graph first) first).count 1 = 0 ∧
      (retire (Heap.begin graph first) first).count 2 = 0 := by decide +kernel

theorem shared_cycle_keeps_one_contributor :
    (Heap.begin graph both).count 1 = 2 ∧
      (retire (Heap.begin graph both) first).count 1 = 1 ∧
      (retire (Heap.begin graph both) first).count 2 = 1 := by decide +kernel

theorem repeated_retirement_keeps_sibling :
    (retireMany (Heap.begin graph both) [first, first]).count 1 = 1 := by decide +kernel

theorem retiring_both_clears_cycle :
    (retireMany (Heap.begin graph both) [first, {(true, 1)}]).count 1 = 0 ∧
      (retireMany (Heap.begin graph both) [first, {(true, 1)}]).count 2 = 0 := by decide +kernel

/-- The independent inductive semantics, not only the ledger, retains the cycle. -/
theorem sibling_retains_actual_liveness : Live graph (both \ first) 2 := by
  apply (Heap.retired_positive_iff_live graph both first (roots_valid both) 2).mp
  decide +kernel

theorem current_lookup_preserves_sibling_and_reclaims_final :
    Heap.lookup graph (retire (Heap.begin graph both) first) 2 = graph.lookup 2 ∧
      Heap.lookup graph (retire (Heap.begin graph first) first) 2 = none := by decide +kernel

theorem stale_positive_requires_refresh :
    decideRelease 0 (reuseAfterRetirement true) = .refresh := rfl

theorem current_positive_still_detects_broken_count :
    decideRelease 0 (some true) = .inconsistent := rfl

theorem current_negative_allows_release :
    decideRelease 0 (some false) = .release := rfl

theorem counted_holder_is_kept : decideRelease 1 none = .keep := rfl

/-- Root addition is outside the deletion-only rule: a prior negative mark
does not remain sound when a new provider protects the cycle. -/
theorem root_addition_invalidates_old_negative :
    (2 : Fin 3) ∉ census graph (∅ : Roots Bool (Fin 3)) ∧
      2 ∈ census graph first := by decide +kernel

def expandedCell (address : Fin 3) : Cell (Fin 3) Nat :=
  { ResourceOwnership.Examples.cyclicCell address with
    references := if address = 1 then {0, 2}
      else (ResourceOwnership.Examples.cyclicCell address).references }

def expandedGraph : ResourceOwnership.Heap (Fin 3) Nat where
  lookup address := some (expandedCell address)
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ child _ := Finset.mem_univ child

/-- Keeping root identities unchanged does not validate a cached support
after outgoing edges change. -/
theorem graph_write_invalidates_old_negative :
    (0 : Fin 3) ∉ census graph first ∧ 0 ∈ census expandedGraph first := by decide +kernel

end Mettapedia.Machines.RootRetirementLedger.Controls
