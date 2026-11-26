import Mettapedia.Machines.NameSupplies.Shares
import Mettapedia.Machines.NameSupplies.Pedigree
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Transferring a supply and bounding its position

Handover moves an occupied lease to a free owner. The supply itself, including
its position and draw state, is preserved. For structural naming, even one
unbounded branch exceeds every fixed bit width. The share tree instead gives a
size bound in terms of the depth of open fork decisions. This bound concerns the
share coordinate. The counter and the number of outstanding forks are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

section Handover

variable {Worker S : Type*} [DecidableEq Worker]

abbrev Leases (Worker S : Type*) := Worker → Option S

def handover (leases : Leases Worker S) (source target : Worker) : Option (Leases Worker S) :=
  match leases source, leases target with
  | some supply, none => some (Function.update (Function.update leases source none) target (some supply))
  | _, _ => none

/-- Moving an occupied lease to a free worker preserves the supplies that can
draw, and removes the old worker's ability to draw from the moved supply. -/
theorem handover_preserves (leases : Leases Worker S) (source target : Worker)
    (supply : S) (held : leases source = some supply) (vacant : leases target = none) :
    ∃ next, handover leases source target = some next ∧ next source = none ∧
      next target = some supply ∧
      ∀ worker, next (Equiv.swap source target worker) = leases worker := by
  have distinct : source ≠ target := by
    intro same
    subst target
    simp [held] at vacant
  let next := Function.update (Function.update leases source none) target (some supply)
  have atSource : next source = none := by simp [next, distinct]
  have atTarget : next target = some supply := by simp [next]
  refine ⟨next, by simp [handover, held, vacant, next], atSource, atTarget, fun worker => ?_⟩
  by_cases atFirst : worker = source
  · subst worker
    rw [Equiv.swap_apply_left, atTarget, held]
  · by_cases atSecond : worker = target
    · subst worker
      rw [Equiv.swap_apply_right, atSource, vacant]
    · rw [Equiv.swap_apply_of_ne_of_ne atFirst atSecond]
      simp [next, atFirst, atSecond]

theorem handover_busy (leases : Leases Worker S) (source target : Worker)
    (supply : S) (held : leases target = some supply) :
    handover leases source target = none := by
  cases h : leases source <;> simp [handover, h, held]

end Handover

/-- Distinct children of an actual pedigree draw at distinct positions. -/
theorem pedigree_children_distinct (parent : Pedigree) {i j : ℕ} (different : i ≠ j) :
    (Pedigree.draw (parent.child i)).1 ≠ (Pedigree.draw (parent.child j)).1 := by
  intro equal
  have starts : (parent.children + i) :: parent.position =
      (parent.children + j) :: parent.position := congrArg Prod.fst equal
  exact different (Nat.add_left_cancel (List.cons.inj starts).1)

/-- The actual sequence of kept children at depths zero through the
vocabulary size exceeds a fixed-width representation. -/
theorem bounded_positions_collide (width : ℕ) (name : List ℕ → Fin (2 ^ width)) :
    let position := fun k => (kept pedigreeDiscipline Pedigree.root k).position
    ∃ i j : Fin (2 ^ width + 1), position i ≠ position j ∧ name (position i) = name (position j) := by
  dsimp only
  obtain ⟨i, j, distinct, same⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (2 ^ width + 1) =>
      name (kept pedigreeDiscipline Pedigree.root k).position) (by simp)
  refine ⟨i, j, ?_, same⟩
  intro equal
  exact distinct (Fin.ext ((pedigree_kept_depth i).symm.trans
    ((congrArg List.length equal).trans (pedigree_kept_depth j))))

private theorem split_size (share : Share) :
    (share.split.1).size ≤ share.size + 2 ∧ (share.split.2).size ≤ share.size + 2 := by
  induction share with
  | none => decide
  | all => decide
  | node left right ihLeft ihRight =>
      cases left <;> cases right <;> simp only [Share.split, Share.size] at *
      all_goals constructor <;> omega

/-- The share along an outstanding chain of fork decisions. Joining closed
branches discards their decisions by the split/join law. -/
def shareAt : Share → List Bool → Share
  | share, [] => share
  | share, false :: rest => shareAt share.split.1 rest
  | share, true :: rest => shareAt share.split.2 rest

theorem shareAt_size (share : Share) (path : List Bool) :
    (shareAt share path).size ≤ share.size + 2 * path.length := by
  induction path generalizing share with
  | nil => simp [shareAt]
  | cons move rest ih =>
      obtain ⟨left, right⟩ := split_size share
      cases move
      · have next := ih share.split.1
        simp only [shareAt, List.length_cons]
        omega
      · have next := ih share.split.2
        simp only [shareAt, List.length_cons]
        omega

#print axioms handover_preserves
#print axioms handover_busy
#print axioms pedigree_children_distinct
#print axioms bounded_positions_collide
#print axioms shareAt_size

end Mettapedia.Machines.NameSupplies
