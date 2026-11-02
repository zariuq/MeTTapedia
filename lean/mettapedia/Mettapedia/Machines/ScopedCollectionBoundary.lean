import Mettapedia.Machines.NestedSafePoints

/-!
# Collection of one allocation universe

A worker may execute against a shared Space while allocating in another
universe. An offer selects only the current allocation universe, at a
quiescent boundary protected against foreign mutation. Observers of that
universe, including foreign readers, must appear in its activation roots.

This extends the abstract collector model with universe selection. It does
not prove that native C observers register every root or acquire a guard.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCollectionBoundary

open NestedSafePoints

variable {U α : Type} [DecidableEq U] [DecidableEq α]

/-- A refused offer leaves every universe intact; an admitted offer filters
only the current allocation universe through the collector's root closure. -/
def offer (c : Collector α) (active : Option U) (quiescent guarded : Bool)
    (target : U) (activations : U → List (Activation α))
    (heaps : U → Finset α) : U → Finset α :=
  if active = some target ∧ quiescent = true ∧ guarded = true then
    Function.update heaps target (collect c (activations target) (heaps target))
  else heaps

theorem other_universe_unchanged (c : Collector α) (active : Option U)
    (quiescent guarded : Bool) (target other : U)
    (activations : U → List (Activation α)) (heaps : U → Finset α)
    (different : other ≠ target) :
    offer c active quiescent guarded target activations heaps other = heaps other := by
  simp only [offer]
  split_ifs <;> simp [Function.update_of_ne different]

theorem refused_unchanged (c : Collector α) (active : Option U)
    (quiescent guarded : Bool) (target : U)
    (activations : U → List (Activation α)) (heaps : U → Finset α)
    (refused : ¬ (active = some target ∧ quiescent = true ∧ guarded = true)) :
    offer c active quiescent guarded target activations heaps = heaps := by
  simp [offer, refused]

/-- Clean local and foreign observers survive an admitted collection in the
selected universe; numeric identity alone never selects a different heap. -/
theorem admitted_keeps_observers (c : Collector α) (target : U)
    (activations : U → List (Activation α)) (heaps : U → Finset α)
    (clean : ∀ act ∈ activations target, act.Clean)
    {act : Activation α} (present : act ∈ activations target) :
    act.holds ∩ heaps target ⊆
      offer c (some target) true true target activations heaps target := by
  simpa [offer] using collect_keeps_held c (activations target) (heaps target) clean present

private def sampleStacks : Bool → List (Activation ℕ)
  | false => [⟨{0}, ∅⟩, ⟨{2}, ∅⟩]
  | true => [⟨{7}, ∅⟩]

private def sampleHeaps : Bool → Finset ℕ
  | false => {0, 1, 2}
  | true => {0, 7}

-- Private garbage disappears while the independently listed reader survives.
example : offer rootsOnly (some false) true true false sampleStacks sampleHeaps false =
    {0, 2} := by decide

-- Shared storage is unchanged even when its allocation identities overlap.
example : offer rootsOnly (some false) true true false sampleStacks sampleHeaps true =
    {0, 7} := by decide

-- Neither the wrong allocation owner nor a missing physical guard admits work.
example : offer rootsOnly (some true) true true false sampleStacks sampleHeaps false =
    {0, 1, 2} := by decide

example : offer rootsOnly (some false) true false false sampleStacks sampleHeaps false =
    {0, 1, 2} := by decide

-- A hidden foreign observer is insufficient: it loses its unlisted object.
example : offer rootsOnly (some false) true true false
    (fun _ => [⟨{0}, {2}⟩]) sampleHeaps false = {0} := by decide

end Mettapedia.Machines.ScopedCollectionBoundary
