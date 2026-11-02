import Mettapedia.Machines.NamedShapeGraph
import Mettapedia.GSLT.Dynamics.StoreReachability

/-!
# Holders and finite acyclic reference collection across stores

Roots and outgoing slots are counted with multiplicity. A name may include
a store tag; counting does not stop at a store boundary. Repeated zero-count
pruning preserves rooted reachability and reaches a fixed point after at most
the initial number of allocated names. With strictly decreasing edge ranks,
the fixed point is exactly the reachable names. Without that condition an
unrooted cycle survives, as the negative control demonstrates.

This specifies a sequential census-and-prune algorithm, not the runtime's
incremental counter maintenance, root enumeration, or concurrency protocol.
Reusing a reclaimed name requires an independent anti-stale-reference policy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NamedStoreHolders

open Mettapedia.GSLT.Dynamics.StoreReachability

variable {Name : Type} [DecidableEq Name]

def count (roots : List Name) (refs : Name → List Name) (allocated : Finset Name)
    (name : Name) : Nat := roots.count name + ∑ parent ∈ allocated, (refs parent).count name

theorem count_positive (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (name : Name) :
    0 < count roots refs allocated name ↔
      name ∈ roots ∨ ∃ parent ∈ allocated, name ∈ refs parent := by
  simp [count, Finset.sum_pos_iff, List.count_pos_iff]

/-- Multiplicity is retained even when several holders name the same object. -/
theorem root_count_append (a b : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (name : Name) :
    count (a ++ b) refs allocated name = count a refs allocated name + b.count name := by
  simp [count, List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem store_count_union (roots : List Name) (refs : Name → List Name)
    (a b : Finset Name) (separate : Disjoint a b) (name : Name) :
    count roots refs (a ∪ b) name = roots.count name +
      (∑ parent ∈ a, (refs parent).count name) +
      ∑ parent ∈ b, (refs parent).count name := by
  simp [count, Finset.sum_union separate, Nat.add_assoc]

def graph (roots : List Name) (refs : Name → List Name) (allocated : Finset Name) : Store Name where
  root n := n ∈ roots
  pointsTo p c := p ∈ allocated ∧ c ∈ refs p

abbrev Closed (roots : List Name) (refs : Name → List Name) (allocated : Finset Name) : Prop :=
  (∀ n ∈ roots, n ∈ allocated) ∧ ∀ p ∈ allocated, ∀ c ∈ refs p, c ∈ allocated

omit [DecidableEq Name] in
theorem reach_allocated (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (closed : Closed roots refs allocated)
    (n : Name) (live : Reach (graph roots refs allocated) n) : n ∈ allocated := by
  induction live with
  | root present => exact closed.1 _ present
  | step _ edge _ => exact closed.2 _ edge.1 _ edge.2

theorem live_positive (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (n : Name) (live : Reach (graph roots refs allocated) n) :
    0 < count roots refs allocated n := by
  apply (count_positive roots refs allocated n).mpr
  cases live with
  | root present => exact Or.inl present
  | @step p c _ edge => exact Or.inr ⟨p, edge⟩

def prune (roots : List Name) (refs : Name → List Name) (allocated : Finset Name) : Finset Name :=
  allocated.filter (fun n => 0 < count roots refs allocated n)

theorem prune_subset (roots : List Name) (refs : Name → List Name) (allocated : Finset Name) :
    prune roots refs allocated ⊆ allocated := Finset.filter_subset _ _

theorem prune_closed (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (closed : Closed roots refs allocated) :
    Closed roots refs (prune roots refs allocated) := by
  constructor
  · intro n hn
    exact Finset.mem_filter.mpr ⟨closed.1 n hn,
      (count_positive roots refs allocated n).mpr (Or.inl hn)⟩
  · intro p hp c hc
    have old := prune_subset roots refs allocated hp
    exact Finset.mem_filter.mpr ⟨closed.2 p old c hc,
      (count_positive roots refs allocated c).mpr (Or.inr ⟨p, old, hc⟩)⟩

theorem prune_preserves_reach (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (n : Name) :
    Reach (graph roots refs (prune roots refs allocated)) n ↔
      Reach (graph roots refs allocated) n := by
  constructor
  · intro live
    induction live with
    | root present => exact .root present
    | step _ edge ih => exact .step ih ⟨prune_subset roots refs allocated edge.1, edge.2⟩
  · intro live
    induction live with
    | root present => exact .root present
    | @step p c parentLive edge ih =>
        exact .step ih ⟨Finset.mem_filter.mpr
          ⟨edge.1, live_positive roots refs allocated p parentLive⟩, edge.2⟩

def sweep (roots : List Name) (refs : Name → List Name) : Nat → Finset Name → Finset Name
  | 0, allocated => allocated
  | steps + 1, allocated => sweep roots refs steps (prune roots refs allocated)

theorem sweep_subset (roots : List Name) (refs : Name → List Name)
    (steps : Nat) (allocated : Finset Name) : sweep roots refs steps allocated ⊆ allocated := by
  induction steps generalizing allocated with
  | zero => exact Finset.Subset.refl _
  | succ steps ih => exact (ih _).trans (prune_subset roots refs allocated)

theorem sweep_closed (roots : List Name) (refs : Name → List Name)
    (steps : Nat) (allocated : Finset Name) (closed : Closed roots refs allocated) :
    Closed roots refs (sweep roots refs steps allocated) := by
  induction steps generalizing allocated with
  | zero => exact closed
  | succ steps ih => exact ih _ (prune_closed roots refs allocated closed)

theorem sweep_preserves_reach (roots : List Name) (refs : Name → List Name)
    (steps : Nat) (allocated : Finset Name) (closed : Closed roots refs allocated) (n : Name) :
    Reach (graph roots refs (sweep roots refs steps allocated)) n ↔
      Reach (graph roots refs allocated) n := by
  induction steps generalizing allocated with
  | zero => rfl
  | succ steps ih =>
      exact (ih _ (prune_closed roots refs allocated closed)).trans
        (prune_preserves_reach roots refs allocated n)

theorem sweep_of_fixed (roots : List Name) (refs : Name → List Name)
    (steps : Nat) (allocated : Finset Name) (fixed : prune roots refs allocated = allocated) :
    sweep roots refs steps allocated = allocated := by
  induction steps <;> simp_all [sweep]

/-- Strict progress is measured by allocated names, not by elapsed time. -/
theorem sweep_stabilizes (roots : List Name) (refs : Name → List Name)
    (steps : Nat) (allocated : Finset Name) (enough : allocated.card ≤ steps) :
    prune roots refs (sweep roots refs steps allocated) = sweep roots refs steps allocated := by
  induction steps generalizing allocated with
  | zero =>
      have empty : allocated = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [empty, sweep, prune]
  | succ steps ih =>
      by_cases fixed : prune roots refs allocated = allocated
      · rw [sweep_of_fixed roots refs (steps + 1) allocated fixed]
        exact fixed
      · apply ih
        have smaller : (prune roots refs allocated).card < allocated.card :=
          Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨prune_subset roots refs allocated, fixed⟩)
        omega

/-- At a fixed point every remaining nonroot has a remaining predecessor.
Strictly decreasing ranks exclude an infinite backwards chain. -/
theorem fixed_point_live (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (rank : Name → Nat) (bound : Nat)
    (bounded : ∀ n ∈ allocated, rank n ≤ bound)
    (decreases : ∀ p ∈ allocated, ∀ c ∈ refs p, rank c < rank p)
    (fixed : prune roots refs allocated = allocated) (n : Name) (present : n ∈ allocated) :
    Reach (graph roots refs allocated) n := by
  have positive : ∀ x ∈ allocated, 0 < count roots refs allocated x := by
    intro x hx
    rw [← fixed] at hx
    exact (Finset.mem_filter.mp hx).2
  generalize hm : bound - rank n = measure
  induction measure using Nat.strong_induction_on generalizing n with
  | h measure ih =>
      rcases (count_positive roots refs allocated n).mp (positive n present) with root | incoming
      · exact .root root
      · obtain ⟨parent, parentPresent, edge⟩ := incoming
        have upper := bounded parent parentPresent
        have lower := decreases parent parentPresent n edge
        exact .step (ih (bound - rank parent) (by omega) parent parentPresent rfl)
          ⟨parentPresent, edge⟩

/-- Complete acyclic collection: no live name is lost and no dead name remains. -/
theorem sweep_exact (roots : List Name) (refs : Name → List Name)
    (allocated : Finset Name) (closed : Closed roots refs allocated)
    (rank : Name → Nat) (bound : Nat) (bounded : ∀ n ∈ allocated, rank n ≤ bound)
    (decreases : ∀ p ∈ allocated, ∀ c ∈ refs p, rank c < rank p) (n : Name) :
    n ∈ sweep roots refs allocated.card allocated ↔ Reach (graph roots refs allocated) n := by
  constructor
  · intro present
    apply (sweep_preserves_reach roots refs allocated.card allocated closed n).mp
    exact fixed_point_live roots refs _ rank bound
      (fun x hx => bounded x (sweep_subset roots refs _ allocated hx))
      (fun p hp c hc => decreases p (sweep_subset roots refs _ allocated hp) c hc)
      (sweep_stabilizes roots refs allocated.card allocated (le_refl _)) n present
  · intro live
    exact reach_allocated roots refs _ (sweep_closed roots refs _ allocated closed) n
      ((sweep_preserves_reach roots refs _ allocated closed n).mpr live)

namespace Controls

abbrev N := Bool × Nat
def refs : N → List N
  | (true, 1) => [(false, 0), (false, 0)]
  | _ => []
def allocated : Finset N := {(false, 0), (true, 1), (false, 9)}

example : count [(true, 1)] refs allocated (false, 0) = 2 := by decide
example : sweep [(true, 1)] refs 3 allocated = {(false, 0), (true, 1)} := by decide
example : sweep [] refs 3 allocated = ∅ := by decide

/-- Dropping the cross-store slots falsely frees a reachable child. -/
theorem omitted_store_edges_lose_child :
    (false, 0) ∈ sweep [(true, 1)] refs 3 allocated ∧
    (false, 0) ∉ sweep [(true, 1)] (fun _ => []) 3 allocated := by decide

def cycleRefs (n : Bool) : List Bool := [!n]

theorem unrooted_cycle_survives (steps : Nat) :
    sweep [] cycleRefs steps {false, true} = {false, true} :=
  sweep_of_fixed [] cycleRefs steps {false, true} (by decide)

theorem unrooted_cycle_is_dead (n : Bool) : ¬ Reach (graph [] cycleRefs {false, true}) n := by
  intro live
  induction live with
  | root present => exact List.not_mem_nil present
  | step _ _ ih => exact ih

end Controls

#print axioms sweep_stabilizes
#print axioms sweep_exact
#print axioms Controls.unrooted_cycle_survives
#print axioms Controls.omitted_store_edges_lose_child

end Mettapedia.Machines.NamedStoreHolders
