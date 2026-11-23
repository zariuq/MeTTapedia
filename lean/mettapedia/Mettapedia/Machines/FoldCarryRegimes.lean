import Mettapedia.Machines.ResourceOwnershipOptimality
import Mettapedia.Machines.PromotionCopyWork
import Mathlib.Order.Interval.Finset.Nat

/-!
# Fold carries can share without accumulating

The observable state of a carry is the reachable graph, including every
export and retained observer, not the arena that happens to contain its root.
What distinguishes the strategies is the *overlap* of successive reachable
sets. Independent carries can leave all of the old region dead. A growing
prefix need never die during the fold. A sliding carry shares most of its
predecessor and still makes part of it dead at every step.

The weighted accounting uses stable cell identities. Charge one materialization
per newly needed cell, not one per path to it. Scratch space, discovery work,
the cost of individual retirement, and layout constraints are not in that
charge. The model does not give an unconditional lower bound on arena count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.FoldCarryRegimes

section ReadPaths

open ResourceOwnership ResourceOwnership.Optimality

variable {Address Value Owner : Type} [DecidableEq Address]

/-- There exists an observationally equivalent graph in which an entire
region has been retired iff none of its cells is still in the support of
an observed path. An independent staged result can therefore survive a
reset of the old carry. An algorithm must still discover that independence;
graph aliases through a child or another root count. -/
theorem can_retire_whole_region_iff (graph : Heap Address Value)
    (observed : Roots Owner Address) (retired : Finset Address) :
    (∃ remaining : Heap Address Value, SameRootPaths graph remaining observed ∧
      Disjoint remaining.allocated retired) ↔ Disjoint (footprint graph observed) retired := by
  constructor
  · rintro ⟨remaining, same, disjoint⟩
    exact disjoint.mono_left (footprint_subset_candidate graph remaining observed same)
  · intro disjoint
    refine ⟨collect graph observed, collect_same_root_paths graph observed, ?_⟩
    rwa [allocated_collect]

end ReadPaths

open PromotionCopyWork (copyWeight semispaceWork distinctSurvivors promotionWork)

variable {Address : Type*} [DecidableEq Address]

/-- The result of retiring the outgoing part and materializing the missing
part. Returning a new root need not replicate the shared subgraph. -/
def retainAndFill (old next : Finset Address) : Finset Address := (old ∩ next) ∪ (next \ old)

theorem retainAndFill_exact (old next : Finset Address) : retainAndFill old next = next := by
  ext a
  simp only [retainAndFill, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- Any plan that keeps only old cells and allocates enough to materialize
the next live set must allocate at least the newcomers. -/
theorem newcomer_work_le (charge : Address → Nat) (old next made : Finset Address)
    (enough : next ⊆ old ∪ made) : copyWeight charge (next \ old) ≤ copyWeight charge made := by
  unfold copyWeight
  apply Finset.sum_le_sum_of_subset
  intro a ha
  obtain ⟨needed, fresh⟩ := Finset.mem_sdiff.mp ha
  exact (Finset.mem_union.mp (enough needed)).resolve_left fresh

/-- Both carries can still be needed while the next one is staged. With
identity-preserving storage, the joint support is the old footprint plus
the newcomers, not the sum of the two footprints. -/
theorem simultaneous_charge (charge : Address → Nat) (old next : Finset Address) :
    copyWeight charge (old ∪ next) = copyWeight charge old + copyWeight charge (next \ old) := by
  have split : old ∪ next = old ∪ (next \ old) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [split]
  exact Finset.sum_union (Finset.disjoint_left.mpr (fun _ mem new => (Finset.mem_sdiff.mp new).2 mem))

def selectiveWork (charge : Address → Nat) (old : Finset Address) : List (Finset Address) → Nat
  | [] => 0
  | next :: rest => copyWeight charge (next \ old) + selectiveWork charge next rest

def repeatedWork (charge : Address → Nat) (old : Finset Address) : List (Finset Address) → Nat
  | [] => 0
  | next :: rest => copyWeight charge (next ∩ old) + repeatedWork charge next rest

/-- Evacuation pays for the overlap again, including when the overall live
set does not grow and the input is not retained as a whole. -/
theorem evacuation_eq_selective_plus_overlap (charge : Address → Nat) (old : Finset Address)
    (stages : List (Finset Address)) :
    semispaceWork charge stages = selectiveWork charge old stages + repeatedWork charge old stages := by
  induction stages generalizing old with
  | nil => rfl
  | cons next rest ih =>
      have complete : (next \ old) ∪ (next ∩ old) = next := by
        ext a
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have separated : Disjoint (next \ old) (next ∩ old) :=
        Finset.disjoint_left.mpr (fun _ fresh shared => (Finset.mem_sdiff.mp fresh).2 (Finset.mem_inter.mp shared).2)
      have split : copyWeight charge next = copyWeight charge (next \ old) + copyWeight charge (next ∩ old) := by
        unfold copyWeight
        calc
          ∑ a ∈ next, charge a = ∑ a ∈ (next \ old) ∪ (next ∩ old), charge a := by rw [complete]
          _ = _ := Finset.sum_union separated
      simp only [semispaceWork, selectiveWork, repeatedWork, ih next, split]
      omega

/-- A revived identity was not held by the preceding carry, but was already
resident earlier. Retention can save re-materializing it. -/
def revivedWork (charge : Address → Nat) (old ever : Finset Address) : List (Finset Address) → Nat
  | [] => 0
  | next :: rest => copyWeight charge ((next \ old) ∩ ever) +
      revivedWork charge next (ever ∪ next) rest

/-- The exact price of forgetting early in this model is the work of
revivals. When discarded identities never return, selective retirement
does not consume more materialization work than keeping the whole history. -/
theorem selective_eq_append_only_plus_revivals (charge : Address → Nat)
    (old ever : Finset Address) (stages : List (Finset Address)) (known : old ⊆ ever) :
    selectiveWork charge old stages =
      promotionWork charge ever stages + revivedWork charge old ever stages := by
  induction stages generalizing old ever with
  | nil => rfl
  | cons next rest ih =>
      have split : (next \ ever) ∪ ((next \ old) ∩ ever) = next \ old := by
        ext a
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro (⟨inNext, new⟩ | ⟨noOld, _⟩)
          · exact ⟨inNext, fun inOld => new (known inOld)⟩
          · exact noOld
        · intro h
          by_cases prior : a ∈ ever
          · exact Or.inr ⟨h, prior⟩
          · exact Or.inl ⟨h.1, prior⟩
      have apart : Disjoint (next \ ever) ((next \ old) ∩ ever) :=
        Finset.disjoint_left.mpr (fun _ fresh revived => (Finset.mem_sdiff.mp fresh).2 (Finset.mem_inter.mp revived).2)
      have now : copyWeight charge (next \ old) =
          copyWeight charge (next \ ever) + copyWeight charge ((next \ old) ∩ ever) := by
        unfold copyWeight
        calc
          ∑ a ∈ next \ old, charge a = ∑ a ∈ (next \ ever) ∪ ((next \ old) ∩ ever), charge a := by rw [split]
          _ = _ := Finset.sum_union apart
      simp only [selectiveWork, promotionWork, revivedWork, ih next (ever ∪ next) Finset.subset_union_right, now]
      omega

/-! ## A bounded-live phase with persistent sharing -/

def window (width start : Nat) : Finset Nat := Finset.Ico start (start + width)

theorem window_card (width start : Nat) : (window width start).card = width := by
  simp [window, Nat.card_Ico]

theorem window_new (width start : Nat) (positive : 0 < width) :
    window width (start + 1) \ window width start = {start + width} := by
  ext a
  simp only [window, Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_singleton]
  omega

theorem window_outgoing (width start : Nat) (positive : 0 < width) :
    window width start \ window width (start + 1) = {start} := by
  ext a
  simp only [window, Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_singleton]
  omega

theorem window_union_stretch (width start extra : Nat) (positive : 0 < width) :
    window width start ∪ window (width + extra) (start + 1) = window (width + extra + 1) start := by
  ext a
  simp only [window, Finset.mem_union, Finset.mem_Ico]
  omega

/-- Even during a handoff, retaining both views of a width-`k` moving
window requires only `k+1` distinct cells. -/
theorem window_live_peak (width start : Nat) (positive : 0 < width) :
    (window width start ∪ window width (start + 1)).card = width + 1 := by
  have cover := window_union_stretch width start 0 positive
  simp only [add_zero] at cover
  rw [cover, window_card]

def moving (width start : Nat) : Nat → List (Finset Nat)
  | 0 => []
  | n + 1 => window width (start + 1) :: moving width (start + 1) n

theorem moving_transfer (width start stages : Nat) (positive : 0 < width) :
    selectiveWork (fun _ => 1) (window width start) (moving width start stages) = stages ∧
      semispaceWork (fun _ => 1) (moving width start stages) = width * stages := by
  induction stages generalizing start with
  | zero => simp [moving, selectiveWork, semispaceWork]
  | succ stages ih =>
      obtain ⟨one, all⟩ := ih (start + 1)
      simp [moving, selectiveWork, semispaceWork, copyWeight, window_new width start positive,
        window_card, one, all, Nat.mul_succ, Nat.add_comm]

theorem moving_retained_all (width start stages : Nat) (positive : 0 < width) :
    window width start ∪ distinctSurvivors (moving width start stages) = window (width + stages) start := by
  induction stages generalizing start with
  | zero => simp [moving, distinctSurvivors]
  | succ stages ih =>
      simp only [moving, distinctSurvivors, ih (start + 1)]
      exact window_union_stretch width start stages positive

/-- There is no trichotomy by "scalar / independent / growing". This
family shares, copies only one new cell per handoff, and is bounded live;
without retirement its resident size nevertheless grows every time. -/
theorem moving_copy_and_space (width start stages : Nat) (positive : 0 < width) :
    selectiveWork (fun _ => 1) (window width start) (moving width start stages) = stages ∧
    semispaceWork (fun _ => 1) (moving width start stages) = width * stages ∧
    (window width start ∪ distinctSurvivors (moving width start stages)).card = width + stages ∧
    (∀ suffix ≤ stages, (window width (start + suffix)).card = width) := by
  obtain ⟨selective, copied⟩ := moving_transfer width start stages positive
  exact ⟨selective, copied, by rw [moving_retained_all width start stages positive, window_card],
    fun offset _ => window_card width (start + offset)⟩

namespace Controls

/-- The two roots need not be the same, and the carry need not grow, for
the old and new footprints to overlap. -/
theorem distinct_carries_overlap :
    window 4 0 ≠ window 4 1 ∧ (window 4 0 ∩ window 4 1).card = 3 ∧
      (window 4 0 \ window 4 1).card = 1 := by decide

theorem thirty_steps_at_width_ten :
    selectiveWork (fun _ => 1) (window 10 0) (moving 10 0 30) = 30 ∧
    semispaceWork (fun _ => 1) (moving 10 0 30) = 300 ∧
    (window 10 0 ∪ distinctSurvivors (moving 10 0 30)).card = 40 ∧
    (window 10 30).card = 10 := by
  obtain ⟨new, all, retained, live⟩ := moving_copy_and_space 10 0 30 (by decide)
  exact ⟨new, all, retained, live 30 le_rfl⟩

/-- A cache can be valuable even if its entries are not in the current
carry, when the same identities may later be requested again. -/
theorem forgetting_can_pay_again_on_revival :
    selectiveWork (fun _ : Nat => 1) {7} [∅, {7}] = 1 ∧
      promotionWork (fun _ : Nat => 1) {7} [∅, {7}] = 0 ∧
      revivedWork (fun _ : Nat => 1) {7} {7} [∅, {7}] = 1 := by decide

end Controls
end Mettapedia.Machines.FoldCarryRegimes
