import Mettapedia.Machines.ConstraintPropagation
import Mathlib.Order.OrderIsoNat

/-!
# Representation constraints across control transfers

A directed edge requires the destination to accommodate the source. Two
opposite edges require the same representation, as at a return that writes
directly into a receiving slot. An unchanged covering pass certifies
closure. Any completed iteration gives the least solution above its seeds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RepresentationFlow

open ConstraintPropagation

variable {Slot Rule Kind : Type*} [DecidableEq Slot] [SemilatticeSup Kind]

def relax (edge : Slot × Slot) : Propagator (Slot → Kind) where
  apply kinds := Function.update kinds edge.2 (kinds edge.2 ⊔ kinds edge.1)
  monotone_apply := by
    intro lower upper ordered slot
    by_cases atTarget : slot = edge.2
    · subst slot
      simp only [Function.update_self]
      exact sup_le_sup (ordered edge.2) (ordered edge.1)
    · simpa only [Function.update_of_ne atTarget] using ordered slot
  le_apply := by
    intro kinds slot
    by_cases atTarget : slot = edge.2
    · subst slot
      simp only [Function.update_self]
      exact le_sup_left
    · simp only [Function.update_of_ne atTarget, le_refl]

theorem relax_fixed_iff (edge : Slot × Slot) (kinds : Slot → Kind) :
    (relax edge).apply kinds = kinds ↔ kinds edge.1 ≤ kinds edge.2 := by
  constructor
  · intro fixed
    have atTarget := congrFun fixed edge.2
    exact sup_eq_left.mp (by simpa only [relax, Function.update_self] using atTarget)
  · intro admissible
    simp only [relax, sup_eq_left.mpr admissible, Function.update_eq_self]

def Closed (edges : Rule → Slot × Slot) (kinds : Slot → Kind) : Prop :=
  ∀ rule, kinds (edges rule).1 ≤ kinds (edges rule).2

theorem closed_iff_quiescent (edges : Rule → Slot × Slot) (kinds : Slot → Kind) :
    Closed edges kinds ↔ Quiescent (fun rule => relax (edges rule)) kinds := by
  simp only [Closed, Quiescent, relax_fixed_iff]

private theorem fixed_pass {S I : Type*} [PartialOrder S] (propagators : I → Propagator S)
    (schedule : List I) (state : S) (unchanged : run propagators schedule state = state) :
    ∀ rule ∈ schedule, (propagators rule).apply state = state := by
  induction schedule with
  | nil => simp
  | cons first rest ih =>
    have grows := le_run propagators rest ((propagators first).apply state)
    change (propagators first).apply state ≤ run propagators (first :: rest) state at grows
    rw [unchanged] at grows
    have fixed := le_antisymm grows ((propagators first).le_apply state)
    rw [run, fixed] at unchanged
    intro rule member
    rcases List.mem_cons.mp member with rfl | later
    · exact fixed
    · exact ih unchanged rule later

theorem unchanged_pass_closed (edges : Rule → Slot × Slot) (schedule : List Rule)
    (covers : ∀ rule, rule ∈ schedule) (kinds : Slot → Kind)
    (unchanged : run (fun rule => relax (edges rule)) schedule kinds = kinds) :
    Closed edges kinds :=
  (closed_iff_quiescent edges kinds).mpr fun rule => fixed_pass _ _ _ unchanged rule (covers rule)

def rounds (edges : Rule → Slot × Slot) (schedule : List Rule) (seed : Slot → Kind) :
    Nat → Slot → Kind
  | 0 => seed
  | n + 1 => run (fun rule => relax (edges rule)) schedule (rounds edges schedule seed n)

theorem rounds_monotone (edges : Rule → Slot × Slot) (schedule : List Rule) (seed : Slot → Kind) :
    Monotone (rounds edges schedule seed) :=
  monotone_nat_of_le_succ fun n => le_run _ schedule (rounds edges schedule seed n)

theorem settled_least (edges : Rule → Slot × Slot) (schedule : List Rule) (covers : ∀ rule, rule ∈ schedule)
    (seed : Slot → Kind) (n : Nat)
    (settled : rounds edges schedule seed (n + 1) = rounds edges schedule seed n) :
    IsLeast {kinds | seed ≤ kinds ∧ Closed edges kinds} (rounds edges schedule seed n) := by
  refine ⟨⟨rounds_monotone edges schedule seed (Nat.zero_le n),
    unchanged_pass_closed edges schedule covers _ settled⟩, ?_⟩
  intro upper feasible
  have fixed := (closed_iff_quiescent edges upper).mp feasible.2
  clear settled
  induction n with
  | zero => exact feasible.1
  | succ n ih => exact run_le_fixed _ schedule ih fixed

theorem covering_rounds_reach_least [WellFoundedGT (Slot → Kind)] (edges : Rule → Slot × Slot)
    (schedule : List Rule) (covers : ∀ rule, rule ∈ schedule) (seed : Slot → Kind) :
    ∃ n, IsLeast {kinds | seed ≤ kinds ∧ Closed edges kinds} (rounds edges schedule seed n) := by
  obtain ⟨n, stable⟩ := WellFoundedGT.monotone_chain_condition
    (⟨rounds edges schedule seed, rounds_monotone edges schedule seed⟩ : Nat →o (Slot → Kind))
  exact ⟨n, settled_least edges schedule covers seed n (stable (n + 1) (Nat.le_succ n)).symm⟩

omit [DecidableEq Slot] in
theorem equivalent_slots {edges : Rule → Slot × Slot} {kinds : Slot → Kind} (closed : Closed edges kinds)
    {source destination : Slot} {forward backward : Rule}
    (fromSource : edges forward = (source, destination))
    (fromDestination : edges backward = (destination, source)) :
    kinds source = kinds destination := by
  have forwardBound := closed forward
  have backwardBound := closed backward
  rw [fromSource] at forwardBound
  rw [fromDestination] at backwardBound
  exact le_antisymm forwardBound backwardBound

end Mettapedia.Machines.RepresentationFlow
