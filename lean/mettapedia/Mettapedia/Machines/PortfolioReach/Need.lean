import Mettapedia.Machines.PortfolioReach.Effects

/-!
# The units deepening needs

Iterative deepening from bound zero has an outcome once it has run a bound at
which the search either holds `demand` answers or cuts nothing
(`Decides`). Running every bound up to that one to its end costs the states
each visits, counted by the existing `boundedWork`, and one unit for each new
bound: `idWork space root 0 target + target` (`deepen_need`). A round that
fills early stops early, so this is an upper bound.

The unit is one expansion of the search space or one change of bound. An
arithmetic step and a read are expansions of the space they belong to, so
they are counted; what one expansion costs in time is not part of this count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (Step Space Reaches IsAnswer bounded
  boundedWork idWork)
open Mettapedia.Machines.BoundedSearchPortfolio (Origin Task Cursor Status status ready
  expandOne children Iteration beginIteration nextIteration BatchMeaning pendingWork)

universe u v

variable {S : Type u} {A : Type v}

/-- The bound `target` settles the demand: its traversal holds `demand`
answers, or cuts nothing. -/
def Decides (space : Space S A) (root : S) (demand target : Nat) : Prop :=
  demand ≤ (bounded space target root).1.length ∨ (bounded space target root).2 = false

/-- A reachable answer settles a demand of one at its depth. -/
theorem decides_of_reaches {space : Space S A} {root : S} {value : A} {depth : Nat}
    (reaches : Reaches space root value depth) : Decides space root 1 depth := by
  left
  have member := Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.bounded_complete space
    reaches (Nat.le_refl depth)
  exact List.length_pos_of_mem member

/-- What the `later` bounds after `depth` cost when each is run to its end: a
unit to change bound, and the states the round visits. -/
def owed (space : Space S A) (root : S) : Nat → Nat → Nat
  | _, 0 => 0
  | depth, later + 1 =>
      1 + boundedWork space (depth + 1) root + owed space root (depth + 1) later

theorem owed_eq (space : Space S A) (root : S) :
    ∀ (later depth : Nat),
      boundedWork space depth root + owed space root depth later =
        idWork space root depth later + later
  | 0, _ => rfl
  | later + 1, depth => by
      have rest := owed_eq space root later (depth + 1)
      simp only [owed, idWork]
      omega

theorem cutoff_shape {demand : Nat} {cursor : Cursor S A}
    (cut : status demand cursor = .cutoff) :
    cursor.frontier = [] ∧ cursor.cut = true ∧ cursor.reversed.length < demand := by
  unfold BoundedSearchPortfolio.status at cut
  split at cut
  · cases cut
  · rename_i below
    split at cut
    · rename_i empty
      split at cut
      · rename_i isCut
        exact ⟨List.isEmpty_iff.mp empty, isCut, by omega⟩
      · cases cut
    · cases cut

/-- At a bound that settles the demand, a valid round does not end cut off. -/
theorem not_cutoff_at {space : Space S A} {root : S} {demand target : Nat}
    (decides : Decides space root demand target) (iteration : Iteration S A)
    (valid : iteration.Valid space root demand) (here : iteration.depth = target) :
    status demand iteration.cursor ≠ .cutoff := by
  intro cut
  obtain ⟨empty, isCut, short⟩ := cutoff_shape cut
  obtain ⟨occurrences, cuts, _⟩ := valid
  rw [here] at occurrences cuts
  rw [empty] at occurrences cuts
  simp only [BoundedSearchPortfolio.pendingAnswers, List.flatMap_nil, List.append_nil]
    at occurrences
  simp only [BoundedSearchPortfolio.pendingCut, List.any_nil, Bool.or_false] at cuts
  rcases decides with enough | uncut
  · rw [← occurrences, BoundedSearchPortfolio.Cursor.answers, List.length_reverse] at enough
    omega
  · rw [isCut, uncut] at cuts
    cases cuts

theorem deepenOne_paused (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) (paused : status demand iteration.cursor = .paused) :
    deepenOne space root demand iteration =
      { iteration with cursor := expandOne space iteration.cursor } := by
  simp [deepenOne, paused]

theorem deepenOne_cutoff (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) (cut : status demand iteration.cursor = .cutoff) :
    deepenOne space root demand iteration = nextIteration root iteration := by
  simp [deepenOne, cut]

/-- **Deepening has an outcome within its potential**: the states still to
visit at this bound, and what the bounds up to `target` cost after it. -/
theorem deepen_ready_within (space : Space S A) (root : S) (demand target : Nat)
    (decides : Decides space root demand target) :
    ∀ (budget : Nat) (iteration : Iteration S A), iteration.Valid space root demand →
      iteration.depth ≤ target →
      pendingWork space iteration.cursor.frontier +
          owed space root iteration.depth (target - iteration.depth) ≤ budget →
      ∃ units, units ≤ budget ∧
        (deepenResumable space root demand).ready
          ((deepenResumable space root demand).step^[units] iteration) = true := by
  intro budget
  induction budget with
  | zero =>
      intro iteration valid below potential
      by_cases finished : ready (status demand iteration.cursor) = true
      · exact ⟨0, Nat.le_refl 0, finished⟩
      · exfalso
        cases outcome : status demand iteration.cursor with
        | full => simp [outcome, ready] at finished
        | exhausted => simp [outcome, ready] at finished
        | paused =>
            have positive := BoundedSearchPortfolio.pendingWork_positive space
              iteration.cursor.frontier
              (BoundedSearchPortfolio.paused_frontier_nonempty demand iteration.cursor outcome)
            omega
        | cutoff =>
            have here : iteration.depth = target := by
              by_contra apart
              have more : target - iteration.depth = (target - iteration.depth - 1) + 1 := by
                omega
              rw [more] at potential
              simp only [owed] at potential
              omega
            exact not_cutoff_at decides iteration valid here outcome
  | succ budget ih =>
      intro iteration valid below potential
      by_cases finished : ready (status demand iteration.cursor) = true
      · exact ⟨0, Nat.zero_le _, finished⟩
      · cases outcome : status demand iteration.cursor with
        | full => simp [outcome, ready] at finished
        | exhausted => simp [outcome, ready] at finished
        | paused =>
            have nonempty :=
              BoundedSearchPortfolio.paused_frontier_nonempty demand iteration.cursor outcome
            have less := BoundedSearchPortfolio.expandOne_pendingWork space iteration.cursor
              nonempty
            obtain ⟨units, bounded, done⟩ :=
              ih { iteration with cursor := expandOne space iteration.cursor }
                (Iteration.valid_expand space root demand iteration valid outcome) below
                (by simp only; omega)
            refine ⟨units + 1, by omega, ?_⟩
            rw [Function.iterate_succ_apply]
            show (deepenResumable space root demand).ready
              ((deepenResumable space root demand).step^[units]
                (deepenOne space root demand iteration)) = true
            rw [deepenOne_paused space root demand iteration outcome]
            exact done
        | cutoff =>
            have apart : iteration.depth ≠ target := fun here =>
              not_cutoff_at decides iteration valid here outcome
            obtain ⟨empty, _, _⟩ := cutoff_shape outcome
            have more : target - iteration.depth = (target - (iteration.depth + 1)) + 1 := by
              omega
            rw [more, empty] at potential
            simp only [owed, BoundedSearchPortfolio.pendingWork, List.map_nil, List.sum_nil]
              at potential
            obtain ⟨units, bounded, done⟩ := ih (nextIteration root iteration)
              (BoundedSearchPortfolio.nextIteration_valid space root demand iteration)
              (by simp only [nextIteration, beginIteration]; omega)
              (by
                simp only [nextIteration, beginIteration, BoundedSearchPortfolio.start,
                  BoundedSearchPortfolio.pendingWork, List.map_cons, List.map_nil,
                  List.sum_cons, List.sum_nil]
                omega)
            refine ⟨units + 1, by omega, ?_⟩
            rw [Function.iterate_succ_apply]
            show (deepenResumable space root demand).ready
              ((deepenResumable space root demand).step^[units]
                (deepenOne space root demand iteration)) = true
            rw [deepenOne_cutoff space root demand iteration outcome]
            exact done

/-- **The units deepening needs from bound zero**: at most the states of every
round up to a bound that settles the demand, and one unit per change of
bound. -/
theorem deepen_need (space : Space S A) (root : S) (demand target : Nat)
    (decides : Decides space root demand target) :
    ∃ units, units ≤ idWork space root 0 target + target ∧
      (deepenResumable space root demand).ready
        ((deepenResumable space root demand).step^[units] (beginIteration root 0)) = true := by
  have within := deepen_ready_within space root demand target decides
    (idWork space root 0 target + target) (beginIteration root 0)
    (BoundedSearchPortfolio.beginIteration_valid space root demand 0) (Nat.zero_le target)
    (by
      have total := owed_eq space root target 0
      simp only [beginIteration, BoundedSearchPortfolio.start,
        BoundedSearchPortfolio.pendingWork, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.sub_zero]
      omega)
  exact within

#print axioms deepen_ready_within
#print axioms deepen_need

end Mettapedia.Machines.PortfolioReach
