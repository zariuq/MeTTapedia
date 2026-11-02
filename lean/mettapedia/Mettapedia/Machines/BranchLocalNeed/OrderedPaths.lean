import Mettapedia.Machines.BranchLocalNeed.RepresentationRelation

/-!
# Occurrence paths beneath the two Need frontier schedules

A finite occurrence path reaches the breadth-first frontier at its path
length. Every member of a depth-first prefix also has a genuine occurrence
path. The converse for a fixed depth-first schedule is deliberately absent:
an earlier divergent alternative can prevent a later finite path from being
visited. No evaluator or scheduling policy is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedReference.OrderedPaths

open Mettapedia.GSLT.Distinction

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}
  (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

theorem successor_running {source target :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : target ∈ step spec source) : isHalted source = false := by
  cases control : source.control with
  | run _ _ | force _ _ | returned _ _ => simp [isHalted, control]
  | halted _ => simp [step, control] at member

/-- At its exact length, an occurrence-sensitive path appears in the actual
breadth-first frontier without requiring any sibling to finish. -/
theorem path_mem_frontier {length : Nat}
    {source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (path : Steps spec length source target)
    {states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (sourceMember : source ∈ states) : target ∈ runFrontier spec length states := by
  induction path generalizing states with
  | refl => exact sourceMember
  | @cons length source next target occurrence rest ih =>
    have nextMember := occurrence.mem spec
    have running := successor_running spec nextMember
    by_cases stopped : states.all isHalted = true
    · have halted := List.all_eq_true.mp stopped source sourceMember
      rw [running] at halted
      cases halted
    · simp only [runFrontier, stopped]
      apply ih (List.mem_flatMap.mpr ⟨source, sourceMember, ?_⟩)
      cases successors : step spec source with
      | nil => simp [successors] at nextMember
      | cons first remaining => simpa only [advance, successors] using nextMember

private theorem advance_paths (bound : Nat)
    (initial source : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (reachable : ∃ length ≤ bound, Steps spec length initial source)
    {target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (member : target ∈ (NeedRepresentation.needSystem spec).advance source) :
    ∃ length ≤ bound + 1, Steps spec length initial target := by
  rw [NeedRepresentation.needSystem_advance] at member
  obtain ⟨length, bounded, path⟩ := reachable
  cases successors : step spec source with
  | nil =>
    simp only [advance, successors, List.mem_singleton] at member
    subst target
    exact ⟨length, Nat.le_trans bounded (Nat.le_succ _), path⟩
  | cons first remaining =>
    have inStep : target ∈ step spec source := by
      simpa only [advance, successors] using member
    obtain ⟨index, inBounds, selected⟩ := List.mem_iff_getElem.mp inStep
    have occurrence : StepOccurrence spec source target :=
      ⟨index, List.getElem?_eq_some_iff.mpr ⟨inBounds, selected⟩⟩
    exact ⟨length + 1, Nat.add_le_add_right bounded 1,
      path.trans spec (.cons occurrence (.refl _))⟩

private theorem expandFirst_paths (bound : Nat)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect))
    (reachable : ∀ source ∈ states, ∃ length ≤ bound, Steps spec length initial source) :
    ∀ target ∈ (NeedRepresentation.needSystem spec).expandFirst states,
      ∃ length ≤ bound + 1, Steps spec length initial target := by
  induction states with
  | nil => simp [OrderedSystem.expandFirst]
  | cons source rest ih =>
    intro target member
    simp only [OrderedSystem.expandFirst] at member
    split at member
    · rcases List.mem_cons.mp member with rfl | later
      · obtain ⟨length, bounded, path⟩ := reachable _ List.mem_cons_self
        exact ⟨length, Nat.le_trans bounded (Nat.le_succ _), path⟩
      · exact ih (fun node present => reachable node (List.mem_cons_of_mem _ present)) target later
    · rcases List.mem_append.mp member with stepped | later
      · exact advance_paths spec bound initial source (reachable source List.mem_cons_self) stepped
      · obtain ⟨length, bounded, path⟩ := reachable target (List.mem_cons_of_mem _ later)
        exact ⟨length, Nat.le_trans bounded (Nat.le_succ _), path⟩

/-- Finite depth-first work invents no occurrence path, including at an
unfinished frontier. Its selected path length is bounded by expansions. -/
theorem depthFirst_reachable (count : Nat)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    ∀ target ∈ ((NeedRepresentation.needSystem spec).expandFirst)^[count] [initial],
      ∃ length ≤ count, Steps spec length initial target := by
  induction count with
  | zero =>
    intro target member
    simp only [Function.iterate_zero, id_eq, List.mem_singleton] at member
    subst target
    exact ⟨0, Nat.le_refl _, .refl _⟩
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    exact expandFirst_paths spec count initial _ ih

end Mettapedia.Machines.BranchLocalNeed.NeedReference.OrderedPaths
