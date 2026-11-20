import Mettapedia.Machines.ScheduledRun.Certificates

/-!
# Local dependency and phase transport of lasso certificates

The cache footprint is the ordered successor list of each state in the cyclic
word. Changes elsewhere do not invalidate the certificate. Clock transport is
controlled by the LCM of those local arities, not an unrelated transient prefix
or necessarily the word length. No reuse across a changed ordered footprint
is inferred from set equality of successors.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

def certificateClock (next : S → List S) (mode : Mode) (path : List S)
    (positive : 0 < path.length) : Nat :=
  match mode with
  | .canonical => 1
  | .rotating => (Finset.range path.length).lcm (fun offset => (next (cyclicAt path positive offset)).length)

theorem arity_dvd_certificateClock (next : S → List S) (path : List S)
    (positive : 0 < path.length) (index : Fin path.length) :
    (next (path.get index)).length ∣ certificateClock next .rotating path positive := by
  have divides := Finset.dvd_lcm
    (f := fun offset => (next (cyclicAt path positive offset)).length) (Finset.mem_range.mpr index.isLt)
  change (next (cyclicAt path positive index.val)).length ∣ certificateClock next .rotating path positive at divides
  rwa [cyclicAt_lt] at divides

variable [DecidableEq S]

theorem checkLoop_congr_next (first second : S → List S) (mode : Mode) (start : Nat) (path : List S)
    (agrees : ∀ state ∈ path, first state = second state) :
    checkLoop first mode start path = checkLoop second mode start path := by
  by_cases empty : path.length = 0
  · simp [checkLoop, empty]
  · apply Bool.eq_iff_iff.mpr
    rw [checkLoop_spec first mode start path (Nat.pos_of_ne_zero empty),
      checkLoop_spec second mode start path (Nat.pos_of_ne_zero empty)]
    apply forall_congr'
    intro index
    have same := agrees (path.get index) (List.get_mem _ _)
    rw [step_next_congr first second mode.schedule (start + index.val) (path.get index) same, same]

theorem checkLoop_reuse (next : S → List S) (mode : Mode) (first second : Nat)
    (path : List S) (positive : 0 < path.length) (checked : checkLoop next mode first path = true)
    (phase : Nat.ModEq (certificateClock next mode path positive) first second) :
    checkLoop next mode second path = true := by
  have edges := (checkLoop_spec next mode first path positive).mp checked
  apply (checkLoop_spec next mode second path positive).mpr
  intro index
  refine ⟨?_, (edges index).2⟩
  have picks : mode.schedule.pick (second + index.val) (next (path.get index)).length =
      mode.schedule.pick (first + index.val) (next (path.get index)).length := by
    cases mode with
    | canonical => rfl
    | rotating =>
      exact (Nat.ModEq.add_right index.val
        (Nat.ModEq.of_dvd (arity_dvd_certificateClock next path positive index) phase)).symm
  have sameStep := step_eq_of_picks next mode.schedule (second + index.val) (first + index.val)
    (some (path.get index)) (fun state present => by
      have same := Option.some.inj present
      subst state
      exact picks)
  exact sameStep.trans (edges index).1

end Mettapedia.Machines.ScheduledRun
