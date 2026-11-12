import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec
import Mettapedia.Machines.BoundedDeterministicRun

/-!
# Actual source prefixes and resumption through runtime error scopes

The existing bounded deterministic runner retains the full source configuration.
Reading its endpoint with the source's zero-step terminal observer recovers the
source run exactly. A suspended result therefore resumes without repeating its
earlier transitions, regardless of termination, effects or a pending handler.

The observer deliberately preserves the source distinction between unhandled
faults and suspended states. A failed internal unifier can still leave the
source step undefined; this does not make it logical exhaustion or provide an
internal-unifier suspension mechanism.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Machines

theorem run_stopped (registry : SpaceSemantics.Program) (source : Configuration)
    (stopped : step registry source = none) (fuel : Nat) :
    run registry fuel source = run registry 0 source := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases source with
      | mk state control frames input output uses =>
          cases control with
          | fault reason =>
              cases recovered : recoverDynamic [] frames <;> simp only [run, recovered, stopped]
          | returned answers => cases frames <;> simp only [run, stopped]
          | _ => simp only [run, stopped]

/-- The common runner is a genuine state-changing execution, not an identity
surrogate. The source observer classifies its retained endpoint afterwards. -/
theorem run_as_bounded (registry : SpaceSemantics.Program) (fuel : Nat) (source : Configuration) :
    run registry fuel source =
      run registry 0 (BoundedDeterministicRun.run (step registry) fuel source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases taken : step registry source with
      | none =>
          simpa only [BoundedDeterministicRun.run, taken] using run_stopped registry source taken (fuel + 1)
      | some next =>
          rw [run_succ_of_step registry fuel source next taken]
          simpa only [BoundedDeterministicRun.run, taken] using ih next

theorem zero_exhausted_state (registry : SpaceSemantics.Program) (source saved : Configuration)
    (paused : run registry 0 source = .exhausted saved) : source = saved := by
  cases source with
  | mk state control frames input output uses =>
      cases control with
      | fault reason =>
          cases recovered : recoverDynamic [] frames <;>
            simp only [run, recovered] at paused
          · cases paused
          · exact Outcome.exhausted.inj paused
      | returned answers =>
          cases frames
          · cases paused
          · exact Outcome.exhausted.inj paused
      | _ => exact Outcome.exhausted.inj paused

/-- Every bounded endpoint is reached by the independent source rules. -/
theorem bounded_endpoint_reachable (registry : SpaceSemantics.Program) (fuel : Nat) (source : Configuration) :
    Relation.ReflTransGen (Transition registry) source
      (BoundedDeterministicRun.run (step registry) fuel source) := by
  exact Relation.ReflTransGen.mono (fun _ _ computed => step_transition computed)
    source (BoundedDeterministicRun.run (step registry) fuel source)
    (BoundedDeterministicRun.run_reachable (step registry) fuel source)

/-- Source fuel can be split across a retained configuration. Earlier writes,
answers and call-handler state are retained; no restarted query is substituted. -/
theorem resume_exhausted (registry : SpaceSemantics.Program) (first second : Nat)
    (source saved : Configuration) (paused : run registry first source = .exhausted saved) :
    run registry (first + second) source = run registry second saved := by
  have observed := run_as_bounded registry first source
  rw [paused] at observed
  have endpoint := zero_exhausted_state registry _ saved observed.symm
  rw [run_as_bounded, BoundedDeterministicRun.run_add, endpoint]
  exact (run_as_bounded registry second saved).symm

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
