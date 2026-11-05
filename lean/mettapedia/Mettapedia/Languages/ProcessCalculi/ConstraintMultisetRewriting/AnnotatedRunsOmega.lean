import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsRounds
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairFiringRuns

/-!
# ω-runs of the candidate step, and fairness

Fairness and liveness speak about runs that never end. `Liveness.FairRuns` fixes the vocabulary
for any labelled transition system: infinite runs, tasks, weak and strong fairness, and machine
closure. Here the candidate step is such a system.

* **The candidate step as a transition system** (`candidateLTS`): a firing is allowed where it is
  admitted, and leads to its update. On firings without predicate queries it is the existing
  `FairFiringRuns.system` (`candidateLTS_ofPlain`). Its finite executions from a configuration
  with a solution are exactly the runs of the candidate step (`exec_iff`), and every finite window
  of an ω-run is a run (`OmegaRun.window_executable`).
* **Fairness changes no safety result of the candidate step** (`machineClosed`,
  `fair_invariant_iff`). A configuration can be quiescent, so ω-runs are taken in the system with an
  idle step. For finitely many tasks, every run of the candidate step is a prefix of an ω-run that
  is strongly fair for every task. Hence a property of configurations holds along every strongly
  fair ω-run exactly when it holds at the end of every run.
* **Fairness is a property of ω-runs, not of their prefixes** (`OmegaControls.idling_unfair`): idling
  forever beside an admitted firing is an ω-run, and it is not weakly fair for that firing, while
  every finite prefix of it extends to a strongly fair ω-run
  (`OmegaControls.taker_extends_fairly`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits.Liveness (LTS Run InfinitelyOften EventuallyAlways MachineClosed
  machineClosed_stronglyFair)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Omega

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The candidate step as a labelled transition system**: a firing is allowed where it is
admitted, and leads to its update. -/
def candidateLTS : LTS (Configuration T O) (Firing T S O) where
  Allowed C f := f.Valid A label C
  next C f := f.result label C

/-- **On firings without predicate queries the system is `FairFiringRuns.system`**: the same
allowed steps and the same updates. -/
theorem candidateLTS_ofPlain (C : Configuration T O) (x : ConditionalSchedule.Firing T O) :
    ((candidateLTS A label).Allowed C (Firing.ofPlain x : Firing T S O) ↔
        (FairFiringRuns.system A label).Allowed C x) ∧
      (candidateLTS A label).next C (Firing.ofPlain x : Firing T S O) =
        (FairFiringRuns.system A label).next C x :=
  ⟨Firing.valid_ofPlain_iff A label x C, rfl⟩

/-- **Finite executions are runs.** From a configuration with a solution, the finite executions
of the system are exactly the runs of the candidate step, ending where the run leaves it. -/
theorem exec_iff : ∀ (C : Configuration T O) (w : List (Firing T S O)) (C' : Configuration T O),
    A.Consistent C.equations →
      ((candidateLTS A label).Exec C w C' ↔ Executable A label C w ∧ C' = follow label C w)
  | C, [], C', consistent => by
      constructor
      · intro exec
        cases exec
        exact ⟨consistent, rfl⟩
      · rintro ⟨-, rfl⟩
        exact .nil _
  | C, f :: rest, C', _ => by
      constructor
      · intro exec
        cases exec with
        | cons allowed later =>
            have valid : f.Valid A label C := allowed
            obtain ⟨runs, ends⟩ := (exec_iff (f.result label C) rest C'
              valid.firing.consistent).mp later
            exact ⟨⟨valid, runs⟩, ends⟩
      · rintro ⟨⟨valid, runs⟩, rfl⟩
        exact .cons valid ((exec_iff (f.result label C) rest _ valid.firing.consistent).mpr
          ⟨runs, rfl⟩)

/-- **ω-runs of the candidate step.** -/
abbrev OmegaRun := Run (candidateLTS A label)

/-- **Every finite window of an ω-run is a run**, ending where the ω-run is then. -/
theorem OmegaRun.window_executable (r : OmegaRun A label) (k n : ℕ)
    (consistent : A.Consistent (r.state k).equations) :
    Executable A label (r.state k) (r.window k n) ∧
      r.state (k + n) = follow label (r.state k) (r.window k n) :=
  (exec_iff A label _ _ _ consistent).mp (r.exec_window n k)

/-- **Fairness changes no safety result.** For finitely many tasks, every run of the candidate step
from `C` is a prefix of an ω-run of the system with an idle step that is strongly fair for every
task. -/
theorem machineClosed {ι : Type*} [Fintype ι] [DecidableEq ι] (tasks : ι → Firing T S O → Prop)
    (C : Configuration T O) :
    MachineClosed (candidateLTS A label).withIdle C
      (fun r => ∀ i, r.StronglyFair (LTS.liftTask (tasks i))) :=
  machineClosed_stronglyFair (fun i => LTS.liftTask (tasks i)) (LTS.withIdle_nonBlocking _) C

/-- **A property of configurations holds along every strongly fair ω-run exactly when it holds
at the end of every run.** -/
theorem fair_invariant_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : ι → Firing T S O → Prop) (C : Configuration T O) (consistent : A.Consistent C.equations)
    (Inv : Configuration T O → Prop) :
    (∀ r : Run (candidateLTS A label).withIdle, (∀ i, r.StronglyFair (LTS.liftTask (tasks i))) →
        r.state 0 = C → ∀ n, Inv (r.state n)) ↔
      ∀ w : List (Firing T S O), Executable A label C w → Inv (follow label C w) := by
  rw [MachineClosed.invariant_iff (machineClosed A label tasks C) Inv]
  constructor
  · intro holds w runs
    refine holds _ ((LTS.withIdle_reachable_iff _ C _).mpr ⟨w, ?_⟩)
    exact (exec_iff A label C w _ consistent).mpr ⟨runs, rfl⟩
  · intro holds s reachable
    obtain ⟨w, exec⟩ := (LTS.withIdle_reachable_iff _ C s).mp reachable
    obtain ⟨runs, rfl⟩ := (exec_iff A label C w s consistent).mp exec
    exact holds w runs

end Omega

/-! ## Controls -/

namespace OmegaControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker start taker_valid)

/-- Idling forever at the start, beside the admitted taker. -/
def idling : Run (candidateLTS A label).withIdle where
  state _ := start
  label _ := none
  allowed _ := trivial
  step _ := rfl

/-- **Negative control: idling forever is unfair.** The taker is admitted at every moment and never
fires. -/
theorem idling_unfair : ¬ idling.WeaklyFair (LTS.liftTask (· = taker)) := by
  intro fair
  obtain ⟨n, -, fires⟩ := fair ⟨0, fun _ _ => ⟨some taker, rfl, taker_valid⟩⟩ 0
  exact fires

/-- **Positive control: every finite prefix extends fairly.** The run of the taker is a prefix of an
ω-run that is strongly fair for the taker. -/
theorem taker_extends_fairly :
    ∃ r : Run (candidateLTS A label).withIdle,
      (∀ _ : Unit, r.StronglyFair (LTS.liftTask (· = taker))) ∧ r.state 0 = start ∧
        r.window 0 1 = [some taker] :=
  machineClosed A label (fun (_ : Unit) => (· = taker)) start [some taker] _
    (.cons (a := some taker) taker_valid (.nil _))

end OmegaControls

#print axioms candidateLTS_ofPlain
#print axioms exec_iff
#print axioms OmegaRun.window_executable
#print axioms machineClosed
#print axioms fair_invariant_iff
#print axioms OmegaControls.idling_unfair
#print axioms OmegaControls.taker_extends_fairly

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
