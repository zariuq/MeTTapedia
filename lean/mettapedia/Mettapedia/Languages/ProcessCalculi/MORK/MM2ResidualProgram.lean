import Mettapedia.Machines.MachineCoreResidual
import Mettapedia.Languages.ProcessCalculi.MORK.MM2ResumableExecution

/-!
# Whole-rule MM2 suspension as a shared-residual program

The eager rule-scoped MM2 evaluator, paused between rule firings, is the
one-task instance of the shared residual interface: its residual is the whole
ordered workspace, with no return frames.  Bounded execution through the
shared interface is the existing bounded evaluator run, so the proved
pause/resume law (`MM2ResumableExecution.pause_resume_exact`) applies to it.

Suspension inside a firing (a long match or sink batch) is not covered: it
needs the match position, workspace authority and uncommitted sink phase in
the residual, a finer instance of the same interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2ResidualProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ReflectiveComputable
open Mettapedia.Machines
open Mettapedia.Machines.MachineCoreResidual

theorem iterate_exact (policy : UnsupportedExecPolicy) (fuel : Nat) (workspace : List Atom) :
    (SharedContinuation.step (program (MM2ResumableExecution.machine policy)))^[fuel]
        (residual (MM2ResumableExecution.machine policy) workspace) =
      if (cRuleScopedSourceWorkQueueRunN policy fuel workspace).2 = fuel then
        residual (MM2ResumableExecution.machine policy)
          (cRuleScopedSourceWorkQueueRunN policy fuel workspace).1
      else stopped (MM2ResumableExecution.machine policy)
          (cRuleScopedSourceWorkQueueRunN policy fuel workspace).1 := by
  rw [iterate_residual_exact, MM2ResumableExecution.runSlice_eq_existing]

end Mettapedia.Languages.ProcessCalculi.MORK.MM2ResidualProgram
