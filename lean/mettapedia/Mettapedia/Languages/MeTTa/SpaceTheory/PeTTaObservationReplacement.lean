import Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaImportProtection

/-!
# A PeTTa snapshot can replace live definition lookup

The live store is still the state of both executions. The specializing
theory replaces only lookups of a function definition and its argument
demand, not a query of the live store. The proof keeps the actual
configuration chain, before projecting the seven possible observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaObservationReplacement

open Mettapedia.GSLT
open Contracts.OccurrenceObservers (Demand Result Trace)
open Contracts.OccurrenceExecution
  (completed completed_iff_chain readCompleted reports ofTerm reports_congr reports_shown_iff)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
open Eval (ProgramAgreementAt)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open PeTTaExecution (programAt theoryAt)
open EvaluationObservations (pettaView pettaEmit)

theorem live_trace_iff_at_snapshot (atoms : List Atom) (source : Eval.Configuration)
    (agreement : ∀ current, (theoryAt atoms).MultiStep source current →
      ProgramAgreementAt (SpaceSemantics.index current.state.core) (programAt atoms) current)
    (trace : Trace Atom) :
    completed (sys := LiveRegistry.theory) pettaView (·.isSome = true) pettaEmit source trace ↔
      completed (sys := theoryAt atoms) pettaView (·.isSome = true) pettaEmit source trace := by
  refine (completed_iff_chain (sys := LiveRegistry.theory) pettaView _ pettaEmit source trace).trans
    (Iff.trans ?_ (completed_iff_chain (sys := theoryAt atoms) pettaView _ pettaEmit source trace).symm)
  constructor
  · rintro ⟨tail, finish, chain, last, ended, batches⟩
    have same := (PeTTaExecution.live_trace_iff (programAt atoms) source agreement tail).mp chain
    exact ⟨tail, finish, same, last, ended, batches⟩
  · rintro ⟨tail, finish, chain, last, ended, batches⟩
    have same := (PeTTaExecution.live_trace_iff (programAt atoms) source agreement tail).mpr chain
    exact ⟨tail, finish, same, last, ended, batches⟩

theorem snapshot_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) {source : Eval.Configuration} {start : SState O}
    (shown : EvalOnTheStep.Shows source start) (demand : Demand) (answer : Result Atom demand) :
    reports (completed (sys := theoryAt atoms) pettaView (·.isSome = true) pettaEmit source) demand answer ↔
    reports (readCompleted (sys := EvalOnTheStep.stepSystem O (programAt atoms))
      (ofTerm EvalOnTheStep.Shows pettaView) (·.isSome = true) pettaEmit start) demand answer := by
  refine reports_shown_iff (source := theoryAt atoms) (target := EvalOnTheStep.stepSystem O (programAt atoms))
    (shows := EvalOnTheStep.Shows) pettaView ?_ ?_ shown (·.isSome = true) pettaEmit demand answer
  · exact ⟨PeTTaExecution.snapshot_step_on_transform atoms, PeTTaExecution.snapshot_reflect_transform_step atoms⟩
  · exact fun first second => congrArg pettaView (EvalOnTheStep.shows_unique first second)

/-- A closed body can be put on the snapshot theory exactly as long as
the definitions and argument assignments visible to its pending code
stay the same. Reads in the body still see the actual live store. -/
theorem unchanged_heads_preserve_reports {O : Type} [DecidableEq O] [Infinite O]
    (atoms : List Atom) {source : Eval.Configuration} {start : SState O} {supported : String → Bool}
    (shown : EvalOnTheStep.Shows source start)
    (closed : Eval.ProgramClosed supported (programAt atoms))
    (within : Eval.configurationWithin supported source)
    (kept : ∀ current, (theoryAt atoms).MultiStep source current →
      ∀ head, supported head = true →
        PeTTaImportProtection.view (programAt current.state.core) head =
          PeTTaImportProtection.view (programAt atoms) head)
    (demand : Demand) (answer : Result Atom demand) :
    reports (completed (sys := LiveRegistry.theory) pettaView (·.isSome = true) pettaEmit source) demand answer ↔
    reports (readCompleted (sys := EvalOnTheStep.stepSystem O (programAt atoms))
      (ofTerm EvalOnTheStep.Shows pettaView) (·.isSome = true) pettaEmit start) demand answer := by
  have agreement (current : Eval.Configuration) (path : (theoryAt atoms).MultiStep source current) :
      ProgramAgreementAt (SpaceSemantics.index current.state.core) (programAt atoms) current := by
    rw [← PeTTaExecution.programAt_exact]
    exact Eval.configuration_agreement_on (PeTTaImportProtection.protects_queries (kept current path))
      (Eval.path_within closed path within)
  exact (reports_congr (live_trace_iff_at_snapshot atoms source agreement) demand answer).trans
    (snapshot_reports_iff atoms shown demand answer)

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaObservationReplacement
