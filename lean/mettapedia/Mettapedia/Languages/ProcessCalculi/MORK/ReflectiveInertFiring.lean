import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Inert reflective firing

A supported directive with no input match consumes only its own scheduler
shell.  The result is independent of the number or kinds of authored sinks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Conformance.Computable
open ReflectiveComputable
open WQComputable

private theorem cFinalizeSupportSink_nil (sink : Sink)
    (space : List Atom) :
    cFinalizeSupportSink sink [] space = space := by
  cases sink <;>
    simp [cFinalizeSupportSink, cUnionSupport, cSubtractSupport,
      compactExtremaList]

theorem cApplyReflectiveSinkBatch_nil (space : List Atom)
    (sinks : List Sink) :
    cApplyReflectiveSinkBatch [] space sinks = space := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [cApplyReflectiveSinkBatch, List.foldl_nil]
      rw [cFinalizeSupportSink_nil, induction]

/-- With no input match, a reflective directive is precisely an inert shell:
the scheduler consumes the directive atom and no sink can affect support. -/
theorem cFireReflectiveSourceExecFact_eq_erase_of_no_matches
    (space : List Atom) (directive : SourceExecFact)
    (noMatches :
      cmatchInputSpec [] (directive.atom :: space.erase directive.atom)
        directive.rule.input = []) :
    cFireReflectiveSourceExecFact space directive =
      space.erase directive.atom := by
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  dsimp only
  rw [noMatches]
  simp only [List.map_nil]
  exact cApplyReflectiveSinkBatch_nil _ _

#print axioms cApplyReflectiveSinkBatch_nil
#print axioms cFireReflectiveSourceExecFact_eq_erase_of_no_matches

end Mettapedia.Languages.ProcessCalculi.MORK
