import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Scheduler-inert frames for reflective execution

Appending rows that decode to no supported executable preserves the complete
supported inventory, its scheduler choice, and the corresponding one-step
reflective execution equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ReflectiveComputable
open WQComputable

theorem cSupportedSourceExecFacts_append_inert
    (space extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    cSupportedSourceExecFacts (space ++ extra) =
      cSupportedSourceExecFacts space := by
  change List.filterMap extractSupportedSourceExecFact (space ++ extra) =
    List.filterMap extractSupportedSourceExecFact space
  rw [List.filterMap_append]
  change cSupportedSourceExecFacts space ++
      cSupportedSourceExecFacts extra = cSupportedSourceExecFacts space
  rw [inert, List.append_nil]

theorem selectNextScheduled_supported_append_inert
    (space extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    selectNextScheduled (cSupportedSourceExecFacts (space ++ extra)) =
      selectNextScheduled (cSupportedSourceExecFacts space) := by
  rw [cSupportedSourceExecFacts_append_inert space extra inert]

theorem cReflectiveSourceWorkQueueStep_append_inert_of_selected
    (space extra : List Atom) (directive : SourceExecFact)
    (inert : cSupportedSourceExecFacts extra = [])
    (selected :
      selectNextScheduled (cSupportedSourceExecFacts space) = some directive) :
    cReflectiveSourceWorkQueueStep .leaveInert (space ++ extra) =
      some (cFireReflectiveSourceExecFact (space ++ extra) directive) := by
  simp only [cReflectiveSourceWorkQueueStep,
    selectNextScheduled_supported_append_inert space extra inert, selected]

#print axioms cSupportedSourceExecFacts_append_inert
#print axioms selectNextScheduled_supported_append_inert
#print axioms cReflectiveSourceWorkQueueStep_append_inert_of_selected

end Mettapedia.Languages.ProcessCalculi.MORK
