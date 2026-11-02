import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlProgress
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedControlFlowControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSettledPatternFailure

/-! Duplicate pattern slots retain their identities. A successful match at
the later slot enables its own generated rule and cannot authorize failure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.OccurrenceProgressControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open ControlFlowControls
open Mettapedia.Machines.ResumableSearchRunner

#guard patterns captureProgram == [.bind, .bind]
#guard patternReference? (patterns captureProgram) .bind == some (patternId 0)
#guard patternReference? (patterns captureProgram) .bind != some (patternId 1)

theorem later_duplicate_can_step (prepared : Prepared) (built : prepare captureProgram = .ok prepared) :
    (GeneralOccurrenceSemantics.gslt (epochPlan prepared provider) [] (.base "MlConfig")).Step
      (node "MlMatchOne" [patternId 1, value (number 7), code 1, environment [], node "MlKDone"])
      (node "MlEvaluate" [code 1, environment [number 7], node "MlKDone"]) := by
  exact prepared_match_success_step_any_index captureProgram prepared provider 1 .bind (number 7) 1 [] []
    (node "MlKDone") [number 7] built rfl rfl rfl rfl

theorem later_success_cannot_be_exhausted (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (built : prepare captureProgram = .ok prepared) (invariant : SourceEpochInvariant captureProgram prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (request : runner.state = node "MlMatchOne" [patternId 1, value (number 7), code 1, environment [], node "MlKDone"]) :
    runner.phase ≠ .done := by
  intro done
  have failed := settled_match_failure_any_index captureProgram prepared table runner 1 .bind (number 7) 1 [] []
    (node "MlKDone") built invariant rfl rfl reached done request
  cases failed

#print axioms later_duplicate_can_step
#print axioms later_success_cannot_be_exhausted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.OccurrenceProgressControls
