import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData
import Mettapedia.Languages.OCaml.Examples
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! Preparation controls for indexed OCaml programs. These check the actual
shared plan and emitted structural kernel. They do not assert the OCaml
source lowering, primitive service or complete controller correspondence. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

#guard OCaml.Examples.examples.all fun sample => (prepare sample.program).isOk
#guard OCaml.Examples.structuralExamples.all fun sample => (prepare sample.program).isOk

def preparationDiagnostics : List (String × List GeneralExecutionAdmission.Obligation) :=
  (OCaml.Examples.examples ++ OCaml.Examples.structuralExamples).filterMap fun sample =>
    match prepare sample.program with
    | .error _ => none
    | .ok prepared => some (sample.name, (plan prepared).obligations)

#eval preparationDiagnostics.filter (fun entry => !entry.2.isEmpty)
#guard preparationDiagnostics.all (fun entry => entry.2.isEmpty)

#guard OCaml.Examples.structuralExamples.all fun sample =>
  match prepare sample.program with
  | .error _ => false
  | .ok prepared => (CompleteEmission.emitText? (ExecutionData.spec prepared) "ml-prepared" .classes).isOk

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
