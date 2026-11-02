import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochStateChecks
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCanonicalState

/-! The public controller begins from the ordinary encoded source entry,
with the actual shared runner and empty epoch history. Canonical commitment
keeps that source state exactly.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlBeginExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) :
    let runner := OCamlRunnerBeginExecution.begun prepared provider (initial program)
    PureReturns runtime [] state
      (apply "gslt:ml:begin" [encoded (CompletePlanWire.planTerm (epochPlan prepared provider) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern (initial program))]) state
      (encoded (machine "MlRunning" (CompletePlanWire.planTerm (epochPlan prepared provider) [] [] (.base "MlConfig"))
        (OCamlEpochStandard.standard prepared) (CompleteExecution.classMachineTerm (epochPlan prepared provider) runner) (.symbol "LNil"))) := by
  dsimp only
  have admittedSource := epoch_state_checked program prepared provider (OCaml.begin program) (initial program) built
    (initial_state program (patterns program))
  have begun := OCamlRunnerBeginExecution.begin_returns state prepared provider (initial program) admittedSource.1 admittedSource.2
  metta_call checked
  metta_eval [begun] with checked unfolding [machine]

theorem initial_state_exact (program : OCaml.Program) (prepared : Prepared) (built : prepare program = .ok prepared) :
    (OCamlRunnerBeginExecution.begun prepared provider (initial program)).state = initial program := by
  change Mettapedia.OSLF.MeTTaIL.Complete.Normalized.commit (epochPlan prepared provider) .canonical (initial program) = initial program
  exact epoch_state_commit program prepared provider (OCaml.begin program) (initial program) built (initial_state program (patterns program))

#print axioms returns
#print axioms initial_state_exact

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlBeginExecution
