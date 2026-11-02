import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTransition
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick

/-! Every actual source-authorized primitive service transition composes
through the public controller tick. Concrete primitive families supply the
independent source evaluation and loaded computation proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (atRequest : runner.state = node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest])
    (evaluated : operator.eval arguments = .ok result)
    (computed : PureReturns runtime [] state (OCamlPrimitiveReflection.call operator arguments) state
      (encoded (OCamlArithmeticAdequacy.resultTerm result))) :
    let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      PureReturns runtime [] state (apply "gslt:ml:tick"
        [encoded (machine "MlRunning" (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"))
          (OCamlEpochStandard.standard prepared) (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
        (encoded (OCamlPrimitiveTransition.nextMachine prepared table operator arguments result runner epochs)) := by
  obtain ⟨admitted, meaningful, serviced⟩ := OCamlPrimitiveTransition.service_returns state program prepared table
    operator arguments result rest encodedRest runner epochs built complete signatures closed meaning resolved reached done atRequest evaluated computed
  exact ⟨admitted, meaningful, OCamlSettledTick.returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared)
    epochs _ runner done quantum serviced⟩

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlPrimitiveTick
