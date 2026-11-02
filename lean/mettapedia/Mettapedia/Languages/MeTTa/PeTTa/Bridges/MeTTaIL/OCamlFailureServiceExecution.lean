import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlInstallExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceGuards

/-! Literal service dispatch installs a failure row only after a complete,
empty class search. Match and clause requests retain their full runner and
history when delegated to the existing install operation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

macro "service_eval" "[" facts:term,* "]" "unfolding" "[" defs:term,* "]" : tactic =>
  `(tactic|
    (try metta_eval [$facts,*] with checked unfolding [$defs,*]
     all_goals
       (apply pure_if_returns
        · apply OCamlServiceGuards.symbol_self_equal_returns
          exact bound_returns _ _ _ (by rfl)
        · simp only [if_true]
          try metta_eval [$facts,*] with checked unfolding [$defs,*]
          all_goals
            (apply pure_if_returns
             · apply OCamlServiceGuards.symbol_self_equal_returns
               exact bound_returns _ _ _ (by rfl)
             · simp only [if_true]
               metta_eval [$facts,*] with checked unfolding [$defs,*]))))

def matchRequest (parameter argument body captured rest : Term) : Term :=
  .application "PApp" [.string "MlMatchOne", encodeList id [parameter, argument, body, captured, rest]]

def clauseRequest (parameter argument body later captured rest : Term) : Term :=
  .application "PApp" [.string "MlTryClause", encodeList id [parameter, argument, body, later, captured, rest]]

def failureRowTerm (parameter argument : Term) : Term :=
  .application "PremiseProviderRow" [.string "ml-pattern-failure", encodeList id [parameter, argument]]

theorem match_service_returns (state : State) (plan standard parameter argument body captured rest query states receipts epochs answer : Term)
    (finished : PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"), encoded plan, encoded query]) state
      (encoded (.symbol "SearchComplete")))
    (empty : PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded query]) state (encoded (.symbol "LNil")))
    (installed : PureReturns runtime [] state
      (apply "gslt:ml:install" [encoded plan, encoded standard,
        encoded (doneRunner (matchRequest parameter argument body captured rest) query states receipts),
        encoded epochs, encoded (failureRowTerm parameter argument)]) state (encoded answer)) :
    PureReturns runtime [] state
      (apply "gslt:ml:service" [encoded plan, encoded standard,
        encoded (doneRunner (matchRequest parameter argument body captured rest) query states receipts), encoded epochs]) state
      (encoded answer) := by
  metta_call checked
  service_eval [finished, empty, installed] unfolding [doneRunner, matchRequest, failureRowTerm, encodeList]

theorem clause_service_returns (state : State) (plan standard parameter argument body later captured rest query states receipts epochs answer : Term)
    (finished : PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"), encoded plan, encoded query]) state
      (encoded (.symbol "SearchComplete")))
    (empty : PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded query]) state (encoded (.symbol "LNil")))
    (installed : PureReturns runtime [] state
      (apply "gslt:ml:install" [encoded plan, encoded standard,
        encoded (doneRunner (clauseRequest parameter argument body later captured rest) query states receipts),
        encoded epochs, encoded (failureRowTerm parameter argument)]) state (encoded answer)) :
    PureReturns runtime [] state
      (apply "gslt:ml:service" [encoded plan, encoded standard,
        encoded (doneRunner (clauseRequest parameter argument body later captured rest) query states receipts), encoded epochs]) state
      (encoded answer) := by
  metta_call checked
  service_eval [finished, empty, installed] unfolding [doneRunner, clauseRequest, failureRowTerm, encodeList]

#print axioms match_service_returns
#print axioms clause_service_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFailureServiceExecution
