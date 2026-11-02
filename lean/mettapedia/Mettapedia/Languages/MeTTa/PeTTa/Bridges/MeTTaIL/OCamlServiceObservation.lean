import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledServiceExecution

/-! Actual successful service dispatch has one exact operational result:
the target evaluator cannot complete that call with a different state,
answer, input or output history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceObservation

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlFailureServiceExecution
open DeclarativeSpec

theorem match_service_observation (state : State) (plan standard parameter argument body captured rest query states receipts epochs answer : Term)
    (finished : PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"), encoded plan, encoded query]) state
      (encoded (.symbol "SearchComplete")))
    (empty : PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded query]) state (encoded (.symbol "LNil")))
    (installed : PureReturns runtime [] state
      (apply "gslt:ml:install" [encoded plan, encoded standard,
        encoded (doneRunner (matchRequest parameter argument body captured rest) query states receipts),
        encoded epochs, encoded (failureRowTerm parameter argument)]) state (encoded answer))
    (after : State) (answers input output : List Atom) :
    Runs runtime {state := state, control := (.evaluate []
      (apply "gslt:ml:service" [encoded plan, encoded standard,
        encoded (doneRunner (matchRequest parameter argument body captured rest) query states receipts), encoded epochs]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded answer] ∧ input = [] ∧ output = [] := by
  exact pure_returns_derivation_iff runtime [] state state _ (encoded answer)
    (match_service_returns state plan standard parameter argument body captured rest query states receipts epochs answer
      finished empty installed) after answers input output

#print axioms match_service_observation

theorem clause_service_observation (state : State) (plan standard parameter argument body later captured rest query states receipts epochs answer : Term)
    (finished : PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"), encoded plan, encoded query]) state
      (encoded (.symbol "SearchComplete")))
    (empty : PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded query]) state (encoded (.symbol "LNil")))
    (installed : PureReturns runtime [] state
      (apply "gslt:ml:install" [encoded plan, encoded standard,
        encoded (doneRunner (clauseRequest parameter argument body later captured rest) query states receipts),
        encoded epochs, encoded (failureRowTerm parameter argument)]) state (encoded answer))
    (after : State) (answers input output : List Atom) :
    Runs runtime {state := state, control := (.evaluate []
      (apply "gslt:ml:service" [encoded plan, encoded standard,
        encoded (doneRunner (clauseRequest parameter argument body later captured rest) query states receipts), encoded epochs]))}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded answer] ∧ input = [] ∧ output = [] := by
  exact pure_returns_derivation_iff runtime [] state state _ (encoded answer)
    (clause_service_returns state plan standard parameter argument body later captured rest query states receipts epochs answer
      finished empty installed) after answers input output

#print axioms clause_service_observation

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceObservation
