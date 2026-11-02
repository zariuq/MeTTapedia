import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlListLength

/-! Structural comparison composes child computations at actual source
positions. An equal prefix continues; strict orders, refusal and functional
faults stop without inspecting a later field.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareStructure

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution

theorem cons_returns (state : State) (head tail other rest : OCaml.Value) (first later : OCaml.Compared)
    (headReturned : PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm head), encoded (valueTerm other)]) state
      (encoded (view first)))
    (tailReturned : PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm tail), encoded (valueTerm rest)]) state
      (encoded (view later))) :
    PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm (.cons head tail)), encoded (valueTerm (.cons other rest))]) state
      (encoded (view (OCaml.continueCompared first later))) := by
  cases first with
  | error error =>
    metta_call checked
    ml_compare_eval [headReturned, tailReturned] unfolding [value_cons, encodeList, view, OCaml.continueCompared]
  | ok result =>
    cases result with
    | error error =>
      metta_call checked
      ml_compare_eval [headReturned, tailReturned] unfolding [value_cons, encodeList, view, OCaml.continueCompared]
    | ok order =>
      cases order <;> metta_call checked <;>
        ml_compare_eval [headReturned, tailReturned] unfolding [value_cons, encodeList, view, ordering, OCaml.continueCompared]

theorem fields_cons_returns (state : State) (head other : OCaml.Value) (tail rest : List OCaml.Value) (first later : OCaml.Compared)
    (headReturned : PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm head), encoded (valueTerm other)]) state
      (encoded (view first)))
    (tailReturned : PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm tail), encoded (fieldsTerm rest)]) state
      (encoded (view later))) :
    PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm (head :: tail)), encoded (fieldsTerm (other :: rest))]) state
      (encoded (view (OCaml.continueCompared first later))) := by
  cases first with
  | error error =>
    metta_call checked
    ml_compare_eval [headReturned, tailReturned] unfolding [fields_cons, encodeList, view, OCaml.continueCompared]
  | ok result =>
    cases result with
    | error error =>
      metta_call checked
      ml_compare_eval [headReturned, tailReturned] unfolding [fields_cons, encodeList, view, OCaml.continueCompared]
    | ok order =>
      cases order <;> metta_call checked <;>
        ml_compare_eval [headReturned, tailReturned] unfolding [fields_cons, encodeList, view, ordering, OCaml.continueCompared]

theorem fields_nil_returns (state : State) :
    PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm []), encoded (fieldsTerm [])]) state
      (encoded (.symbol "MlEqualOrder")) := by
  metta_call checked
  ml_compare_eval [] unfolding [fields_nil]

theorem fields_empty_cons_returns (state : State) (head : OCaml.Value) (tail : List OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm []), encoded (fieldsTerm (head :: tail))]) state
      (encoded (.symbol "MlLessOrder")) := by
  metta_call checked
  ml_compare_eval [] unfolding [fields_nil, fields_cons, encodeList]

theorem fields_cons_empty_returns (state : State) (head : OCaml.Value) (tail : List OCaml.Value) :
    PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm (head :: tail)), encoded (fieldsTerm [])]) state
      (encoded (.symbol "MlGreaterOrder")) := by
  metta_call checked
  ml_compare_eval [] unfolding [fields_nil, fields_cons, encodeList]

theorem tuple_returns (state : State) (left right : List OCaml.Value)
    (fieldsReturned : PureReturns runtime [] state (apply "gslt:ml:compare-fields" [encoded (fieldsTerm left), encoded (fieldsTerm right)]) state
      (encoded (view (OCaml.compareFields left right)))) :
    PureReturns runtime [] state (apply "gslt:ml:compare" [encoded (valueTerm (.tuple left)), encoded (valueTerm (.tuple right))]) state
      (encoded (view (OCaml.compareValue (.tuple left) (.tuple right)))) := by
  have first := OCamlValuesExecution.values_returns state left
  have second := OCamlValuesExecution.values_returns state right
  have firstLength := OCamlListLength.fields_length_returns state left
  have secondLength := OCamlListLength.fields_length_returns state right
  rw [OCaml.compare_tuple]
  by_cases same : left.length = right.length
  · simp only [same, if_true]
    metta_call checked
    ml_compare_eval [first, second, firstLength, secondLength, fieldsReturned] unfolding [value_tuple, encodeList, same]
  · simp only [same, if_false, view]
    metta_call checked
    ml_compare_eval [first, second, firstLength, secondLength, fieldsReturned] unfolding [value_tuple, encodeList, same]

#print axioms cons_returns
#print axioms fields_cons_returns
#print axioms tuple_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareStructure
