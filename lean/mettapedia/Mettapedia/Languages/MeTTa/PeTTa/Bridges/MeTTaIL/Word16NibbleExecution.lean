import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Word

/-! The shared hexadecimal helper's actual source rows encode and decode
all sixteen nibbles. Invalid constructors remain a separate refusal case.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource

def nibble (digit : Nat) : Term := .application "PApp" [.string ("R16Nibble" ++ toString digit), .symbol "LNil"]

private theorem nibble_selected (digit : Fin 16) :
    ((List.range 16).map (fun d => SpaceSemantics.Equation.mk "gslt:word16:nibble"
      [number d] (encoded (nibble d)))).filterMap (fun equation =>
        (SpaceSemantics.matchValue.matchValues [] equation.arguments [number digit.val]).map
          fun bindings => Control.evaluate bindings equation.body) = [.evaluate [] (encoded (nibble digit.val))] := by
  fin_cases digit <;> simp [List.range_succ, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    nibble, number, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem nibble_clauses (digit : Fin 16) :
    clauses wordLibrary.runtime "gslt:word16:nibble" [number digit.val] =
      [.evaluate [] (encoded (nibble digit.val))] := by
  rw [clauses_use_only_the_named_equations]
  rw [Library.owned_equations word_checked (by decide +kernel)]
  have rows : wordLibrary.source.equations.filter (fun row => row.head == "gslt:word16:nibble") =
      (List.range 16).map (fun digit => SpaceSemantics.Equation.mk "gslt:word16:nibble"
        [number digit] (encoded (nibble digit))) := by rfl
  rw [rows]
  exact nibble_selected digit

theorem nibble_data (state : State) (digit : Nat) :
    PureReturns wordLibrary.runtime [] state (encoded (nibble digit)) state (encoded (nibble digit)) := by
  have inert : (ioHead "PApp" || StdLib.known "PApp" || wordLibrary.runtime.equations.any (·.head == "PApp")) = false := by
    decide +kernel
  have template : PureData.Template wordLibrary.runtime (encoded (nibble digit)) := by
    apply PureData.Template.constructor "PApp" _ inert (by decide)
    intro item member
    simp only [CettaWireAtom.encode, CettaWireAtom.encodeMany, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with same | same <;> subst item
    · exact .grounded _
    · exact .symbol _
  have returned := PureData.template_return wordLibrary.runtime [] state _ template
  simpa [nibble, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList] using returned

theorem nibble_returns (state : State) (digit : Fin 16) :
    PureReturns wordLibrary.runtime [] state (apply "gslt:word16:nibble" [number digit.val]) state
      (encoded (nibble digit.val)) := by
  apply call_returns wordLibrary.runtime [] state state "gslt:word16:nibble" [number digit.val] _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns wordLibrary.runtime [] state state state (.function "gslt:word16:nibble")
    (number digit.val) (number digit.val) _ [] [] 0 (by decide +kernel) (number_returns _ _ _ _)
  apply authored_function_arguments_return wordLibrary.runtime [] [] state state "gslt:word16:nibble"
    [number digit.val] 1 _ _ (by decide) (by decide) (nibble_clauses digit)
  exact nibble_data state digit.val

private def valueRows : SpaceSemantics.Cases :=
  ((List.range 16).map fun digit => (encoded (nibble digit), encoded (.application "Some" [.natural digit]))) ++
    [(.var "bad", .symbol "None")]

private theorem value_body : wordLibrary.body "gslt:word16:nibble-value" =
    .expression [.symbol "case", .var "nibble", .expression (valueRows.map fun row => .expression [row.1, row.2])] := by rfl

private theorem value_selection (digit : Fin 16) : SpaceSemantics.selectCase
    (Library.bind ["nibble"] [encoded (nibble digit.val)]) (encoded (nibble digit.val)) valueRows =
      some (Library.bind ["nibble"] [encoded (nibble digit.val)], encoded (.application "Some" [.natural digit.val])) := by
  fin_cases digit <;> metta_select [valueRows, List.range_succ, nibble, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]

theorem nibble_value_returns (state : State) (digit : Fin 16) :
    PureReturns wordLibrary.runtime [] state (apply "gslt:word16:nibble-value" [encoded (nibble digit.val)]) state
      (encoded (.application "Some" [.natural digit.val])) := by
  apply Library.call word_checked (by decide +kernel) [] state state _ [encoded (nibble digit.val)] _
    (by metta_literal; rfl) rfl
  rw [value_body]
  metta_literal
  apply rows_case_returns _ _ _ state state state _ (encoded (nibble digit.val)) _ _ _ valueRows rfl
  · exact bound_returns _ _ _ (by rfl)
  · exact value_selection digit
  · apply data_returns _ _ _ _ _
    · change inertHead wordLibrary.runtime "Some" && true = true
      decide +kernel
    · simp [encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList]

theorem bad_nibble_returns (state : State) :
    PureReturns wordLibrary.runtime [] state (apply "gslt:word16:nibble-value" [encoded (nibble 16)]) state
      (encoded (.symbol "None")) := by
  apply Library.call word_checked (by decide +kernel) [] state state _ [encoded (nibble 16)] _
    (by metta_literal; rfl) rfl
  rw [value_body]
  metta_literal
  apply rows_case_returns _ _ _ state state state _ (encoded (nibble 16)) _ _ _ valueRows rfl
  · exact bound_returns _ _ _ (by rfl)
  · metta_select [valueRows, List.range_succ, nibble, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    exact ⟨rfl, rfl⟩
  · exact symbol_returns _ _ _ _

#print axioms nibble_returns
#print axioms nibble_value_returns
#print axioms bad_nibble_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.Word16NibbleExecution
