import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire

/-! The common comparator's fallback and functional-right cases depend
only on the outer value shapes, preserving the encoded fields unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareShapes

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire

def scalarOrCompound (name : String) : Prop :=
  name = "MlInteger" ∨ name = "MlFalse" ∨ name = "MlTrue" ∨ name = "MlUnit" ∨
  name = "MlNil" ∨ name = "MlCons" ∨ name = "MlTuple" ∨ name = "MlVariant" ∨ name = "MlString"

def rows : List Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  match library.body "gslt:ml:compare" with
  | .expression [.symbol "case", _, .expression rows] => rows
  | _ => []

def cases : SpaceSemantics.Cases := (readCases rows).getD []

theorem body_exact : library.body "gslt:ml:compare" = apply "case"
    [apply "MlComparePair" [.var "left", .var "right"], .expression rows] := by metta_literal; rfl

theorem cases_exact : readCases rows = some cases := by rfl

private theorem body_returns (state : State) (left right : String) (first second : Term)
    (selection : ∃ selected, SpaceSemantics.selectCase
      (Library.bind ["left", "right"] [encoded (.application "PApp" [.string left, first]), encoded (.application "PApp" [.string right, second])])
      (encoded (.application "MlComparePair" [.application "PApp" [.string left, first], .application "PApp" [.string right, second]])) cases =
        some (selected, .symbol "MlIncomparable")) :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (.application "PApp" [.string left, first]), encoded (.application "PApp" [.string right, second])]) state
      (encoded (.symbol "MlIncomparable")) := by
  apply Library.call checked (by decide +kernel) [] state state _ _ _ (by metta_literal; rfl) rfl
  have formals : library.formals "gslt:ml:compare" = ["left", "right"] := by metta_literal; rfl
  simp only [List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode, formals]
  rw [body_exact]
  obtain ⟨selected, selectedRow⟩ := selection
  apply rows_case_returns _ _ selected _ _ _ _ _ _ _ rows cases cases_exact
  · metta_eval with checked
  · convert selectedRow using 1
    simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · exact symbol_returns _ _ _ _

theorem different_returns (state : State) (left right : String) (first second : Term)
    (notClosureLeft : left ≠ "MlClosure") (notClosureRight : right ≠ "MlClosure")
    (leftShape : scalarOrCompound left) (rightShape : scalarOrCompound right)
    (different : left ≠ right)
    (notNilCons : left ≠ "MlNil" ∨ right ≠ "MlCons")
    (notConsNil : left ≠ "MlCons" ∨ right ≠ "MlNil")
    (notFalseTrue : left ≠ "MlFalse" ∨ right ≠ "MlTrue")
    (notTrueFalse : left ≠ "MlTrue" ∨ right ≠ "MlFalse") :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (.application "PApp" [.string left, first]), encoded (.application "PApp" [.string right, second])]) state
      (encoded (.symbol "MlIncomparable")) := by
  apply body_returns
  refine ⟨("bad", encoded (.application "MlComparePair" [.application "PApp" [.string left, first],
    .application "PApp" [.string right, second]])) :: Library.bind ["left", "right"]
      [encoded (.application "PApp" [.string left, first]), encoded (.application "PApp" [.string right, second])], ?_⟩
  rcases leftShape with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases rightShape with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try contradiction
  all_goals
    unfold cases rows
    metta_literal
    simp [Eval.readCases, Option.getD, Option.map, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue_literal (.symbol _),
      SpaceSemantics.matchValue_literal (.grounded _),
      SpaceSemantics.matchValue_expression_of_not_cons, SpaceSemantics.matchValue.matchValues,
      OCamlCompareWire.variable_match, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
      Library.bind, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem functional_right_returns (state : State) (left : String) (first second : Term)
    (notClosure : left ≠ "MlClosure") (leftShape : scalarOrCompound left) :
    PureReturns runtime [] state (apply "gslt:ml:compare"
      [encoded (.application "PApp" [.string left, first]), encoded (.application "PApp" [.string "MlClosure", second])]) state
      (encoded (.symbol "MlFunctionalOrder")) := by
  metta_call checked
  rcases leftShape with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals ml_compare_eval [] unfolding []

#print axioms different_returns
#print axioms functional_right_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareShapes
