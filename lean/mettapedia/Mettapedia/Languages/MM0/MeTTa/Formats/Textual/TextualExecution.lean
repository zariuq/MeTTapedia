import Mettapedia.Languages.MM0.MeTTa.Program
import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualData
import Mettapedia.Languages.MM0.MeTTa.Formation.SortFormation

/-!
# Execution of the authored textual projection

The projection is quoted from its retained MeTTa file. Its source bodies
execute in the existing PeTTa semantics and retain the complete state.
The native parser and generated environment program are separate interfaces;
these laws concern projection of their constructor data.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.TextualExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SpaceSemantics (Program)
open Eval
open Effects (State boolean)
open Store (natural)
open scoped ProgramQuotation

def textualSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/textual.metta"
    sha256 "72794a8106b8052a1d1130c47b9058cf1a1480db94d1ddf7a26b4029764f4178"

def program : Program := MeTTa.program.append textualSource.program

private def flagEquation : SpaceSemantics.Equation :=
  textualSource.program.equations[2]'(by decide)

private def flagCases : SpaceSemantics.Cases :=
  match flagEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def flagEnvironment (value : Atom) : Subst := [("value", value)]

private theorem flag_unique :
    program.equations.filter (fun row => row.head == "mm0:text:flag") = [flagEquation] := by
  decide

private theorem flag_formals : flagEquation.arguments = [.var "value"] := by decide

private theorem flag_shape : flagEquation.body =
    .expression [.symbol "case", .var "value",
      .expression (flagCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem flag_cases : flagCases =
    [(.symbol "MM0ModifierAbsentV1", .expression [.symbol "Some", boolean false]),
     (.symbol "MM0ModifierPresentV1", .expression [.symbol "Some", boolean true]),
     (.var "bad", .symbol "None")] := by decide

private theorem some_returns (bindings : Subst) (state : State)
    (expression value : Atom)
    (computed : PureReturns program bindings state expression state value) :
    PureReturns program bindings state (.expression [.symbol "Some", expression]) state
      (.expression [.symbol "Some", value]) := by
  apply data_call_returns program bindings state state "Some" [expression] _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data
    (.symbol "Some") (.symbol "Some") _ [expression] [] 0 rfl
    (symbol_returns program bindings state "Some")
  exact evaluated_argument_returns program bindings state state state .data expression value _
    [] [.symbol "Some"] 1 rfl computed
    (data_arguments_values_return program bindings state [.symbol "Some", value] 2)

private def indexEquation : SpaceSemantics.Equation :=
  textualSource.program.equations[1]'(by decide)

private def indexCases : SpaceSemantics.Cases :=
  match indexEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def indexEnvironment (value : Atom) : Subst := [("value", value)]

private def successorBody : Atom := indexCases[1]'(by decide) |>.2

private def previousCases : SpaceSemantics.Cases :=
  match successorBody with
  | .expression [_, _, _, .expression [_, _, .expression rows]] => (readCases rows).getD []
  | _ => []

private theorem index_unique :
    program.equations.filter (fun row => row.head == "mm0:text:index") = [indexEquation] := by
  decide

private theorem index_formals : indexEquation.arguments = [.var "value"] := by decide

private theorem index_shape : indexEquation.body =
    .expression [.symbol "case", .var "value",
      .expression (indexCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem index_cases : indexCases =
    [(.symbol "NatZeroV1", .expression [.symbol "Some", natural 0]),
     (.expression [.symbol "NatSuccV1", .var "rest"], successorBody),
     (.var "bad", .symbol "None")] := by decide

private theorem successor_shape : successorBody =
    .expression [.symbol "let", .var "previous",
      .expression [.symbol "mm0:text:index", .var "rest"],
      .expression [.symbol "case", .var "previous",
        .expression (previousCases.map fun row => .expression [row.1, row.2])]] := by decide

private theorem previous_cases : previousCases =
    [(.expression [.symbol "Some", .var "index"],
       .expression [.symbol "Some", .expression [.symbol "+", .var "index", natural 1]]),
     (.var "bad", .symbol "None")] := by decide

private theorem index_call_returns (bindings : Subst) (state : State) (value answer : Atom)
    (name : String) (captured : applySubst bindings (.var name) = value)
    (body : PureReturns program (indexEnvironment value) state indexEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:index", .var name]) state
      answer := by
  apply authored_variable_call_returns program bindings (indexEnvironment value)
    state state "mm0:text:index" [name] indexEquation.body answer
    (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, index_unique]
  simp [captured, index_formals, indexEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem index_body_returns (state : State) (value : Nat) :
    PureReturns program (indexEnvironment (TextualData.indexValue value)) state
      indexEquation.body state (.expression [.symbol "Some", natural value]) := by
  induction value with
  | zero =>
      rw [index_shape]
      apply case_returns program _ (indexEnvironment (TextualData.indexValue 0))
        state state state (.var "value") (TextualData.indexValue 0)
        (.expression [.symbol "Some", natural 0]) _ _ indexCases (read_cases_encoded _)
      · simpa [indexEnvironment, applySubst, Subst.lookup] using
          variable_returns program (indexEnvironment (TextualData.indexValue 0)) state "value"
      · simp [index_cases, TextualData.indexValue, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · exact some_returns _ state (natural 0) (natural 0)
          (grounded_returns program _ state (.int 0))
  | succ value ih =>
      let outer := indexEnvironment (TextualData.indexValue (value + 1))
      let restBound : Subst := ("rest", TextualData.indexValue value) :: outer
      let previousBound : Subst := ("previous", .expression [.symbol "Some", natural value]) :: restBound
      let indexBound : Subst := ("index", natural value) :: previousBound
      rw [index_shape]
      apply case_returns program outer restBound state state state (.var "value")
        (TextualData.indexValue (value + 1)) successorBody _ _ indexCases (read_cases_encoded _)
      · simpa [outer, indexEnvironment, applySubst, Subst.lookup] using
          variable_returns program outer state "value"
      · simp [outer, restBound, indexEnvironment, index_cases, TextualData.indexValue,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · rw [successor_shape]
        apply let_returns program restBound previousBound state state state
          (.var "previous") _ _ (.expression [.symbol "Some", natural value]) _
        · exact index_call_returns restBound state (TextualData.indexValue value)
            (.expression [.symbol "Some", natural value]) "rest"
            (by simp [restBound, applySubst, Subst.lookup]) ih
        · simp [previousBound, restBound, outer, indexEnvironment, SpaceSemantics.matchValue,
            matchAtom, Subst.lookup]
        · apply case_returns program previousBound indexBound state state state (.var "previous")
            (.expression [.symbol "Some", natural value])
            (.expression [.symbol "Some", .expression [.symbol "+", .var "index", natural 1]])
            _ _ previousCases (read_cases_encoded _)
          · simpa [previousBound, applySubst, Subst.lookup] using
              variable_returns program previousBound state "previous"
          · simp [previous_cases, indexBound, previousBound, restBound, outer, indexEnvironment,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · apply some_returns indexBound state _ (natural (value + 1))
            apply native_binary_call_returns program indexBound state state state state "+"
              (.var "index") (natural 1) (natural value) (natural 1) (natural (value + 1))
              (by decide) (by decide) (by decide) (by decide)
            · simpa [indexBound, applySubst, Subst.lookup] using
                variable_returns program indexBound state "index"
            · exact grounded_returns program indexBound state (.int 1)
            · simp [StdLib.apply, natural]
            · decide

/-- Arbitrarily long unary source indices execute as the existing numeric IDs. -/
theorem index_captured_returns (bindings : Subst) (state : State) (value : Nat)
    (name : String)
    (captured : applySubst bindings (.var name) = TextualData.indexValue value) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:index", .var name]) state
      (.expression [.symbol "Some", natural value]) :=
  index_call_returns bindings state _ _ name captured (index_body_returns state value)

theorem decoded_index_returns (bindings : Subst) (state : State) (source : Atom)
    (value : Nat) (name : String) (captured : applySubst bindings (.var name) = source)
    (decoded : TextualData.decodeIndex source = some value) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:index", .var name]) state
      (.expression [.symbol "Some", natural value]) := by
  apply index_captured_returns bindings state value name
  exact captured.trans (TextualData.decodeIndex_reflects source value decoded)

theorem index_sufficient_fuel (bindings : Subst) (state : State) (value : Nat)
    (name : String)
    (captured : applySubst bindings (.var name) = TextualData.indexValue value) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings (.expression [.symbol "mm0:text:index", .var name]) } =
      .complete state [.expression [.symbol "Some", natural value]] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (index_captured_returns bindings state value name captured)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [.expression [.symbol "Some", natural value]] [] [] completed⟩

/-- A native number is not an authored unary source position. -/
theorem index_native_number_refused (bindings : Subst) (state : State) (value : Nat)
    (name : String) (captured : applySubst bindings (.var name) = natural value) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:index", .var name]) state
      (.symbol "None") := by
  apply index_call_returns bindings state (natural value) (.symbol "None") name captured
  rw [index_shape]
  let selected : Subst := ("bad", natural value) :: indexEnvironment (natural value)
  apply case_returns program _ selected state state state (.var "value") (natural value)
    (.symbol "None") _ _ indexCases (read_cases_encoded _)
  · simpa [indexEnvironment, applySubst, Subst.lookup] using
      variable_returns program (indexEnvironment (natural value)) state "value"
  · simp [selected, index_cases, indexEnvironment, natural,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · exact symbol_returns program selected state "None"

/-- Malformed source-position data stays distinct from a valid zero index. -/
theorem index_native_number_sufficient_fuel (bindings : Subst) (state : State) (value : Nat)
    (name : String) (captured : applySubst bindings (.var name) = natural value) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings (.expression [.symbol "mm0:text:index", .var name]) } =
      .complete state [.symbol "None"] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (index_native_number_refused bindings state value name captured)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [.symbol "None"] [] [] completed⟩

private theorem flag_body_returns (state : State) (value : Bool) :
    PureReturns program (flagEnvironment (TextualData.modifierValue value)) state
      flagEquation.body state (.expression [.symbol "Some", boolean value]) := by
  rw [flag_shape]
  apply case_returns program (flagEnvironment (TextualData.modifierValue value))
    (flagEnvironment (TextualData.modifierValue value)) state state state
    (.var "value") (TextualData.modifierValue value)
    (.expression [.symbol "Some", boolean value]) _ _ flagCases (read_cases_encoded _)
  · simpa [flagEnvironment, applySubst, Subst.lookup] using
      variable_returns program (flagEnvironment (TextualData.modifierValue value)) state "value"
  · cases value <;>
      simp [flag_cases, flagEnvironment, TextualData.modifierValue,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · exact some_returns _ state (boolean value) (boolean value)
      (grounded_returns program _ state (.bool value))

/-- The real source decodes a captured modifier without changing any store. -/
theorem flag_captured_returns (bindings : Subst) (state : State) (value : Bool)
    (name : String)
    (captured : applySubst bindings (.var name) = TextualData.modifierValue value) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:flag", .var name]) state
      (.expression [.symbol "Some", boolean value]) := by
  apply authored_variable_call_returns program bindings
    (flagEnvironment (TextualData.modifierValue value)) state state "mm0:text:flag"
    [name] flagEquation.body _ (by decide) (by decide) (by decide) _
    (flag_body_returns state value) (by decide)
  rw [clauses_use_only_the_named_equations, flag_unique]
  simp [captured, flag_formals, flagEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

theorem decoded_flag_returns (bindings : Subst) (state : State) (source : Atom)
    (value : Bool) (name : String) (captured : applySubst bindings (.var name) = source)
    (decoded : TextualData.decodeModifier source = some value) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:flag", .var name]) state
      (.expression [.symbol "Some", boolean value]) := by
  apply flag_captured_returns bindings state value name
  exact captured.trans (TextualData.decodeModifier_reflects source value decoded)

/-- Native booleans are not the frontend's presence/absence constructors. -/
theorem flag_native_boolean_refused (bindings : Subst) (state : State) (value : Bool)
    (name : String) (captured : applySubst bindings (.var name) = boolean value) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:flag", .var name]) state
      (.symbol "None") := by
  apply authored_variable_call_returns program bindings (flagEnvironment (boolean value))
    state state "mm0:text:flag" [name] flagEquation.body (.symbol "None")
    (by decide) (by decide) (by decide) _ _ (by decide)
  · rw [clauses_use_only_the_named_equations, flag_unique]
    simp [captured, flag_formals, flagEnvironment, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · rw [flag_shape]
    let selected : Subst := ("bad", boolean value) :: flagEnvironment (boolean value)
    apply case_returns program _ selected state state state (.var "value") (boolean value)
      (.symbol "None") _ _ flagCases (read_cases_encoded _)
    · simpa [flagEnvironment, applySubst, Subst.lookup] using
        variable_returns program (flagEnvironment (boolean value)) state "value"
    · simp [selected, flag_cases, flagEnvironment, boolean,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · exact symbol_returns program selected state "None"

theorem flag_sufficient_fuel (bindings : Subst) (state : State) (value : Bool)
    (name : String)
    (captured : applySubst bindings (.var name) = TextualData.modifierValue value) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings (.expression [.symbol "mm0:text:flag", .var name]) } =
      .complete state [.expression [.symbol "Some", boolean value]] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (flag_captured_returns bindings state value name captured)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [.expression [.symbol "Some", boolean value]] [] [] completed⟩

private def sortInfoEquation : SpaceSemantics.Equation :=
  textualSource.program.equations[3]'(by decide)

private def sortInfoEnvironment (info : Kernel.SortInfo) : Subst :=
  [("value", TextualData.modifiersValue info)]

private theorem sort_info_unique :
    program.equations.filter (fun row => row.head == "mm0:text:sort-info") = [sortInfoEquation] := by
  decide

private theorem sort_info_formals : sortInfoEquation.arguments = [.var "value"] := by decide

private def sortInfoCases : SpaceSemantics.Cases :=
  match sortInfoEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def modifierBody : Atom := sortInfoCases[0]'(by decide) |>.2

private def flagPairs : List Atom :=
  match modifierBody with
  | .expression [_, .expression pairs, _] => pairs
  | _ => []

private def modifierResult : Atom :=
  match modifierBody with
  | .expression [_, _, result] => result
  | _ => .symbol "None"

private def modifierNested : Atom := (nestedLets flagPairs modifierResult).getD (.symbol "None")

private def modifierCases : SpaceSemantics.Cases :=
  match modifierResult with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def sortFields (info : Kernel.SortInfo) : Subst :=
  [("free", TextualData.modifierValue info.free),
   ("provable", TextualData.modifierValue info.provable),
   ("strict", TextualData.modifierValue info.strict),
   ("pure", TextualData.modifierValue info.pure)] ++ sortInfoEnvironment info

private def someBool (value : Bool) : Atom := .expression [.symbol "Some", boolean value]

private def projectedFlags (info : Kernel.SortInfo) (bindings : Subst) : Subst :=
  [("freeFlag", boolean info.free), ("provableFlag", boolean info.provable),
   ("strictFlag", boolean info.strict), ("pureFlag", boolean info.pure)] ++ bindings

private theorem sort_info_shape : sortInfoEquation.body =
    .expression [.symbol "case", .var "value",
      .expression (sortInfoCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem modifier_shape : modifierBody =
    .expression [.symbol "let*", .expression flagPairs, modifierResult] := by decide

private theorem modifier_expanded : nestedLets flagPairs modifierResult = some modifierNested := by decide

private theorem modifier_nested : modifierNested =
    .expression [.symbol "let", .var "p", .expression [.symbol "mm0:text:flag", .var "pure"],
      .expression [.symbol "let", .var "s", .expression [.symbol "mm0:text:flag", .var "strict"],
        .expression [.symbol "let", .var "v", .expression [.symbol "mm0:text:flag", .var "provable"],
          .expression [.symbol "let", .var "f", .expression [.symbol "mm0:text:flag", .var "free"],
            modifierResult]]]] := by decide

private theorem modifier_result_shape : modifierResult =
    .expression [.symbol "case", .expression [.var "p", .var "s", .var "v", .var "f"],
      .expression (modifierCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem sort_info_cases : sortInfoCases =
    [(.expression [.symbol "MM0SortModifiersV1", .var "pure", .var "strict", .var "provable", .var "free"],
       modifierBody), (.var "bad", .symbol "None")] := by decide

private theorem modifier_cases : modifierCases =
    [(.expression [.expression [.symbol "Some", .var "pureFlag"],
                  .expression [.symbol "Some", .var "strictFlag"],
                  .expression [.symbol "Some", .var "provableFlag"],
                  .expression [.symbol "Some", .var "freeFlag"]],
      .expression [.symbol "Some", .expression [.symbol "MM0:L",
        .expression [.symbol "MM0:Sort", .var "pureFlag", .var "strictFlag", .var "provableFlag", .var "freeFlag"]]]),
     (.var "bad", .symbol "None")] := by decide

private theorem sort_info_body_returns (state : State) (info : Kernel.SortInfo) :
    PureReturns program (sortInfoEnvironment info) state sortInfoEquation.body state
      (.expression [.symbol "Some", SortFormation.sortValue info]) := by
  rw [sort_info_shape]
  apply case_returns program _ (sortFields info) state state state (.var "value")
    (TextualData.modifiersValue info) modifierBody _ _ sortInfoCases (read_cases_encoded _)
  · simpa [sortInfoEnvironment, applySubst, Subst.lookup] using
      variable_returns program (sortInfoEnvironment info) state "value"
  · simp [sort_info_cases, sortFields, sortInfoEnvironment, TextualData.modifiersValue,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · rw [modifier_shape]
    apply let_star_returns program (sortFields info) state state flagPairs modifierResult
      modifierNested _ modifier_expanded
    rw [modifier_nested]
    let p : Subst := ("p", someBool info.pure) :: sortFields info
    let s : Subst := ("s", someBool info.strict) :: p
    let v : Subst := ("v", someBool info.provable) :: s
    let f : Subst := ("f", someBool info.free) :: v
    apply let_returns program _ p state state state (.var "p") _ _ (someBool info.pure) _
    · exact flag_captured_returns _ state info.pure "pure"
        (by simp [sortFields, applySubst, Subst.lookup])
    · simp [p, sortFields, sortInfoEnvironment, SpaceSemantics.matchBinding,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · apply let_returns program p s state state state (.var "s") _ _ (someBool info.strict) _
      · exact flag_captured_returns p state info.strict "strict"
          (by simp [p, sortFields, applySubst, Subst.lookup])
      · simp [s, p, sortFields, sortInfoEnvironment, SpaceSemantics.matchBinding,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · apply let_returns program s v state state state (.var "v") _ _ (someBool info.provable) _
        · exact flag_captured_returns s state info.provable "provable"
            (by simp [s, p, sortFields, applySubst, Subst.lookup])
        · simp [v, s, p, sortFields, sortInfoEnvironment, SpaceSemantics.matchBinding,
            SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · apply let_returns program v f state state state (.var "f") _ _ (someBool info.free) _
          · exact flag_captured_returns v state info.free "free"
              (by simp [v, s, p, sortFields, applySubst, Subst.lookup])
          · simp [f, v, s, p, sortFields, sortInfoEnvironment, SpaceSemantics.matchBinding,
              SpaceSemantics.matchValue, matchAtom, Subst.lookup]
          · rw [modifier_result_shape]
            apply case_returns program f (projectedFlags info f) state state state _
              (.expression [someBool info.pure, someBool info.strict, someBool info.provable, someBool info.free])
              (.expression [.symbol "Some", .expression [.symbol "MM0:L",
                .expression [.symbol "MM0:Sort", .var "pureFlag", .var "strictFlag", .var "provableFlag", .var "freeFlag"]]])
              _ _ modifierCases (read_cases_encoded _)
            · simpa [f, v, s, p, applySubst, Subst.lookup] using
                tuple_variables_return program f state ["p", "s", "v", "f"]
            · simp [modifier_cases, projectedFlags, f, v, s, p, sortFields, sortInfoEnvironment, someBool,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · apply some_returns _ state _ (SortFormation.sortValue info)
              apply unary_constructor_of_returns program _ state state "MM0:L" _ _ (by decide) (by decide)
              simpa [SortFormation.sortValue, ListAccess.listValue, projectedFlags, applySubst, Subst.lookup] using
                constructor_variables_return program (projectedFlags info f) state "MM0:Sort"
                  ["pureFlag", "strictFlag", "provableFlag", "freeFlag"] (by decide) (by decide)

/-- All sixteen sort profiles produce the existing kernel sort encoding. -/
theorem sort_info_captured_returns (bindings : Subst) (state : State) (info : Kernel.SortInfo)
    (name : String)
    (captured : applySubst bindings (.var name) = TextualData.modifiersValue info) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:sort-info", .var name]) state
      (.expression [.symbol "Some", SortFormation.sortValue info]) := by
  apply authored_variable_call_returns program bindings (sortInfoEnvironment info)
    state state "mm0:text:sort-info" [name] sortInfoEquation.body _
    (by decide) (by decide) (by decide) _ (sort_info_body_returns state info) (by decide)
  rw [clauses_use_only_the_named_equations, sort_info_unique]
  simp [captured, sort_info_formals, sortInfoEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

theorem decoded_sort_info_returns (bindings : Subst) (state : State) (source : Atom)
    (info : Kernel.SortInfo) (name : String) (captured : applySubst bindings (.var name) = source)
    (decoded : TextualData.decodeModifiers source = some info) :
    PureReturns program bindings state (.expression [.symbol "mm0:text:sort-info", .var name]) state
      (.expression [.symbol "Some", SortFormation.sortValue info]) := by
  apply sort_info_captured_returns bindings state info name
  exact captured.trans (TextualData.decodeModifiers_reflects source info decoded)

theorem sort_info_sufficient_fuel (bindings : Subst) (state : State) (info : Kernel.SortInfo)
    (name : String)
    (captured : applySubst bindings (.var name) = TextualData.modifiersValue info) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state, control := .evaluate bindings (.expression [.symbol "mm0:text:sort-info", .var name]) } =
      .complete state [.expression [.symbol "Some", SortFormation.sortValue info]] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (sort_info_captured_returns bindings state info name captured)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [.expression [.symbol "Some", SortFormation.sortValue info]] [] [] completed⟩

end Mettapedia.Languages.MM0.MeTTa.TextualExecution
