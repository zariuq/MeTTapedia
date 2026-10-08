import Mettapedia.Languages.MM0.MeTTa.Kernel.Dependencies
import Mettapedia.Languages.MM0.MeTTa.Kernel.SubstitutionEntries

/-!
# Dependency matrix traversal in the retained MM0 source

Every bound-variable replacement is compared with all substitution entries,
including earlier ones. Source traversals retain order and short-circuit on
refusal. They leave the store unchanged and compute the independent kernel's
pair and row checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.DependencyMatrix

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Context Preterm)
open Store (natural)
open ListAccess (viewValue)
open SubstitutionEntries (entryValue entriesValue)

private def pairsEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 48)[47]'(by decide)
private def pairsViewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 49)[48]'(by decide)
private def pairsNextEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 50)[49]'(by decide)
private def rowEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 51)[50]'(by decide)
private def rowsEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 52)[51]'(by decide)
private def rowsViewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 53)[52]'(by decide)
private def rowsNextEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 54)[53]'(by decide)

private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def pairsCases := sourceCases pairsViewEquation.body
private def pairsNextCases := sourceCases pairsNextEquation.body
private def pairsConsBody : Atom := (pairsCases[1]'(by decide)).2
private def rowCases := sourceCases rowEquation.body
private def rowsCases := sourceCases rowsViewEquation.body
private def rowsNextCases := sourceCases rowsNextEquation.body
private def rowsConsBody : Atom := (rowsCases[1]'(by decide)).2

private def pairsEnvironment (target : Context) (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry) : Subst :=
  [("entries", entriesValue entries), ("target-bound", natural targetBound),
    ("formal-bound", natural formalBound), ("target", Data.context target)]
private def pairsViewEnvironment (target : Context) (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry) : Subst :=
  [("target-bound", natural targetBound), ("formal-bound", natural formalBound),
    ("target", Data.context target), ("valueInput", viewValue (entries.map entryValue))]
private def pairsNextEnvironment (answer : Bool) (target : Context) (formalBound targetBound : Nat)
    (entries : List Kernel.Substitution.Entry) : Subst :=
  [("rest", entriesValue entries), ("target-bound", natural targetBound),
    ("formal-bound", natural formalBound), ("target", Data.context target), ("conditionInput", boolean answer)]
private def rowEnvironment (target : Context) (allEntries : List Kernel.Substitution.Entry) (entry : Kernel.Substitution.Entry) : Subst :=
  [("valueInput", entryValue entry), ("all", entriesValue allEntries), ("target", Data.context target)]
private def rowsEnvironment (target : Context) (allEntries entries : List Kernel.Substitution.Entry) : Subst :=
  [("entries", entriesValue entries), ("all", entriesValue allEntries), ("target", Data.context target)]
private def rowsViewEnvironment (target : Context) (allEntries entries : List Kernel.Substitution.Entry) : Subst :=
  [("all", entriesValue allEntries), ("target", Data.context target), ("valueInput", viewValue (entries.map entryValue))]
private def rowsNextEnvironment (answer : Bool) (target : Context) (allEntries entries : List Kernel.Substitution.Entry) : Subst :=
  [("rest", entriesValue entries), ("all", entriesValue allEntries), ("target", Data.context target), ("conditionInput", boolean answer)]

private theorem pairs_unique : program.equations.filter (fun e => e.head == "mm0:check-pairs") = [pairsEquation] := by decide
private theorem pairs_view_unique : program.equations.filter (fun e => e.head == "mm0:pairs-view") = [pairsViewEquation] := by decide
private theorem pairs_next_unique : program.equations.filter (fun e => e.head == "mm0:pairs-next") = [pairsNextEquation] := by decide
private theorem row_unique : program.equations.filter (fun e => e.head == "mm0:check-row") = [rowEquation] := by decide
private theorem rows_unique : program.equations.filter (fun e => e.head == "mm0:check-rows") = [rowsEquation] := by decide
private theorem rows_view_unique : program.equations.filter (fun e => e.head == "mm0:rows-view") = [rowsViewEquation] := by decide
private theorem rows_next_unique : program.equations.filter (fun e => e.head == "mm0:rows-next") = [rowsNextEquation] := by decide
private theorem pairs_formals : pairsEquation.arguments = [.var "target", .var "formal-bound", .var "target-bound", .var "entries"] := by decide
private theorem pairs_view_formals : pairsViewEquation.arguments = [.var "valueInput", .var "target", .var "formal-bound", .var "target-bound"] := by decide
private theorem pairs_next_formals : pairsNextEquation.arguments = [.var "conditionInput", .var "target", .var "formal-bound", .var "target-bound", .var "rest"] := by decide
private theorem row_formals : rowEquation.arguments = [.var "target", .var "all", .var "valueInput"] := by decide
private theorem rows_formals : rowsEquation.arguments = [.var "target", .var "all", .var "entries"] := by decide
private theorem rows_view_formals : rowsViewEquation.arguments = [.var "valueInput", .var "target", .var "all"] := by decide
private theorem rows_next_formals : rowsNextEquation.arguments = [.var "conditionInput", .var "target", .var "all", .var "rest"] := by decide

private theorem pairs_body_shape : pairsEquation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "entries"],
      .expression [.symbol "mm0:pairs-view", .var "view", .var "target", .var "formal-bound", .var "target-bound"]] := by decide
private theorem pairs_view_body_shape : pairsViewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (pairsCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem pairs_cases_shape : pairsCases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .expression [.symbol "MM0:Entry", .var "binder", .var "expression", .var "position"], .var "rest"], pairsConsBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem pairs_cons_body_shape : pairsConsBody =
    .expression [.symbol "let", .var "checkPairResult",
      .expression [.symbol "mm0:check-pair", .var "target", .var "formal-bound", .var "target-bound", .var "binder", .var "position", .var "expression"],
      .expression [.symbol "mm0:pairs-next", .var "checkPairResult", .var "target", .var "formal-bound", .var "target-bound", .var "rest"]] := by decide
private theorem pairs_next_body_shape : pairsNextEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (pairsNextCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem pairs_next_cases_shape : pairsNextCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:check-pairs", .var "target", .var "formal-bound", .var "target-bound", .var "rest"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem pairs_clause (target : Context) (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:check-pairs" [Data.context target, natural formalBound, natural targetBound, entriesValue entries] =
      [.evaluate (pairsEnvironment target formalBound targetBound entries) pairsEquation.body] := by
  rw [clauses_use_only_the_named_equations, pairs_unique]
  simp [pairs_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, pairsEnvironment]
private theorem pairs_view_clause (target : Context) (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:pairs-view" [viewValue (entries.map entryValue), Data.context target, natural formalBound, natural targetBound] =
      [.evaluate (pairsViewEnvironment target formalBound targetBound entries) pairsViewEquation.body] := by
  rw [clauses_use_only_the_named_equations, pairs_view_unique]
  simp [pairs_view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, pairsViewEnvironment]
private theorem pairs_next_clause (answer : Bool) (target : Context) (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:pairs-next" [boolean answer, Data.context target, natural formalBound, natural targetBound, entriesValue entries] =
      [.evaluate (pairsNextEnvironment answer target formalBound targetBound entries) pairsNextEquation.body] := by
  rw [clauses_use_only_the_named_equations, pairs_next_unique]
  simp [pairs_next_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, pairsNextEnvironment]

private theorem pairs_call_from_body (bindings : Subst) (state : State) (target : Context)
    (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry)
    (targetName formalBoundName targetBoundName entriesName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedFormalBound : applySubst bindings (.var formalBoundName) = natural formalBound)
    (capturedTargetBound : applySubst bindings (.var targetBoundName) = natural targetBound)
    (capturedEntries : applySubst bindings (.var entriesName) = entriesValue entries)
    (computed : PureReturns program (pairsEnvironment target formalBound targetBound entries) state pairsEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkPair target formalBound targetBound)))) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:check-pairs", .var targetName, .var formalBoundName, .var targetBoundName, .var entriesName]) state
      (boolean (entries.all (Kernel.Substitution.checkPair target formalBound targetBound))) := by
  apply authored_variable_call_returns program bindings (pairsEnvironment target formalBound targetBound entries) state state
    "mm0:check-pairs" [targetName, formalBoundName, targetBoundName, entriesName] pairsEquation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTarget, capturedFormalBound, capturedTargetBound, capturedEntries] using pairs_clause target formalBound targetBound entries

private theorem pairs_next_returns (state : State) (answer : Bool) (target : Context)
    (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry)
    (computed : PureReturns program (pairsEnvironment target formalBound targetBound entries) state pairsEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkPair target formalBound targetBound)))) :
    PureReturns program (pairsNextEnvironment answer target formalBound targetBound entries) state pairsNextEquation.body state
      (boolean (answer && entries.all (Kernel.Substitution.checkPair target formalBound targetBound))) := by
  rw [pairs_next_body_shape]
  cases answer with
  | false =>
      let bindings := pairsNextEnvironment false target formalBound targetBound entries
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (boolean false)
        _ _ pairsNextCases (read_cases_encoded pairsNextCases)
      · simpa [bindings, pairsNextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [pairs_next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      let bindings := pairsNextEnvironment true target formalBound targetBound entries
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        (.expression [.symbol "mm0:check-pairs", .var "target", .var "formal-bound", .var "target-bound", .var "rest"])
        _ _ pairsNextCases (read_cases_encoded pairsNextCases)
      · simpa [bindings, pairsNextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [pairs_next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact pairs_call_from_body bindings state target formalBound targetBound entries "target" "formal-bound" "target-bound" "rest" rfl rfl rfl rfl computed

theorem pairs_body_returns (state : State) (target : Context) (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry) :
    PureReturns program (pairsEnvironment target formalBound targetBound entries) state pairsEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkPair target formalBound targetBound))) := by
  induction entries with
  | nil =>
      rw [pairs_body_shape]
      let bindings := pairsEnvironment target formalBound targetBound []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "entries" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, pairsEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (pairsViewEnvironment target formalBound targetBound []) state state
          "mm0:pairs-view" ["view", "target", "formal-bound", "target-bound"] pairsViewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, pairsEnvironment, applySubst, Subst.lookup] using pairs_view_clause target formalBound targetBound []
        · rw [pairs_view_body_shape]
          let callee := pairsViewEnvironment target formalBound targetBound []
          apply case_returns program callee callee state state state (.var "valueInput") (viewValue []) (boolean true)
            _ _ pairsCases (read_cases_encoded pairsCases)
          · simpa [callee, pairsViewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [pairs_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · exact grounded_returns program callee state (.bool true)
  | cons entry entries ih =>
      rcases entry with ⟨⟨binder, expression⟩, position⟩
      rw [pairs_body_shape]
      let bindings := pairsEnvironment target formalBound targetBound (((binder, expression), position) :: entries)
      let viewed := ("view", viewValue ((((binder, expression), position) :: entries).map entryValue)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((((binder, expression), position) :: entries).map entryValue)) _
      · exact ListAccess.view_captured_returns bindings state "entries" _ rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, pairsEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (pairsViewEnvironment target formalBound targetBound (((binder, expression), position) :: entries)) state state
          "mm0:pairs-view" ["view", "target", "formal-bound", "target-bound"] pairsViewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, pairsEnvironment, applySubst, Subst.lookup] using pairs_view_clause target formalBound targetBound (((binder, expression), position) :: entries)
        · rw [pairs_view_body_shape]
          let callee := pairsViewEnvironment target formalBound targetBound (((binder, expression), position) :: entries)
          let bound := ("rest", entriesValue entries) :: ("position", natural position) :: ("expression", Data.preterm expression) ::
            ("binder", Data.binder binder) :: callee
          apply case_returns program callee bound state state state (.var "valueInput")
            (viewValue ((((binder, expression), position) :: entries).map entryValue)) pairsConsBody
            _ _ pairsCases (read_cases_encoded pairsCases)
          · simpa [callee, pairsViewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [pairs_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, entryValue, entriesValue, viewValue, bound, callee, pairsViewEnvironment, Subst.lookup]
          · rw [pairs_cons_body_shape]
            let answer := Kernel.Substitution.checkPair target formalBound targetBound ((binder, expression), position)
            let checked := ("checkPairResult", boolean answer) :: bound
            apply let_returns program bound checked state state state (.var "checkPairResult") _ _ (boolean answer) _
            · exact Dependencies.pair_captured_returns bound state target formalBound targetBound binder position expression
                "target" "formal-bound" "target-bound" "binder" "position" "expression" rfl rfl rfl rfl rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, callee, pairsViewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program checked (pairsNextEnvironment answer target formalBound targetBound entries) state state
                "mm0:pairs-next" ["checkPairResult", "target", "formal-bound", "target-bound", "rest"] pairsNextEquation.body _
                (by decide) (by decide) (by decide) _ (pairs_next_returns state answer target formalBound targetBound entries ih) (by decide)
              simpa [checked, bound, callee, pairsViewEnvironment, applySubst, Subst.lookup] using pairs_next_clause answer target formalBound targetBound entries

theorem pairs_captured_returns (bindings : Subst) (state : State) (target : Context)
    (formalBound targetBound : Nat) (entries : List Kernel.Substitution.Entry)
    (targetName formalBoundName targetBoundName entriesName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedFormalBound : applySubst bindings (.var formalBoundName) = natural formalBound)
    (capturedTargetBound : applySubst bindings (.var targetBoundName) = natural targetBound)
    (capturedEntries : applySubst bindings (.var entriesName) = entriesValue entries) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:check-pairs", .var targetName, .var formalBoundName, .var targetBoundName, .var entriesName]) state
      (boolean (entries.all (Kernel.Substitution.checkPair target formalBound targetBound))) :=
  pairs_call_from_body bindings state target formalBound targetBound entries targetName formalBoundName targetBoundName entriesName
    capturedTarget capturedFormalBound capturedTargetBound capturedEntries (pairs_body_returns state target formalBound targetBound entries)

private theorem row_body_shape : rowEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (rowCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem row_cases_shape : rowCases = [
    (.expression [.symbol "MM0:Entry", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
      .expression [.symbol "MM0:Var", .var "image"], .var "position"],
      .expression [.symbol "mm0:check-pairs", .var "target", .var "position", .var "image", .var "all"]),
    (.expression [.symbol "MM0:Entry", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
      .expression [.symbol "MM0:Term", .var "symbol"], .var "position"], boolean true),
    (.expression [.symbol "MM0:Entry", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
      .expression [.symbol "MM0:App", .var "function", .var "argument"], .var "position"], boolean true),
    (.expression [.symbol "MM0:Entry", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]],
      .var "expression", .var "position"], boolean true),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem row_clause (target : Context) (allEntries : List Kernel.Substitution.Entry) (entry : Kernel.Substitution.Entry) :
    clauses program "mm0:check-row" [Data.context target, entriesValue allEntries, entryValue entry] =
      [.evaluate (rowEnvironment target allEntries entry) rowEquation.body] := by
  rw [clauses_use_only_the_named_equations, row_unique]
  simp [row_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, rowEnvironment]

theorem row_body_returns (state : State) (target : Context) (allEntries : List Kernel.Substitution.Entry) (entry : Kernel.Substitution.Entry) :
    PureReturns program (rowEnvironment target allEntries entry) state rowEquation.body state
      (boolean (Kernel.Substitution.checkRow target allEntries entry)) := by
  rcases entry with ⟨⟨binder, expression⟩, position⟩
  rw [row_body_shape]
  cases binder with
  | regular sort dependencies =>
      let bindings := rowEnvironment target allEntries ((.regular sort dependencies, expression), position)
      let bound := ("position", natural position) :: ("expression", Data.preterm expression) ::
        ("dependencies", Data.dependencies dependencies) :: ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (entryValue ((.regular sort dependencies, expression), position)) (boolean true) _ _ rowCases (read_cases_encoded rowCases)
      · simpa [bindings, rowEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
      · simp [row_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, entryValue, Data.binder, ListAccess.listValue, bound, bindings, rowEnvironment, Subst.lookup]
      · exact grounded_returns program bound state (.bool true)
  | bound sort =>
      cases expression with
      | var image =>
          let bindings := rowEnvironment target allEntries ((.bound sort, .var image), position)
          let bound := ("position", natural position) :: ("image", natural image) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (entryValue ((.bound sort, .var image), position))
            (.expression [.symbol "mm0:check-pairs", .var "target", .var "position", .var "image", .var "all"])
            _ _ rowCases (read_cases_encoded rowCases)
          · simpa [bindings, rowEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
          · simp [row_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, entryValue, Data.binder, Data.preterm, ListAccess.listValue, bound, bindings, rowEnvironment, Subst.lookup]
          · exact pairs_captured_returns bound state target position image allEntries "target" "position" "image" "all" rfl rfl rfl rfl
      | term symbol =>
          let bindings := rowEnvironment target allEntries ((.bound sort, .term symbol), position)
          let bound := ("position", natural position) :: ("symbol", natural symbol) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (entryValue ((.bound sort, .term symbol), position)) (boolean true) _ _ rowCases (read_cases_encoded rowCases)
          · simpa [bindings, rowEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
          · simp [row_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, entryValue, Data.binder, Data.preterm, ListAccess.listValue, bound, bindings, rowEnvironment, Subst.lookup]
          · exact grounded_returns program bound state (.bool true)
      | app function argument =>
          let bindings := rowEnvironment target allEntries ((.bound sort, .app function argument), position)
          let bound := ("position", natural position) :: ("argument", Data.preterm argument) ::
            ("function", Data.preterm function) :: ("sort", natural sort) :: bindings
          apply case_returns program bindings bound state state state (.var "valueInput")
            (entryValue ((.bound sort, .app function argument), position)) (boolean true) _ _ rowCases (read_cases_encoded rowCases)
          · simpa [bindings, rowEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
          · simp [row_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, entryValue, Data.binder, Data.preterm, ListAccess.listValue, bound, bindings, rowEnvironment, Subst.lookup]
          · exact grounded_returns program bound state (.bool true)

theorem row_captured_returns (bindings : Subst) (state : State) (target : Context)
    (allEntries : List Kernel.Substitution.Entry) (entry : Kernel.Substitution.Entry) (targetName allName entryName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedAll : applySubst bindings (.var allName) = entriesValue allEntries)
    (capturedEntry : applySubst bindings (.var entryName) = entryValue entry) :
    PureReturns program bindings state (.expression [.symbol "mm0:check-row", .var targetName, .var allName, .var entryName]) state
      (boolean (Kernel.Substitution.checkRow target allEntries entry)) := by
  apply authored_variable_call_returns program bindings (rowEnvironment target allEntries entry) state state
    "mm0:check-row" [targetName, allName, entryName] rowEquation.body _
    (by decide) (by decide) (by decide) _ (row_body_returns state target allEntries entry) (by decide)
  simpa [capturedTarget, capturedAll, capturedEntry] using row_clause target allEntries entry

private theorem rows_body_shape : rowsEquation.body =
    .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "entries"],
      .expression [.symbol "mm0:rows-view", .var "view", .var "target", .var "all"]] := by decide
private theorem rows_view_body_shape : rowsViewEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (rowsCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem rows_cases_shape : rowsCases = [(.symbol "List:Nil", boolean true),
    (.expression [.symbol "List:Cons", .var "entry", .var "rest"], rowsConsBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem rows_cons_body_shape : rowsConsBody =
    .expression [.symbol "let", .var "checkRowResult", .expression [.symbol "mm0:check-row", .var "target", .var "all", .var "entry"],
      .expression [.symbol "mm0:rows-next", .var "checkRowResult", .var "target", .var "all", .var "rest"]] := by decide
private theorem rows_next_body_shape : rowsNextEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (rowsNextCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem rows_next_cases_shape : rowsNextCases = [(boolean false, boolean false),
    (boolean true, .expression [.symbol "mm0:check-rows", .var "target", .var "all", .var "rest"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem rows_clause (target : Context) (allEntries entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:check-rows" [Data.context target, entriesValue allEntries, entriesValue entries] =
      [.evaluate (rowsEnvironment target allEntries entries) rowsEquation.body] := by
  rw [clauses_use_only_the_named_equations, rows_unique]
  simp [rows_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, rowsEnvironment]
private theorem rows_view_clause (target : Context) (allEntries entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:rows-view" [viewValue (entries.map entryValue), Data.context target, entriesValue allEntries] =
      [.evaluate (rowsViewEnvironment target allEntries entries) rowsViewEquation.body] := by
  rw [clauses_use_only_the_named_equations, rows_view_unique]
  simp [rows_view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, rowsViewEnvironment]
private theorem rows_next_clause (answer : Bool) (target : Context) (allEntries entries : List Kernel.Substitution.Entry) :
    clauses program "mm0:rows-next" [boolean answer, Data.context target, entriesValue allEntries, entriesValue entries] =
      [.evaluate (rowsNextEnvironment answer target allEntries entries) rowsNextEquation.body] := by
  rw [clauses_use_only_the_named_equations, rows_next_unique]
  simp [rows_next_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, rowsNextEnvironment]

private theorem rows_call_from_body (bindings : Subst) (state : State) (target : Context)
    (allEntries entries : List Kernel.Substitution.Entry) (targetName allName entriesName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedAll : applySubst bindings (.var allName) = entriesValue allEntries)
    (capturedEntries : applySubst bindings (.var entriesName) = entriesValue entries)
    (computed : PureReturns program (rowsEnvironment target allEntries entries) state rowsEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkRow target allEntries)))) :
    PureReturns program bindings state (.expression [.symbol "mm0:check-rows", .var targetName, .var allName, .var entriesName]) state
      (boolean (entries.all (Kernel.Substitution.checkRow target allEntries))) := by
  apply authored_variable_call_returns program bindings (rowsEnvironment target allEntries entries) state state
    "mm0:check-rows" [targetName, allName, entriesName] rowsEquation.body _
    (by decide) (by decide) (by decide) _ computed (by decide)
  simpa [capturedTarget, capturedAll, capturedEntries] using rows_clause target allEntries entries

private theorem rows_next_returns (state : State) (answer : Bool) (target : Context)
    (allEntries entries : List Kernel.Substitution.Entry)
    (computed : PureReturns program (rowsEnvironment target allEntries entries) state rowsEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkRow target allEntries)))) :
    PureReturns program (rowsNextEnvironment answer target allEntries entries) state rowsNextEquation.body state
      (boolean (answer && entries.all (Kernel.Substitution.checkRow target allEntries))) := by
  rw [rows_next_body_shape]
  cases answer with
  | false =>
      let bindings := rowsNextEnvironment false target allEntries entries
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false) (boolean false)
        _ _ rowsNextCases (read_cases_encoded rowsNextCases)
      · simpa [bindings, rowsNextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [rows_next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool false)
  | true =>
      let bindings := rowsNextEnvironment true target allEntries entries
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        (.expression [.symbol "mm0:check-rows", .var "target", .var "all", .var "rest"])
        _ _ rowsNextCases (read_cases_encoded rowsNextCases)
      · simpa [bindings, rowsNextEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
      · simp [rows_next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact rows_call_from_body bindings state target allEntries entries "target" "all" "rest" rfl rfl rfl computed

theorem rows_body_returns (state : State) (target : Context) (allEntries entries : List Kernel.Substitution.Entry) :
    PureReturns program (rowsEnvironment target allEntries entries) state rowsEquation.body state
      (boolean (entries.all (Kernel.Substitution.checkRow target allEntries))) := by
  induction entries with
  | nil =>
      rw [rows_body_shape]
      let bindings := rowsEnvironment target allEntries []
      let viewed := ("view", viewValue []) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "entries" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, rowsEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (rowsViewEnvironment target allEntries []) state state
          "mm0:rows-view" ["view", "target", "all"] rowsViewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, rowsEnvironment, applySubst, Subst.lookup] using rows_view_clause target allEntries []
        · rw [rows_view_body_shape]
          let callee := rowsViewEnvironment target allEntries []
          apply case_returns program callee callee state state state (.var "valueInput") (viewValue []) (boolean true)
            _ _ rowsCases (read_cases_encoded rowsCases)
          · simpa [callee, rowsViewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [rows_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · exact grounded_returns program callee state (.bool true)
  | cons entry entries ih =>
      rw [rows_body_shape]
      let bindings := rowsEnvironment target allEntries (entry :: entries)
      let viewed := ("view", viewValue ((entry :: entries).map entryValue)) :: bindings
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((entry :: entries).map entryValue)) _
      · exact ListAccess.view_captured_returns bindings state "entries" _ rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, rowsEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (rowsViewEnvironment target allEntries (entry :: entries)) state state
          "mm0:rows-view" ["view", "target", "all"] rowsViewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, rowsEnvironment, applySubst, Subst.lookup] using rows_view_clause target allEntries (entry :: entries)
        · rw [rows_view_body_shape]
          let callee := rowsViewEnvironment target allEntries (entry :: entries)
          let bound := ("rest", entriesValue entries) :: ("entry", entryValue entry) :: callee
          apply case_returns program callee bound state state state (.var "valueInput")
            (viewValue ((entry :: entries).map entryValue)) rowsConsBody _ _ rowsCases (read_cases_encoded rowsCases)
          · simpa [callee, rowsViewEnvironment, applySubst, Subst.lookup] using variable_returns program callee state "valueInput"
          · simp [rows_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, entriesValue, viewValue, bound, callee, rowsViewEnvironment, Subst.lookup]
          · rw [rows_cons_body_shape]
            let answer := Kernel.Substitution.checkRow target allEntries entry
            let checked := ("checkRowResult", boolean answer) :: bound
            apply let_returns program bound checked state state state (.var "checkRowResult") _ _ (boolean answer) _
            · exact row_captured_returns bound state target allEntries entry "target" "all" "entry" rfl rfl rfl
            · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, callee, rowsViewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program checked (rowsNextEnvironment answer target allEntries entries) state state
                "mm0:rows-next" ["checkRowResult", "target", "all", "rest"] rowsNextEquation.body _
                (by decide) (by decide) (by decide) _ (rows_next_returns state answer target allEntries entries ih) (by decide)
              simpa [checked, bound, callee, rowsViewEnvironment, applySubst, Subst.lookup] using rows_next_clause answer target allEntries entries

theorem rows_captured_returns (bindings : Subst) (state : State) (target : Context)
    (allEntries entries : List Kernel.Substitution.Entry) (targetName allName entriesName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedAll : applySubst bindings (.var allName) = entriesValue allEntries)
    (capturedEntries : applySubst bindings (.var entriesName) = entriesValue entries) :
    PureReturns program bindings state (.expression [.symbol "mm0:check-rows", .var targetName, .var allName, .var entriesName]) state
      (boolean (entries.all (Kernel.Substitution.checkRow target allEntries))) :=
  rows_call_from_body bindings state target allEntries entries targetName allName entriesName
    capturedTarget capturedAll capturedEntries (rows_body_returns state target allEntries entries)

end Mettapedia.Languages.MM0.MeTTa.DependencyMatrix
