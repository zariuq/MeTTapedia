import Mettapedia.Languages.MM0.MeTTa.Kernel.Support
import Mettapedia.Languages.MM0.MeTTa.Data.Scalar
import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# Dependency tests in the retained MM0 source

Formal dependencies select the independence obligation. Occurrence support in
the target context checks that obligation. The source traverses ordinary
lists, retaining their order and multiplicity; membership observes presence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Dependencies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Context Preterm)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open Support (indicesValue resultValue)

private def memberEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 150)[149]'(by decide +kernel)
private def viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 151)[150]'(by decide +kernel)
private def equalEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 152)[151]'(by decide +kernel)
private def dependsEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 153)[152]'(by decide +kernel)
private def disjointEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 154)[153]'(by decide +kernel)
private def notEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 155)[154]'(by decide +kernel)

private def memberEnvironment (index : Nat) (values : List Nat) : Subst :=
  [("values", indicesValue values), ("index", natural index)]
private def viewEnvironment (index : Nat) (values : List Nat) : Subst :=
  [("valueInput", viewValue (values.map natural)), ("index", natural index)]
private def equalEnvironment (condition : Bool) (index : Nat) (rest : List Nat) : Subst :=
  [("rest", indicesValue rest), ("index", natural index), ("conditionInput", boolean condition)]

private def sourceCases (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def viewCases := sourceCases viewEquation.body
private def equalCases := sourceCases equalEquation.body
private def consBody : Atom := (viewCases[1]'(by decide)).2

private theorem member_unique :
    program.equations.filter (fun entry => entry.head == "mm0:nat-member") = [memberEquation] := by decide
private theorem view_unique :
    program.equations.filter (fun entry => entry.head == "mm0:member-view") = [viewEquation] := by decide
private theorem equal_unique :
    program.equations.filter (fun entry => entry.head == "mm0:member-equal") = [equalEquation] := by decide
private theorem member_formals : memberEquation.arguments = [.var "index", .var "values"] := by decide
private theorem view_formals : viewEquation.arguments = [.var "index", .var "valueInput"] := by decide
private theorem equal_formals :
    equalEquation.arguments = [.var "conditionInput", .var "index", .var "rest"] := by decide

private theorem member_body_shape :
    memberEquation.body = .expression [.symbol "let", .var "view",
      .expression [.symbol "mm0:list-view", .var "values"],
      .expression [.symbol "mm0:member-view", .var "index", .var "view"]] := by decide
private theorem view_body_shape :
    viewEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (viewCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem view_cases_shape :
    viewCases = [(.symbol "List:Nil", boolean false),
      (.expression [.symbol "List:Cons", .var "first", .var "rest"], consBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem cons_body_shape :
    consBody = .expression [.symbol "let", .var "equal",
      .expression [.symbol "mm0:nat-eq", .var "index", .var "first"],
      .expression [.symbol "mm0:member-equal", .var "equal", .var "index", .var "rest"]] := by decide
private theorem equal_body_shape :
    equalEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (equalCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem equal_cases_shape :
    equalCases = [(boolean true, boolean true),
      (boolean false, .expression [.symbol "mm0:nat-member", .var "index", .var "rest"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem member_clause (index : Nat) (values : List Nat) :
    clauses program "mm0:nat-member" [natural index, indicesValue values] =
      [.evaluate (memberEnvironment index values) memberEquation.body] := by
  rw [clauses_use_only_the_named_equations, member_unique]
  simp [member_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, memberEnvironment]
private theorem view_clause (index : Nat) (values : List Nat) :
    clauses program "mm0:member-view" [natural index, viewValue (values.map natural)] =
      [.evaluate (viewEnvironment index values) viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, view_unique]
  simp [view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, viewEnvironment]
private theorem equal_clause (condition : Bool) (index : Nat) (rest : List Nat) :
    clauses program "mm0:member-equal" [boolean condition, natural index, indicesValue rest] =
      [.evaluate (equalEnvironment condition index rest) equalEquation.body] := by
  rw [clauses_use_only_the_named_equations, equal_unique]
  simp [equal_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, equalEnvironment]

private theorem equal_body_returns (state : State) (condition : Bool) (index : Nat) (rest : List Nat)
    (recursive : PureReturns program (memberEnvironment index rest) state memberEquation.body state
      (boolean (decide (index ∈ rest)))) :
    PureReturns program (equalEnvironment condition index rest) state equalEquation.body state
      (boolean (condition || decide (index ∈ rest))) := by
  rw [equal_body_shape]
  let bindings := equalEnvironment condition index rest
  have input : PureReturns program bindings state (.var "conditionInput") state (boolean condition) := by
    simpa [bindings, equalEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "conditionInput"
  cases condition with
  | true =>
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean true) (boolean true) _ _ equalCases (read_cases_encoded equalCases) input
      · simp [equal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool true)
  | false =>
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean false) (.expression [.symbol "mm0:nat-member", .var "index", .var "rest"])
        _ _ equalCases (read_cases_encoded equalCases) input
      · simp [equal_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · apply authored_variable_call_returns program bindings (memberEnvironment index rest) state state
          "mm0:nat-member" ["index", "rest"] memberEquation.body _
          (by decide) (by decide) (by decide) _ recursive (by decide)
        simpa [bindings, equalEnvironment, applySubst, Subst.lookup] using member_clause index rest

theorem member_body_returns (state : State) (index : Nat) (values : List Nat) :
    PureReturns program (memberEnvironment index values) state memberEquation.body state
      (boolean (decide (index ∈ values))) := by
  induction values with
  | nil =>
      let bindings := memberEnvironment index []
      let viewed := ("view", viewValue []) :: bindings
      rw [member_body_shape]
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "values" [] (by rfl)
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, memberEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment index []) state state
          "mm0:member-view" ["index", "view"] viewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, memberEnvironment, applySubst, Subst.lookup] using view_clause index []
        · rw [view_body_shape]
          let inner := viewEnvironment index []
          apply case_returns program inner inner state state state (.var "valueInput")
            (viewValue []) (boolean false) _ _ viewCases (read_cases_encoded viewCases)
          · simpa [inner, viewEnvironment, applySubst, Subst.lookup] using
              variable_returns program inner state "valueInput"
          · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, viewValue]
          · exact grounded_returns program inner state (.bool false)
  | cons first rest recursive =>
      let bindings := memberEnvironment index (first :: rest)
      let viewed := ("view", viewValue ((first :: rest).map natural)) :: bindings
      rw [member_body_shape]
      apply let_returns program bindings viewed state state state (.var "view") _ _
        (viewValue ((first :: rest).map natural)) _
      · exact ListAccess.view_captured_returns bindings state "values" ((first :: rest).map natural) (by rfl)
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, memberEnvironment, Subst.lookup]
      · apply authored_variable_call_returns program viewed (viewEnvironment index (first :: rest)) state state
          "mm0:member-view" ["index", "view"] viewEquation.body _
          (by decide) (by decide) (by decide) _ _ (by decide)
        · simpa [viewed, bindings, memberEnvironment, applySubst, Subst.lookup] using view_clause index (first :: rest)
        · rw [view_body_shape]
          let inner := viewEnvironment index (first :: rest)
          let bound := ("rest", indicesValue rest) :: ("first", natural first) :: inner
          apply case_returns program inner bound state state state (.var "valueInput")
            (viewValue ((first :: rest).map natural)) consBody _ _ viewCases (read_cases_encoded viewCases)
          · simpa [inner, viewEnvironment, applySubst, Subst.lookup] using
              variable_returns program inner state "valueInput"
          · simp [view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, indicesValue,
              bound, inner, viewEnvironment, Subst.lookup]
          · rw [cons_body_shape]
            let compared := ("equal", boolean (decide (index = first))) :: bound
            apply let_returns program bound compared state state state (.var "equal") _ _
              (boolean (decide (index = first))) _
            · exact Scalar.equality_captured_returns bound state "index" "first" index first
                (by simp [bound, inner, viewEnvironment, applySubst, Subst.lookup]) (by rfl)
            · simp [SpaceSemantics.matchValue, matchAtom, compared, bound, inner, viewEnvironment, Subst.lookup]
            · apply authored_variable_call_returns program compared
                (equalEnvironment (decide (index = first)) index rest) state state
                "mm0:member-equal" ["equal", "index", "rest"] equalEquation.body _
                (by decide) (by decide) (by decide) _ _ (by decide)
              · simpa [compared, bound, inner, viewEnvironment, applySubst, Subst.lookup] using
                  equal_clause (decide (index = first)) index rest
              · simpa [List.mem_cons] using
                  equal_body_returns state (decide (index = first)) index rest recursive

theorem member_captured_returns (bindings : Subst) (state : State) (index : Nat) (values : List Nat)
    (indexName valuesName : String)
    (capturedIndex : applySubst bindings (.var indexName) = natural index)
    (capturedValues : applySubst bindings (.var valuesName) = indicesValue values) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:nat-member", .var indexName, .var valuesName]) state
      (boolean (decide (index ∈ values))) := by
  apply authored_variable_call_returns program bindings (memberEnvironment index values) state state
    "mm0:nat-member" [indexName, valuesName] memberEquation.body _
    (by decide) (by decide) (by decide) _ (member_body_returns state index values) (by decide)
  simpa [capturedIndex, capturedValues] using member_clause index values

private def dependsEnvironment (binder : Kernel.Binder) (position index : Nat) : Subst :=
  [("index", natural index), ("position", natural position), ("valueInput", Data.binder binder)]
private def dependsCases := sourceCases dependsEquation.body

private theorem depends_unique :
    program.equations.filter (fun entry => entry.head == "mm0:depends") = [dependsEquation] := by decide
private theorem depends_formals :
    dependsEquation.arguments = [.var "valueInput", .var "position", .var "index"] := by decide
private theorem depends_body_shape :
    dependsEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (dependsCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem depends_cases_shape :
    dependsCases = [(.expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]],
        .expression [.symbol "mm0:nat-eq", .var "index", .var "position"]),
      (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]],
        .expression [.symbol "mm0:nat-member", .var "index", .var "dependencies"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem depends_clause (binder : Kernel.Binder) (position index : Nat) :
    clauses program "mm0:depends" [Data.binder binder, natural position, natural index] =
      [.evaluate (dependsEnvironment binder position index) dependsEquation.body] := by
  rw [clauses_use_only_the_named_equations, depends_unique]
  simp [depends_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, dependsEnvironment]

theorem depends_body_returns (state : State) (binder : Kernel.Binder) (position index : Nat) :
    PureReturns program (dependsEnvironment binder position index) state dependsEquation.body state
      (boolean (decide (binder.DependsOn position index))) := by
  rw [depends_body_shape]
  let bindings := dependsEnvironment binder position index
  have input : PureReturns program bindings state (.var "valueInput") state (Data.binder binder) := by
    simpa [bindings, dependsEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "valueInput"
  cases binder with
  | bound sort =>
      let bound := ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (Data.binder (.bound sort))
        (.expression [.symbol "mm0:nat-eq", .var "index", .var "position"])
        _ _ dependsCases (read_cases_encoded dependsCases) input
      · simp [depends_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.binder, listValue,
          bound, bindings, dependsEnvironment, Subst.lookup]
      · exact Scalar.equality_captured_returns bound state "index" "position" index position
          (by simp [bound, bindings, dependsEnvironment, applySubst, Subst.lookup])
          (by simp [bound, bindings, dependsEnvironment, applySubst, Subst.lookup])
  | regular sort values =>
      let bound := ("dependencies", Data.dependencies values) :: ("sort", natural sort) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (Data.binder (.regular sort values))
        (.expression [.symbol "mm0:nat-member", .var "index", .var "dependencies"])
        _ _ dependsCases (read_cases_encoded dependsCases) input
      · simp [depends_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Data.binder, listValue,
          bound, bindings, dependsEnvironment, Subst.lookup]
      · simpa [Kernel.Binder.DependsOn, Finset.mem_sort] using
          (member_captured_returns bound state index (values.sort (· ≤ ·)) "index" "dependencies"
            (by simp [bound, bindings, dependsEnvironment, applySubst, Subst.lookup]) (by rfl))

theorem depends_captured_returns (bindings : Subst) (state : State) (binder : Kernel.Binder)
    (position index : Nat) (binderName positionName indexName : String)
    (capturedBinder : applySubst bindings (.var binderName) = Data.binder binder)
    (capturedPosition : applySubst bindings (.var positionName) = natural position)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:depends", .var binderName, .var positionName, .var indexName]) state
      (boolean (decide (binder.DependsOn position index))) := by
  apply authored_variable_call_returns program bindings (dependsEnvironment binder position index) state state
    "mm0:depends" [binderName, positionName, indexName] dependsEquation.body _
    (by decide) (by decide) (by decide) _ (depends_body_returns state binder position index) (by decide)
  simpa [capturedBinder, capturedPosition, capturedIndex] using depends_clause binder position index

private def notEnvironment (value : Bool) : Subst := [("conditionInput", boolean value)]
private def notCases := sourceCases notEquation.body
private theorem not_unique :
    program.equations.filter (fun entry => entry.head == "mm0:dependency-not") = [notEquation] := by decide
private theorem not_formals : notEquation.arguments = [.var "conditionInput"] := by decide
private theorem not_body_shape :
    notEquation.body = .expression [.symbol "case", .expression [.var "conditionInput"],
      .expression (notCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem not_cases_shape :
    notCases = [(.expression [boolean true], boolean false),
      (.expression [boolean false], boolean true),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem not_clause (value : Bool) :
    clauses program "mm0:dependency-not" [boolean value] =
      [.evaluate (notEnvironment value) notEquation.body] := by
  rw [clauses_use_only_the_named_equations, not_unique]
  simp [not_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, notEnvironment]

private theorem not_body_returns (state : State) (value : Bool) :
    PureReturns program (notEnvironment value) state notEquation.body state (boolean (!value)) := by
  rw [not_body_shape]
  have input : PureReturns program (notEnvironment value) state (.expression [.var "conditionInput"])
      state (.expression [boolean value]) := by
    simpa [notEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program (notEnvironment value) state ["conditionInput"]
  cases value with
  | false =>
      apply case_returns program (notEnvironment false) (notEnvironment false) state state state
        (.expression [.var "conditionInput"]) (.expression [boolean false]) (boolean true)
        _ _ notCases (read_cases_encoded notCases) input
      · simp [not_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool true)
  | true =>
      apply case_returns program (notEnvironment true) (notEnvironment true) state state state
        (.expression [.var "conditionInput"]) (.expression [boolean true]) (boolean false)
        _ _ notCases (read_cases_encoded notCases) input
      · simp [not_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, boolean]
      · exact grounded_returns program _ state (.bool false)

private theorem not_captured_returns (bindings : Subst) (state : State) (name : String) (value : Bool)
    (captured : applySubst bindings (.var name) = boolean value) :
    PureReturns program bindings state (.expression [.symbol "mm0:dependency-not", .var name]) state
      (boolean (!value)) := by
  apply authored_variable_call_returns program bindings (notEnvironment value) state state
    "mm0:dependency-not" [name] notEquation.body _
    (by decide) (by decide) (by decide) _ (not_body_returns state value) (by decide)
  simpa [captured] using not_clause value

private def disjointEnvironment (result : Option (List Nat)) (index : Nat) : Subst :=
  [("target-bound", natural index), ("valueInput", resultValue result)]
private def disjointCases := sourceCases disjointEquation.body
private def disjointBody : Atom := (disjointCases[1]'(by decide)).2
private theorem disjoint_unique :
    program.equations.filter (fun entry => entry.head == "mm0:support-disjoint") = [disjointEquation] := by decide
private theorem disjoint_formals : disjointEquation.arguments = [.var "valueInput", .var "target-bound"] := by decide
private theorem disjoint_body_shape :
    disjointEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (disjointCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem disjoint_cases_shape :
    disjointCases = [(.symbol "None", boolean false),
      (.expression [.symbol "Some", .var "indices"], disjointBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem disjoint_some_body_shape :
    disjointBody = .expression [.symbol "let", .var "natMemberResult",
      .expression [.symbol "mm0:nat-member", .var "target-bound", .var "indices"],
      .expression [.symbol "mm0:dependency-not", .var "natMemberResult"]] := by decide
private theorem disjoint_clause (result : Option (List Nat)) (index : Nat) :
    clauses program "mm0:support-disjoint" [resultValue result, natural index] =
      [.evaluate (disjointEnvironment result index) disjointEquation.body] := by
  rw [clauses_use_only_the_named_equations, disjoint_unique]
  simp [disjoint_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, disjointEnvironment]

private theorem disjoint_body_returns (state : State) (result : Option (List Nat)) (index : Nat) :
    PureReturns program (disjointEnvironment result index) state disjointEquation.body state
      (boolean (match result with | none => false | some values => decide (index ∉ values))) := by
  rw [disjoint_body_shape]
  let bindings := disjointEnvironment result index
  have input : PureReturns program bindings state (.var "valueInput") state (resultValue result) := by
    simpa [bindings, disjointEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "valueInput"
  cases result with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (boolean false) _ _ disjointCases (read_cases_encoded disjointCases) input
      · simp [disjoint_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool false)
  | some values =>
      let bound := ("indices", indicesValue values) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (resultValue (some values)) disjointBody _ _ disjointCases (read_cases_encoded disjointCases) input
      · simp [disjoint_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
          bound, bindings, disjointEnvironment, Subst.lookup]
      · rw [disjoint_some_body_shape]
        let queried := ("natMemberResult", boolean (decide (index ∈ values))) :: bound
        apply let_returns program bound queried state state state (.var "natMemberResult") _ _
          (boolean (decide (index ∈ values))) _
        · exact member_captured_returns bound state index values "target-bound" "indices"
            (by simp [bound, bindings, disjointEnvironment, applySubst, Subst.lookup]) (by rfl)
        · simp [SpaceSemantics.matchValue, matchAtom, queried, bound, bindings, disjointEnvironment, Subst.lookup]
        · simpa using not_captured_returns queried state "natMemberResult" (decide (index ∈ values)) (by rfl)

private def pairEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 37)[36]'(by decide)
private def pairDependsEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 38)[37]'(by decide)
private def pairEnvironment (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("position", natural position), ("binder", Data.binder binder),
    ("target-bound", natural targetBound), ("formal-bound", natural formalBound), ("target", Data.context target)]
private def pairDependsEnvironment (condition : Bool) (target : Context) (targetBound : Nat)
    (expression : Preterm) : Subst :=
  [("expression", Data.preterm expression), ("target-bound", natural targetBound),
    ("target", Data.context target), ("conditionInput", boolean condition)]
private def pairDependsCases := sourceCases pairDependsEquation.body
private def independentBody : Atom := (pairDependsCases[1]'(by decide)).2
private theorem pair_unique :
    program.equations.filter (fun entry => entry.head == "mm0:check-pair") = [pairEquation] := by decide
private theorem pair_depends_unique :
    program.equations.filter (fun entry => entry.head == "mm0:pair-depends") = [pairDependsEquation] := by decide
private theorem pair_formals : pairEquation.arguments = [.var "target", .var "formal-bound",
    .var "target-bound", .var "binder", .var "position", .var "expression"] := by decide
private theorem pair_depends_formals : pairDependsEquation.arguments = [.var "conditionInput",
    .var "target", .var "target-bound", .var "expression"] := by decide
private theorem pair_body_shape :
    pairEquation.body = .expression [.symbol "let", .var "dependsResult",
      .expression [.symbol "mm0:depends", .var "binder", .var "position", .var "formal-bound"],
      .expression [.symbol "mm0:pair-depends", .var "dependsResult", .var "target",
        .var "target-bound", .var "expression"]] := by decide
private theorem pair_depends_body_shape :
    pairDependsEquation.body = .expression [.symbol "case", .var "conditionInput",
      .expression (pairDependsCases.map fun entry => .expression [entry.1, entry.2])] := by decide
private theorem pair_depends_cases_shape :
    pairDependsCases = [(boolean true, boolean true), (boolean false, independentBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem independent_body_shape :
    independentBody = .expression [.symbol "let", .var "supportResult",
      .expression [.symbol "mm0:support", .var "target", .var "expression"],
      .expression [.symbol "mm0:support-disjoint", .var "supportResult", .var "target-bound"]] := by decide
theorem pair_clause (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) :
    clauses program "mm0:check-pair" [Data.context target, natural formalBound, natural targetBound,
      Data.binder binder, natural position, Data.preterm expression] =
      [.evaluate (pairEnvironment target formalBound targetBound binder position expression) pairEquation.body] := by
  rw [clauses_use_only_the_named_equations, pair_unique]
  simp [pair_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, pairEnvironment]
private theorem pair_depends_clause (condition : Bool) (target : Context) (targetBound : Nat)
    (expression : Preterm) :
    clauses program "mm0:pair-depends" [boolean condition, Data.context target, natural targetBound,
      Data.preterm expression] =
      [.evaluate (pairDependsEnvironment condition target targetBound expression) pairDependsEquation.body] := by
  rw [clauses_use_only_the_named_equations, pair_depends_unique]
  simp [pair_depends_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, pairDependsEnvironment]

private theorem pair_depends_body_returns (state : State) (condition : Bool) (target : Context)
    (targetBound : Nat) (expression : Preterm) :
    PureReturns program (pairDependsEnvironment condition target targetBound expression) state
      pairDependsEquation.body state
      (boolean (condition || match Preterm.support? target expression with
        | none => false | some values => decide (targetBound ∉ values))) := by
  rw [pair_depends_body_shape]
  let bindings := pairDependsEnvironment condition target targetBound expression
  have input : PureReturns program bindings state (.var "conditionInput") state (boolean condition) := by
    simpa [bindings, pairDependsEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "conditionInput"
  cases condition with
  | true =>
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean true) (boolean true) _ _ pairDependsCases (read_cases_encoded pairDependsCases) input
      · simp [pair_depends_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · exact grounded_returns program bindings state (.bool true)
  | false =>
      apply case_returns program bindings bindings state state state (.var "conditionInput")
        (boolean false) independentBody _ _ pairDependsCases (read_cases_encoded pairDependsCases) input
      · simp [pair_depends_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [independent_body_shape]
        let supported := ("supportResult", resultValue (Presentation.ComputationalSupport.indices? target expression)) :: bindings
        apply let_returns program bindings supported state state state (.var "supportResult") _ _
          (resultValue (Presentation.ComputationalSupport.indices? target expression)) _
        · exact Support.captured_returns bindings state target expression "target" "expression"
            (by rfl) (by rfl)
        · simp [SpaceSemantics.matchValue, matchAtom, supported, bindings, pairDependsEnvironment, Subst.lookup]
        · apply authored_variable_call_returns program supported
            (disjointEnvironment (Presentation.ComputationalSupport.indices? target expression) targetBound)
            state state "mm0:support-disjoint" ["supportResult", "target-bound"] disjointEquation.body _
            (by decide) (by decide) (by decide) _ _ (by decide)
          · simpa [supported, bindings, pairDependsEnvironment, applySubst, Subst.lookup] using
              disjoint_clause (Presentation.ComputationalSupport.indices? target expression) targetBound
          · rw [← Presentation.ComputationalSupport.indices_meaning]
            cases result : Presentation.ComputationalSupport.indices? target expression <;>
              simpa [result] using disjoint_body_returns state
                (Presentation.ComputationalSupport.indices? target expression) targetBound

theorem pair_body_returns (state : State) (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) :
    PureReturns program (pairEnvironment target formalBound targetBound binder position expression)
      state pairEquation.body state
      (boolean (Kernel.Substitution.checkPair target formalBound targetBound ((binder, expression), position))) := by
  let bindings := pairEnvironment target formalBound targetBound binder position expression
  let dependent := decide (binder.DependsOn position formalBound)
  let tested := ("dependsResult", boolean dependent) :: bindings
  rw [pair_body_shape]
  apply let_returns program bindings tested state state state (.var "dependsResult") _ _ (boolean dependent) _
  · exact depends_captured_returns bindings state binder position formalBound "binder" "position" "formal-bound"
      (by rfl) (by rfl) (by rfl)
  · simp [SpaceSemantics.matchValue, matchAtom, tested, bindings, pairEnvironment, Subst.lookup]
  · apply authored_variable_call_returns program tested (pairDependsEnvironment dependent target targetBound expression)
      state state "mm0:pair-depends" ["dependsResult", "target", "target-bound", "expression"]
      pairDependsEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
    · simpa [tested, bindings, pairEnvironment, applySubst, Subst.lookup] using
        pair_depends_clause dependent target targetBound expression
    · by_cases depends : binder.DependsOn position formalBound
      · simpa [dependent, Kernel.Substitution.checkPair, depends] using
          pair_depends_body_returns state dependent target targetBound expression
      · cases supported : Preterm.support? target expression <;>
          simpa [dependent, Kernel.Substitution.checkPair, depends, supported] using
            pair_depends_body_returns state dependent target targetBound expression

theorem pair_captured_returns (bindings : Subst) (state : State) (target : Context)
    (formalBound targetBound : Nat) (binder : Kernel.Binder) (position : Nat) (expression : Preterm)
    (targetName formalBoundName targetBoundName binderName positionName expressionName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedFormalBound : applySubst bindings (.var formalBoundName) = natural formalBound)
    (capturedTargetBound : applySubst bindings (.var targetBoundName) = natural targetBound)
    (capturedBinder : applySubst bindings (.var binderName) = Data.binder binder)
    (capturedPosition : applySubst bindings (.var positionName) = natural position)
    (capturedExpression : applySubst bindings (.var expressionName) = Data.preterm expression) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:check-pair", .var targetName, .var formalBoundName, .var targetBoundName,
        .var binderName, .var positionName, .var expressionName]) state
      (boolean (Kernel.Substitution.checkPair target formalBound targetBound ((binder, expression), position))) := by
  apply authored_variable_call_returns program bindings
    (pairEnvironment target formalBound targetBound binder position expression) state state
    "mm0:check-pair" [targetName, formalBoundName, targetBoundName, binderName, positionName, expressionName]
    pairEquation.body _ (by decide) (by decide) (by decide) _
    (pair_body_returns state target formalBound targetBound binder position expression) (by decide)
  simpa [capturedTarget, capturedFormalBound, capturedTargetBound, capturedBinder,
    capturedPosition, capturedExpression] using pair_clause target formalBound targetBound binder position expression

def requestConfiguration (state : State) (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) : Configuration :=
  { state, control := .evaluate (pairEnvironment target formalBound targetBound binder position expression)
      (.expression [.symbol "mm0:check-pair", .var "target", .var "formal-bound", .var "target-bound",
        .var "binder", .var "position", .var "expression"]) }

theorem sufficient_fuel (state : State) (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      (requestConfiguration state target formalBound targetBound binder position expression) =
        .complete state
          [boolean (Kernel.Substitution.checkPair target formalBound targetBound ((binder, expression), position))]
          [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    (pairEnvironment target formalBound targetBound binder position expression) state state _ _
    (pair_captured_returns (pairEnvironment target formalBound targetBound binder position expression)
      state target formalBound targetBound binder position expression "target" "formal-bound" "target-bound"
      "binder" "position" "expression" rfl rfl rfl rfl rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem result_iff_source_returns (state : State) (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) (answer : Bool) :
    Kernel.Substitution.checkPair target formalBound targetBound ((binder, expression), position) = answer ↔
      ∃ fuel, run program fuel
        (requestConfiguration state target formalBound targetBound binder position expression) =
          .complete state [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := sufficient_fuel state target formalBound targetBound binder position expression
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same
    exact ⟨referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state state _ [] [] _ [] [] reference returned
    simpa [boolean] using List.singleton_inj.mp same.2.1

/-- Defined target support is supplied by argument typing in the complete
substitution check. Without it, absence of an occurrence is not enough. -/
theorem independent_iff_source_accepts (state : State) (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) (support : Finset Nat)
    (supported : Preterm.Supports target expression support) :
    Kernel.Substitution.PairIndependent target formalBound targetBound ((binder, expression), position) ↔
      ∃ fuel, run program fuel
        (requestConfiguration state target formalBound targetBound binder position expression) =
          .complete state [boolean true] [] [] :=
  (Kernel.Substitution.checkPair_iff supported).symm.trans
    (result_iff_source_returns state target formalBound targetBound binder position expression true)

theorem forbidden_occurrence_refused (state : State) :
    ∃ fuel, run program fuel
      (requestConfiguration state [.bound 0] 0 0 (.regular 0 ∅) 1 (.var 0)) =
        .complete state [boolean false] [] [] := by
  apply (result_iff_source_returns state [.bound 0] 0 0 (.regular 0 ∅) 1 (.var 0) false).mp
  simp [Kernel.Substitution.checkPair, Kernel.Binder.DependsOn, Preterm.support?]

theorem declared_dependency_permitted (state : State) :
    ∃ fuel, run program fuel
      (requestConfiguration state [.bound 0] 0 0 (.regular 0 {0}) 1 (.var 0)) =
        .complete state [boolean true] [] [] := by
  apply (result_iff_source_returns state [.bound 0] 0 0 (.regular 0 {0}) 1 (.var 0) true).mp
  simp [Kernel.Substitution.checkPair, Kernel.Binder.DependsOn]

end Mettapedia.Languages.MM0.MeTTa.Dependencies
