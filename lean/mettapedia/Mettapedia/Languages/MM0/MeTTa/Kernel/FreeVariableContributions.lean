import Mettapedia.Languages.MM0.MeTTa.Kernel.FreeVariableImages
import Mettapedia.Languages.MM0.MeTTa.Kernel.NaturalDifference

/-!
# Binder contributions in the retained MM0 source

The actual source resolves declared binder images, removes exactly those
occurrences from each regular argument, and concatenates the remaining lists.
Bound arguments contribute no occurrences. Every branch is read-only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.FreeVariableContributions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Context Preterm Binder)
open Store (natural)
open ListAccess (listValue optionValue viewValue)
open Support (indicesValue resultValue)
open Presentation.ComputationalFreeVariables (images? contributions? subtract)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def free_contributionsEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 171)[170]'(by decide +kernel)
private def free_contributionsEnvironment (target full arguments formal free_lists : Atom) : Subst :=
  [("free-lists", free_lists), ("formal", formal), ("arguments", arguments), ("full", full), ("target", target)]
private theorem free_contributions_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-contributions") = [free_contributionsEquation] := by decide +kernel
private theorem free_contributions_formals :
    free_contributionsEquation.arguments = [.var "target", .var "full", .var "arguments", .var "formal", .var "free-lists"] := by decide +kernel
private theorem free_contributions_clause (target full arguments formal free_lists : Atom) :
    clauses program "mm0:free-contributions" [target, full, arguments, formal, free_lists] =
      [.evaluate (free_contributionsEnvironment target full arguments formal free_lists) free_contributionsEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_contributions_unique]
  simp [free_contributions_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_contributionsEnvironment]
private theorem free_contributions_captured_of_body (bindings : Subst) (before after : State)
    (target full arguments formal free_lists : Atom) (targetName fullName argumentsName formalName free_listsName : String) (answer : Atom)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_full : applySubst bindings (.var fullName) = full)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_free_lists : applySubst bindings (.var free_listsName) = free_lists)
    (computed : PureReturns program (free_contributionsEnvironment target full arguments formal free_lists) before free_contributionsEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-contributions", .var targetName, .var fullName, .var argumentsName, .var formalName, .var free_listsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_contributionsEnvironment target full arguments formal free_lists) before after "mm0:free-contributions"
    [targetName, fullName, argumentsName, formalName, free_listsName] free_contributionsEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_target, capture_full, capture_arguments, capture_formal, capture_free_lists] using free_contributions_clause target full arguments formal free_lists
private theorem free_contributions_shape :
    free_contributionsEquation.body = .expression [.symbol "let", .var "view", .expression [.symbol "mm0:list-view", .var "formal"], .expression [.symbol "let", .var "view2", .expression [.symbol "mm0:list-view", .var "free-lists"], .expression [.symbol "mm0:free-contributions-view", .var "view", .var "view2", .var "target", .var "full", .var "arguments"]]] := by decide +kernel

private def free_contributions_viewEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 172)[171]'(by decide +kernel)
private def free_contributions_viewEnvironment (valueInput valueInputValue target full arguments : Atom) : Subst :=
  [("arguments", arguments), ("full", full), ("target", target), ("valueInputValue", valueInputValue), ("valueInput", valueInput)]
private theorem free_contributions_view_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-contributions-view") = [free_contributions_viewEquation] := by decide +kernel
private theorem free_contributions_view_formals :
    free_contributions_viewEquation.arguments = [.var "valueInput", .var "valueInputValue", .var "target", .var "full", .var "arguments"] := by decide +kernel
private theorem free_contributions_view_clause (valueInput valueInputValue target full arguments : Atom) :
    clauses program "mm0:free-contributions-view" [valueInput, valueInputValue, target, full, arguments] =
      [.evaluate (free_contributions_viewEnvironment valueInput valueInputValue target full arguments) free_contributions_viewEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_contributions_view_unique]
  simp [free_contributions_view_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_contributions_viewEnvironment]
private theorem free_contributions_view_captured_of_body (bindings : Subst) (before after : State)
    (valueInput valueInputValue target full arguments : Atom) (valueInputName valueInputValueName targetName fullName argumentsName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_valueInputValue : applySubst bindings (.var valueInputValueName) = valueInputValue)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_full : applySubst bindings (.var fullName) = full)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (computed : PureReturns program (free_contributions_viewEnvironment valueInput valueInputValue target full arguments) before free_contributions_viewEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-contributions-view", .var valueInputName, .var valueInputValueName, .var targetName, .var fullName, .var argumentsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_contributions_viewEnvironment valueInput valueInputValue target full arguments) before after "mm0:free-contributions-view"
    [valueInputName, valueInputValueName, targetName, fullName, argumentsName] free_contributions_viewEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_valueInputValue, capture_target, capture_full, capture_arguments] using free_contributions_view_clause valueInput valueInputValue target full arguments
private def free_contributions_viewCases := casesOf free_contributions_viewEquation.body
private def free_contributions_viewBody0 : Atom := (free_contributions_viewCases[0]'(by decide +kernel)).2
private theorem free_contributions_view_body_0_shape :
    free_contributions_viewBody0 = .expression [.symbol "let", .var "items", .expression [.symbol "MM0:L", .expression []], .expression [.symbol "Some", .var "items"]] := by decide +kernel
private def free_contributions_viewBody3 : Atom := (free_contributions_viewCases[3]'(by decide +kernel)).2
private theorem free_contributions_view_body_3_shape :
    free_contributions_viewBody3 = .expression [.symbol "mm0:free-contributions", .var "target", .var "full", .var "arguments", .var "formal", .var "free-lists"] := by decide +kernel
private def free_contributions_viewBody4 : Atom := (free_contributions_viewCases[4]'(by decide +kernel)).2
private theorem free_contributions_view_body_4_shape :
    free_contributions_viewBody4 = .expression [.symbol "let", .var "freeImagesResult", .expression [.symbol "mm0:free-images", .var "target", .var "full", .var "arguments", .var "dependencies"], .expression [.symbol "mm0:free-contribution-bound", .var "freeImagesResult", .var "target", .var "full", .var "arguments", .var "formal", .var "free", .var "free-lists"]] := by decide +kernel
private theorem free_contributions_view_shape :
    free_contributions_viewEquation.body = .expression [.symbol "case", .expression [.var "valueInput", .var "valueInputValue"],
      .expression (free_contributions_viewCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_contributions_view_cases_shape :
    free_contributions_viewCases = [
      (.expression [.symbol "List:Nil", .symbol "List:Nil"], free_contributions_viewBody0),
      (.expression [.symbol "List:Nil", .expression [.symbol "List:Cons", .var "free", .var "free-lists"]], .symbol "None"),
      (.expression [.expression [.symbol "List:Cons", .var "binder", .var "formal"], .symbol "List:Nil"], .symbol "None"),
      (.expression [.expression [.symbol "List:Cons", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Bound", .var "sort"]], .var "formal"], .expression [.symbol "List:Cons", .var "free", .var "free-lists"]], free_contributions_viewBody3),
      (.expression [.expression [.symbol "List:Cons", .expression [.symbol "MM0:L", .expression [.symbol "MM0:Regular", .var "sort", .var "dependencies"]], .var "formal"], .expression [.symbol "List:Cons", .var "free", .var "free-lists"]], free_contributions_viewBody4),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_contribution_boundEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 173)[172]'(by decide +kernel)
private def free_contribution_boundEnvironment (valueInput target full arguments formal free free_lists : Atom) : Subst :=
  [("free-lists", free_lists), ("free", free), ("formal", formal), ("arguments", arguments), ("full", full), ("target", target), ("valueInput", valueInput)]
private theorem free_contribution_bound_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-contribution-bound") = [free_contribution_boundEquation] := by decide +kernel
private theorem free_contribution_bound_formals :
    free_contribution_boundEquation.arguments = [.var "valueInput", .var "target", .var "full", .var "arguments", .var "formal", .var "free", .var "free-lists"] := by decide +kernel
private theorem free_contribution_bound_clause (valueInput target full arguments formal free free_lists : Atom) :
    clauses program "mm0:free-contribution-bound" [valueInput, target, full, arguments, formal, free, free_lists] =
      [.evaluate (free_contribution_boundEnvironment valueInput target full arguments formal free free_lists) free_contribution_boundEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_contribution_bound_unique]
  simp [free_contribution_bound_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_contribution_boundEnvironment]
private theorem free_contribution_bound_captured_of_body (bindings : Subst) (before after : State)
    (valueInput target full arguments formal free free_lists : Atom) (valueInputName targetName fullName argumentsName formalName freeName free_listsName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (capture_target : applySubst bindings (.var targetName) = target)
    (capture_full : applySubst bindings (.var fullName) = full)
    (capture_arguments : applySubst bindings (.var argumentsName) = arguments)
    (capture_formal : applySubst bindings (.var formalName) = formal)
    (capture_free : applySubst bindings (.var freeName) = free)
    (capture_free_lists : applySubst bindings (.var free_listsName) = free_lists)
    (computed : PureReturns program (free_contribution_boundEnvironment valueInput target full arguments formal free free_lists) before free_contribution_boundEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-contribution-bound", .var valueInputName, .var targetName, .var fullName, .var argumentsName, .var formalName, .var freeName, .var free_listsName]) after answer := by
  apply authored_variable_call_returns program bindings (free_contribution_boundEnvironment valueInput target full arguments formal free free_lists) before after "mm0:free-contribution-bound"
    [valueInputName, targetName, fullName, argumentsName, formalName, freeName, free_listsName] free_contribution_boundEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_target, capture_full, capture_arguments, capture_formal, capture_free, capture_free_lists] using free_contribution_bound_clause valueInput target full arguments formal free free_lists
private def free_contribution_boundCases := casesOf free_contribution_boundEquation.body
private def free_contribution_boundBody1 : Atom := (free_contribution_boundCases[1]'(by decide +kernel)).2
private theorem free_contribution_bound_body_1_shape :
    free_contribution_boundBody1 = .expression [.symbol "let", .var "natDifferenceResult", .expression [.symbol "mm0:nat-difference", .var "free", .var "bound"], .expression [.symbol "let", .var "freeContributionsResult", .expression [.symbol "mm0:free-contributions", .var "target", .var "full", .var "arguments", .var "formal", .var "free-lists"], .expression [.symbol "mm0:free-contribution-tail", .var "natDifferenceResult", .var "freeContributionsResult"]]] := by decide +kernel
private theorem free_contribution_bound_shape :
    free_contribution_boundEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_contribution_boundCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_contribution_bound_cases_shape :
    free_contribution_boundCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "bound"], free_contribution_boundBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def free_contribution_tailEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 174)[173]'(by decide +kernel)
private def free_contribution_tailEnvironment (free valueInput : Atom) : Subst :=
  [("valueInput", valueInput), ("free", free)]
private theorem free_contribution_tail_unique :
    program.equations.filter (fun entry => entry.head == "mm0:free-contribution-tail") = [free_contribution_tailEquation] := by decide +kernel
private theorem free_contribution_tail_formals :
    free_contribution_tailEquation.arguments = [.var "free", .var "valueInput"] := by decide +kernel
private theorem free_contribution_tail_clause (free valueInput : Atom) :
    clauses program "mm0:free-contribution-tail" [free, valueInput] =
      [.evaluate (free_contribution_tailEnvironment free valueInput) free_contribution_tailEquation.body] := by
  rw [clauses_use_only_the_named_equations, free_contribution_tail_unique]
  simp [free_contribution_tail_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, free_contribution_tailEnvironment]
private theorem free_contribution_tail_captured_of_body (bindings : Subst) (before after : State)
    (free valueInput : Atom) (freeName valueInputName : String) (answer : Atom)
    (capture_free : applySubst bindings (.var freeName) = free)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (computed : PureReturns program (free_contribution_tailEnvironment free valueInput) before free_contribution_tailEquation.body after answer) :
    PureReturns program bindings before (.expression [.symbol "mm0:free-contribution-tail", .var freeName, .var valueInputName]) after answer := by
  apply authored_variable_call_returns program bindings (free_contribution_tailEnvironment free valueInput) before after "mm0:free-contribution-tail"
    [freeName, valueInputName] free_contribution_tailEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_free, capture_valueInput] using free_contribution_tail_clause free valueInput
private def free_contribution_tailCases := casesOf free_contribution_tailEquation.body
private def free_contribution_tailBody1 : Atom := (free_contribution_tailCases[1]'(by decide +kernel)).2
private theorem free_contribution_tail_body_1_shape :
    free_contribution_tailBody1 = .expression [.symbol "let", .var "combined", .expression [.symbol "mm0:list-append", .var "free", .var "rest"], .expression [.symbol "Some", .var "combined"]] := by decide +kernel
private theorem free_contribution_tail_shape :
    free_contribution_tailEquation.body = .expression [.symbol "case", .var "valueInput",
      .expression (free_contribution_tailCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem free_contribution_tail_cases_shape :
    free_contribution_tailCases = [
      (.symbol "None", .symbol "None"),
      (.expression [.symbol "Some", .var "rest"], free_contribution_tailBody1),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private def freeListsValue (values : List (List Nat)) : Atom := listValue (values.map indicesValue)

private theorem tail_body_returns (state : State) (free : List Nat) (tail : Option (List Nat)) :
    PureReturns program (free_contribution_tailEnvironment (indicesValue free) (resultValue tail)) state
      free_contribution_tailEquation.body state (resultValue (tail.map (free ++ ·))) := by
  rw [free_contribution_tail_shape]
  let bindings := free_contribution_tailEnvironment (indicesValue free) (resultValue tail)
  cases tail with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_contribution_tailCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_contribution_tail_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some rest =>
      let bound := ("rest", indicesValue rest) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some rest))
        free_contribution_tailBody1 _ _ free_contribution_tailCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_contribution_tail_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
          bound, bindings, free_contribution_tailEnvironment, Subst.lookup]
      · rw [free_contribution_tail_body_1_shape]
        let combined := ("combined", indicesValue (free ++ rest)) :: bound
        apply let_returns program bound combined state state state (.var "combined") _ _ (indicesValue (free ++ rest)) _
        · simpa [indicesValue, List.map_append] using ListAccess.append_captured_returns bound state
            (free.map natural) (rest.map natural) "free" "rest"
            (by simp [bound, bindings, free_contribution_tailEnvironment, applySubst, Subst.lookup, indicesValue]) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, combined, bound, bindings, free_contribution_tailEnvironment, Subst.lookup]
        · simpa [combined, resultValue, optionValue, applySubst, Subst.lookup] using
            unary_constructor_returns program combined state "Some" "combined" some_is_data_constructor (by decide)

theorem tail_captured_returns (bindings : Subst) (state : State) (free : List Nat) (tail : Option (List Nat))
    (freeName tailName : String)
    (capturedFree : applySubst bindings (.var freeName) = indicesValue free)
    (capturedTail : applySubst bindings (.var tailName) = resultValue tail) :
    PureReturns program bindings state (.expression [.symbol "mm0:free-contribution-tail", .var freeName, .var tailName])
      state (resultValue (tail.map (free ++ ·))) :=
  free_contribution_tail_captured_of_body bindings state state _ _ freeName tailName _
    capturedFree capturedTail (tail_body_returns state free tail)

private theorem bound_body_returns (state : State) (target full : Context) (arguments : List Preterm)
    (formal : Context) (free : List Nat) (freeLists : List (List Nat)) (images : Option (List Nat))
    (recursive : PureReturns program (free_contributionsEnvironment (Data.context target) (Data.context full)
      (listValue (arguments.map Data.preterm)) (Data.context formal) (freeListsValue freeLists)) state
      free_contributionsEquation.body state (resultValue (contributions? target full arguments formal freeLists))) :
    PureReturns program (free_contribution_boundEnvironment (resultValue images) (Data.context target)
      (Data.context full) (listValue (arguments.map Data.preterm)) (Data.context formal)
      (indicesValue free) (freeListsValue freeLists)) state free_contribution_boundEquation.body state
      (resultValue (do
        let bound ← images
        let remaining ← contributions? target full arguments formal freeLists
        pure (subtract free bound ++ remaining))) := by
  rw [free_contribution_bound_shape]
  let bindings := free_contribution_boundEnvironment (resultValue images) (Data.context target)
    (Data.context full) (listValue (arguments.map Data.preterm)) (Data.context formal)
    (indicesValue free) (freeListsValue freeLists)
  cases images with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ free_contribution_boundCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_contribution_bound_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | some images =>
      let bound := ("bound", indicesValue images) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput") (resultValue (some images))
        free_contribution_boundBody1 _ _ free_contribution_boundCases (read_cases_encoded _)
      · exact variable_returns program bindings state "valueInput"
      · simp [free_contribution_bound_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue,
          bound, bindings, free_contribution_boundEnvironment, Subst.lookup]
      · rw [free_contribution_bound_body_1_shape]
        let difference := ("natDifferenceResult", indicesValue (subtract free images)) :: bound
        apply let_returns program bound difference state state state (.var "natDifferenceResult") _ _
          (indicesValue (subtract free images)) _
        · exact NaturalDifference.captured_returns bound state free images "free" "bound"
            (by simp [bound, bindings, free_contribution_boundEnvironment, applySubst, Subst.lookup]) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, difference, bound, bindings, free_contribution_boundEnvironment, Subst.lookup]
        · let remaining := ("freeContributionsResult", resultValue (contributions? target full arguments formal freeLists)) :: difference
          apply let_returns program difference remaining state state state (.var "freeContributionsResult") _ _
            (resultValue (contributions? target full arguments formal freeLists)) _
          · exact free_contributions_captured_of_body difference state state _ _ _ _ _
              "target" "full" "arguments" "formal" "free-lists" _
              (by simp [difference, bound, bindings, free_contribution_boundEnvironment, applySubst, Subst.lookup])
              (by simp [difference, bound, bindings, free_contribution_boundEnvironment, applySubst, Subst.lookup])
              (by simp [difference, bound, bindings, free_contribution_boundEnvironment, applySubst, Subst.lookup])
              (by simp [difference, bound, bindings, free_contribution_boundEnvironment, applySubst, Subst.lookup])
              (by simp [difference, bound, bindings, free_contribution_boundEnvironment, applySubst, Subst.lookup]) recursive
          · simp [SpaceSemantics.matchValue, matchAtom, remaining, difference, bound, bindings, free_contribution_boundEnvironment, Subst.lookup]
          · have computed := tail_captured_returns remaining state (subtract free images)
              (contributions? target full arguments formal freeLists) "natDifferenceResult" "freeContributionsResult"
              (by simp [remaining, difference, applySubst, Subst.lookup]) rfl
            cases tail : contributions? target full arguments formal freeLists <;> simpa [tail] using computed

theorem body_returns (state : State) (target full : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) :
    PureReturns program (free_contributionsEnvironment (Data.context target) (Data.context full)
      (listValue (arguments.map Data.preterm)) (Data.context formal) (freeListsValue freeLists)) state
      free_contributionsEquation.body state (resultValue (contributions? target full arguments formal freeLists)) := by
  induction formal generalizing freeLists with
  | nil =>
      rw [free_contributions_shape]
      let bindings := free_contributionsEnvironment (Data.context target) (Data.context full)
        (listValue (arguments.map Data.preterm)) (Data.context []) (freeListsValue freeLists)
      let viewed := ("view", viewValue []) :: bindings
      let both := ("view2", viewValue (freeLists.map indicesValue)) :: viewed
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue []) _
      · exact ListAccess.view_captured_returns bindings state "formal" [] rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, free_contributionsEnvironment, Subst.lookup]
      · apply let_returns program viewed both state state state (.var "view2") _ _
          (viewValue (freeLists.map indicesValue)) _
        · exact ListAccess.view_captured_returns viewed state "free-lists" (freeLists.map indicesValue) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, both, viewed, bindings, free_contributionsEnvironment, Subst.lookup]
        · apply free_contributions_view_captured_of_body both state state (viewValue [])
            (viewValue (freeLists.map indicesValue)) (Data.context target) (Data.context full)
            (listValue (arguments.map Data.preterm)) "view" "view2" "target" "full" "arguments" _
            (by simp [both, viewed, applySubst, Subst.lookup]) rfl
            (by simp [both, viewed, bindings, free_contributionsEnvironment, applySubst, Subst.lookup])
            (by simp [both, viewed, bindings, free_contributionsEnvironment, applySubst, Subst.lookup])
            (by simp [both, viewed, bindings, free_contributionsEnvironment, applySubst, Subst.lookup])
          rw [free_contributions_view_shape]
          cases freeLists with
          | nil =>
              let callee := free_contributions_viewEnvironment (viewValue []) (viewValue [])
                (Data.context target) (Data.context full) (listValue (arguments.map Data.preterm))
              apply case_returns program callee callee state state state _
                (.expression [viewValue [], viewValue []]) free_contributions_viewBody0 _ _ free_contributions_viewCases (read_cases_encoded _)
              · exact tuple_variables_return program callee state ["valueInput", "valueInputValue"]
              · simp [free_contributions_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, viewValue]
              · rw [free_contributions_view_body_0_shape]
                let wrapped := ("items", indicesValue []) :: callee
                apply let_returns program callee wrapped state state state (.var "items") _ _ (indicesValue []) _
                · exact empty_constructor_returns program callee state "MM0:L" list_is_data_constructor (by decide)
                · simp [SpaceSemantics.matchValue, matchAtom, wrapped, callee, free_contributions_viewEnvironment, Subst.lookup]
                · simpa [wrapped, resultValue, optionValue, contributions?, applySubst, Subst.lookup] using
                    unary_constructor_returns program wrapped state "Some" "items" some_is_data_constructor (by decide)
          | cons free freeLists =>
              let callee := free_contributions_viewEnvironment (viewValue []) (viewValue ((free :: freeLists).map indicesValue))
                (Data.context target) (Data.context full) (listValue (arguments.map Data.preterm))
              let bound := ("free-lists", freeListsValue freeLists) :: ("free", indicesValue free) :: callee
              apply case_returns program callee bound state state state _
                (.expression [viewValue [], viewValue ((free :: freeLists).map indicesValue)]) (.symbol "None") _ _
                free_contributions_viewCases (read_cases_encoded _)
              · exact tuple_variables_return program callee state ["valueInput", "valueInputValue"]
              · simp [free_contributions_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, freeListsValue,
                  bound, callee, free_contributions_viewEnvironment, Subst.lookup]
              · exact symbol_returns program bound state "None"
  | cons binder formal ih =>
      rw [free_contributions_shape]
      let bindings := free_contributionsEnvironment (Data.context target) (Data.context full)
        (listValue (arguments.map Data.preterm)) (Data.context (binder :: formal)) (freeListsValue freeLists)
      let viewed := ("view", viewValue ((binder :: formal).map Data.binder)) :: bindings
      let both := ("view2", viewValue (freeLists.map indicesValue)) :: viewed
      apply let_returns program bindings viewed state state state (.var "view") _ _ (viewValue ((binder :: formal).map Data.binder)) _
      · exact ListAccess.view_captured_returns bindings state "formal" ((binder :: formal).map Data.binder) rfl
      · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, free_contributionsEnvironment, Subst.lookup]
      · apply let_returns program viewed both state state state (.var "view2") _ _ (viewValue (freeLists.map indicesValue)) _
        · exact ListAccess.view_captured_returns viewed state "free-lists" (freeLists.map indicesValue) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, both, viewed, bindings, free_contributionsEnvironment, Subst.lookup]
        · apply free_contributions_view_captured_of_body both state state (viewValue ((binder :: formal).map Data.binder))
            (viewValue (freeLists.map indicesValue)) (Data.context target) (Data.context full)
            (listValue (arguments.map Data.preterm)) "view" "view2" "target" "full" "arguments" _
            (by simp [both, viewed, applySubst, Subst.lookup]) rfl
            (by simp [both, viewed, bindings, free_contributionsEnvironment, applySubst, Subst.lookup])
            (by simp [both, viewed, bindings, free_contributionsEnvironment, applySubst, Subst.lookup])
            (by simp [both, viewed, bindings, free_contributionsEnvironment, applySubst, Subst.lookup])
          rw [free_contributions_view_shape]
          cases freeLists with
          | nil =>
              let callee := free_contributions_viewEnvironment (viewValue ((binder :: formal).map Data.binder)) (viewValue [])
                (Data.context target) (Data.context full) (listValue (arguments.map Data.preterm))
              let bound := ("formal", Data.context formal) :: ("binder", Data.binder binder) :: callee
              apply case_returns program callee bound state state state _
                (.expression [viewValue ((binder :: formal).map Data.binder), viewValue []]) (.symbol "None") _ _
                free_contributions_viewCases (read_cases_encoded _)
              · exact tuple_variables_return program callee state ["valueInput", "valueInputValue"]
              · simp [free_contributions_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, Data.context,
                  bound, callee, free_contributions_viewEnvironment, Subst.lookup]
              · cases binder <;> exact symbol_returns program bound state "None"
          | cons free freeLists =>
              cases binder with
              | bound sort =>
                  let callee := free_contributions_viewEnvironment (viewValue ((Binder.bound sort :: formal).map Data.binder))
                    (viewValue ((free :: freeLists).map indicesValue)) (Data.context target) (Data.context full)
                    (listValue (arguments.map Data.preterm))
                  let bound := ("free-lists", freeListsValue freeLists) :: ("free", indicesValue free) ::
                    ("formal", Data.context formal) :: ("sort", natural sort) :: callee
                  apply case_returns program callee bound state state state _
                    (.expression [viewValue ((Binder.bound sort :: formal).map Data.binder), viewValue ((free :: freeLists).map indicesValue)])
                    free_contributions_viewBody3 _ _ free_contributions_viewCases (read_cases_encoded _)
                  · exact tuple_variables_return program callee state ["valueInput", "valueInputValue"]
                  · simp [free_contributions_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, Data.binder, Data.context, listValue,
                      freeListsValue, bound, callee, free_contributions_viewEnvironment, Subst.lookup]
                  · rw [free_contributions_view_body_3_shape]
                    exact free_contributions_captured_of_body bound state state _ _ _ _ _
                      "target" "full" "arguments" "formal" "free-lists" _
                      (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                      (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                      (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                      (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup]) rfl (ih freeLists)
              | regular sort deps =>
                  let callee := free_contributions_viewEnvironment (viewValue ((Binder.regular sort deps :: formal).map Data.binder))
                    (viewValue ((free :: freeLists).map indicesValue)) (Data.context target) (Data.context full)
                    (listValue (arguments.map Data.preterm))
                  let bound := ("free-lists", freeListsValue freeLists) :: ("free", indicesValue free) ::
                    ("formal", Data.context formal) :: ("dependencies", Data.dependencies deps) :: ("sort", natural sort) :: callee
                  apply case_returns program callee bound state state state _
                    (.expression [viewValue ((Binder.regular sort deps :: formal).map Data.binder), viewValue ((free :: freeLists).map indicesValue)])
                    free_contributions_viewBody4 _ _ free_contributions_viewCases (read_cases_encoded _)
                  · exact tuple_variables_return program callee state ["valueInput", "valueInputValue"]
                  · simp [free_contributions_view_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, Data.binder, Data.context, listValue,
                      freeListsValue, bound, callee, free_contributions_viewEnvironment, Subst.lookup]
                  · rw [free_contributions_view_body_4_shape]
                    let images := ("freeImagesResult", resultValue (images? target full arguments (deps.sort (· ≤ ·)))) :: bound
                    apply let_returns program bound images state state state (.var "freeImagesResult") _ _
                      (resultValue (images? target full arguments (deps.sort (· ≤ ·)))) _
                    · exact FreeVariableImages.captured_returns bound state target full arguments (deps.sort (· ≤ ·))
                        "target" "full" "arguments" "dependencies"
                        (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [bound, applySubst, Subst.lookup, Data.dependencies, indicesValue])
                    · simp [SpaceSemantics.matchValue, matchAtom, images, bound, callee, free_contributions_viewEnvironment, Subst.lookup]
                    · apply free_contribution_bound_captured_of_body images state state
                        (resultValue (images? target full arguments (deps.sort (· ≤ ·)))) (Data.context target)
                        (Data.context full) (listValue (arguments.map Data.preterm)) (Data.context formal)
                        (indicesValue free) (freeListsValue freeLists)
                        "freeImagesResult" "target" "full" "arguments" "formal" "free" "free-lists" _ rfl
                        (by simp [images, bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [images, bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [images, bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [images, bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [images, bound, callee, free_contributions_viewEnvironment, applySubst, Subst.lookup])
                        (by simp [images, bound, applySubst, Subst.lookup])
                      exact bound_body_returns state target full arguments formal free freeLists
                        (images? target full arguments (deps.sort (· ≤ ·))) (ih freeLists)

theorem captured_returns (bindings : Subst) (state : State) (target full : Context) (arguments : List Preterm)
    (formal : Context) (freeLists : List (List Nat)) (targetName fullName argumentsName formalName freeListsName : String)
    (capturedTarget : applySubst bindings (.var targetName) = Data.context target)
    (capturedFull : applySubst bindings (.var fullName) = Data.context full)
    (capturedArguments : applySubst bindings (.var argumentsName) = listValue (arguments.map Data.preterm))
    (capturedFormal : applySubst bindings (.var formalName) = Data.context formal)
    (capturedFreeLists : applySubst bindings (.var freeListsName) = listValue (freeLists.map indicesValue)) :
    PureReturns program bindings state (.expression [.symbol "mm0:free-contributions", .var targetName,
      .var fullName, .var argumentsName, .var formalName, .var freeListsName]) state
      (resultValue (contributions? target full arguments formal freeLists)) :=
  free_contributions_captured_of_body bindings state state _ _ _ _ _ targetName fullName argumentsName formalName freeListsName _
    capturedTarget capturedFull capturedArguments capturedFormal capturedFreeLists (body_returns state target full arguments formal freeLists)

end Mettapedia.Languages.MM0.MeTTa.FreeVariableContributions
