import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AssertionMatchExecution
import Mettapedia.Languages.MeTTa.PeTTa.CallComposition

/-!
# Ordered recursion in the original assertion matcher

The execution laws use the unchanged binary-source equations. Recursive calls
compute the original fuel decrement, preserve physical slots and unread command
suffixes, and propagate explicit refusals. The target entries retain their source
allocation identity and complete inert payload.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MM0.MeTTa.MMBRecursiveMatchExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (expressionValue)
open MMBAssertionMatchExecution (matchingValue matchedValue)

abbrev program := MMBAssertionMatchExecution.program

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD
    ⟨"", [], .symbol "None"⟩
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

/-- Readout of the original successful slots and unread command suffix. -/
def resultValue (images context resolver : Atom) : Option (List Atom × List Atom) → Atom
  | none => .symbol "None"
  | some (slots, rest) => matchedValue slots images context resolver rest

def callBindings (fuel : Nat) (matching codes target : Atom) : Subst :=
  [("target", target), ("codes", codes), ("matching", matching), ("fuel", natural fuel)]
def callExpression (head : String) : Atom :=
  .expression [.symbol head, .var "fuel", .var "matching", .var "codes", .var "target"]

private theorem decrement_call_returns (state : State) (head : String) (fuel : Nat)
    (matching codes target answer : Atom) (bindings : Subst) (remaining : List Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (number : argumentIsRaw program head 0 = false)
    (raw : ∀ offset < remaining.length, argumentIsRaw program head (1 + offset) = true)
    (fuelCaptured : applySubst bindings (.var "fuel") = natural (fuel + 1))
    (captured : remaining.map (applySubst bindings) = [matching, codes, target])
    (returned : PureReturns program (callBindings fuel matching codes target) state (callExpression head) state answer) :
    PureReturns program bindings state
      (.expression (.symbol head :: .expression [.symbol "-", .var "fuel", natural 1] :: remaining)) state answer := by
  -- Four arguments: never the three-argument `match` query.
  have three : remaining.length = 3 := by simpa using congrArg List.length captured
  apply application_answers program bindings state state head
    (.expression [.symbol "-", .var "fuel", natural 1] :: remaining) [answer] dispatch _
    (controlForm_application ordinary (.inr (by simp [three])))
  apply evaluated_argument_returns program bindings state state state (.function head)
    (.expression [.symbol "-", .var "fuel", natural 1]) (natural fuel) _ remaining [] 0 number
  · apply native_binary_call_returns program bindings state state state state "-" (.var "fuel") (natural 1)
      (natural (fuel + 1)) (natural 1) (natural fuel)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · simpa [fuelCaptured] using variable_returns program bindings state "fuel"
    · exact grounded_returns program bindings state (.int 1)
    · simp [StdLib.integer_subtraction, natural]
  · apply raw_arguments_return program bindings state state head remaining [natural fuel] 1 answer raw
    have stage := captured_function_arguments_returns_of_shape program
      (callBindings fuel matching codes target) bindings state state head
      [.var "fuel", .var "matching", .var "codes", .var "target"] (1 + remaining.length) answer
      dispatch (controlForm_application ordinary (.inr (by simp))) (by
        intro offset argument found
        have bounded : offset < 4 := by
          have inside := (getElem?_eq_some_iff.mp found).choose
          simpa using inside
        interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl) returned
    simpa [callBindings, applySubst, applySubst.applySubstList, Subst.lookup, captured] using stage

private def childrenEquation := sourceEquation "mm0:mmb:match-expressions"
private def childrenCases := casesOf childrenEquation.body
private def childrenCons := (childrenCases[1]'(by decide)).2
private def childrenNext := match childrenCons with
  | .expression [_, _, next, _] => next
  | _ => .symbol "None"
private def childrenNextCases := casesOf childrenNext
private def childrenTail := (childrenNextCases[0]'(by decide)).2
private def childrenEnvironment (fuel : Nat) (matching codes : Atom) (arguments : List Atom) : Subst :=
  [("arguments", .expression arguments), ("codes", codes), ("matching", matching), ("fuel", natural fuel)]

private theorem children_unique : program.equations.filter (·.head == "mm0:mmb:match-expressions") = [childrenEquation] := by
  decide +kernel
private theorem children_formals : childrenEquation.arguments =
    [.var "fuel", .var "matching", .var "codes", .expression [.symbol "MM0:L", .var "arguments"]] := by decide
private theorem children_shape : childrenEquation.body = .expression [.symbol "case", .var "arguments",
    .expression (childrenCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem children_cases_shape : childrenCases =
    [(.expression [], .expression [.symbol "Some", .expression [.symbol "MM0:MMBMatched", .var "matching", .var "codes"]]),
     (.expression [.symbol "cons", .var "first", .var "rest"], childrenCons), (.var "bad", .symbol "None")] := by decide
private theorem children_cons_shape : childrenCons = .expression [.symbol "if",
    .expression [.symbol "<", natural 0, .var "fuel"], childrenNext, .symbol "None"] := by decide
private theorem children_next_shape : childrenNext = .expression [.symbol "case",
    .expression [.symbol "mm0:mmb:match-expression", .expression [.symbol "-", .var "fuel", natural 1],
      .var "matching", .var "codes", .var "first"],
    .expression (childrenNextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem children_next_cases_shape : childrenNextCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBMatched", .var "after", .var "remaining"]], childrenTail),
     (.var "bad", .symbol "None")] := by decide
private theorem children_tail_shape : childrenTail = .expression [.symbol "mm0:mmb:match-expressions",
    .expression [.symbol "-", .var "fuel", natural 1], .var "after", .var "remaining",
    .expression [.symbol "MM0:L", .var "rest"]] := by decide
private theorem children_clause (fuel : Nat) (matching codes : Atom) (arguments : List Atom) :
    clauses program "mm0:mmb:match-expressions" [natural fuel, matching, codes, listValue arguments] =
      [.evaluate (childrenEnvironment fuel matching codes arguments) childrenEquation.body] := by
  rw [clauses_use_only_the_named_equations, children_unique]
  simp [children_formals, childrenEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem children_from_body (state : State) (fuel : Nat) (matching codes : Atom)
    (arguments : List Atom) (answer : Atom)
    (body : PureReturns program (childrenEnvironment fuel matching codes arguments) state childrenEquation.body state answer) :
    PureReturns program (callBindings fuel matching codes (listValue arguments)) state
      (callExpression "mm0:mmb:match-expressions") state answer := by
  apply call_returns program _ state state "mm0:mmb:match-expressions" _ _ (by decide +kernel) _ (by decide)
  apply variable_arguments_return program _ state state (.function "mm0:mmb:match-expressions")
    ["fuel", "matching", "codes", "target"] [] 0 answer
  simpa [callBindings, applySubst, Subst.lookup] using
    authored_function_arguments_return program _ (childrenEnvironment fuel matching codes arguments) state state
      "mm0:mmb:match-expressions" [natural fuel, matching, codes, listValue arguments] 4 childrenEquation.body answer
      (by decide) (by decide) (children_clause fuel matching codes arguments) body

private theorem positive_test (state : State) (bindings : Subst) (fuel : Nat)
    (captured : applySubst bindings (.var "fuel") = natural (fuel + 1)) :
    PureReturns program bindings state (.expression [.symbol "<", natural 0, .var "fuel"]) state (boolean true) := by
  apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
    (natural 0) (natural (fuel + 1)) (boolean true)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · exact grounded_returns program bindings state (.int 0)
  · simpa [captured] using variable_returns program bindings state "fuel"
  · simp [StdLib.less_comparison, natural, boolean]

private theorem children_empty_body (state : State) (fuel : Nat) (matching codes : Atom) :
    PureReturns program (childrenEnvironment fuel matching codes []) state childrenEquation.body state
      (optionValue (some (.expression [.symbol "MM0:MMBMatched", matching, codes]))) := by
  let bindings := childrenEnvironment fuel matching codes []
  rw [children_shape]
  apply case_returns program bindings bindings state state state (.var "arguments") (.expression [])
    (.expression [.symbol "Some", .expression [.symbol "MM0:MMBMatched", .var "matching", .var "codes"]]) _ _
    childrenCases (read_cases_encoded childrenCases)
  · exact variable_returns program bindings state "arguments"
  · simp [children_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, bindings, childrenEnvironment]
  · apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
    simpa [bindings, childrenEnvironment, applySubst, Subst.lookup, optionValue] using
      constructor_variables_return program bindings state "MM0:MMBMatched" ["matching", "codes"]
        (by decide +kernel) (by decide)

/-- Empty child lists return before the original fuel test. -/
theorem children_empty_returns (state : State) (fuel : Nat) (matching codes : Atom) :
    PureReturns program (callBindings fuel matching codes (listValue [])) state
      (callExpression "mm0:mmb:match-expressions") state
      (optionValue (some (.expression [.symbol "MM0:MMBMatched", matching, codes]))) :=
  children_from_body state fuel matching codes [] _ (children_empty_body state fuel matching codes)

private theorem children_cons_body (state : State) (fuel : Nat) (matching codes first : Atom) (rest : List Atom)
    (child : Atom) (answer : Atom)
    (firstReturned : PureReturns program (callBindings fuel matching codes first) state
      (callExpression "mm0:mmb:match-expression") state child)
    (continuation : ∀ after remaining, child = optionValue (some (.expression [.symbol "MM0:MMBMatched", after, remaining])) →
      PureReturns program (callBindings fuel after remaining (listValue rest)) state
        (callExpression "mm0:mmb:match-expressions") state answer)
    (refused : child = .symbol "None" → answer = .symbol "None")
    (shape : child = .symbol "None" ∨ ∃ after remaining, child = optionValue (some (.expression [.symbol "MM0:MMBMatched", after, remaining]))) :
    PureReturns program (childrenEnvironment (fuel + 1) matching codes (first :: rest)) state childrenEquation.body state answer := by
  let bindings := childrenEnvironment (fuel + 1) matching codes (first :: rest)
  let bound := ("rest", .expression rest) :: ("first", first) :: bindings
  rw [children_shape]
  apply case_returns program bindings bound state state state (.var "arguments") (.expression (first :: rest))
    childrenCons _ _ childrenCases (read_cases_encoded childrenCases)
  · exact variable_returns program bindings state "arguments"
  · simp [children_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, childrenEnvironment]
  · rw [children_cons_shape]
    apply if_returns program bound state state state _ (boolean true) _ _ _
    · exact positive_test state bound fuel rfl
    · simpa [boolean] using (show PureReturns program bound state childrenNext state answer from by
        rw [children_next_shape]
        have evaluated := decrement_call_returns state "mm0:mmb:match-expression" fuel matching codes first child bound
          [.var "matching", .var "codes", .var "first"] (by decide +kernel) (by decide) (by decide +kernel)
          (by intro offset inside; have bounded : offset < 3 := (by simpa using inside); interval_cases offset <;> decide +kernel) rfl rfl firstReturned
        rcases shape with absent | ⟨after, remaining, present⟩
        · let failed := ("bad", child) :: bound
          apply case_returns program bound failed state state state _ child (.symbol "None") answer _
            childrenNextCases (read_cases_encoded childrenNextCases) evaluated
          · simp [children_next_cases_shape, absent, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              matchAtom, Subst.lookup, failed, bound, bindings, childrenEnvironment]
          · rw [refused absent]
            exact symbol_returns program failed state "None"
        · let next := ("remaining", remaining) :: ("after", after) :: bound
          apply case_returns program bound next state state state _ child childrenTail answer _
            childrenNextCases (read_cases_encoded childrenNextCases) evaluated
          · simp [children_next_cases_shape, present, optionValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, next, bound, bindings, childrenEnvironment]
          · rw [children_tail_shape]
            exact decrement_call_returns state "mm0:mmb:match-expressions" fuel after remaining (listValue rest) answer next
              [.var "after", .var "remaining", .expression [.symbol "MM0:L", .var "rest"]]
              (by decide +kernel) (by decide) (by decide +kernel)
              (by intro offset inside; have bounded : offset < 3 := (by simpa using inside); interval_cases offset <;> decide +kernel) rfl rfl
              (continuation after remaining present))


private theorem children_zero_body (state : State) (matching codes first : Atom) (rest : List Atom) :
    PureReturns program (childrenEnvironment 0 matching codes (first :: rest)) state childrenEquation.body state (.symbol "None") := by
  let bindings := childrenEnvironment 0 matching codes (first :: rest)
  let bound := ("rest", .expression rest) :: ("first", first) :: bindings
  rw [children_shape]
  apply case_returns program bindings bound state state state (.var "arguments") (.expression (first :: rest))
    childrenCons _ _ childrenCases (read_cases_encoded childrenCases)
  · exact variable_returns program bindings state "arguments"
  · simp [children_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, childrenEnvironment]
  · rw [children_cons_shape]
    apply if_returns program bound state state state _ (boolean false) _ _ _
    · apply native_binary_call_returns program bound state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural 0) (boolean false)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program bound state (.int 0)
      · exact variable_returns program bound state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · simpa [boolean] using symbol_returns program bound state "None"

/-- Nonempty child lists are refused at zero matching fuel. -/
theorem children_zero_returns (state : State) (matching codes first : Atom) (rest : List Atom) :
    PureReturns program (callBindings 0 matching codes (listValue (first :: rest))) state
      (callExpression "mm0:mmb:match-expressions") state (.symbol "None") :=
  children_from_body state 0 matching codes (first :: rest) _ (children_zero_body state matching codes first rest)

private def hypothesesEquation := sourceEquation "mm0:mmb:match-hypotheses"
private def hypothesesCases := casesOf hypothesesEquation.body
private def hypothesesCons := (hypothesesCases[1]'(by decide)).2
private def hypothesesNext := match hypothesesCons with
  | .expression [_, _, next, _] => next
  | _ => .symbol "None"
private def hypothesesNextCases := casesOf hypothesesNext
private def hypothesesTail := (hypothesesNextCases[0]'(by decide)).2
private def hypothesesEnvironment (fuel : Nat) (matching : Atom) (codes hypotheses : List Atom) : Subst :=
  [("hypotheses", .expression hypotheses), ("codes", .expression codes), ("matching", matching), ("fuel", natural fuel)]
private theorem hypotheses_unique : program.equations.filter (·.head == "mm0:mmb:match-hypotheses") = [hypothesesEquation] := by
  decide +kernel
private theorem hypotheses_formals : hypothesesEquation.arguments =
    [.var "fuel", .var "matching", .expression [.symbol "MM0:L", .var "codes"],
      .expression [.symbol "MM0:L", .var "hypotheses"]] := by decide
private theorem hypotheses_shape : hypothesesEquation.body = .expression [.symbol "case",
    .expression [.var "codes", .var "hypotheses"],
    .expression (hypothesesCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem hypotheses_cases_shape : hypothesesCases =
    [(.expression [.expression [], .expression []], .expression [.symbol "Some", .var "matching"]),
     (.expression [.expression [.symbol "cons", .expression [.symbol "MM0:MMBCode", natural 54,
        .var "data", .var "start", .var "after"], .var "rest"],
        .expression [.symbol "cons", .var "first", .var "earlier"]], hypothesesCons),
      (.var "bad", .symbol "None")] := by decide
private theorem hypotheses_cons_shape : hypothesesCons = .expression [.symbol "if",
    .expression [.symbol "<", natural 0, .var "fuel"], hypothesesNext, .symbol "None"] := by decide
private theorem hypotheses_next_shape : hypothesesNext = .expression [.symbol "case",
    .expression [.symbol "mm0:mmb:match-expression", .expression [.symbol "-", .var "fuel", natural 1],
      .var "matching", .expression [.symbol "MM0:L", .var "rest"], .var "first"],
    .expression (hypothesesNextCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem hypotheses_next_cases_shape : hypothesesNextCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBMatched", .var "next", .var "remaining"]], hypothesesTail),
     (.var "bad", .symbol "None")] := by decide
private theorem hypotheses_tail_shape : hypothesesTail = .expression [.symbol "mm0:mmb:match-hypotheses",
    .expression [.symbol "-", .var "fuel", natural 1], .var "next", .var "remaining",
    .expression [.symbol "MM0:L", .var "earlier"]] := by decide
private theorem hypotheses_clause (fuel : Nat) (matching : Atom) (codes hypotheses : List Atom) :
    clauses program "mm0:mmb:match-hypotheses" [natural fuel, matching, listValue codes, listValue hypotheses] =
      [.evaluate (hypothesesEnvironment fuel matching codes hypotheses) hypothesesEquation.body] := by
  rw [clauses_use_only_the_named_equations, hypotheses_unique]
  simp [hypotheses_formals, hypothesesEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem hypotheses_from_body (state : State) (fuel : Nat) (matching : Atom)
    (codes hypotheses : List Atom) (answer : Atom)
    (body : PureReturns program (hypothesesEnvironment fuel matching codes hypotheses) state hypothesesEquation.body state answer) :
    PureReturns program (callBindings fuel matching (listValue codes) (listValue hypotheses)) state
      (callExpression "mm0:mmb:match-hypotheses") state answer := by
  apply call_returns program _ state state "mm0:mmb:match-hypotheses" _ _ (by decide +kernel) _ (by decide)
  apply variable_arguments_return program _ state state (.function "mm0:mmb:match-hypotheses")
    ["fuel", "matching", "codes", "target"] [] 0 answer
  simpa [callBindings, applySubst, Subst.lookup] using
    authored_function_arguments_return program _ (hypothesesEnvironment fuel matching codes hypotheses) state state
      "mm0:mmb:match-hypotheses" [natural fuel, matching, listValue codes, listValue hypotheses] 4 hypothesesEquation.body answer
      (by decide) (by decide) (hypotheses_clause fuel matching codes hypotheses) body

/-- The original hypothesis matcher accepts exactly the empty pair without
inspecting fuel. A nonempty command suffix is not silently discarded. -/
theorem hypotheses_empty_returns (state : State) (fuel : Nat) (matching : Atom) :
    PureReturns program (callBindings fuel matching (listValue []) (listValue [])) state
      (callExpression "mm0:mmb:match-hypotheses") state (optionValue (some matching)) := by
  apply hypotheses_from_body state fuel matching [] [] _
  let bindings := hypothesesEnvironment fuel matching [] []
  rw [hypotheses_shape]
  apply case_returns program bindings bindings state state state (.expression [.var "codes", .var "hypotheses"])
    (.expression [.expression [], .expression []]) (.expression [.symbol "Some", .var "matching"]) _ _
    hypothesesCases (read_cases_encoded hypothesesCases)
  · simpa [bindings, hypothesesEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["codes", "hypotheses"]
  · simp [hypotheses_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, bindings, hypothesesEnvironment]
  · simpa [bindings, hypothesesEnvironment, applySubst, Subst.lookup, optionValue] using
      unary_constructor_returns program bindings state "Some" "matching" (by decide +kernel) (by decide)

private theorem hypotheses_cons_body (state : State) (fuel data start after : Nat) (matching : Atom)
    (codes : List Atom) (first : Atom) (earlier : List Atom) (child answer : Atom)
    (firstReturned : PureReturns program (callBindings fuel matching (listValue codes) first) state
      (callExpression "mm0:mmb:match-expression") state child)
    (continuation : ∀ next remaining, child = optionValue (some (.expression [.symbol "MM0:MMBMatched", next, remaining])) →
      PureReturns program (callBindings fuel next remaining (listValue earlier)) state
        (callExpression "mm0:mmb:match-hypotheses") state answer)
    (refused : child = .symbol "None" → answer = .symbol "None")
    (shape : child = .symbol "None" ∨ ∃ next remaining, child = optionValue (some (.expression [.symbol "MM0:MMBMatched", next, remaining]))) :
    PureReturns program
      (hypothesesEnvironment (fuel + 1) matching (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier))
      state hypothesesEquation.body state answer := by
  let bindings := hypothesesEnvironment (fuel + 1) matching (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier)
  let bound := ("earlier", .expression earlier) :: ("first", first) :: ("rest", .expression codes) ::
    ("after", natural after) :: ("start", natural start) :: ("data", natural data) :: bindings
  rw [hypotheses_shape]
  apply case_returns program bindings bound state state state (.expression [.var "codes", .var "hypotheses"])
    (.expression [.expression (MMBExecution.commandValue 54 data start after :: codes), .expression (first :: earlier)])
    hypothesesCons _ _ hypothesesCases (read_cases_encoded hypothesesCases)
  · simpa [bindings, hypothesesEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["codes", "hypotheses"]
  · simp [hypotheses_cases_shape, MMBExecution.commandValue, natural, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, hypothesesEnvironment]
  · rw [hypotheses_cons_shape]
    apply if_returns program bound state state state _ (boolean true) _ _ _
    · exact positive_test state bound fuel rfl
    · simpa [boolean] using (show PureReturns program bound state hypothesesNext state answer from by
        rw [hypotheses_next_shape]
        have evaluated := decrement_call_returns state "mm0:mmb:match-expression" fuel matching (listValue codes) first child bound
          [.var "matching", .expression [.symbol "MM0:L", .var "rest"], .var "first"]
          (by decide +kernel) (by decide) (by decide +kernel)
          (by intro offset inside; have bounded : offset < 3 := (by simpa using inside); interval_cases offset <;> decide +kernel)
          rfl rfl firstReturned
        rcases shape with absent | ⟨next, remaining, present⟩
        · let failed := ("bad", child) :: bound
          apply case_returns program bound failed state state state _ child (.symbol "None") answer _
            hypothesesNextCases (read_cases_encoded hypothesesNextCases) evaluated
          · simp [hypotheses_next_cases_shape, absent, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              matchAtom, Subst.lookup, failed, bound, bindings, hypothesesEnvironment]
          · rw [refused absent]
            exact symbol_returns program failed state "None"
        · let continued := ("remaining", remaining) :: ("next", next) :: bound
          apply case_returns program bound continued state state state _ child hypothesesTail answer _
            hypothesesNextCases (read_cases_encoded hypothesesNextCases) evaluated
          · simp [hypotheses_next_cases_shape, present, optionValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, continued, bound, bindings, hypothesesEnvironment]
          · rw [hypotheses_tail_shape]
            exact decrement_call_returns state "mm0:mmb:match-hypotheses" fuel next remaining (listValue earlier) answer continued
              [.var "next", .var "remaining", .expression [.symbol "MM0:L", .var "earlier"]]
              (by decide +kernel) (by decide) (by decide +kernel)
              (by intro offset inside; have bounded : offset < 3 := (by simpa using inside); interval_cases offset <;> decide +kernel)
              rfl rfl (continuation next remaining present))


/-- The source reserves one unavailable slot before matching saved children. -/
def reservedSlots (save : Bool) (slots : List Atom) : List Atom :=
  if save then slots ++ [.symbol "None"] else slots

/-- The source fills exactly the original reservation after successful children.
The existing out-of-range refusal is retained in the readout. -/
def finishedMatch (save : Bool) (slots : List Atom) (target : Atom) :
    Option (List Atom × List Atom) → Option (List Atom × List Atom)
  | none => none
  | some (after, rest) =>
      if save then (after[slots.length]?).map fun _ => (after.set slots.length (optionValue (some target)), rest)
      else some (after, rest)

private def termEquation := sourceEquation "mm0:mmb:match-term"
private def termCases := casesOf termEquation.body
private def termApplication := (termCases[0]'(by decide)).2
private def termWork := match termApplication with | .expression [_, _, work, _] => work | _ => .symbol "None"
private def termChildren := match termWork with | .expression [_, _, children] => children | _ => .symbol "None"
private def termChildrenCases := casesOf termChildren
private def termUpdate := (termChildrenCases[0]'(by decide)).2
private def termFinish := match termUpdate with | .expression [_, _, _, finish] => finish | _ => .symbol "None"
private def termFinishCases := casesOf termFinish
private def termRebuild := (termFinishCases[0]'(by decide)).2
private def termEnvironment (fuel term : Nat) (save : Bool) (slots : List Atom)
    (images context resolver codes target : Atom) : Subst :=
  [("target", target), ("codes", codes), ("save", boolean save), ("term", natural term),
    ("mode", .symbol "MM0:MMBAssertionMatch"), ("resolver", resolver), ("context", context),
    ("images", images), ("slots", .expression slots), ("fuel", natural fuel)]
private def termCaptured (fuel term : Nat) (save : Bool) (slots : List Atom)
    (images context resolver codes target : Atom) : Subst :=
  [("target", target), ("codes", codes), ("save", boolean save), ("term", natural term),
    ("matching", matchingValue slots images context resolver), ("fuel", natural fuel)]
private def termCall : Atom := .expression [.symbol "mm0:mmb:match-term", .var "fuel", .var "matching",
  .var "term", .var "save", .var "codes", .var "target"]
private theorem term_unique : program.equations.filter (·.head == "mm0:mmb:match-term") = [termEquation] := by
  decide +kernel
private theorem term_formals : termEquation.arguments =
    [.var "fuel", .expression [.symbol "MM0:MMBMState", .expression [.symbol "MM0:L", .var "slots"],
      .var "images", .var "context", .var "resolver", .var "mode"],
     .var "term", .var "save", .var "codes", .var "target"] := by decide
private theorem term_shape : termEquation.body = .expression [.symbol "case", .var "target",
    .expression (termCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_cases_shape : termCases =
    [(.expression [.symbol "MM0:MMBExpression", .var "pointer", .var "value",
        .expression [.symbol "MM0:MMBApplication", .var "binary", .var "args"]], termApplication),
      (.var "bad", .symbol "None")] := by decide
private theorem term_application_shape : termApplication = .expression [.symbol "if",
    .expression [.symbol "==", .var "binary", .var "term"], termWork, .symbol "None"] := by decide
private theorem term_work_shape : termWork = .expression [.symbol "let*",
    .expression [.expression [.var "index", .expression [.symbol "size-atom", .var "slots"]],
      .expression [.var "reserved", .expression [.symbol "if", .var "save",
        .expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "slots"], .symbol "None"],
        .expression [.symbol "MM0:L", .var "slots"]]]], termChildren] := by decide
private theorem term_children_shape : termChildren = .expression [.symbol "case",
    .expression [.symbol "mm0:mmb:match-expressions", .expression [.symbol "-", .var "fuel", natural 1],
      .expression [.symbol "MM0:MMBMState", .var "reserved", .var "images", .var "context", .var "resolver", .var "mode"],
      .var "codes", .var "args"], .expression (termChildrenCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_children_cases_shape : termChildrenCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBMatched",
      .expression [.symbol "MM0:MMBMState", .var "after", .var "extra", .var "ctx", .var "state", .var "kind"], .var "rest"]],
      termUpdate), (.var "bad", .symbol "None")] := by decide
private theorem term_update_shape : termUpdate = .expression [.symbol "let", .var "updated",
    .expression [.symbol "if", .var "save",
      .expression [.symbol "mm0:mmb:set-at", .var "after", .var "index", .expression [.symbol "Some", .var "target"]],
      .expression [.symbol "Some", .var "after"]], termFinish] := by decide
private theorem term_finish_shape : termFinish = .expression [.symbol "case", .var "updated",
    .expression (termFinishCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_finish_cases_shape : termFinishCases =
    [(.expression [.symbol "Some", .var "final"], termRebuild), (.var "bad", .symbol "None")] := by decide
private theorem term_rebuild_shape : termRebuild = .expression [.symbol "Some", .expression [.symbol "MM0:MMBMatched",
    .expression [.symbol "MM0:MMBMState", .var "final", .var "extra", .var "ctx", .var "state", .var "kind"],
    .var "rest"]] := by decide
private theorem term_clause (fuel term : Nat) (save : Bool) (slots : List Atom)
    (images context resolver codes target : Atom) :
    clauses program "mm0:mmb:match-term"
      [natural fuel, matchingValue slots images context resolver, natural term, boolean save, codes, target] =
      [.evaluate (termEnvironment fuel term save slots images context resolver codes target) termEquation.body] := by
  rw [clauses_use_only_the_named_equations, term_unique]
  simp [term_formals, termEnvironment, matchingValue, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem term_from_body (state : State) (fuel term : Nat) (save : Bool) (slots : List Atom)
    (images context resolver codes target answer : Atom)
    (body : PureReturns program (termEnvironment fuel term save slots images context resolver codes target)
      state termEquation.body state answer) :
    PureReturns program (termCaptured fuel term save slots images context resolver codes target)
      state termCall state answer := by
  apply call_returns program _ state state "mm0:mmb:match-term" _ _ (by decide +kernel) _ (by decide)
  apply variable_arguments_return program _ state state (.function "mm0:mmb:match-term")
    ["fuel", "matching", "term", "save", "codes", "target"] [] 0 answer
  simpa [termCaptured, applySubst, Subst.lookup] using
    authored_function_arguments_return program _ (termEnvironment fuel term save slots images context resolver codes target)
      state state "mm0:mmb:match-term"
      [natural fuel, matchingValue slots images context resolver, natural term, boolean save, codes, target]
      6 termEquation.body answer (by decide) (by decide)
      (term_clause fuel term save slots images context resolver codes target) body

private theorem term_rebuild_returns (state : State) (bindings : Subst) (final rest : List Atom)
    (images context resolver : Atom)
    (finalCaptured : applySubst bindings (.var "final") = listValue final)
    (extraCaptured : applySubst bindings (.var "extra") = images)
    (ctxCaptured : applySubst bindings (.var "ctx") = context)
    (stateCaptured : applySubst bindings (.var "state") = resolver)
    (kindCaptured : applySubst bindings (.var "kind") = .symbol "MM0:MMBAssertionMatch")
    (restCaptured : applySubst bindings (.var "rest") = listValue rest) :
    PureReturns program bindings state termRebuild state (matchedValue final images context resolver rest) := by
  rw [term_rebuild_shape]
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply binary_constructor_returns program bindings state state state "MM0:MMBMatched" _ _ _ _
    (by decide +kernel) (by decide)
  · simpa [finalCaptured, extraCaptured, ctxCaptured, stateCaptured, kindCaptured, matchingValue] using
      constructor_variables_return program bindings state "MM0:MMBMState" ["final", "extra", "ctx", "state", "kind"]
        (by decide +kernel) (by decide)
  · simpa [restCaptured] using variable_returns program bindings state "rest"

private theorem set_saved_returns (state : State) (bindings : Subst) (after : List Atom) (index : Nat) (target : Atom)
    (afterCaptured : applySubst bindings (.var "after") = listValue after)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (targetCaptured : applySubst bindings (.var "target") = target) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:set-at", .var "after", .var "index", .expression [.symbol "Some", .var "target"]])
      state (MMBSlotExecution.setResult after index (optionValue (some target))) := by
  let prior : Subst := [("items", listValue after), ("index", natural index), ("value", optionValue (some target))]
  have returned := MMBSlotExecution.set_at_returns prior state after index (optionValue (some target)) "items" "index" "value" rfl rfl rfl
  apply captured_call_returns program prior bindings state state "mm0:mmb:set-at"
    [.var "items", .var "index", .var "value"] [.var "after", .var "index", .expression [.symbol "Some", .var "target"]] _
    (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have bounded : offset < 3 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
    interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
  · intro offset argument found
    have bounded : offset < 3 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
    interval_cases offset
    · right; simp at found; subst argument; rfl
    · right; simp at found; subst argument; rfl
    · left; decide +kernel
  · change [listValue after, natural index, optionValue (some target)] =
      [applySubst bindings (.var "after"), applySubst bindings (.var "index"),
        .expression [.symbol "Some", applySubst bindings (.var "target")]]
    simp only [afterCaptured, indexCaptured, targetCaptured, optionValue]

private theorem term_update_returns (state : State) (fuel term pointer : Nat) (save : Bool)
    (slots children after rest : List Atom) (images context resolver codes value : Atom) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
    let bindings := ("rest", listValue rest) :: ("kind", .symbol "MM0:MMBAssertionMatch") :: ("state", resolver) ::
      ("ctx", context) :: ("extra", images) :: ("after", listValue after) ::
      ("reserved", listValue (reservedSlots save slots)) :: ("index", natural slots.length) ::
      ("args", listValue children) :: ("binary", natural term) :: ("value", value) :: ("pointer", natural pointer) ::
      termEnvironment (fuel + 1) term save slots images context resolver codes target
    PureReturns program bindings state termUpdate state
      (resultValue images context resolver (finishedMatch save slots target (some (after, rest)))) := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
  let bindings := ("rest", listValue rest) :: ("kind", .symbol "MM0:MMBAssertionMatch") :: ("state", resolver) ::
      ("ctx", context) :: ("extra", images) :: ("after", listValue after) ::
      ("reserved", listValue (reservedSlots save slots)) :: ("index", natural slots.length) ::
      ("args", listValue children) :: ("binary", natural term) :: ("value", value) :: ("pointer", natural pointer) ::
      termEnvironment (fuel + 1) term save slots images context resolver codes target
  let updated : Option (List Atom) := if save then (after[slots.length]?).map fun _ => after.set slots.length (optionValue (some target)) else some after
  let bound := ("updated", optionValue (updated.map listValue)) :: bindings
  rw [term_update_shape]
  apply let_returns program bindings bound state state state (.var "updated") _ _ (optionValue (updated.map listValue)) _
  · apply if_returns program bindings state state state (.var "save") (boolean save) _ _ _
    · exact variable_returns program bindings state "save"
    · cases save
      · simpa [boolean, updated, bindings, termEnvironment, applySubst, Subst.lookup, optionValue] using
          unary_constructor_returns program bindings state "Some" "after" (by decide +kernel) (by decide)
      · simpa [boolean, updated, MMBSlotExecution.setResult, bindings, termEnvironment, Function.comp_def] using
          set_saved_returns state bindings after slots.length target rfl rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, bindings, termEnvironment]
  · rw [term_finish_shape]
    cases accepted : updated with
    | none =>
        let failed := ("bad", .symbol "None") :: bound
        apply case_returns program bound failed state state state (.var "updated") (.symbol "None") (.symbol "None") _ _
          termFinishCases (read_cases_encoded termFinishCases)
        · simpa [bound, accepted, optionValue, applySubst, Subst.lookup] using variable_returns program bound state "updated"
        · simp [term_finish_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
            Subst.lookup, failed, bound, accepted, optionValue, bindings, termEnvironment]
        · have refused : finishedMatch save slots target (some (after, rest)) = none := by
            cases save <;> simp_all [updated, finishedMatch]
          dsimp only [target] at refused
          simpa [refused, resultValue] using symbol_returns program failed state "None"
    | some final =>
        let finalBindings := ("final", listValue final) :: bound
        apply case_returns program bound finalBindings state state state (.var "updated") (optionValue (some (listValue final)))
          termRebuild _ _ termFinishCases (read_cases_encoded termFinishCases)
        · simpa [bound, accepted, applySubst, Subst.lookup] using variable_returns program bound state "updated"
        · simp [term_finish_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, finalBindings, bound, accepted, optionValue, bindings, termEnvironment]
        · have successful : finishedMatch save slots target (some (after, rest)) = some (final, rest) := by
            cases save <;> simp_all [updated, finishedMatch]
          dsimp only [target] at successful
          simpa [successful, resultValue] using
            term_rebuild_returns state finalBindings final rest images context resolver rfl rfl rfl rfl rfl rfl

private theorem term_reserve_returns (state : State) (bindings : Subst) (slots : List Atom) (save : Bool)
    (slotsCaptured : applySubst bindings (.var "slots") = .expression slots)
    (saveCaptured : applySubst bindings (.var "save") = boolean save) :
    PureReturns program bindings state
      (.expression [.symbol "if", .var "save", .expression [.symbol "mm0:mmb:snoc",
        .expression [.symbol "MM0:L", .var "slots"], .symbol "None"], .expression [.symbol "MM0:L", .var "slots"]])
      state (listValue (reservedSlots save slots)) := by
  apply if_returns program bindings state state state (.var "save") (boolean save) _ _ _
  · simpa [saveCaptured] using variable_returns program bindings state "save"
  · cases save
    · simpa [boolean, reservedSlots, slotsCaptured, listValue] using
        unary_constructor_returns program bindings state "MM0:L" "slots" (by decide +kernel) (by decide)
    · let prior : Subst := [("items", listValue slots), ("value", .symbol "None")]
      have returned := MMBProofRunExecution.snoc_returns prior state slots (.symbol "None") "items" "value" rfl rfl
      simpa [boolean, reservedSlots] using (show PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:snoc", .expression [.symbol "MM0:L", .var "slots"], .symbol "None"])
        state (listValue (slots ++ [.symbol "None"])) from by
          apply captured_call_returns program prior bindings state state "mm0:mmb:snoc"
            [.var "items", .var "value"] [.expression [.symbol "MM0:L", .var "slots"], .symbol "None"] _
            (by decide +kernel) (by decide) _ _ _ returned
          · intro offset argument found
            have bounded : offset < 2 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
            interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
          · intro offset argument found
            have bounded : offset < 2 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
            interval_cases offset <;> left <;> decide +kernel
          · change [listValue slots, .symbol "None"] =
              [.expression [.symbol "MM0:L", applySubst bindings (.var "slots")], .symbol "None"]
            simp only [slotsCaptured, listValue])


private theorem term_work_returns (state : State) (fuel term pointer : Nat) (save : Bool)
    (slots codes children : List Atom) (images context resolver value : Atom) (child : Option (List Atom × List Atom))
    (returned : PureReturns program
      (callBindings fuel (matchingValue (reservedSlots save slots) images context resolver) (listValue codes) (listValue children))
      state (callExpression "mm0:mmb:match-expressions") state (resultValue images context resolver child)) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
    let bindings := ("args", listValue children) :: ("binary", natural term) :: ("value", value) :: ("pointer", natural pointer) ::
      termEnvironment (fuel + 1) term save slots images context resolver (listValue codes) target
    PureReturns program bindings state termWork state
      (resultValue images context resolver (finishedMatch save slots target child)) := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
  let bindings := ("args", listValue children) :: ("binary", natural term) :: ("value", value) :: ("pointer", natural pointer) ::
      termEnvironment (fuel + 1) term save slots images context resolver (listValue codes) target
  let indexed := ("index", natural slots.length) :: bindings
  let reserved := ("reserved", listValue (reservedSlots save slots)) :: indexed
  let reservation : Atom := .expression [.symbol "if", .var "save", .expression [.symbol "mm0:mmb:snoc",
    .expression [.symbol "MM0:L", .var "slots"], .symbol "None"], .expression [.symbol "MM0:L", .var "slots"]]
  rw [term_work_shape]
  apply let_star_returns program bindings state state _ termChildren
    (.expression [.symbol "let", .var "index", .expression [.symbol "size-atom", .var "slots"],
      .expression [.symbol "let", .var "reserved", reservation, termChildren]]) _ rfl
  apply let_returns program bindings indexed state state state (.var "index") _ _ (natural slots.length) _
  · apply native_variable_call_returns program bindings state state "size-atom" ["slots"] (natural slots.length)
      (by decide) (by decide) _ (by decide)
    simp [bindings, termEnvironment, applySubst, Subst.lookup, StdLib.size_of_expression, natural]
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, indexed, bindings, termEnvironment]
  · apply let_returns program indexed reserved state state state (.var "reserved") reservation termChildren
      (listValue (reservedSlots save slots)) _
    · exact term_reserve_returns state indexed slots save rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, reserved, indexed, bindings, termEnvironment]
    · rw [term_children_shape]
      have evaluated := decrement_call_returns state "mm0:mmb:match-expressions" fuel
        (matchingValue (reservedSlots save slots) images context resolver) (listValue codes) (listValue children)
        (resultValue images context resolver child) reserved
        [.expression [.symbol "MM0:MMBMState", .var "reserved", .var "images", .var "context", .var "resolver", .var "mode"],
          .var "codes", .var "args"] (by decide +kernel) (by decide) (by decide +kernel)
        (by intro offset inside; have bounded : offset < 3 := (by simpa using inside); interval_cases offset <;> decide +kernel)
        rfl rfl returned
      cases child with
      | none =>
          let failed := ("bad", .symbol "None") :: reserved
          apply case_returns program reserved failed state state state _ (.symbol "None") (.symbol "None") _ _
            termChildrenCases (read_cases_encoded termChildrenCases) evaluated
          · simp [term_children_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
              Subst.lookup, failed, reserved, indexed, bindings, termEnvironment]
          · simpa [finishedMatch, resultValue] using symbol_returns program failed state "None"
      | some matched =>
          obtain ⟨after, rest⟩ := matched
          let continued := ("rest", listValue rest) :: ("kind", .symbol "MM0:MMBAssertionMatch") :: ("state", resolver) ::
            ("ctx", context) :: ("extra", images) :: ("after", listValue after) :: reserved
          apply case_returns program reserved continued state state state _ (matchedValue after images context resolver rest)
            termUpdate _ _ termChildrenCases (read_cases_encoded termChildrenCases) evaluated
          · simp [term_children_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, continued, reserved, indexed,
              bindings, termEnvironment, matchedValue, matchingValue, optionValue, listValue]
          · exact term_update_returns state fuel term pointer save slots children after rest images context resolver (listValue codes) value

/-- Constructor matching executes the original reservation, recursive children
and delayed update, preserving the complete target entry. -/
theorem term_children_returns (state : State) (fuel term pointer : Nat) (save : Bool)
    (slots codes children : List Atom) (images context resolver value : Atom) (child : Option (List Atom × List Atom))
    (returned : PureReturns program
      (callBindings fuel (matchingValue (reservedSlots save slots) images context resolver) (listValue codes) (listValue children))
      state (callExpression "mm0:mmb:match-expressions") state (resultValue images context resolver child)) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
    PureReturns program (termCaptured (fuel + 1) term save slots images context resolver (listValue codes) target)
      state termCall state (resultValue images context resolver (finishedMatch save slots target child)) := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
  let bindings := termEnvironment (fuel + 1) term save slots images context resolver (listValue codes) target
  let bound := ("args", listValue children) :: ("binary", natural term) :: ("value", value) :: ("pointer", natural pointer) :: bindings
  apply term_from_body
  rw [term_shape]
  apply case_returns program bindings bound state state state (.var "target") target termApplication _ _
    termCases (read_cases_encoded termCases)
  · exact variable_returns program bindings state "target"
  · simp [term_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, termEnvironment, target, expressionValue]
  · rw [term_application_shape]
    apply if_returns program bound state state state _ (boolean true) _ _ _
    · apply native_binary_call_returns program bound state state state state "==" (.var "binary") (.var "term")
        (natural term) (natural term) (boolean true)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact variable_returns program bound state "binary"
      · exact variable_returns program bound state "term"
      · simp [StdLib.structural_equality, boolean]
    · simpa [boolean] using term_work_returns state fuel term pointer save slots codes children images context resolver value child returned


private def expressionEquation := sourceEquation "mm0:mmb:match-expression"
private def expressionElse := match expressionEquation.body with | .expression [_, _, body, _] => body | _ => .symbol "None"
private def expressionCases := casesOf expressionElse
private def opcodeBody := (expressionCases[0]'(by decide)).2
private def opcodeCases := casesOf opcodeBody
private def noSaveTermBody := (opcodeCases[0]'(by decide)).2
private def saveTermBody := (opcodeCases[1]'(by decide)).2
private def referenceBody := (opcodeCases[2]'(by decide)).2
private def dummyBody := (opcodeCases[3]'(by decide)).2
private def expressionEnvironment (fuel pointer : Nat) (slots codes : List Atom)
    (images context resolver expression node : Atom) : Subst :=
  [("node", node), ("expression", expression), ("pointer", natural pointer), ("codes", .expression codes),
    ("mode", .symbol "MM0:MMBAssertionMatch"), ("resolver", resolver), ("context", context), ("images", images),
    ("slots", .expression slots), ("fuel", natural fuel)]
private def opcodeEnvironment (fuel pointer opcode data start after : Nat) (slots rest : List Atom)
    (images context resolver expression node : Atom) : Subst :=
  ("rest", .expression rest) :: ("after", natural after) :: ("start", natural start) ::
    ("data", natural data) :: ("opcode", natural opcode) ::
    expressionEnvironment (fuel + 1) pointer slots (MMBExecution.commandValue opcode data start after :: rest)
      images context resolver expression node
private theorem expression_unique : program.equations.filter (·.head == "mm0:mmb:match-expression") = [expressionEquation] := by
  decide +kernel
private theorem expression_formals : expressionEquation.arguments =
    [.var "fuel", .expression [.symbol "MM0:MMBMState", .expression [.symbol "MM0:L", .var "slots"],
      .var "images", .var "context", .var "resolver", .var "mode"],
     .expression [.symbol "MM0:L", .var "codes"],
     .expression [.symbol "MM0:MMBExpression", .var "pointer", .var "expression", .var "node"]] := by decide
private theorem expression_shape : expressionEquation.body = .expression [.symbol "if",
    .expression [.symbol "<", natural 0, .var "fuel"], expressionElse, .symbol "None"] := by decide
private theorem expression_else_shape : expressionElse = .expression [.symbol "case", .var "codes",
    .expression (expressionCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem expression_cases_shape : expressionCases =
    [(.expression [.symbol "cons", .expression [.symbol "MM0:MMBCode", .var "opcode", .var "data", .var "start", .var "after"],
      .var "rest"], opcodeBody), (.var "bad", .symbol "None")] := by decide
private theorem opcode_shape : opcodeBody = .expression [.symbol "case", .var "opcode",
    .expression (opcodeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem opcode_cases_shape : opcodeCases =
    [(natural 48, noSaveTermBody), (natural 49, saveTermBody), (natural 50, referenceBody),
      (natural 51, dummyBody), (.var "bad", .symbol "None")] := by decide
private theorem term_command_shape (save : Bool) : (if save then saveTermBody else noSaveTermBody) =
    .expression [.symbol "mm0:mmb:match-term", .var "fuel",
      .expression [.symbol "MM0:MMBMState", .expression [.symbol "MM0:L", .var "slots"], .var "images", .var "context", .var "resolver", .var "mode"],
      .var "data", boolean save, .expression [.symbol "MM0:L", .var "rest"],
      .expression [.symbol "MM0:MMBExpression", .var "pointer", .var "expression", .var "node"]] := by cases save <;> decide
private theorem expression_clause (fuel pointer : Nat) (slots codes : List Atom)
    (images context resolver expression node : Atom) :
    clauses program "mm0:mmb:match-expression"
      [natural fuel, matchingValue slots images context resolver, listValue codes, expressionValue pointer expression node] =
      [.evaluate (expressionEnvironment fuel pointer slots codes images context resolver expression node) expressionEquation.body] := by
  rw [clauses_use_only_the_named_equations, expression_unique]
  simp [expression_formals, expressionEnvironment, matchingValue, expressionValue, listValue,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem expression_from_body (state : State) (fuel pointer : Nat) (slots codes : List Atom)
    (images context resolver expression node answer : Atom)
    (body : PureReturns program (expressionEnvironment fuel pointer slots codes images context resolver expression node)
      state expressionEquation.body state answer) :
    PureReturns program
      (callBindings fuel (matchingValue slots images context resolver) (listValue codes) (expressionValue pointer expression node))
      state (callExpression "mm0:mmb:match-expression") state answer := by
  apply call_returns program _ state state "mm0:mmb:match-expression" _ _ (by decide +kernel) _ (by decide)
  apply variable_arguments_return program _ state state (.function "mm0:mmb:match-expression")
    ["fuel", "matching", "codes", "target"] [] 0 answer
  simpa [callBindings, applySubst, Subst.lookup] using
    authored_function_arguments_return program _ (expressionEnvironment fuel pointer slots codes images context resolver expression node)
      state state "mm0:mmb:match-expression"
      [natural fuel, matchingValue slots images context resolver, listValue codes, expressionValue pointer expression node]
      4 expressionEquation.body answer (by decide) (by decide)
      (expression_clause fuel pointer slots codes images context resolver expression node) body

private theorem expression_opcode_from_body (state : State) (fuel pointer opcode data start after : Nat)
    (slots rest : List Atom) (images context resolver expression node answer : Atom)
    (body : PureReturns program (opcodeEnvironment fuel pointer opcode data start after slots rest images context resolver expression node)
      state opcodeBody state answer) :
    PureReturns program
      (callBindings (fuel + 1) (matchingValue slots images context resolver)
        (listValue (MMBExecution.commandValue opcode data start after :: rest)) (expressionValue pointer expression node))
      state (callExpression "mm0:mmb:match-expression") state answer := by
  apply expression_from_body
  let bindings := expressionEnvironment (fuel + 1) pointer slots (MMBExecution.commandValue opcode data start after :: rest)
    images context resolver expression node
  let bound := opcodeEnvironment fuel pointer opcode data start after slots rest images context resolver expression node
  rw [expression_shape]
  apply if_returns program bindings state state state _ (boolean true) _ _ _
  · exact positive_test state bindings fuel rfl
  · simpa [boolean] using (show PureReturns program bindings state expressionElse state answer from by
      rw [expression_else_shape]
      apply case_returns program bindings bound state state state (.var "codes")
        (.expression (MMBExecution.commandValue opcode data start after :: rest)) opcodeBody _ _
        expressionCases (read_cases_encoded expressionCases)
      · exact variable_returns program bindings state "codes"
      · simp [expression_cases_shape, MMBExecution.commandValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, opcodeEnvironment, expressionEnvironment]
      · exact body)

private theorem expression_term_from_call (state : State) (fuel pointer term start after : Nat)
    (save : Bool) (slots rest : List Atom) (images context resolver expression node answer : Atom)
    (returned : PureReturns program
      (termCaptured (fuel + 1) term save slots images context resolver (listValue rest) (expressionValue pointer expression node))
      state termCall state answer) :
    PureReturns program
      (callBindings (fuel + 1) (matchingValue slots images context resolver)
        (listValue (MMBExecution.commandValue (if save then 49 else 48) term start after :: rest)) (expressionValue pointer expression node))
      state (callExpression "mm0:mmb:match-expression") state answer := by
  apply expression_opcode_from_body
  let opcode := if save then 49 else 48
  let bindings := opcodeEnvironment fuel pointer opcode term start after slots rest images context resolver expression node
  rw [opcode_shape]
  apply case_returns program bindings bindings state state state (.var "opcode") (natural opcode)
    (if save then saveTermBody else noSaveTermBody) _ _ opcodeCases (read_cases_encoded opcodeCases)
  · exact variable_returns program bindings state "opcode"
  · cases save <;> simp [opcode_cases_shape, opcode, natural, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, bindings, opcodeEnvironment, expressionEnvironment]
  · rw [term_command_shape]
    apply captured_call_returns program
      (termCaptured (fuel + 1) term save slots images context resolver (listValue rest) (expressionValue pointer expression node))
      bindings state state "mm0:mmb:match-term"
      [.var "fuel", .var "matching", .var "term", .var "save", .var "codes", .var "target"] _ _
      (by decide +kernel) (by decide) _ _ _ returned
    · intro offset argument found
      have bounded : offset < 6 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
      interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
    · intro offset argument found
      have bounded : offset < 6 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
      interval_cases offset
      · right; simp at found; subst argument; rfl
      · left; decide +kernel
      · right; simp at found; subst argument; rfl
      · left; decide +kernel
      · left; decide +kernel
      · left; decide +kernel
    · cases save <;> simp [bindings, opcodeEnvironment, expressionEnvironment, termCaptured, applySubst, applySubst.applySubstList,
        Subst.lookup, matchingValue, expressionValue, listValue, boolean]


/-- A positive-fuel call with no unread command refuses in the original source. -/
theorem expression_empty_codes_returns (state : State) (fuel pointer : Nat)
    (slots : List Atom) (images context resolver expression node : Atom) :
    PureReturns program
      (callBindings (fuel + 1) (matchingValue slots images context resolver) (listValue [])
        (expressionValue pointer expression node)) state
      (callExpression "mm0:mmb:match-expression") state (.symbol "None") := by
  apply expression_from_body
  let bindings := expressionEnvironment (fuel + 1) pointer slots [] images context resolver expression node
  let bound := ("bad", .expression []) :: bindings
  rw [expression_shape]
  apply if_returns program bindings state state state _ (boolean true) _ _ _
  · exact positive_test state bindings fuel rfl
  · simpa [boolean] using (show PureReturns program bindings state expressionElse state (.symbol "None") from by
      rw [expression_else_shape]
      apply case_returns program bindings bound state state state (.var "codes") (.expression [])
        (.symbol "None") _ _ expressionCases (read_cases_encoded expressionCases)
      · exact variable_returns program bindings state "codes"
      · simp [expression_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, Subst.lookup, bound, bindings, expressionEnvironment]
      · exact symbol_returns program bound state "None")

/-- Opcodes outside the original assertion instruction cases explicitly refuse. -/
theorem expression_unknown_opcode_returns (state : State) (fuel pointer opcode data start after : Nat)
    (slots rest : List Atom) (images context resolver expression node : Atom)
    (unsupported : opcode ≠ 48 ∧ opcode ≠ 49 ∧ opcode ≠ 50 ∧ opcode ≠ 51) :
    PureReturns program
      (callBindings (fuel + 1) (matchingValue slots images context resolver)
        (listValue (MMBExecution.commandValue opcode data start after :: rest)) (expressionValue pointer expression node))
      state (callExpression "mm0:mmb:match-expression") state (.symbol "None") := by
  apply expression_opcode_from_body
  let bindings := opcodeEnvironment fuel pointer opcode data start after slots rest images context resolver expression node
  let bound := ("bad", natural opcode) :: bindings
  rw [opcode_shape]
  apply case_returns program bindings bound state state state (.var "opcode") (natural opcode)
    (.symbol "None") _ _ opcodeCases (read_cases_encoded opcodeCases)
  · exact variable_returns program bindings state "opcode"
  · rcases unsupported with ⟨h48, h49, h50, h51⟩
    have h48i : (48 : Int) ≠ (opcode : Int) := by omega
    have h49i : (49 : Int) ≠ (opcode : Int) := by omega
    have h50i : (50 : Int) ≠ (opcode : Int) := by omega
    have h51i : (51 : Int) ≠ (opcode : Int) := by omega
    simp [opcode_cases_shape, natural, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      matchAtom, Subst.lookup, bound, bindings, opcodeEnvironment, expressionEnvironment, h48i, h49i, h50i, h51i]
  · exact symbol_returns program bound state "None"

/-- A constructor instruction cannot match a different physical constructor index. -/
theorem term_index_mismatch_returns (state : State) (fuel term binary pointer : Nat) (save : Bool)
    (slots children : List Atom) (images context resolver codes value : Atom) (different : binary ≠ term) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural binary, listValue children])
    PureReturns program (termCaptured fuel term save slots images context resolver codes target)
      state termCall state (.symbol "None") := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural binary, listValue children])
  let bindings := termEnvironment fuel term save slots images context resolver codes target
  let bound := ("args", listValue children) :: ("binary", natural binary) :: ("value", value) :: ("pointer", natural pointer) :: bindings
  apply term_from_body
  rw [term_shape]
  apply case_returns program bindings bound state state state (.var "target") target termApplication _ _
    termCases (read_cases_encoded termCases)
  · exact variable_returns program bindings state "target"
  · simp [term_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, termEnvironment, target, expressionValue]
  · rw [term_application_shape]
    apply if_returns program bound state state state _ (boolean false) _ _ _
    · apply native_binary_call_returns program bound state state state state "==" (.var "binary") (.var "term")
        (natural binary) (natural term) (boolean false)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact variable_returns program bound state "binary"
      · exact variable_returns program bound state "term"
      · simp [StdLib.structural_equality, natural, boolean, different]
    · simpa [boolean] using symbol_returns program bound state "None"

/-- Original variable entries are outside the constructor matcher shape. -/
theorem term_variable_returns (state : State) (fuel term pointer index : Nat) (save : Bool)
    (slots : List Atom) (images context resolver codes value : Atom) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBVariable", natural index])
    PureReturns program (termCaptured fuel term save slots images context resolver codes target)
      state termCall state (.symbol "None") := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBVariable", natural index])
  let bindings := termEnvironment fuel term save slots images context resolver codes target
  let bound := ("bad", target) :: bindings
  apply term_from_body
  rw [term_shape]
  apply case_returns program bindings bound state state state (.var "target") target (.symbol "None") _ _
    termCases (read_cases_encoded termCases)
  · exact variable_returns program bindings state "target"
  · simp [term_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, termEnvironment, target, expressionValue]
  · exact symbol_returns program bound state "None"


private def dummyEquation := sourceEquation "mm0:mmb:match-dummy"
private def dummyCases := casesOf dummyEquation.body
private def dummyVariable := (dummyCases[0]'(by decide)).2
private def dummyMode := match dummyVariable with | .expression [_, mode, _, _] => mode | _ => .symbol "None"
private def dummyModeCases := casesOf dummyMode
private def dummyWork := match dummyVariable with | .expression [_, _, work, _] => work | _ => .symbol "None"
private def dummyEnvironment (sort : Nat) (slots images : List Atom) (context resolver rest target : Atom) : Subst :=
  [("target", target), ("rest", rest), ("sort", natural sort), ("mode", .symbol "MM0:MMBAssertionMatch"),
    ("resolver", resolver), ("context", context), ("images", .expression images), ("slots", listValue slots)]
private def dummyCaptured (sort : Nat) (slots images : List Atom) (context resolver rest target : Atom) : Subst :=
  [("target", target), ("rest", rest), ("sort", natural sort),
    ("matching", matchingValue slots (listValue images) context resolver)]
private def dummyCall : Atom := .expression [.symbol "mm0:mmb:match-dummy", .var "matching", .var "sort", .var "rest", .var "target"]
private theorem dummy_unique : program.equations.filter (·.head == "mm0:mmb:match-dummy") = [dummyEquation] := by
  decide +kernel
private theorem dummy_formals : dummyEquation.arguments =
    [.expression [.symbol "MM0:MMBMState", .var "slots", .expression [.symbol "MM0:L", .var "images"],
      .var "context", .var "resolver", .var "mode"], .var "sort", .var "rest", .var "target"] := by decide
private theorem dummy_shape : dummyEquation.body = .expression [.symbol "case", .var "target",
    .expression (dummyCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem dummy_cases_shape : dummyCases =
    [(.expression [.symbol "MM0:MMBExpression", .var "pointer", .var "expression",
      .expression [.symbol "MM0:MMBVariable", .var "index"]], dummyVariable), (.var "bad", .symbol "None")] := by decide
private theorem dummy_variable_shape : dummyVariable = .expression [.symbol "if", dummyMode, dummyWork, .symbol "None"] := by decide
private theorem dummy_mode_shape : dummyMode = .expression [.symbol "case", .var "mode",
    .expression (dummyModeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem dummy_mode_cases_shape : dummyModeCases =
    [(.symbol "MM0:MMBUnfold", boolean true),
      (.expression [.symbol "MM0:MMBDefinitionMatch", .var "arity"], .expression [.symbol "<=", .var "arity", .var "index"]),
      (.var "bad", boolean false)] := by decide
private theorem dummy_clause (sort : Nat) (slots images : List Atom) (context resolver rest target : Atom) :
    clauses program "mm0:mmb:match-dummy"
      [matchingValue slots (listValue images) context resolver, natural sort, rest, target] =
      [.evaluate (dummyEnvironment sort slots images context resolver rest target) dummyEquation.body] := by
  rw [clauses_use_only_the_named_equations, dummy_unique]
  simp [dummy_formals, dummyEnvironment, matchingValue, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem dummy_from_body (state : State) (sort : Nat) (slots images : List Atom)
    (context resolver rest target answer : Atom)
    (body : PureReturns program (dummyEnvironment sort slots images context resolver rest target)
      state dummyEquation.body state answer) :
    PureReturns program (dummyCaptured sort slots images context resolver rest target) state dummyCall state answer := by
  apply call_returns program _ state state "mm0:mmb:match-dummy" _ _ (by decide +kernel) _ (by decide)
  apply variable_arguments_return program _ state state (.function "mm0:mmb:match-dummy")
    ["matching", "sort", "rest", "target"] [] 0 answer
  simpa [dummyCaptured, applySubst, Subst.lookup] using
    authored_function_arguments_return program _ (dummyEnvironment sort slots images context resolver rest target)
      state state "mm0:mmb:match-dummy"
      [matchingValue slots (listValue images) context resolver, natural sort, rest, target] 4 dummyEquation.body answer
      (by decide) (by decide) (dummy_clause sort slots images context resolver rest target) body

/-- Assertion matching refuses dummies before any sort or context query. -/
theorem dummy_variable_returns (state : State) (sort pointer index : Nat) (slots images : List Atom)
    (context resolver rest value : Atom) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBVariable", natural index])
    PureReturns program (dummyCaptured sort slots images context resolver rest target) state dummyCall state (.symbol "None") := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBVariable", natural index])
  let bindings := dummyEnvironment sort slots images context resolver rest target
  let bound := ("index", natural index) :: ("expression", value) :: ("pointer", natural pointer) :: bindings
  apply dummy_from_body
  rw [dummy_shape]
  apply case_returns program bindings bound state state state (.var "target") target dummyVariable _ _
    dummyCases (read_cases_encoded dummyCases)
  · exact variable_returns program bindings state "target"
  · simp [dummy_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, dummyEnvironment, target, expressionValue]
  · rw [dummy_variable_shape]
    apply if_returns program bound state state state _ (boolean false) _ _ _
    · rw [dummy_mode_shape]
      let refused := ("bad", .symbol "MM0:MMBAssertionMatch") :: bound
      apply case_returns program bound refused state state state (.var "mode") (.symbol "MM0:MMBAssertionMatch")
        (boolean false) _ _ dummyModeCases (read_cases_encoded dummyModeCases)
      · exact variable_returns program bound state "mode"
      · simp [dummy_mode_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom, Subst.lookup, refused, bound, bindings, dummyEnvironment]
      · exact grounded_returns program refused state (.bool false)
    · simpa [boolean] using symbol_returns program bound state "None"

/-- Application entries also refuse the original dummy instruction. -/
theorem dummy_application_returns (state : State) (sort pointer term : Nat) (slots images children : List Atom)
    (context resolver rest value : Atom) :
    let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
    PureReturns program (dummyCaptured sort slots images context resolver rest target) state dummyCall state (.symbol "None") := by
  dsimp only
  let target := expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
  let bindings := dummyEnvironment sort slots images context resolver rest target
  let bound := ("bad", target) :: bindings
  apply dummy_from_body
  rw [dummy_shape]
  apply case_returns program bindings bound state state state (.var "target") target (.symbol "None") _ _
    dummyCases (read_cases_encoded dummyCases)
  · exact variable_returns program bindings state "target"
  · simp [dummy_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, dummyEnvironment, target, expressionValue]
  · exact symbol_returns program bound state "None"

private theorem expression_dummy_from_call (state : State) (fuel pointer sort start after : Nat)
    (slots images rest : List Atom) (context resolver expression node answer : Atom)
    (returned : PureReturns program
      (dummyCaptured sort slots images context resolver (listValue rest) (expressionValue pointer expression node))
      state dummyCall state answer) :
    PureReturns program
      (callBindings (fuel + 1) (matchingValue slots (listValue images) context resolver)
        (listValue (MMBExecution.commandValue 51 sort start after :: rest)) (expressionValue pointer expression node))
      state (callExpression "mm0:mmb:match-expression") state answer := by
  apply expression_opcode_from_body
  let bindings := opcodeEnvironment fuel pointer 51 sort start after slots rest (listValue images) context resolver expression node
  rw [opcode_shape]
  apply case_returns program bindings bindings state state state (.var "opcode") (natural 51)
    dummyBody _ _ opcodeCases (read_cases_encoded opcodeCases)
  · exact variable_returns program bindings state "opcode"
  · simp [opcode_cases_shape, natural, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
      bindings, opcodeEnvironment, expressionEnvironment]
  · have shape : dummyBody = .expression [.symbol "mm0:mmb:match-dummy",
        .expression [.symbol "MM0:MMBMState", .expression [.symbol "MM0:L", .var "slots"], .var "images",
          .var "context", .var "resolver", .var "mode"], .var "data", .expression [.symbol "MM0:L", .var "rest"],
          .expression [.symbol "MM0:MMBExpression", .var "pointer", .var "expression", .var "node"]] := by decide
    rw [shape]
    apply captured_call_returns program _ bindings state state "mm0:mmb:match-dummy"
      [.var "matching", .var "sort", .var "rest", .var "target"] _ _ (by decide +kernel) (by decide) _ _ _ returned
    · intro offset argument found
      have bounded : offset < 4 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
      interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
    · intro offset argument found
      have bounded : offset < 4 := (by have inside := (getElem?_eq_some_iff.mp found).choose; simpa using inside)
      interval_cases offset
      · left; decide +kernel
      · right; simp at found; subst argument; rfl
      · left; decide +kernel
      · left; decide +kernel
    · simp [bindings, opcodeEnvironment, expressionEnvironment, dummyCaptured, applySubst, applySubst.applySubstList,
        Subst.lookup, matchingValue, expressionValue, listValue]


mutual
  /-- Execution evidence for original assertion instructions. Leaves are the
  already qualified identity checks; constructor children use this same evidence. -/
  inductive ExpressionMatch (images context resolver : Atom) :
      Nat → List Atom → List Atom → Atom → Option (List Atom × List Atom) → Prop where
    | zero (slots codes : List Atom) (pointer : Nat) (value node : Atom) :
        ExpressionMatch images context resolver 0 slots codes (expressionValue pointer value node) none
    | emptyCodes (fuel pointer : Nat) (slots : List Atom) (value node : Atom) :
        ExpressionMatch images context resolver (fuel + 1) slots [] (expressionValue pointer value node) none
    | unknown (fuel pointer opcode data start after : Nat) (slots rest : List Atom) (value node : Atom)
        (unsupported : opcode ≠ 48 ∧ opcode ≠ 49 ∧ opcode ≠ 50 ∧ opcode ≠ 51) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue opcode data start after :: rest) (expressionValue pointer value node) none
    | wrongConstructor (fuel pointer term binary start after : Nat) (save : Bool)
        (slots rest children : List Atom) (value : Atom) (different : binary ≠ term) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue (if save then 49 else 48) term start after :: rest)
          (expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural binary, listValue children])) none
    | variableConstructor (fuel pointer term index start after : Nat) (save : Bool)
        (slots rest : List Atom) (value : Atom) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue (if save then 49 else 48) term start after :: rest)
          (expressionValue pointer value (.expression [.symbol "MM0:MMBVariable", natural index])) none
    | dummyVariable (fuel pointer sort index start after : Nat) (slots rest rows : List Atom) (value : Atom)
        (imagesShape : images = listValue rows) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue 51 sort start after :: rest)
          (expressionValue pointer value (.expression [.symbol "MM0:MMBVariable", natural index])) none
    | dummyApplication (fuel pointer sort term start after : Nat) (slots rest rows children : List Atom) (value : Atom)
        (imagesShape : images = listValue rows) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue 51 sort start after :: rest)
          (expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])) none
    | reference (fuel pointer index start after stored : Nat) (slots rest : List Atom)
        (expression node value shape : Atom)
        (found : slots[index]? = some (optionValue (some (expressionValue stored value shape)))) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue 50 index start after :: rest) (expressionValue pointer expression node)
          (if stored = pointer then some (slots, rest) else none)
    | unavailable (fuel pointer index start after : Nat) (slots rest : List Atom) (expression node : Atom)
        (found : slots[index]? = none ∨ slots[index]? = some (.symbol "None")) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue 50 index start after :: rest) (expressionValue pointer expression node) none
    | constructor (fuel pointer term start after : Nat) (save : Bool) (slots rest children : List Atom) (value : Atom)
        (child : Option (List Atom × List Atom))
        (matched : ExpressionListMatch images context resolver fuel (reservedSlots save slots) rest children child) :
        ExpressionMatch images context resolver (fuel + 1) slots
          (MMBExecution.commandValue (if save then 49 else 48) term start after :: rest)
          (expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children]))
          (finishedMatch save slots
            (expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])) child)
  /-- The original head-first child traversal, including refusal propagation. -/
  inductive ExpressionListMatch (images context resolver : Atom) :
      Nat → List Atom → List Atom → List Atom → Option (List Atom × List Atom) → Prop where
    | empty (fuel : Nat) (slots codes : List Atom) :
        ExpressionListMatch images context resolver fuel slots codes [] (some (slots, codes))
    | zero (slots codes : List Atom) (first : Atom) (rest : List Atom) :
        ExpressionListMatch images context resolver 0 slots codes (first :: rest) none
    | refused (fuel : Nat) (slots codes : List Atom) (first : Atom) (rest : List Atom)
        (matched : ExpressionMatch images context resolver fuel slots codes first none) :
        ExpressionListMatch images context resolver (fuel + 1) slots codes (first :: rest) none
    | next (fuel : Nat) (slots codes intermediate unread : List Atom) (first : Atom) (rest : List Atom)
        (result : Option (List Atom × List Atom))
        (matched : ExpressionMatch images context resolver fuel slots codes first (some (intermediate, unread)))
        (remaining : ExpressionListMatch images context resolver fuel intermediate unread rest result) :
        ExpressionListMatch images context resolver (fuel + 1) slots codes (first :: rest) result
end

private theorem resultValue_shape (images context resolver : Atom) (result : Option (List Atom × List Atom)) :
    resultValue images context resolver result = .symbol "None" ∨
      ∃ after rest, resultValue images context resolver result =
        optionValue (some (.expression [.symbol "MM0:MMBMatched", after, rest])) := by
  cases result with
  | none => exact .inl rfl
  | some pair => exact .inr ⟨matchingValue pair.1 images context resolver, listValue pair.2, rfl⟩

private theorem resultValue_success (images context resolver : Atom) (slots codes : List Atom) (after rest : Atom)
    (same : matchedValue slots images context resolver codes =
      optionValue (some (.expression [.symbol "MM0:MMBMatched", after, rest]))) :
    after = matchingValue slots images context resolver ∧ rest = listValue codes := by
  simpa [matchedValue, optionValue] using same.symm

private theorem match_returns (state : State) (images context resolver : Atom) (fuel : Nat) :
    (∀ slots codes target result, ExpressionMatch images context resolver fuel slots codes target result →
      PureReturns program (callBindings fuel (matchingValue slots images context resolver) (listValue codes) target)
        state (callExpression "mm0:mmb:match-expression") state (resultValue images context resolver result)) ∧
    (∀ slots codes children result, ExpressionListMatch images context resolver fuel slots codes children result →
      PureReturns program (callBindings fuel (matchingValue slots images context resolver) (listValue codes) (listValue children))
        state (callExpression "mm0:mmb:match-expressions") state (resultValue images context resolver result)) := by
  induction fuel with
  | zero =>
      constructor
      · intro slots codes target result trace
        cases trace with
        | zero slots codes pointer value node =>
            exact MMBAssertionMatchExecution.match_zero_fuel_returns _ state pointer slots codes images context resolver value node
              "fuel" "matching" "codes" "target" rfl rfl rfl rfl
      · intro slots codes children result trace
        cases trace with
        | empty slots codes => exact children_empty_returns state 0 _ _
        | zero slots codes first rest => exact children_zero_returns state _ _ first rest
  | succ fuel ih =>
      constructor
      · intro slots codes target result trace
        cases trace with
        | emptyCodes _ pointer _ value node =>
            exact expression_empty_codes_returns state fuel pointer slots images context resolver value node
        | unknown _ pointer opcode data start after _ rest value node unsupported =>
            exact expression_unknown_opcode_returns state fuel pointer opcode data start after slots rest images context resolver value node unsupported
        | wrongConstructor _ pointer term binary start after save _ rest children value different =>
            exact expression_term_from_call state fuel pointer term start after save slots rest images context resolver value _ _
              (term_index_mismatch_returns state (fuel + 1) term binary pointer save slots children images context resolver (listValue rest) value different)
        | variableConstructor _ pointer term index start after save _ rest value =>
            exact expression_term_from_call state fuel pointer term start after save slots rest images context resolver value _ _
              (term_variable_returns state (fuel + 1) term pointer index save slots images context resolver (listValue rest) value)
        | dummyVariable _ pointer sort index start after _ rest rows value imagesShape =>
            rw [imagesShape]
            exact expression_dummy_from_call state fuel pointer sort start after slots rows rest context resolver value _ _
              (dummy_variable_returns state sort pointer index slots rows context resolver (listValue rest) value)
        | dummyApplication _ pointer sort term start after _ rest rows children value imagesShape =>
            rw [imagesShape]
            exact expression_dummy_from_call state fuel pointer sort start after slots rows rest context resolver value _ _
              (dummy_application_returns state sort pointer term slots rows children context resolver (listValue rest) value)
        | reference _ pointer index start after stored _ rest expression node value shape found =>
            have returned := MMBAssertionMatchExecution.match_reference_returns
              (callBindings (fuel + 1) (matchingValue slots images context resolver)
                (listValue (MMBExecution.commandValue 50 index start after :: rest)) (expressionValue pointer expression node))
              state fuel pointer index start after stored slots rest
              images context resolver expression node value shape "fuel" "matching" "codes" "target" rfl rfl rfl rfl found
            by_cases same : stored = pointer <;> simpa only [same, if_true, if_false, resultValue, callExpression] using returned
        | unavailable _ pointer index start after _ rest expression node found =>
            exact MMBAssertionMatchExecution.match_reference_unavailable_returns _ state fuel pointer index start after slots rest
              images context resolver expression node "fuel" "matching" "codes" "target" rfl rfl rfl rfl found
        | constructor _ pointer term start after save _ rest children value child matched =>
            exact expression_term_from_call state fuel pointer term start after save slots rest images context resolver value _ _
              (term_children_returns state fuel term pointer save slots rest children images context resolver value child
                (ih.2 _ _ _ _ matched))
      · intro slots codes children result trace
        cases trace with
        | empty slots codes => exact children_empty_returns state (fuel + 1) _ _
        | refused _ _ _ first rest matched =>
            apply children_from_body
            exact children_cons_body state fuel _ _ first rest (.symbol "None") (.symbol "None")
              (ih.1 _ _ _ _ matched) (by intro after remaining present; simp [optionValue] at present) (by simp) (.inl rfl)
        | next _ _ _ intermediate unread first rest _ matched remaining =>
            apply children_from_body
            apply children_cons_body state fuel _ _ first rest
              (matchedValue intermediate images context resolver unread) (resultValue images context resolver result)
              (ih.1 _ _ _ _ matched)
            · intro after rest same
              obtain ⟨rfl, rfl⟩ := resultValue_success images context resolver intermediate unread after rest same
              exact ih.2 _ _ _ _ remaining
            · intro impossible
              simp [matchedValue, optionValue] at impossible
            · exact .inr ⟨matchingValue intermediate images context resolver, listValue unread, rfl⟩

/-- Every finite recursively constructed assertion trace executes in the
unchanged authored matcher. No subcall-correctness callback is required. -/
theorem expression_returns (state : State) (images context resolver : Atom)
    (fuel : Nat) (slots codes : List Atom) (target : Atom) (result : Option (List Atom × List Atom))
    (trace : ExpressionMatch images context resolver fuel slots codes target result) :
    PureReturns program (callBindings fuel (matchingValue slots images context resolver) (listValue codes) target)
      state (callExpression "mm0:mmb:match-expression") state (resultValue images context resolver result) :=
  (match_returns state images context resolver fuel).1 slots codes target result trace

/-- Ordered child matching uses the recursively earned source calls, retaining
all duplicate children and the exact physical unread command suffix. -/
theorem children_returns (state : State) (images context resolver : Atom)
    (fuel : Nat) (slots codes children : List Atom) (result : Option (List Atom × List Atom))
    (trace : ExpressionListMatch images context resolver fuel slots codes children result) :
    PureReturns program (callBindings fuel (matchingValue slots images context resolver) (listValue codes) (listValue children))
      state (callExpression "mm0:mmb:match-expressions") state (resultValue images context resolver result) :=
  (match_returns state images context resolver fuel).2 slots codes children result trace


private theorem hypotheses_zero_body (state : State) (data start after : Nat) (matching : Atom)
    (codes : List Atom) (first : Atom) (earlier : List Atom) :
    PureReturns program
      (hypothesesEnvironment 0 matching (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier))
      state hypothesesEquation.body state (.symbol "None") := by
  let bindings := hypothesesEnvironment 0 matching (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier)
  let bound := ("earlier", .expression earlier) :: ("first", first) :: ("rest", .expression codes) ::
    ("after", natural after) :: ("start", natural start) :: ("data", natural data) :: bindings
  rw [hypotheses_shape]
  apply case_returns program bindings bound state state state (.expression [.var "codes", .var "hypotheses"])
    (.expression [.expression (MMBExecution.commandValue 54 data start after :: codes), .expression (first :: earlier)])
    hypothesesCons _ _ hypothesesCases (read_cases_encoded hypothesesCases)
  · simpa [bindings, hypothesesEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["codes", "hypotheses"]
  · simp [hypotheses_cases_shape, MMBExecution.commandValue, natural, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, hypothesesEnvironment]
  · rw [hypotheses_cons_shape]
    apply if_returns program bound state state state _ (boolean false) _ _ _
    · apply native_binary_call_returns program bound state state state state "<" (natural 0) (.var "fuel")
        (natural 0) (natural 0) (boolean false)
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact grounded_returns program bound state (.int 0)
      · exact variable_returns program bound state "fuel"
      · simp [StdLib.less_comparison, natural, boolean]
    · simpa [boolean] using symbol_returns program bound state "None"

private theorem hypotheses_wrong_frame_returns (state : State) (fuel : Nat) (matching : Atom)
    (codes hypotheses : List Atom)
    (selected : SpaceSemantics.selectCase (hypothesesEnvironment fuel matching codes hypotheses)
      (.expression [.expression codes, .expression hypotheses]) hypothesesCases =
      some (("bad", .expression [.expression codes, .expression hypotheses]) ::
        hypothesesEnvironment fuel matching codes hypotheses, .symbol "None")) :
    PureReturns program (callBindings fuel matching (listValue codes) (listValue hypotheses)) state
      (callExpression "mm0:mmb:match-hypotheses") state (.symbol "None") := by
  apply hypotheses_from_body
  let bindings := hypothesesEnvironment fuel matching codes hypotheses
  let bound := ("bad", .expression [.expression codes, .expression hypotheses]) :: bindings
  rw [hypotheses_shape]
  apply case_returns program bindings bound state state state (.expression [.var "codes", .var "hypotheses"])
    (.expression [.expression codes, .expression hypotheses]) (.symbol "None") _ _
    hypothesesCases (read_cases_encoded hypothesesCases)
  · simpa [bindings, hypothesesEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["codes", "hypotheses"]
  · exact selected
  · exact symbol_returns program bound state "None"

/-- An unmatched hypothesis remains an explicit source refusal. -/
theorem hypotheses_missing_code_returns (state : State) (fuel : Nat) (matching first : Atom) (earlier : List Atom) :
    PureReturns program (callBindings fuel matching (listValue []) (listValue (first :: earlier))) state
      (callExpression "mm0:mmb:match-hypotheses") state (.symbol "None") := by
  apply hypotheses_wrong_frame_returns
  simp [hypotheses_cases_shape, hypothesesEnvironment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- A nonempty command suffix cannot be discarded after the last hypothesis. -/
theorem hypotheses_extra_code_returns (state : State) (fuel : Nat) (matching first : Atom) (rest : List Atom) :
    PureReturns program (callBindings fuel matching (listValue (first :: rest)) (listValue [])) state
      (callExpression "mm0:mmb:match-hypotheses") state (.symbol "None") := by
  apply hypotheses_wrong_frame_returns
  simp [hypotheses_cases_shape, hypothesesEnvironment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- A wrong physical opcode at a hypothesis boundary explicitly refuses. -/
theorem hypotheses_wrong_opcode_returns (state : State) (fuel opcode data start after : Nat)
    (matching first : Atom) (rest earlier : List Atom) (different : opcode ≠ 54) :
    PureReturns program
      (callBindings fuel matching (listValue (MMBExecution.commandValue opcode data start after :: rest)) (listValue (first :: earlier)))
      state (callExpression "mm0:mmb:match-hypotheses") state (.symbol "None") := by
  apply hypotheses_wrong_frame_returns
  have differentInt : (54 : Int) ≠ (opcode : Int) := by omega
  simp [hypotheses_cases_shape, hypothesesEnvironment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, MMBExecution.commandValue, natural, matchAtom, Subst.lookup, differentInt]

/-- Hypothesis evidence consumes the source's exact command-54 boundary and
then the same recursively earned assertion matches. -/
inductive HypothesisMatch (images context resolver : Atom) :
    Nat → List Atom → List Atom → List Atom → Option (List Atom) → Prop where
  | empty (fuel : Nat) (slots : List Atom) : HypothesisMatch images context resolver fuel slots [] [] (some slots)
  | missingCode (fuel : Nat) (slots : List Atom) (first : Atom) (earlier : List Atom) :
      HypothesisMatch images context resolver fuel slots [] (first :: earlier) none
  | extraCode (fuel : Nat) (slots : List Atom) (first : Atom) (rest : List Atom) :
      HypothesisMatch images context resolver fuel slots (first :: rest) [] none
  | wrongBoundary (fuel opcode data start after : Nat) (slots codes : List Atom) (first : Atom) (earlier : List Atom)
      (different : opcode ≠ 54) :
      HypothesisMatch images context resolver fuel slots (MMBExecution.commandValue opcode data start after :: codes) (first :: earlier) none
  | zero (data start after : Nat) (slots codes : List Atom) (first : Atom) (earlier : List Atom) :
      HypothesisMatch images context resolver 0 slots (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier) none
  | refused (fuel data start after : Nat) (slots codes : List Atom) (first : Atom) (earlier : List Atom)
      (matched : ExpressionMatch images context resolver fuel slots codes first none) :
      HypothesisMatch images context resolver (fuel + 1) slots
        (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier) none
  | next (fuel data start after : Nat) (slots codes intermediate unread : List Atom) (first : Atom) (earlier : List Atom)
      (result : Option (List Atom))
      (matched : ExpressionMatch images context resolver fuel slots codes first (some (intermediate, unread)))
      (remaining : HypothesisMatch images context resolver fuel intermediate unread earlier result) :
      HypothesisMatch images context resolver (fuel + 1) slots
        (MMBExecution.commandValue 54 data start after :: codes) (first :: earlier) result

def hypothesisValue (images context resolver : Atom) (result : Option (List Atom)) : Atom :=
  optionValue (result.map fun slots => matchingValue slots images context resolver)

/-- Arbitrary finite ordered hypothesis recursion executes in the unchanged
source and requires each original command boundary, including the final suffix. -/
theorem hypotheses_returns (state : State) (images context resolver : Atom) (fuel : Nat)
    (slots codes hypotheses : List Atom) (result : Option (List Atom))
    (trace : HypothesisMatch images context resolver fuel slots codes hypotheses result) :
    PureReturns program (callBindings fuel (matchingValue slots images context resolver) (listValue codes) (listValue hypotheses))
      state (callExpression "mm0:mmb:match-hypotheses") state (hypothesisValue images context resolver result) := by
  induction fuel generalizing slots codes hypotheses result with
  | zero =>
      cases trace with
      | empty slots => exact hypotheses_empty_returns state 0 _
      | missingCode _ _ first earlier => exact hypotheses_missing_code_returns state 0 _ first earlier
      | extraCode _ _ first rest => exact hypotheses_extra_code_returns state 0 _ first rest
      | wrongBoundary _ opcode data start after _ codes first earlier different =>
          exact hypotheses_wrong_opcode_returns state 0 opcode data start after _ first codes earlier different
      | zero data start after slots codes first earlier =>
          exact hypotheses_from_body state 0 _ _ _ _ (hypotheses_zero_body state data start after _ codes first earlier)
  | succ fuel ih =>
      cases trace with
      | empty slots => exact hypotheses_empty_returns state (fuel + 1) _
      | missingCode _ _ first earlier => exact hypotheses_missing_code_returns state (fuel + 1) _ first earlier
      | extraCode _ _ first rest => exact hypotheses_extra_code_returns state (fuel + 1) _ first rest
      | wrongBoundary _ opcode data start after _ codes first earlier different =>
          exact hypotheses_wrong_opcode_returns state (fuel + 1) opcode data start after _ first codes earlier different
      | refused _ data start after _ codes first earlier matched =>
          apply hypotheses_from_body
          exact hypotheses_cons_body state fuel data start after _ codes first earlier (.symbol "None") (.symbol "None")
            (expression_returns state images context resolver fuel _ _ _ _ matched)
            (by intro next remaining same; simp [optionValue] at same) (by simp) (.inl rfl)
      | next _ data start after _ codes intermediate unread first earlier _ matched remaining =>
          apply hypotheses_from_body
          apply hypotheses_cons_body state fuel data start after _ codes first earlier
            (matchedValue intermediate images context resolver unread) (hypothesisValue images context resolver result)
            (expression_returns state images context resolver fuel _ _ _ _ matched)
          · intro next rest same
            obtain ⟨rfl, rfl⟩ := resultValue_success images context resolver intermediate unread next rest same
            exact ih _ _ _ _ remaining
          · intro impossible
            simp [matchedValue, optionValue] at impossible
          · exact .inr ⟨matchingValue intermediate images context resolver, listValue unread, rfl⟩


/-- Filling a successful reservation retains the complete old slot prefix and
writes the complete original entry at its own physical reservation index. -/
theorem finishedMatch_append (save : Bool) (slots fresh : List Atom) (target : Atom) (rest : List Atom) :
    finishedMatch save slots target (some (reservedSlots save slots ++ fresh, rest)) =
      some (slots ++ (if save then optionValue (some target) :: fresh else fresh), rest) := by
  cases save <;> simp [finishedMatch, reservedSlots]

private theorem slots_prefix (images context resolver : Atom) (fuel : Nat) :
    (∀ slots codes target result, ExpressionMatch images context resolver fuel slots codes target result →
      ∀ after rest, result = some (after, rest) → ∃ fresh, after = slots ++ fresh) ∧
    (∀ slots codes children result, ExpressionListMatch images context resolver fuel slots codes children result →
      ∀ after rest, result = some (after, rest) → ∃ fresh, after = slots ++ fresh) := by
  induction fuel with
  | zero =>
      constructor
      · intro slots codes target result trace after rest accepted
        cases trace with
        | zero => simp at accepted
      · intro slots codes children result trace after rest accepted
        cases trace with
        | empty => cases accepted; exact ⟨[], by simp⟩
        | zero => simp at accepted
  | succ fuel ih =>
      constructor
      · intro slots codes target result trace after rest accepted
        cases trace with
        | emptyCodes => simp at accepted
        | unknown => simp at accepted
        | wrongConstructor => simp at accepted
        | variableConstructor => simp at accepted
        | dummyVariable => simp at accepted
        | dummyApplication => simp at accepted
        | reference _ pointer index start next stored _ unread expression node value shape found =>
            by_cases same : stored = pointer
            · simp only [same, if_true, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact ⟨[], by simp⟩
            · simp [same] at accepted
        | unavailable => simp at accepted
        | constructor _ pointer term start next save _ unread children value child matched =>
            cases child with
            | none => simp [finishedMatch] at accepted
            | some pair =>
                obtain ⟨middle, remaining⟩ := pair
                obtain ⟨fresh, same⟩ := ih.2 _ _ _ _ matched middle remaining rfl
                rw [same, finishedMatch_append] at accepted
                cases accepted
                exact ⟨if save then optionValue (some (expressionValue pointer value
                  (.expression [.symbol "MM0:MMBApplication", natural term, listValue children]))) :: fresh else fresh, rfl⟩
      · intro slots codes children result trace after rest accepted
        cases trace with
        | empty => cases accepted; exact ⟨[], by simp⟩
        | refused => simp at accepted
        | next _ _ _ middle remaining first tail _ matched continued =>
            obtain ⟨headFresh, headSame⟩ := ih.1 _ _ _ _ matched middle remaining rfl
            obtain ⟨tailFresh, tailSame⟩ := ih.2 _ _ _ _ continued after rest accepted
            exact ⟨headFresh ++ tailFresh, by rw [tailSame, headSame, List.append_assoc]⟩

/-- A successful match cannot overwrite any supplied slot or change its pointer
or inert payload. New saved entries occur only after that exact old prefix. -/
theorem ExpressionMatch.preserves_slots (images context resolver : Atom) (fuel : Nat)
    (slots codes : List Atom) (target : Atom) (after rest : List Atom)
    (trace : ExpressionMatch images context resolver fuel slots codes target (some (after, rest))) :
    ∃ fresh, after = slots ++ fresh :=
  (slots_prefix images context resolver fuel).1 _ _ _ _ trace after rest rfl

theorem ExpressionListMatch.preserves_slots (images context resolver : Atom) (fuel : Nat)
    (slots codes children after rest : List Atom)
    (trace : ExpressionListMatch images context resolver fuel slots codes children (some (after, rest))) :
    ∃ fresh, after = slots ++ fresh :=
  (slots_prefix images context resolver fuel).2 _ _ _ _ trace after rest rfl

/-- A recursively earned matcher result is the exact completed observation of
its original quoted source call, for any sufficiently large execution budget. -/
theorem expression_result_iff (state : State) (images context resolver : Atom)
    (fuel : Nat) (slots codes : List Atom) (target answer : Atom) (result : Option (List Atom × List Atom))
    (trace : ExpressionMatch images context resolver fuel slots codes target result) :
    (∃ budget, run program budget
      {state := state, control := .evaluate (callBindings fuel (matchingValue slots images context resolver) (listValue codes) target)
        (callExpression "mm0:mmb:match-expression")} = .complete state [answer] [] []) ↔
      answer = resultValue images context resolver result := by
  obtain ⟨budget, known⟩ := pure_returns_has_sufficient_fuel program _ state state _ _
    (expression_returns state images context resolver fuel slots codes target result trace)
  constructor
  · rintro ⟨other, observed⟩
    have same := completed_result_unique program budget other _ state state _ [] [] [answer] [] [] known observed
    simpa using same.2.1.symm
  · intro same
    exact ⟨budget, by simpa only [same] using known⟩

theorem children_result_iff (state : State) (images context resolver : Atom)
    (fuel : Nat) (slots codes children : List Atom) (answer : Atom) (result : Option (List Atom × List Atom))
    (trace : ExpressionListMatch images context resolver fuel slots codes children result) :
    (∃ budget, run program budget
      {state := state, control := .evaluate (callBindings fuel (matchingValue slots images context resolver) (listValue codes) (listValue children))
        (callExpression "mm0:mmb:match-expressions")} = .complete state [answer] [] []) ↔
      answer = resultValue images context resolver result := by
  obtain ⟨budget, known⟩ := pure_returns_has_sufficient_fuel program _ state state _ _
    (children_returns state images context resolver fuel slots codes children result trace)
  constructor
  · rintro ⟨other, observed⟩
    have same := completed_result_unique program budget other _ state state _ [] [] [answer] [] [] known observed
    simpa using same.2.1.symm
  · intro same
    exact ⟨budget, by simpa only [same] using known⟩

theorem hypotheses_result_iff (state : State) (images context resolver : Atom)
    (fuel : Nat) (slots codes hypotheses : List Atom) (answer : Atom) (result : Option (List Atom))
    (trace : HypothesisMatch images context resolver fuel slots codes hypotheses result) :
    (∃ budget, run program budget
      {state := state, control := .evaluate (callBindings fuel (matchingValue slots images context resolver) (listValue codes) (listValue hypotheses))
        (callExpression "mm0:mmb:match-hypotheses")} = .complete state [answer] [] []) ↔
      answer = hypothesisValue images context resolver result := by
  obtain ⟨budget, known⟩ := pure_returns_has_sufficient_fuel program _ state state _ _
    (hypotheses_returns state images context resolver fuel slots codes hypotheses result trace)
  constructor
  · rintro ⟨other, observed⟩
    have same := completed_result_unique program budget other _ state state _ [] [] [answer] [] [] known observed
    simpa using same.2.1.symm
  · intro same
    exact ⟨budget, by simpa only [same] using known⟩


mutual
  /-- Original expression-entry syntax, with source values left inert and complete.
  This refines `Atom`; it does not allocate entries or authorize proofs. -/
  inductive ExpressionEntry : Atom → Prop where
    | entry (pointer : Nat) (value node : Atom) (shaped : ExpressionNode node) :
        ExpressionEntry (expressionValue pointer value node)
  inductive ExpressionNode : Atom → Prop where
    | variableNode (index : Nat) : ExpressionNode (.expression [.symbol "MM0:MMBVariable", natural index])
    | application (term : Nat) (children : List Atom)
        (shaped : ∀ child ∈ children, ExpressionEntry child) :
        ExpressionNode (.expression [.symbol "MM0:MMBApplication", natural term, listValue children])
end

/-- The decoded assertion instruction shape, retaining every numeric field. -/
def CodeWellFormed (code : Atom) : Prop :=
  ∃ opcode data start after : Nat, code = MMBExecution.commandValue opcode data start after

def CodesWellFormed (codes : List Atom) : Prop := ∀ code ∈ codes, CodeWellFormed code

/-- Original optional physical entries, including unavailable reservations. -/
def SlotWellFormed (slot : Atom) : Prop :=
  slot = .symbol "None" ∨ ∃ pointer : Nat, ∃ value node : Atom,
    slot = optionValue (some (expressionValue pointer value node))

def SlotsWellFormed (slots : List Atom) : Prop := ∀ slot ∈ slots, SlotWellFormed slot

def ResultWellFormed (result : Option (List Atom × List Atom)) : Prop :=
  ∀ slots rest, result = some (slots, rest) → SlotsWellFormed slots ∧ CodesWellFormed rest

private theorem resultWellFormed_none : ResultWellFormed none := by
  intro slots rest impossible
  simp at impossible

private theorem SlotsWellFormed.reserve (save : Bool) (slots : List Atom) (shaped : SlotsWellFormed slots) :
    SlotsWellFormed (reservedSlots save slots) := by
  intro slot member
  cases save
  · exact shaped slot member
  · simp only [reservedSlots, if_true, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact shaped slot old
    · exact .inl rfl

private theorem SlotsWellFormed.set (slots : List Atom) (index : Nat) (entry : Atom)
    (shaped : SlotsWellFormed slots) (entryShape : SlotWellFormed entry) :
    SlotsWellFormed (slots.set index entry) := by
  intro slot member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact shaped slot old
  · exact entryShape

private theorem finishedMatch_wellFormed (save : Bool) (slots : List Atom) (pointer : Nat)
    (value node : Atom) (child : Option (List Atom × List Atom)) (shaped : ResultWellFormed child) :
    ResultWellFormed (finishedMatch save slots (expressionValue pointer value node) child) := by
  intro after rest accepted
  cases child with
  | none => simp [finishedMatch] at accepted
  | some pair =>
      obtain ⟨middle, unread⟩ := pair
      obtain ⟨slotsShape, codesShape⟩ := shaped middle unread rfl
      cases save
      · simp only [finishedMatch, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨slotsShape, codesShape⟩
      · cases lookup : middle[slots.length]? with
        | none => simp [finishedMatch, lookup] at accepted
        | some entry =>
            simp only [finishedMatch, ↓reduceIte, lookup, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
            obtain ⟨rfl, rfl⟩ := accepted
            exact ⟨SlotsWellFormed.set middle slots.length _ slotsShape (.inr ⟨pointer, value, node, rfl⟩), codesShape⟩

private theorem match_total (images : List Atom) (context resolver : Atom) (fuel : Nat) :
    (∀ slots codes target, SlotsWellFormed slots → CodesWellFormed codes → ExpressionEntry target →
      ∃ result, ExpressionMatch (listValue images) context resolver fuel slots codes target result ∧ ResultWellFormed result) ∧
    (∀ slots codes children, SlotsWellFormed slots → CodesWellFormed codes →
      (∀ child ∈ children, ExpressionEntry child) →
      ∃ result, ExpressionListMatch (listValue images) context resolver fuel slots codes children result ∧ ResultWellFormed result) := by
  induction fuel with
  | zero =>
      constructor
      · intro slots codes target _ _ targetShape
        cases targetShape with
        | entry pointer value node shaped => exact ⟨none, .zero slots codes pointer value node, resultWellFormed_none⟩
      · intro slots codes children slotsShape codesShape childrenShape
        cases children with
        | nil => exact ⟨some (slots, codes), .empty 0 slots codes, by intro after rest accepted; cases accepted; exact ⟨slotsShape, codesShape⟩⟩
        | cons first rest => exact ⟨none, .zero slots codes first rest, resultWellFormed_none⟩
  | succ fuel ih =>
      constructor
      · intro slots codes target slotsShape codesShape targetShape
        cases targetShape with
        | entry pointer value node nodeShape =>
          cases codes with
          | nil => exact ⟨none, .emptyCodes fuel pointer slots value node, resultWellFormed_none⟩
          | cons first rest =>
            obtain ⟨opcode, data, start, after, rfl⟩ := codesShape first (by simp)
            have restShape : CodesWellFormed rest := by
              intro code member
              exact codesShape code (List.mem_cons_of_mem _ member)
            have constructorTrace (save : Bool) :
                ∃ result, ExpressionMatch (listValue images) context resolver (fuel + 1) slots
                  (MMBExecution.commandValue (if save then 49 else 48) data start after :: rest)
                  (expressionValue pointer value node) result ∧ ResultWellFormed result := by
              cases nodeShape with
              | variableNode index => exact ⟨none, .variableConstructor fuel pointer data index start after save slots rest value, resultWellFormed_none⟩
              | application binary children childrenShape =>
                  by_cases same : binary = data
                  · subst binary
                    obtain ⟨child, matched, shaped⟩ := ih.2 (reservedSlots save slots) rest children
                      (SlotsWellFormed.reserve save slots slotsShape) restShape childrenShape
                    exact ⟨_, .constructor fuel pointer data start after save slots rest children value child matched,
                      finishedMatch_wellFormed save slots pointer value _ child shaped⟩
                  · exact ⟨none, .wrongConstructor fuel pointer data binary start after save slots rest children value same, resultWellFormed_none⟩
            by_cases is48 : opcode = 48
            · subst opcode
              simpa only [Bool.false_eq_true, ↓reduceIte] using constructorTrace false
            by_cases is49 : opcode = 49
            · subst opcode
              simpa only [↓reduceIte] using constructorTrace true
            by_cases is50 : opcode = 50
            · subst opcode
              cases lookup : slots[data]? with
              | none => exact ⟨none, .unavailable fuel pointer data start after slots rest value node (.inl lookup), resultWellFormed_none⟩
              | some slot =>
                  rcases slotsShape slot (List.mem_of_getElem? lookup) with absent | ⟨stored, expression, shape, rfl⟩
                  · subst slot
                    exact ⟨none, .unavailable fuel pointer data start after slots rest value node (.inr lookup), resultWellFormed_none⟩
                  · refine ⟨_, .reference fuel pointer data start after stored slots rest value node expression shape lookup, ?_⟩
                    by_cases same : stored = pointer
                    · simp only [same, if_true]
                      intro middle unread accepted
                      cases accepted
                      exact ⟨slotsShape, restShape⟩
                    · simpa only [same, if_false] using resultWellFormed_none
            by_cases is51 : opcode = 51
            · subst opcode
              cases nodeShape with
              | variableNode index => exact ⟨none, .dummyVariable fuel pointer data index start after slots rest images value rfl, resultWellFormed_none⟩
              | application binary children childrenShape =>
                  exact ⟨none, .dummyApplication fuel pointer data binary start after slots rest images children value rfl, resultWellFormed_none⟩
            exact ⟨none, .unknown fuel pointer opcode data start after slots rest value node ⟨is48, is49, is50, is51⟩, resultWellFormed_none⟩
      · intro slots codes children slotsShape codesShape childrenShape
        cases children with
        | nil => exact ⟨some (slots, codes), .empty (fuel + 1) slots codes, by intro after rest accepted; cases accepted; exact ⟨slotsShape, codesShape⟩⟩
        | cons first rest =>
            obtain ⟨head, matched, headShape⟩ := ih.1 slots codes first slotsShape codesShape (childrenShape first (by simp))
            cases head with
            | none => exact ⟨none, .refused fuel slots codes first rest matched, resultWellFormed_none⟩
            | some pair =>
                obtain ⟨middle, unread⟩ := pair
                obtain ⟨middleShape, unreadShape⟩ := headShape middle unread rfl
                obtain ⟨tail, remaining, tailShape⟩ := ih.2 middle unread rest middleShape unreadShape
                  (by intro child member; exact childrenShape child (List.mem_cons_of_mem _ member))
                exact ⟨tail, .next fuel slots codes middle unread first rest tail matched remaining, tailShape⟩

/-- Every finite well-shaped assertion input has an earned success or explicit
refusal trace of the original source. This does not authorize its pointer payload. -/
theorem expression_total (images : List Atom) (context resolver : Atom) (fuel : Nat)
    (slots codes : List Atom) (target : Atom) (slotsShape : SlotsWellFormed slots)
    (codesShape : CodesWellFormed codes) (targetShape : ExpressionEntry target) :
    ∃ result, ExpressionMatch (listValue images) context resolver fuel slots codes target result ∧ ResultWellFormed result :=
  (match_total images context resolver fuel).1 slots codes target slotsShape codesShape targetShape

theorem children_total (images : List Atom) (context resolver : Atom) (fuel : Nat)
    (slots codes children : List Atom) (slotsShape : SlotsWellFormed slots) (codesShape : CodesWellFormed codes)
    (childrenShape : ∀ child ∈ children, ExpressionEntry child) :
    ∃ result, ExpressionListMatch (listValue images) context resolver fuel slots codes children result ∧ ResultWellFormed result :=
  (match_total images context resolver fuel).2 slots codes children slotsShape codesShape childrenShape


/-- Every finite well-shaped hypothesis sequence is accepted or explicitly
refused by the original boundary-sensitive matcher. -/
theorem hypotheses_total (images : List Atom) (context resolver : Atom) (fuel : Nat)
    (slots codes hypotheses : List Atom) (slotsShape : SlotsWellFormed slots) (codesShape : CodesWellFormed codes)
    (hypothesesShape : ∀ target ∈ hypotheses, ExpressionEntry target) :
    ∃ result, HypothesisMatch (listValue images) context resolver fuel slots codes hypotheses result ∧
      ∀ after, result = some after → SlotsWellFormed after := by
  induction fuel generalizing slots codes hypotheses with
  | zero =>
      cases hypotheses with
      | nil =>
          cases codes with
          | nil => exact ⟨some slots, .empty 0 slots, by intro after accepted; cases accepted; exact slotsShape⟩
          | cons first rest => exact ⟨none, .extraCode 0 slots first rest, by intro after impossible; simp at impossible⟩
      | cons first earlier =>
          cases codes with
          | nil => exact ⟨none, .missingCode 0 slots first earlier, by intro after impossible; simp at impossible⟩
          | cons code rest =>
              obtain ⟨opcode, data, start, next, rfl⟩ := codesShape code (by simp)
              by_cases boundary : opcode = 54
              · subst opcode
                exact ⟨none, .zero data start next slots rest first earlier, by intro after impossible; simp at impossible⟩
              · exact ⟨none, .wrongBoundary 0 opcode data start next slots rest first earlier boundary, by intro after impossible; simp at impossible⟩
  | succ fuel ih =>
      cases hypotheses with
      | nil =>
          cases codes with
          | nil => exact ⟨some slots, .empty (fuel + 1) slots, by intro after accepted; cases accepted; exact slotsShape⟩
          | cons first rest => exact ⟨none, .extraCode (fuel + 1) slots first rest, by intro after impossible; simp at impossible⟩
      | cons first earlier =>
          cases codes with
          | nil => exact ⟨none, .missingCode (fuel + 1) slots first earlier, by intro after impossible; simp at impossible⟩
          | cons code rest =>
              obtain ⟨opcode, data, start, next, rfl⟩ := codesShape code (by simp)
              by_cases boundary : opcode = 54
              · subst opcode
                have restShape : CodesWellFormed rest := by
                  intro instruction member
                  exact codesShape instruction (List.mem_cons_of_mem _ member)
                obtain ⟨child, matched, childShape⟩ := expression_total images context resolver fuel slots rest first slotsShape restShape
                  (hypothesesShape first (by simp))
                cases child with
                | none => exact ⟨none, .refused fuel data start next slots rest first earlier matched, by intro after impossible; simp at impossible⟩
                | some pair =>
                    obtain ⟨middle, unread⟩ := pair
                    obtain ⟨middleShape, unreadShape⟩ := childShape middle unread rfl
                    obtain ⟨tail, continued, tailShape⟩ := ih middle unread earlier middleShape unreadShape
                      (by intro target member; exact hypothesesShape target (List.mem_cons_of_mem _ member))
                    exact ⟨tail, .next fuel data start next slots rest middle unread first earlier tail matched continued, tailShape⟩
              · exact ⟨none, .wrongBoundary (fuel + 1) opcode data start next slots rest first earlier boundary, by intro after impossible; simp at impossible⟩

/-- Actual completed observations of every structurally admitted assertion call.
The general source execution is earned here rather than supplied as a premise. -/
theorem expression_completed_total (state : State) (images : List Atom) (context resolver : Atom)
    (fuel : Nat) (slots codes : List Atom) (target : Atom)
    (slotsShape : SlotsWellFormed slots) (codesShape : CodesWellFormed codes) (targetShape : ExpressionEntry target) :
    ∃ result, ResultWellFormed result ∧ ∀ after answers input output,
      (∃ budget, run program budget
        {state := state, control := .evaluate
          (callBindings fuel (matchingValue slots (listValue images) context resolver) (listValue codes) target)
          (callExpression "mm0:mmb:match-expression")} = .complete after answers input output) ↔
      after = state ∧ answers = [resultValue (listValue images) context resolver result] ∧ input = [] ∧ output = [] := by
  obtain ⟨result, trace, shaped⟩ := expression_total images context resolver fuel slots codes target slotsShape codesShape targetShape
  refine ⟨result, shaped, ?_⟩
  intro after answers input output
  exact pure_returns_completed_iff program _ state state _ _
    (expression_returns state (listValue images) context resolver fuel slots codes target result trace) after answers input output

theorem children_completed_total (state : State) (images : List Atom) (context resolver : Atom)
    (fuel : Nat) (slots codes children : List Atom)
    (slotsShape : SlotsWellFormed slots) (codesShape : CodesWellFormed codes)
    (childrenShape : ∀ target ∈ children, ExpressionEntry target) :
    ∃ result, ResultWellFormed result ∧ ∀ after answers input output,
      (∃ budget, run program budget
        {state := state, control := .evaluate
          (callBindings fuel (matchingValue slots (listValue images) context resolver) (listValue codes) (listValue children))
          (callExpression "mm0:mmb:match-expressions")} = .complete after answers input output) ↔
      after = state ∧ answers = [resultValue (listValue images) context resolver result] ∧ input = [] ∧ output = [] := by
  obtain ⟨result, trace, shaped⟩ := children_total images context resolver fuel slots codes children slotsShape codesShape childrenShape
  refine ⟨result, shaped, ?_⟩
  intro after answers input output
  exact pure_returns_completed_iff program _ state state _ _
    (children_returns state (listValue images) context resolver fuel slots codes children result trace) after answers input output

theorem hypotheses_completed_total (state : State) (images : List Atom) (context resolver : Atom)
    (fuel : Nat) (slots codes hypotheses : List Atom)
    (slotsShape : SlotsWellFormed slots) (codesShape : CodesWellFormed codes)
    (hypothesesShape : ∀ target ∈ hypotheses, ExpressionEntry target) :
    ∃ result, (∀ after, result = some after → SlotsWellFormed after) ∧ ∀ after answers input output,
      (∃ budget, run program budget
        {state := state, control := .evaluate
          (callBindings fuel (matchingValue slots (listValue images) context resolver) (listValue codes) (listValue hypotheses))
          (callExpression "mm0:mmb:match-hypotheses")} = .complete after answers input output) ↔
      after = state ∧ answers = [hypothesisValue (listValue images) context resolver result] ∧ input = [] ∧ output = [] := by
  obtain ⟨result, trace, shaped⟩ := hypotheses_total images context resolver fuel slots codes hypotheses slotsShape codesShape hypothesesShape
  refine ⟨result, shaped, ?_⟩
  intro after answers input output
  exact pure_returns_completed_iff program _ state state _ _
    (hypotheses_returns state (listValue images) context resolver fuel slots codes hypotheses result trace) after answers input output


/-- The original argument-slot initializer supplies well-shaped optional slots. -/
theorem SlotsWellFormed.initialSlots (arguments : List Atom)
    (shaped : ∀ argument ∈ arguments, ExpressionEntry argument) :
    SlotsWellFormed (MMBAssertionMatchExecution.initialSlots arguments) := by
  intro slot member
  obtain ⟨argument, inArguments, rfl⟩ :=
    (List.mem_map (f := fun argument : Atom => optionValue (some argument)) (l := arguments)).mp member
  cases shaped argument inArguments with
  | entry pointer value node _ => exact .inr ⟨pointer, value, node, rfl⟩

private theorem resultValue_injective (images context resolver : Atom) :
    Function.Injective (resultValue images context resolver) := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => simp [resultValue, matchedValue, optionValue] at same
  | some first =>
      cases second with
      | none => simp [resultValue, matchedValue, optionValue] at same
      | some second =>
          simpa [resultValue, matchedValue, matchingValue, listValue, optionValue, Prod.ext_iff] using same

/-- Earned traces cannot disagree on a successful suffix or a refusal result. -/
theorem ExpressionMatch.result_unique (images context resolver : Atom) (fuel : Nat)
    (slots codes : List Atom) (target : Atom) (first second : Option (List Atom × List Atom))
    (left : ExpressionMatch images context resolver fuel slots codes target first)
    (right : ExpressionMatch images context resolver fuel slots codes target second) : first = second := by
  obtain ⟨budget, observed⟩ := pure_returns_has_sufficient_fuel program _ (Effects.loaded program) (Effects.loaded program) _ _
    (expression_returns (Effects.loaded program) images context resolver fuel slots codes target first left)
  have unique := (expression_result_iff (Effects.loaded program) images context resolver fuel slots codes target
    (resultValue images context resolver first) second right).mp ⟨budget, observed⟩
  exact resultValue_injective images context resolver unique

theorem ExpressionListMatch.result_unique (images context resolver : Atom) (fuel : Nat)
    (slots codes children : List Atom) (first second : Option (List Atom × List Atom))
    (left : ExpressionListMatch images context resolver fuel slots codes children first)
    (right : ExpressionListMatch images context resolver fuel slots codes children second) : first = second := by
  obtain ⟨budget, observed⟩ := pure_returns_has_sufficient_fuel program _ (Effects.loaded program) (Effects.loaded program) _ _
    (children_returns (Effects.loaded program) images context resolver fuel slots codes children first left)
  have unique := (children_result_iff (Effects.loaded program) images context resolver fuel slots codes children
    (resultValue images context resolver first) second right).mp ⟨budget, observed⟩
  exact resultValue_injective images context resolver unique

end Mettapedia.Languages.MM0.MeTTa.MMBRecursiveMatchExecution
