import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataDerivativeExecution

/-!
# Compiling and observing through the retained matching source

The source compiler, preorder observation traversal and candidate seeding
execute their own equations. Their outputs agree with the independent
position-derivative machine for arbitrary finite constructor trees and paths.
Opaque wire heads remain captured data, including heads resembling calls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataCompilationExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire OrderedPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval MatchAutomataProgram
open MatchAutomataSourceExecution (listValue)
open MatchAutomataDerivativeExecution (positionTerm keyTerm obligationTerm locationTerm goalTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev number (value : Nat) : Atom := CettaWireAtom.encode (.natural value)

mutual
  /-- The structural pattern wire used by the retained source compiler. -/
  def shapeTerm : Pattern Term → Term
    | .wildcard => .symbol "MAny"
    | .node head children => .application "MNode" [head, encodeList id (shapeTerms children)]

  def shapeTerms : List (Pattern Term) → List Term
    | [] => []
    | first :: rest => shapeTerm first :: shapeTerms rest
end

@[simp] theorem shapeTerms_eq_map (patterns : List (Pattern Term)) :
    shapeTerms patterns = patterns.map shapeTerm := by
  induction patterns with
  | nil => rfl
  | cons first rest ih => simp only [shapeTerms, List.map_cons, ih]

@[simp] theorem shapeTerm_node (head : Term) (children : List (Pattern Term)) :
    shapeTerm (.node head children) = .application "MNode" [head, encodeList shapeTerm children] := by
  simp [shapeTerm]

private theorem listTerm_injective : Function.Injective (encodeList (id : Term → Term)) := by
  intro left right same
  induction left generalizing right with
  | nil => cases right <;> simp_all [encodeList]
  | cons first rest ih =>
      cases right with
      | nil => simp [encodeList] at same
      | cons other tail =>
          have arguments := (Term.application.inj same).2
          exact congrArg₂ List.cons (List.cons.inj arguments).1
            (ih (List.cons.inj (List.cons.inj arguments).2).1)

mutual
  theorem shapeTerm_injective : Function.Injective shapeTerm := by
    intro left right same
    cases left with
    | wildcard => cases right <;> simp_all [shapeTerm]
    | node head children =>
        cases right with
        | wildcard => simp [shapeTerm] at same
        | node other rest =>
            have arguments := (Term.application.inj same).2
            have heads := (List.cons.inj arguments).1
            have tails := (List.cons.inj (List.cons.inj arguments).2).1
            exact congrArg₂ Pattern.node heads (shapeTerms_injective (listTerm_injective tails))

  theorem shapeTerms_injective : Function.Injective shapeTerms := by
    intro left right same
    cases left with
    | nil => cases right <;> simp_all [shapeTerms]
    | cons first rest =>
        cases right with
        | nil => simp [shapeTerms] at same
        | cons other tail =>
            have parts := List.cons.inj same
            exact congrArg₂ List.cons (shapeTerm_injective parts.1) (shapeTerms_injective parts.2)
end

mutual
  /-- The subject wire read by the retained preorder observation traversal. -/
  def subjectTerm : Subject Term → Term
    | .node head children => .application "MNode" [head, encodeList id (subjectTerms children)]

  def subjectTerms : List (Subject Term) → List Term
    | [] => []
    | first :: rest => subjectTerm first :: subjectTerms rest
end

@[simp] theorem subjectTerms_eq_map (subjects : List (Subject Term)) :
    subjectTerms subjects = subjects.map subjectTerm := by
  induction subjects with
  | nil => rfl
  | cons first rest ih => simp only [subjectTerms, List.map_cons, ih]

@[simp] theorem subjectTerm_node (head : Term) (children : List (Subject Term)) :
    subjectTerm (.node head children) = .application "MNode" [head, encodeList subjectTerm children] := by
  simp [subjectTerm]

private def obligationsValue (obligations : List (TopDownMatchDerivatives.Obligation Term)) : Atom :=
  listValue (obligations.map obligationTerm)
private def programsValue (programs : List (List (TopDownMatchDerivatives.Obligation Term))) : Atom :=
  listValue (programs.map (encodeList obligationTerm))

private theorem append_captured (bindings : Subst) (state : State) (left right : List Term)
    (leftArg rightArg : Atom)
    (leftCaptured : applySubst bindings leftArg = listValue left)
    (rightCaptured : applySubst bindings rightArg = listValue right) :
    PureReturns program bindings state (a "gslt:automata:append" [leftArg, rightArg]) state
      (listValue (left ++ right)) := by
  let equation := (equations "gslt:automata:append")[0]'(by decide +kernel)
  let callee : Subst := [("right", listValue right), ("left", listValue left)]
  apply PureData.raw_authored_call_return program bindings callee state state
    "gslt:automata:append" [leftArg, rightArg] equation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ _
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
    rw [clauses_use_only_the_named_equations]
    change (equations "gslt:automata:append").filterMap _ = _
    rw [show equations "gslt:automata:append" = [equation] from rfl]
    have formals : equation.arguments = [v "left", v "right"] := by decide +kernel
    simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, callee]
  · exact MatchAutomataSourceExecution.append_body_returns state left right

private theorem increment_returns (bindings : Subst) (state : State) (count : Nat)
    (captured : applySubst bindings (v "next") = number count) :
    PureReturns program bindings state (a "+" [v "next", number 1]) state (number (count + 1)) := by
  apply native_binary_call_returns program bindings state state state state "+"
    (v "next") (number 1) (number count) (number 1) (number (count + 1))
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · simpa [captured] using variable_returns program bindings state "next"
  · exact grounded_returns program bindings state (.int 1)
  · simpa only [number, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one]
      using StdLib.integer_addition state (count : Int) 1

private theorem two_raw_number_call (bindings callee : Subst) (state : State)
    (head : String) (one two third oneValue twoValue : Atom) (count : Nat) (body answer : Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (notIO : ioHead head = false) (notNative : StdLib.known head = false)
    (firstRaw : argumentIsRaw program head 0 = true)
    (secondRaw : argumentIsRaw program head 1 = true)
    (thirdDemanded : argumentIsRaw program head 2 = false)
    (firstCaptured : applySubst bindings one = oneValue)
    (secondCaptured : applySubst bindings two = twoValue)
    (thirdComputed : PureReturns program bindings state third state (number count))
    (selected : clauses program head [oneValue, twoValue, number count] = [.evaluate callee body])
    (returned : PureReturns program callee state body state answer) :
    PureReturns program bindings state (a head [one, two, third]) state answer := by
  apply call_returns program bindings state state head _ _ dispatch _ ordinary
  apply raw_argument_answers program bindings state state head one _ [] 0 _ firstRaw
  simp only [firstCaptured, List.nil_append]
  apply raw_argument_answers program bindings state state head two _ _ 1 _ secondRaw
  simp only [secondCaptured, List.singleton_append]
  apply evaluated_argument_returns program bindings state state state (.function head)
    third (number count) _ [] _ 2 thirdDemanded thirdComputed
  simpa using authored_function_arguments_return program bindings callee state state head
    _ 3 body answer notIO notNative selected returned

private theorem let_two_returns (bindings : Subst) (state : State)
    (firstName secondName : String) (first second body firstValue secondValue answer : Atom)
    (firstReturned : PureReturns program bindings state first state firstValue)
    (firstMatch : SpaceSemantics.matchBinding bindings (v firstName) firstValue =
      some ((firstName, firstValue) :: bindings))
    (secondReturned : PureReturns program ((firstName, firstValue) :: bindings) state
      second state secondValue)
    (secondMatch : SpaceSemantics.matchBinding ((firstName, firstValue) :: bindings)
      (v secondName) secondValue = some ((secondName, secondValue) :: (firstName, firstValue) :: bindings))
    (bodyReturned : PureReturns program ((secondName, secondValue) :: (firstName, firstValue) :: bindings)
      state body state answer) :
    PureReturns program bindings state
      (a "let*" [.expression [.expression [v firstName, first], .expression [v secondName, second]], body])
      state answer := by
  apply let_star_returns program bindings state state _ body
    (a "let" [v firstName, first, a "let" [v secondName, second, body]]) answer rfl
  apply let_returns program bindings ((firstName, firstValue) :: bindings) state state state
    _ _ _ _ _ firstReturned firstMatch
  exact let_returns program _ _ state state state _ _ _ _ _ secondReturned secondMatch bodyReturned

private theorem let_three_returns (bindings : Subst) (state : State)
    (firstName secondName thirdName : String) (first second third body firstValue secondValue thirdValue answer : Atom)
    (firstReturned : PureReturns program bindings state first state firstValue)
    (firstMatch : SpaceSemantics.matchBinding bindings (v firstName) firstValue =
      some ((firstName, firstValue) :: bindings))
    (secondReturned : PureReturns program ((firstName, firstValue) :: bindings) state
      second state secondValue)
    (secondMatch : SpaceSemantics.matchBinding ((firstName, firstValue) :: bindings)
      (v secondName) secondValue = some ((secondName, secondValue) :: (firstName, firstValue) :: bindings))
    (thirdReturned : PureReturns program ((secondName, secondValue) :: (firstName, firstValue) :: bindings)
      state third state thirdValue)
    (thirdMatch : SpaceSemantics.matchBinding ((secondName, secondValue) :: (firstName, firstValue) :: bindings)
      (v thirdName) thirdValue = some
        ((thirdName, thirdValue) :: (secondName, secondValue) :: (firstName, firstValue) :: bindings))
    (bodyReturned : PureReturns program
      ((thirdName, thirdValue) :: (secondName, secondValue) :: (firstName, firstValue) :: bindings)
      state body state answer) :
    PureReturns program bindings state
      (a "let*" [.expression [.expression [v firstName, first], .expression [v secondName, second],
        .expression [v thirdName, third]], body]) state answer := by
  apply let_star_returns program bindings state state _ body
    (a "let" [v firstName, first, a "let" [v secondName, second, a "let" [v thirdName, third, body]]])
    answer rfl
  apply let_returns program bindings ((firstName, firstValue) :: bindings) state state state
    _ _ _ _ _ firstReturned firstMatch
  apply let_returns program _ ((secondName, secondValue) :: (firstName, firstValue) :: bindings)
    state state state _ _ _ _ _ secondReturned secondMatch
  exact let_returns program _ _ state state state _ _ _ _ _ thirdReturned thirdMatch bodyReturned

private def shiftEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:shift")[0]'(by decide +kernel)
private def shiftCons : Atom :=
  a "let*" [.expression [.expression [v "position", a "gslt:automata:append" [v "root", v "path"]],
    .expression [v "tail", a "gslt:automata:shift" [v "root", v "rest"]]],
    a "LCons" [a "Observe" [v "position", v "key"], v "tail"]]
private def shiftCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "Observe" [v "path", v "key"], v "rest"], shiftCons)]
private def shiftEnv (root : SubtermMatching.Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) : Subst :=
  [("obligations", obligationsValue pending), ("root", CettaWireAtom.encode (positionTerm root))]
private theorem shift_shape : shiftEquation.body =
    a "case" [v "obligations", .expression (shiftCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem shift_clause (root : SubtermMatching.Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    clauses program "gslt:automata:shift" [CettaWireAtom.encode (positionTerm root), obligationsValue pending] =
      [.evaluate (shiftEnv root pending) shiftEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:shift").filterMap _ = _
  rw [show equations "gslt:automata:shift" = [shiftEquation] from rfl]
  have formals : shiftEquation.arguments = [v "root", v "obligations"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, shiftEnv]
private theorem shift_call (bindings : Subst) (state : State) (root : SubtermMatching.Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (one two : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (positionTerm root))
    (secondCaptured : applySubst bindings two = obligationsValue pending)
    (bodyReturned : PureReturns program (shiftEnv root pending) state shiftEquation.body state
      (obligationsValue (TopDownMatchDerivatives.shift root pending))) :
    PureReturns program bindings state (a "gslt:automata:shift" [one, two]) state
      (obligationsValue (TopDownMatchDerivatives.shift root pending)) := by
  apply PureData.raw_authored_call_return program bindings (shiftEnv root pending) state state
    "gslt:automata:shift" [one, two] shiftEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ bodyReturned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, firstCaptured, secondCaptured]
    exact shift_clause root pending

private theorem shift_template : PureData.Template program
    (a "LCons" [a "Observe" [v "position", v "key"], v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Observe" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

theorem shift_body_returns (state : State) (root : SubtermMatching.Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program (shiftEnv root pending) state shiftEquation.body state
      (obligationsValue (TopDownMatchDerivatives.shift root pending)) := by
  induction pending with
  | nil =>
      rw [shift_shape]
      apply case_returns program (shiftEnv root []) (shiftEnv root []) state state state
        (v "obligations") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _ shiftCases
        (read_cases_encoded _) _ _ _
      · simpa [shiftEnv, obligationsValue, listValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program (shiftEnv root []) state "obligations"
      · simp [shiftCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons first rest ih =>
      let bindings := shiftEnv root (first :: rest)
      let selected := ("rest", obligationsValue rest) :: ("key", CettaWireAtom.encode (keyTerm first.key)) ::
        ("path", CettaWireAtom.encode (positionTerm first.position)) :: bindings
      let position := CettaWireAtom.encode (positionTerm (root ++ first.position))
      let positionBound := ("position", position) :: selected
      let tail := obligationsValue (TopDownMatchDerivatives.shift root rest)
      let tailBound := ("tail", tail) :: positionBound
      rw [shift_shape]
      apply case_returns program bindings selected state state state (v "obligations")
        (obligationsValue (first :: rest)) shiftCons _ _ shiftCases (read_cases_encoded _) _ _ _
      · simpa [bindings, shiftEnv, applySubst, Subst.lookup] using variable_returns program bindings state "obligations"
      · simp [shiftCases, obligationsValue, listValue, encodeList, obligationTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, bindings, shiftEnv]
      · apply let_two_returns selected state "position" "tail" _ _ _ position tail _
        · simpa [position, positionTerm, listValue, ← List.map_append] using append_captured selected state
            (root.map Term.natural) (first.position.map Term.natural) (v "root") (v "path")
            (by simp [selected, bindings, shiftEnv, applySubst, Subst.lookup, positionTerm, listValue])
            (by simp [selected, applySubst, Subst.lookup, positionTerm, listValue])
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, shiftEnv]
        · exact shift_call positionBound state root rest (v "root") (v "rest")
            (by simp [positionBound, selected, bindings, shiftEnv, applySubst, Subst.lookup])
            (by simp [positionBound, selected, applySubst, Subst.lookup]) ih
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            selected, bindings, shiftEnv]
        · simpa [TopDownMatchDerivatives.shift, obligationsValue, listValue, encodeList,
            obligationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
            applySubst.applySubstList, Subst.lookup, tailBound, positionBound, selected,
            bindings, shiftEnv, position, tail] using
            PureData.template_return program tailBound state _ shift_template

theorem shift_captured_returns (bindings : Subst) (state : State) (root : SubtermMatching.Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) (one two : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (positionTerm root))
    (secondCaptured : applySubst bindings two = listValue (pending.map obligationTerm)) :
    PureReturns program bindings state (a "gslt:automata:shift" [one, two]) state
      (listValue ((TopDownMatchDerivatives.shift root pending).map obligationTerm)) :=
  shift_call bindings state root pending one two firstCaptured secondCaptured (shift_body_returns state root pending)

theorem shift_returns (state : State) (root : SubtermMatching.Position)
    (pending : List (TopDownMatchDerivatives.Obligation Term)) :
    PureReturns program [] state (a "gslt:automata:shift"
      [CettaWireAtom.encode (positionTerm root), listValue (pending.map obligationTerm)]) state
      (listValue ((TopDownMatchDerivatives.shift root pending).map obligationTerm)) :=
  shift_captured_returns [] state root pending _ _ (by simp) (by simp)

private def compileEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:compile")[0]'(by decide +kernel)
private def compileChildrenEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:compile-children")[0]'(by decide +kernel)
private def compileNode : Atom :=
  a "let*" [.expression [.expression [v "arity", a "gslt:automata:length" [v "children"]],
    .expression [v "tail", a "gslt:automata:compile-children" [v "children", v "path", number 0]]],
    a "LCons" [a "Observe" [v "path", a "MKey" [v "head", v "arity"]], v "tail"]]
private def compileCases : SpaceSemantics.Cases :=
  [(.symbol "MAny", .symbol "LNil"), (a "MNode" [v "head", v "children"], compileNode)]
private def traversalCons (childHead childrenHead : String) : Atom :=
  a "let*" [.expression
    [.expression [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [v "next", .symbol "LNil"]]],
      .expression [v "head", a childHead [v "child", v "child-path"]],
      .expression [v "tail", a childrenHead [v "rest", v "path", a "+" [v "next", number 1]]]],
    a "gslt:automata:append" [v "head", v "tail"]]
private def traversalCases (childHead childrenHead : String) : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [v "child", v "rest"], traversalCons childHead childrenHead)]
private def compileEnv (pattern : Pattern Term) (path : SubtermMatching.Position) : Subst :=
  [("path", CettaWireAtom.encode (positionTerm path)), ("pattern", CettaWireAtom.encode (shapeTerm pattern))]
private def childrenEnv (children : List Term) (path : SubtermMatching.Position) (next : Nat) : Subst :=
  [("next", number next), ("path", CettaWireAtom.encode (positionTerm path)), ("children", listValue children)]
private theorem compile_shape : compileEquation.body =
    a "case" [v "pattern", .expression (compileCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem compile_children_shape : compileChildrenEquation.body =
    a "case" [v "children", .expression ((traversalCases "gslt:automata:compile"
      "gslt:automata:compile-children").map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem compile_clause (pattern : Pattern Term) (path : SubtermMatching.Position) :
    clauses program "gslt:automata:compile"
      [CettaWireAtom.encode (shapeTerm pattern), CettaWireAtom.encode (positionTerm path)] =
      [.evaluate (compileEnv pattern path) compileEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:compile").filterMap _ = _
  rw [show equations "gslt:automata:compile" = [compileEquation] from rfl]
  have formals : compileEquation.arguments = [v "pattern", v "path"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, compileEnv]
private theorem compile_children_clause (children : List (Pattern Term))
    (path : SubtermMatching.Position) (next : Nat) :
    clauses program "gslt:automata:compile-children"
      [listValue (children.map shapeTerm), CettaWireAtom.encode (positionTerm path), number next] =
      [.evaluate (childrenEnv (children.map shapeTerm) path next) compileChildrenEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:compile-children").filterMap _ = _
  rw [show equations "gslt:automata:compile-children" = [compileChildrenEquation] from rfl]
  have formals : compileChildrenEquation.arguments = [v "children", v "path", v "next"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, childrenEnv]
private theorem compile_call (bindings : Subst) (state : State) (pattern : Pattern Term)
    (path : SubtermMatching.Position) (one two : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (shapeTerm pattern))
    (secondCaptured : applySubst bindings two = CettaWireAtom.encode (positionTerm path))
    (bodyReturned : PureReturns program (compileEnv pattern path) state compileEquation.body state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compile pattern)))) :
    PureReturns program bindings state (a "gslt:automata:compile" [one, two]) state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compile pattern))) := by
  apply PureData.raw_authored_call_return program bindings (compileEnv pattern path) state state
    "gslt:automata:compile" [one, two] compileEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ bodyReturned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, firstCaptured, secondCaptured]
    exact compile_clause pattern path
private theorem compile_children_call (bindings : Subst) (state : State) (children : List (Pattern Term))
    (path : SubtermMatching.Position) (next : Nat) (one two third : Atom)
    (firstCaptured : applySubst bindings one = listValue (children.map shapeTerm))
    (secondCaptured : applySubst bindings two = CettaWireAtom.encode (positionTerm path))
    (thirdComputed : PureReturns program bindings state third state (number next))
    (bodyReturned : PureReturns program (childrenEnv (children.map shapeTerm) path next)
      state compileChildrenEquation.body state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren next children)))) :
    PureReturns program bindings state (a "gslt:automata:compile-children" [one, two, third]) state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren next children))) :=
  two_raw_number_call bindings (childrenEnv (children.map shapeTerm) path next) state
    "gslt:automata:compile-children" one two third _ _ next compileChildrenEquation.body _
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) firstCaptured secondCaptured thirdComputed
    (compile_children_clause children path next) bodyReturned

private theorem observation_template : PureData.Template program
    (a "LCons" [a "Observe" [v "path", a "MKey" [v "head", v "arity"]], v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Observe" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .captured _
    · apply PureData.Template.constructor "MKey" _ (by decide +kernel) (by decide)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

private theorem compile_children_cons (path : SubtermMatching.Position) (next : Nat)
    (first : Pattern Term) (rest : List (Pattern Term)) :
    TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren next (first :: rest)) =
      TopDownMatchDerivatives.shift (path ++ [next]) (TopDownMatchDerivatives.compile first) ++
        TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren (next + 1) rest) := by
  simp [TopDownMatchDerivatives.shift, TopDownMatchDerivatives.compileChildren,
    List.map_map, Function.comp_def, List.append_assoc]

mutual
  theorem compile_body_returns (state : State) (pattern : Pattern Term) (path : SubtermMatching.Position) :
      PureReturns program (compileEnv pattern path) state compileEquation.body state
        (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compile pattern))) := by
    cases pattern with
    | wildcard =>
        rw [compile_shape]
        apply case_returns program (compileEnv .wildcard path) (compileEnv .wildcard path) state state state
          (v "pattern") (.symbol "MAny") (.symbol "LNil") (.symbol "LNil") _ compileCases
          (read_cases_encoded _) _ _ _
        · simpa [compileEnv, shapeTerm, CettaWireAtom.encode, applySubst, Subst.lookup] using
            variable_returns program (compileEnv .wildcard path) state "pattern"
        · simp [compileCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program _ state "LNil"
    | node head children =>
        let bindings := compileEnv (.node head children) path
        let selected := ("children", listValue (children.map shapeTerm)) :: ("head", CettaWireAtom.encode head) :: bindings
        let arityBound := ("arity", number children.length) :: selected
        let tail := obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren 0 children))
        let tailBound := ("tail", tail) :: arityBound
        rw [compile_shape]
        apply case_returns program bindings selected state state state (v "pattern")
          (CettaWireAtom.encode (shapeTerm (.node head children))) compileNode _ _ compileCases (read_cases_encoded _) _ _ _
        · simpa [bindings, compileEnv, applySubst, Subst.lookup] using variable_returns program bindings state "pattern"
        · simp [compileCases, shapeTerm, listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selected, bindings, compileEnv]
        · apply let_two_returns selected state "arity" "tail" _ _ _ (number children.length) tail _
          · simpa using MatchAutomataSourceExecution.length_captured_returns selected state (children.map shapeTerm)
              (v "children") (by simp [selected, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, compileEnv]
          · apply compile_children_call arityBound state children path 0 (v "children") (v "path") (number 0)
            · simp [arityBound, selected, applySubst, Subst.lookup]
            · simp [arityBound, selected, bindings, compileEnv, applySubst, Subst.lookup]
            · exact grounded_returns program arityBound state (.int 0)
            · exact compile_children_body_returns state children path 0
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, compileEnv]
          · simpa [TopDownMatchDerivatives.compile, TopDownMatchDerivatives.shift, obligationsValue,
              listValue, encodeList, obligationTerm, keyTerm, positionTerm, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
              tailBound, arityBound, selected, bindings, compileEnv, tail, number] using
              PureData.template_return program tailBound state _ observation_template

  theorem compile_children_body_returns (state : State) (children : List (Pattern Term))
      (path : SubtermMatching.Position) (next : Nat) :
      PureReturns program (childrenEnv (children.map shapeTerm) path next) state compileChildrenEquation.body state
        (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren next children))) := by
    cases children with
    | nil =>
        rw [compile_children_shape]
        apply case_returns program (childrenEnv [] path next) (childrenEnv [] path next) state state state
          (v "children") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _
          (traversalCases "gslt:automata:compile" "gslt:automata:compile-children") (read_cases_encoded _) _ _ _
        · simpa [childrenEnv, listValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
            variable_returns program (childrenEnv [] path next) state "children"
        · simp [traversalCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program _ state "LNil"
    | cons first rest =>
        let bindings := childrenEnv ((first :: rest).map shapeTerm) path next
        let selected := ("rest", listValue (rest.map shapeTerm)) :: ("child", CettaWireAtom.encode (shapeTerm first)) :: bindings
        let childPath := CettaWireAtom.encode (positionTerm (path ++ [next]))
        let pathBound := ("child-path", childPath) :: selected
        let headValue := obligationsValue (TopDownMatchDerivatives.shift (path ++ [next]) (TopDownMatchDerivatives.compile first))
        let headBound := ("head", headValue) :: pathBound
        let tailValue := obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren (next + 1) rest))
        let tailBound := ("tail", tailValue) :: headBound
        rw [compile_children_shape]
        apply case_returns program bindings selected state state state (v "children")
          (listValue ((first :: rest).map shapeTerm)) (traversalCons "gslt:automata:compile" "gslt:automata:compile-children")
          _ _ (traversalCases "gslt:automata:compile" "gslt:automata:compile-children") (read_cases_encoded _) _ _ _
        · simpa [bindings, childrenEnv, applySubst, Subst.lookup] using variable_returns program bindings state "children"
        · simp [traversalCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selected, bindings, childrenEnv]
        · apply let_three_returns selected state "child-path" "head" "tail" _ _ _ _ childPath headValue tailValue _
          · have appended := append_captured selected state (path.map Term.natural) [.natural next]
              (v "path") (a "LCons" [v "next", .symbol "LNil"])
              (by simp [selected, bindings, childrenEnv, applySubst, Subst.lookup, positionTerm, listValue])
              (by simp [selected, bindings, childrenEnv, applySubst, applySubst.applySubstList, Subst.lookup,
                number, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany])
            rw [show path.map Term.natural ++ [.natural next] = (path ++ [next]).map Term.natural from by simp] at appended
            simpa only [childPath, positionTerm, listValue, encodeList_map, Function.id_comp] using appended
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, childrenEnv]
          · exact compile_call pathBound state first (path ++ [next]) (v "child") (v "child-path")
              (by simp [pathBound, selected, applySubst, Subst.lookup])
              (by simp [pathBound, childPath, applySubst, Subst.lookup])
              (compile_body_returns state first (path ++ [next]))
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, childrenEnv]
          · exact compile_children_call headBound state rest path (next + 1) (v "rest") (v "path")
              (a "+" [v "next", number 1])
              (by simp [headBound, pathBound, selected, applySubst, Subst.lookup])
              (by simp [headBound, pathBound, selected, bindings, childrenEnv, applySubst, Subst.lookup])
              (increment_returns headBound state next
                (by simp [headBound, pathBound, selected, bindings, childrenEnv, applySubst, Subst.lookup]))
              (compile_children_body_returns state rest path (next + 1))
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, childrenEnv]
          · rw [compile_children_cons]
            simpa [obligationsValue, List.map_append] using append_captured tailBound state
              ((TopDownMatchDerivatives.shift (path ++ [next]) (TopDownMatchDerivatives.compile first)).map obligationTerm)
              ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren (next + 1) rest)).map obligationTerm)
              (v "head") (v "tail")
              (by simp [tailBound, headBound, headValue, applySubst, Subst.lookup, obligationsValue])
              (by simp [tailBound, tailValue, applySubst, Subst.lookup, obligationsValue])
end

theorem compile_captured_returns (bindings : Subst) (state : State) (pattern : Pattern Term)
    (path : SubtermMatching.Position) (one two : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (shapeTerm pattern))
    (secondCaptured : applySubst bindings two = CettaWireAtom.encode (positionTerm path)) :
    PureReturns program bindings state (a "gslt:automata:compile" [one, two]) state
      (listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compile pattern)).map obligationTerm)) :=
  compile_call bindings state pattern path one two firstCaptured secondCaptured (compile_body_returns state pattern path)

theorem compile_returns (state : State) (pattern : Pattern Term) (path : SubtermMatching.Position) :
    PureReturns program [] state (a "gslt:automata:compile"
      [CettaWireAtom.encode (shapeTerm pattern), CettaWireAtom.encode (positionTerm path)]) state
      (listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compile pattern)).map obligationTerm)) :=
  compile_captured_returns [] state pattern path _ _ (by simp) (by simp)

theorem compile_children_returns (state : State) (children : List (Pattern Term))
    (path : SubtermMatching.Position) (next : Nat) :
    PureReturns program [] state (a "gslt:automata:compile-children"
      [listValue (children.map shapeTerm), CettaWireAtom.encode (positionTerm path), number next]) state
      (listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compileChildren next children)).map obligationTerm)) :=
  compile_children_call [] state children path next _ _ _ (by simp) (by simp)
    (grounded_returns program [] state (.int next)) (compile_children_body_returns state children path next)

private def observeEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:observe")[0]'(by decide +kernel)
private def observeChildrenEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:observe-children")[0]'(by decide +kernel)
private def observeNode : Atom :=
  a "let*" [.expression [.expression [v "arity", a "gslt:automata:length" [v "children"]],
    .expression [v "tail", a "gslt:automata:observe-children" [v "children", v "path", number 0]]],
    a "LCons" [a "Observe" [v "path", a "MKey" [v "head", v "arity"]], v "tail"]]
private def observeEnv : Subject Term → SubtermMatching.Position → Subst
  | .node head children, path =>
      [("path", CettaWireAtom.encode (positionTerm path)),
        ("children", listValue (children.map subjectTerm)), ("head", CettaWireAtom.encode head)]
private theorem observe_shape : observeEquation.body = observeNode := by decide +kernel
private theorem observe_children_shape : observeChildrenEquation.body =
    a "case" [v "children", .expression ((traversalCases "gslt:automata:observe"
      "gslt:automata:observe-children").map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem observe_clause (subject : Subject Term) (path : SubtermMatching.Position) :
    clauses program "gslt:automata:observe"
      [CettaWireAtom.encode (subjectTerm subject), CettaWireAtom.encode (positionTerm path)] =
      [.evaluate (observeEnv subject path) observeEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:observe").filterMap _ = _
  rw [show equations "gslt:automata:observe" = [observeEquation] from rfl]
  have formals : observeEquation.arguments = [a "MNode" [v "head", v "children"], v "path"] := by decide +kernel
  cases subject with
  | node head children =>
      simp [formals, subjectTerm, listValue, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, observeEnv]
private theorem observe_children_clause (children : List (Subject Term))
    (path : SubtermMatching.Position) (next : Nat) :
    clauses program "gslt:automata:observe-children"
      [listValue (children.map subjectTerm), CettaWireAtom.encode (positionTerm path), number next] =
      [.evaluate (childrenEnv (children.map subjectTerm) path next) observeChildrenEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:observe-children").filterMap _ = _
  rw [show equations "gslt:automata:observe-children" = [observeChildrenEquation] from rfl]
  have formals : observeChildrenEquation.arguments = [v "children", v "path", v "next"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, childrenEnv]
private theorem observe_call (bindings : Subst) (state : State) (subject : Subject Term)
    (path : SubtermMatching.Position) (one two : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (subjectTerm subject))
    (secondCaptured : applySubst bindings two = CettaWireAtom.encode (positionTerm path))
    (bodyReturned : PureReturns program (observeEnv subject path) state observeEquation.body state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observe subject)))) :
    PureReturns program bindings state (a "gslt:automata:observe" [one, two]) state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observe subject))) := by
  apply PureData.raw_authored_call_return program bindings (observeEnv subject path) state state
    "gslt:automata:observe" [one, two] observeEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ bodyReturned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, firstCaptured, secondCaptured]
    exact observe_clause subject path
private theorem observe_children_call (bindings : Subst) (state : State) (children : List (Subject Term))
    (path : SubtermMatching.Position) (next : Nat) (one two third : Atom)
    (firstCaptured : applySubst bindings one = listValue (children.map subjectTerm))
    (secondCaptured : applySubst bindings two = CettaWireAtom.encode (positionTerm path))
    (thirdComputed : PureReturns program bindings state third state (number next))
    (bodyReturned : PureReturns program (childrenEnv (children.map subjectTerm) path next)
      state observeChildrenEquation.body state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren next children)))) :
    PureReturns program bindings state (a "gslt:automata:observe-children" [one, two, third]) state
      (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren next children))) :=
  two_raw_number_call bindings (childrenEnv (children.map subjectTerm) path next) state
    "gslt:automata:observe-children" one two third _ _ next observeChildrenEquation.body _
    (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) firstCaptured secondCaptured thirdComputed
    (observe_children_clause children path next) bodyReturned

private theorem observe_children_cons (path : SubtermMatching.Position) (next : Nat)
    (first : Subject Term) (rest : List (Subject Term)) :
    TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren next (first :: rest)) =
      TopDownMatchDerivatives.shift (path ++ [next]) (TopDownMatchDerivatives.observe first) ++
        TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren (next + 1) rest) := by
  simp [TopDownMatchDerivatives.shift, TopDownMatchDerivatives.observeChildren,
    List.map_map, Function.comp_def, List.append_assoc]

mutual
  theorem observe_body_returns (state : State) (subject : Subject Term) (path : SubtermMatching.Position) :
      PureReturns program (observeEnv subject path) state observeEquation.body state
        (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observe subject))) := by
    cases subject with
    | node head children =>
        let bindings := observeEnv (.node head children) path
        let arityBound := ("arity", number children.length) :: bindings
        let tail := obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren 0 children))
        let tailBound := ("tail", tail) :: arityBound
        rw [observe_shape]
        apply let_two_returns bindings state "arity" "tail" _ _ _ (number children.length) tail _
        · simpa using MatchAutomataSourceExecution.length_captured_returns bindings state (children.map subjectTerm)
            (v "children") (by simp [bindings, observeEnv, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bindings, observeEnv]
        · apply observe_children_call arityBound state children path 0 (v "children") (v "path") (number 0)
          · simp [arityBound, bindings, observeEnv, applySubst, Subst.lookup]
          · simp [arityBound, bindings, observeEnv, applySubst, Subst.lookup]
          · exact grounded_returns program arityBound state (.int 0)
          · exact observe_children_body_returns state children path 0
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bindings, observeEnv]
        · simpa [TopDownMatchDerivatives.observe, TopDownMatchDerivatives.shift, obligationsValue,
            listValue, encodeList, obligationTerm, keyTerm, positionTerm, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            tailBound, arityBound, bindings, observeEnv, tail, number] using
            PureData.template_return program tailBound state _ observation_template

  theorem observe_children_body_returns (state : State) (children : List (Subject Term))
      (path : SubtermMatching.Position) (next : Nat) :
      PureReturns program (childrenEnv (children.map subjectTerm) path next) state observeChildrenEquation.body state
        (obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren next children))) := by
    cases children with
    | nil =>
        rw [observe_children_shape]
        apply case_returns program (childrenEnv [] path next) (childrenEnv [] path next) state state state
          (v "children") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _
          (traversalCases "gslt:automata:observe" "gslt:automata:observe-children") (read_cases_encoded _) _ _ _
        · simpa [childrenEnv, listValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
            variable_returns program (childrenEnv [] path next) state "children"
        · simp [traversalCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program _ state "LNil"
    | cons first rest =>
        let bindings := childrenEnv ((first :: rest).map subjectTerm) path next
        let selected := ("rest", listValue (rest.map subjectTerm)) :: ("child", CettaWireAtom.encode (subjectTerm first)) :: bindings
        let childPath := CettaWireAtom.encode (positionTerm (path ++ [next]))
        let pathBound := ("child-path", childPath) :: selected
        let headValue := obligationsValue (TopDownMatchDerivatives.shift (path ++ [next]) (TopDownMatchDerivatives.observe first))
        let headBound := ("head", headValue) :: pathBound
        let tailValue := obligationsValue (TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren (next + 1) rest))
        let tailBound := ("tail", tailValue) :: headBound
        rw [observe_children_shape]
        apply case_returns program bindings selected state state state (v "children")
          (listValue ((first :: rest).map subjectTerm)) (traversalCons "gslt:automata:observe" "gslt:automata:observe-children")
          _ _ (traversalCases "gslt:automata:observe" "gslt:automata:observe-children") (read_cases_encoded _) _ _ _
        · simpa [bindings, childrenEnv, applySubst, Subst.lookup] using variable_returns program bindings state "children"
        · simp [traversalCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selected, bindings, childrenEnv]
        · apply let_three_returns selected state "child-path" "head" "tail" _ _ _ _ childPath headValue tailValue _
          · have appended := append_captured selected state (path.map Term.natural) [.natural next]
              (v "path") (a "LCons" [v "next", .symbol "LNil"])
              (by simp [selected, bindings, childrenEnv, applySubst, Subst.lookup, positionTerm, listValue])
              (by simp [selected, bindings, childrenEnv, applySubst, applySubst.applySubstList, Subst.lookup,
                number, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany])
            rw [show path.map Term.natural ++ [.natural next] = (path ++ [next]).map Term.natural from by simp] at appended
            simpa only [childPath, positionTerm, listValue, encodeList_map, Function.id_comp] using appended
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, childrenEnv]
          · exact observe_call pathBound state first (path ++ [next]) (v "child") (v "child-path")
              (by simp [pathBound, selected, applySubst, Subst.lookup])
              (by simp [pathBound, childPath, applySubst, Subst.lookup])
              (observe_body_returns state first (path ++ [next]))
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, childrenEnv]
          · exact observe_children_call headBound state rest path (next + 1) (v "rest") (v "path")
              (a "+" [v "next", number 1])
              (by simp [headBound, pathBound, selected, applySubst, Subst.lookup])
              (by simp [headBound, pathBound, selected, bindings, childrenEnv, applySubst, Subst.lookup])
              (increment_returns headBound state next
                (by simp [headBound, pathBound, selected, bindings, childrenEnv, applySubst, Subst.lookup]))
              (observe_children_body_returns state rest path (next + 1))
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, childrenEnv]
          · rw [observe_children_cons]
            simpa [obligationsValue, List.map_append] using append_captured tailBound state
              ((TopDownMatchDerivatives.shift (path ++ [next]) (TopDownMatchDerivatives.observe first)).map obligationTerm)
              ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren (next + 1) rest)).map obligationTerm)
              (v "head") (v "tail")
              (by simp [tailBound, headBound, headValue, applySubst, Subst.lookup, obligationsValue])
              (by simp [tailBound, tailValue, applySubst, Subst.lookup, obligationsValue])
end

theorem observe_captured_returns (bindings : Subst) (state : State) (subject : Subject Term)
    (path : SubtermMatching.Position) (one two : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (subjectTerm subject))
    (secondCaptured : applySubst bindings two = CettaWireAtom.encode (positionTerm path)) :
    PureReturns program bindings state (a "gslt:automata:observe" [one, two]) state
      (listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observe subject)).map obligationTerm)) :=
  observe_call bindings state subject path one two firstCaptured secondCaptured (observe_body_returns state subject path)

theorem observe_returns (state : State) (subject : Subject Term) (path : SubtermMatching.Position) :
    PureReturns program [] state (a "gslt:automata:observe"
      [CettaWireAtom.encode (subjectTerm subject), CettaWireAtom.encode (positionTerm path)]) state
      (listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observe subject)).map obligationTerm)) :=
  observe_captured_returns [] state subject path _ _ (by simp) (by simp)

theorem observe_children_returns (state : State) (children : List (Subject Term))
    (path : SubtermMatching.Position) (next : Nat) :
    PureReturns program [] state (a "gslt:automata:observe-children"
      [listValue (children.map subjectTerm), CettaWireAtom.encode (positionTerm path), number next]) state
      (listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observeChildren next children)).map obligationTerm)) :=
  observe_children_call [] state children path next _ _ _ (by simp) (by simp)
    (grounded_returns program [] state (.int next)) (observe_children_body_returns state children path next)

private def programsEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:programs")[0]'(by decide +kernel)
private def programsCons : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:automata:compile" [v "p", .symbol "LNil"]],
    .expression [v "tail", a "gslt:automata:programs" [v "ps"]]], a "LCons" [v "head", v "tail"]]
private def programsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "p", v "ps"], programsCons)]
private def programsEnv (patterns : List (Pattern Term)) : Subst :=
  [("patterns", listValue (patterns.map shapeTerm))]
private theorem programs_shape : programsEquation.body =
    a "case" [v "patterns", .expression (programsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem programs_clause (patterns : List (Pattern Term)) :
    clauses program "gslt:automata:programs" [listValue (patterns.map shapeTerm)] =
      [.evaluate (programsEnv patterns) programsEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:programs").filterMap _ = _
  rw [show equations "gslt:automata:programs" = [programsEquation] from rfl]
  have formals : programsEquation.arguments = [v "patterns"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, programsEnv]
private theorem programs_call (bindings : Subst) (state : State) (patterns : List (Pattern Term))
    (argument : Atom) (captured : applySubst bindings argument = listValue (patterns.map shapeTerm))
    (bodyReturned : PureReturns program (programsEnv patterns) state programsEquation.body state
      (programsValue (patterns.map TopDownMatchDerivatives.compile))) :
    PureReturns program bindings state (a "gslt:automata:programs" [argument]) state
      (programsValue (patterns.map TopDownMatchDerivatives.compile)) := by
  apply PureData.raw_authored_call_return program bindings (programsEnv patterns) state state
    "gslt:automata:programs" [argument] programsEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ bodyReturned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · simpa only [List.map_cons, List.map_nil, captured] using programs_clause patterns
private theorem pair_template : PureData.Template program (a "LCons" [v "head", v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

theorem programs_body_returns (state : State) (patterns : List (Pattern Term)) :
    PureReturns program (programsEnv patterns) state programsEquation.body state
      (programsValue (patterns.map TopDownMatchDerivatives.compile)) := by
  induction patterns with
  | nil =>
      rw [programs_shape]
      apply case_returns program (programsEnv []) (programsEnv []) state state state
        (v "patterns") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _ programsCases
        (read_cases_encoded _) _ _ _
      · simpa [programsEnv, listValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup]
          using variable_returns program (programsEnv []) state "patterns"
      · simp [programsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons first rest ih =>
      let bindings := programsEnv (first :: rest)
      let selected := ("ps", listValue (rest.map shapeTerm)) :: ("p", CettaWireAtom.encode (shapeTerm first)) :: bindings
      let headValue := obligationsValue (TopDownMatchDerivatives.compile first)
      let headBound := ("head", headValue) :: selected
      let tailValue := programsValue (rest.map TopDownMatchDerivatives.compile)
      let tailBound := ("tail", tailValue) :: headBound
      rw [programs_shape]
      apply case_returns program bindings selected state state state (v "patterns")
        (listValue ((first :: rest).map shapeTerm)) programsCons _ _ programsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, programsEnv, applySubst, Subst.lookup] using variable_returns program bindings state "patterns"
      · simp [programsCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, programsEnv]
      · apply let_two_returns selected state "head" "tail" _ _ _ headValue tailValue _
        · simpa [headValue, obligationsValue, TopDownMatchDerivatives.shift, positionTerm,
            CettaWireAtom.encode, encodeList] using compile_captured_returns selected state first []
            (v "p") (.symbol "LNil") (by simp [selected, applySubst, Subst.lookup]) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, programsEnv]
        · exact programs_call headBound state rest (v "ps")
            (by simp [headBound, selected, applySubst, Subst.lookup]) ih
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, programsEnv]
        · simpa [programsValue, obligationsValue, listValue, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            tailBound, headBound, selected, bindings, programsEnv, headValue, tailValue] using
            PureData.template_return program tailBound state _ pair_template

theorem programs_captured_returns (bindings : Subst) (state : State) (patterns : List (Pattern Term))
    (argument : Atom) (captured : applySubst bindings argument = listValue (patterns.map shapeTerm)) :
    PureReturns program bindings state (a "gslt:automata:programs" [argument]) state
      (listValue ((patterns.map TopDownMatchDerivatives.compile).map (encodeList obligationTerm))) :=
  programs_call bindings state patterns argument captured (programs_body_returns state patterns)

theorem programs_returns (state : State) (patterns : List (Pattern Term)) :
    PureReturns program [] state (a "gslt:automata:programs" [listValue (patterns.map shapeTerm)]) state
      (listValue ((patterns.map TopDownMatchDerivatives.compile).map (encodeList obligationTerm))) :=
  programs_captured_returns [] state patterns _ (by simp)

private def seedEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:seed")[0]'(by decide +kernel)
private def seedCons : Atom :=
  a "let*" [.expression [.expression [v "pending", a "gslt:automata:shift" [v "root", v "program"]],
    .expression [v "tail", a "gslt:automata:seed" [v "root", v "rest", a "+" [v "next", number 1]]]],
    a "LCons" [a "MGoal" [a "At" [v "root", v "next"], v "pending"], v "tail"]]
private def seedCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "program", v "rest"], seedCons)]
private def seedEnv (root : SubtermMatching.Position)
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (next : Nat) : Subst :=
  [("next", number next), ("programs", programsValue programs), ("root", CettaWireAtom.encode (positionTerm root))]
private theorem seed_shape : seedEquation.body =
    a "case" [v "programs", .expression (seedCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem seed_clause (root : SubtermMatching.Position)
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (next : Nat) :
    clauses program "gslt:automata:seed"
      [CettaWireAtom.encode (positionTerm root), programsValue programs, number next] =
      [.evaluate (seedEnv root programs next) seedEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:seed").filterMap _ = _
  rw [show equations "gslt:automata:seed" = [seedEquation] from rfl]
  have formals : seedEquation.arguments = [v "root", v "programs", v "next"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, seedEnv]
private theorem seed_call (bindings : Subst) (state : State) (root : SubtermMatching.Position)
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (next : Nat) (one two third : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (positionTerm root))
    (secondCaptured : applySubst bindings two = programsValue programs)
    (thirdComputed : PureReturns program bindings state third state (number next))
    (bodyReturned : PureReturns program (seedEnv root programs next) state seedEquation.body state
      (listValue ((TopDownMatchDerivatives.seed root next programs).map goalTerm))) :
    PureReturns program bindings state (a "gslt:automata:seed" [one, two, third]) state
      (listValue ((TopDownMatchDerivatives.seed root next programs).map goalTerm)) :=
  two_raw_number_call bindings (seedEnv root programs next) state "gslt:automata:seed"
    one two third _ _ next seedEquation.body _ (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) firstCaptured secondCaptured thirdComputed
    (seed_clause root programs next) bodyReturned
private theorem seed_template : PureData.Template program
    (a "LCons" [a "MGoal" [a "At" [v "root", v "next"], v "pending"], v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "MGoal" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply PureData.Template.constructor "At" _ (by decide +kernel) (by decide)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .captured _
    · exact .captured _
  · exact .captured _

theorem seed_body_returns (state : State) (root : SubtermMatching.Position)
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (next : Nat) :
    PureReturns program (seedEnv root programs next) state seedEquation.body state
      (listValue ((TopDownMatchDerivatives.seed root next programs).map goalTerm)) := by
  induction programs generalizing next with
  | nil =>
      rw [seed_shape]
      apply case_returns program (seedEnv root [] next) (seedEnv root [] next) state state state
        (v "programs") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _ seedCases
        (read_cases_encoded _) _ _ _
      · simpa [seedEnv, programsValue, listValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup]
          using variable_returns program (seedEnv root [] next) state "programs"
      · simp [seedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons first rest ih =>
      let bindings := seedEnv root (first :: rest) next
      let selected := ("rest", programsValue rest) :: ("program", obligationsValue first) :: bindings
      let pending := obligationsValue (TopDownMatchDerivatives.shift root first)
      let pendingBound := ("pending", pending) :: selected
      let tail := listValue ((TopDownMatchDerivatives.seed root (next + 1) rest).map goalTerm)
      let tailBound := ("tail", tail) :: pendingBound
      rw [seed_shape]
      apply case_returns program bindings selected state state state (v "programs")
        (programsValue (first :: rest)) seedCons _ _ seedCases (read_cases_encoded _) _ _ _
      · simpa [bindings, seedEnv, applySubst, Subst.lookup] using variable_returns program bindings state "programs"
      · simp [seedCases, programsValue, obligationsValue, listValue, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, seedEnv]
      · apply let_two_returns selected state "pending" "tail" _ _ _ pending tail _
        · exact shift_captured_returns selected state root first (v "root") (v "program")
            (by simp [selected, bindings, seedEnv, applySubst, Subst.lookup])
            (by simp [selected, obligationsValue, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, seedEnv]
        · exact seed_call pendingBound state root rest (next + 1) (v "root") (v "rest")
            (a "+" [v "next", number 1])
            (by simp [pendingBound, selected, bindings, seedEnv, applySubst, Subst.lookup])
            (by simp [pendingBound, selected, applySubst, Subst.lookup])
            (increment_returns pendingBound state next
              (by simp [pendingBound, selected, bindings, seedEnv, applySubst, Subst.lookup])) (ih (next + 1))
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, seedEnv]
        · simpa [TopDownMatchDerivatives.seed, goalTerm, locationTerm, obligationsValue, listValue,
            encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
            applySubst.applySubstList, Subst.lookup, tailBound, pendingBound, selected,
            bindings, seedEnv, pending, tail, number] using
            PureData.template_return program tailBound state _ seed_template

theorem seed_captured_returns (bindings : Subst) (state : State) (root : SubtermMatching.Position)
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (next : Nat) (one two third : Atom)
    (firstCaptured : applySubst bindings one = CettaWireAtom.encode (positionTerm root))
    (secondCaptured : applySubst bindings two = listValue (programs.map (encodeList obligationTerm)))
    (thirdComputed : PureReturns program bindings state third state (number next)) :
    PureReturns program bindings state (a "gslt:automata:seed" [one, two, third]) state
      (listValue ((TopDownMatchDerivatives.seed root next programs).map goalTerm)) :=
  seed_call bindings state root programs next one two third firstCaptured secondCaptured thirdComputed
    (seed_body_returns state root programs next)

theorem seed_returns (state : State) (root : SubtermMatching.Position)
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (next : Nat) :
    PureReturns program [] state (a "gslt:automata:seed"
      [CettaWireAtom.encode (positionTerm root), listValue (programs.map (encodeList obligationTerm)), number next]) state
      (listValue ((TopDownMatchDerivatives.seed root next programs).map goalTerm)) :=
  seed_captured_returns [] state root programs next _ _ _ (by simp) (by simp)
    (grounded_returns program [] state (.int next))

private def seedAllEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:seed-all")[0]'(by decide +kernel)
private def seedAllCons : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:automata:seed" [v "root", v "programs", number 0]],
    .expression [v "tail", a "gslt:automata:seed-all" [v "rest", v "programs"]]],
    a "gslt:automata:append" [v "head", v "tail"]]
private def seedAllCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "Observe" [v "root", v "key"], v "rest"], seedAllCons)]
private def seedAllEnv (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) : Subst :=
  [("programs", programsValue programs), ("observations", obligationsValue observations)]
private theorem seed_all_shape : seedAllEquation.body =
    a "case" [v "observations", .expression (seedAllCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem seed_all_clause (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) :
    clauses program "gslt:automata:seed-all" [obligationsValue observations, programsValue programs] =
      [.evaluate (seedAllEnv observations programs) seedAllEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:seed-all").filterMap _ = _
  rw [show equations "gslt:automata:seed-all" = [seedAllEquation] from rfl]
  have formals : seedAllEquation.arguments = [v "observations", v "programs"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, seedAllEnv]
private theorem seed_all_call (bindings : Subst) (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (one two : Atom)
    (firstCaptured : applySubst bindings one = obligationsValue observations)
    (secondCaptured : applySubst bindings two = programsValue programs)
    (bodyReturned : PureReturns program (seedAllEnv observations programs) state seedAllEquation.body state
      (listValue ((observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm))) :
    PureReturns program bindings state (a "gslt:automata:seed-all" [one, two]) state
      (listValue ((observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)) := by
  apply PureData.raw_authored_call_return program bindings (seedAllEnv observations programs) state state
    "gslt:automata:seed-all" [one, two] seedAllEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ bodyReturned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simp only [List.map_cons, List.map_nil, firstCaptured, secondCaptured]
    exact seed_all_clause observations programs

theorem seed_all_body_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) :
    PureReturns program (seedAllEnv observations programs) state seedAllEquation.body state
      (listValue ((observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)) := by
  induction observations with
  | nil =>
      rw [seed_all_shape]
      apply case_returns program (seedAllEnv [] programs) (seedAllEnv [] programs) state state state
        (v "observations") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _ seedAllCases
        (read_cases_encoded _) _ _ _
      · simpa [seedAllEnv, obligationsValue, listValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program (seedAllEnv [] programs) state "observations"
      · simp [seedAllCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons first rest ih =>
      let bindings := seedAllEnv (first :: rest) programs
      let selected := ("rest", obligationsValue rest) :: ("key", CettaWireAtom.encode (keyTerm first.key)) ::
        ("root", CettaWireAtom.encode (positionTerm first.position)) :: bindings
      let headValue := listValue ((TopDownMatchDerivatives.seed first.position 0 programs).map goalTerm)
      let headBound := ("head", headValue) :: selected
      let tailValue := listValue ((rest.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)
      let tailBound := ("tail", tailValue) :: headBound
      rw [seed_all_shape]
      apply case_returns program bindings selected state state state (v "observations")
        (obligationsValue (first :: rest)) seedAllCons _ _ seedAllCases (read_cases_encoded _) _ _ _
      · simpa [bindings, seedAllEnv, applySubst, Subst.lookup] using variable_returns program bindings state "observations"
      · simp [seedAllCases, obligationsValue, listValue, encodeList, obligationTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, bindings, seedAllEnv]
      · apply let_two_returns selected state "head" "tail" _ _ _ headValue tailValue _
        · exact seed_captured_returns selected state first.position programs 0 (v "root") (v "programs") (number 0)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, bindings, seedAllEnv, programsValue, applySubst, Subst.lookup])
            (grounded_returns program selected state (.int 0))
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, seedAllEnv]
        · exact seed_all_call headBound state rest programs (v "rest") (v "programs")
            (by simp [headBound, selected, applySubst, Subst.lookup])
            (by simp [headBound, selected, bindings, seedAllEnv, applySubst, Subst.lookup]) ih
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, selected, bindings, seedAllEnv]
        · simpa only [List.flatMap_cons, List.map_append] using append_captured tailBound state
            ((TopDownMatchDerivatives.seed first.position 0 programs).map goalTerm)
            ((rest.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)
            (v "head") (v "tail")
            (by simp [tailBound, headBound, headValue, applySubst, Subst.lookup])
            (by simp [tailBound, tailValue, applySubst, Subst.lookup])

theorem seed_all_captured_returns (bindings : Subst) (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) (one two : Atom)
    (firstCaptured : applySubst bindings one = listValue (observations.map obligationTerm))
    (secondCaptured : applySubst bindings two = listValue (programs.map (encodeList obligationTerm))) :
    PureReturns program bindings state (a "gslt:automata:seed-all" [one, two]) state
      (listValue ((observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)) :=
  seed_all_call bindings state observations programs one two firstCaptured secondCaptured
    (seed_all_body_returns state observations programs)

theorem seed_all_returns (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term))) :
    PureReturns program [] state (a "gslt:automata:seed-all"
      [listValue (observations.map obligationTerm), listValue (programs.map (encodeList obligationTerm))]) state
      (listValue ((observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)) :=
  seed_all_captured_returns [] state observations programs _ _ (by simp) (by simp)

/-- Completed source compilation has exactly the independent obligation
vector and preserves the complete state and I/O observations. -/
theorem compile_derivation_iff (state : State) (pattern : Pattern Term)
    (path : SubtermMatching.Position) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (a "gslt:automata:compile"
        [CettaWireAtom.encode (shapeTerm pattern), CettaWireAtom.encode (positionTerm path)]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.compile pattern)).map obligationTerm)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (compile_returns state pattern path)
    after answers input output

theorem programs_derivation_iff (state : State) (patterns : List (Pattern Term))
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (a "gslt:automata:programs" [listValue (patterns.map shapeTerm)]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [listValue ((patterns.map TopDownMatchDerivatives.compile).map (encodeList obligationTerm))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (programs_returns state patterns)
    after answers input output

/-- Preorder observations are produced by the retained source traversal;
no subject constructor is delegated to a host-computed observation stream. -/
theorem observe_derivation_iff (state : State) (subject : Subject Term)
    (path : SubtermMatching.Position) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (a "gslt:automata:observe"
        [CettaWireAtom.encode (subjectTerm subject), CettaWireAtom.encode (positionTerm path)]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [listValue ((TopDownMatchDerivatives.shift path (TopDownMatchDerivatives.observe subject)).map obligationTerm)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (observe_returns state subject path)
    after answers input output

/-- Candidate seeding preserves observation and authored-program order,
including identical program occurrences and identical observation roots. -/
theorem seed_all_derivation_iff (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (programs : List (List (TopDownMatchDerivatives.Obligation Term)))
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (a "gslt:automata:seed-all"
        [listValue (observations.map obligationTerm), listValue (programs.map (encodeList obligationTerm))]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [listValue ((observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)).map goalTerm)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (seed_all_returns state observations programs)
    after answers input output

#print axioms shapeTerm_injective
#print axioms compile_returns
#print axioms compile_children_returns
#print axioms programs_returns
#print axioms observe_returns
#print axioms observe_children_returns
#print axioms shift_returns
#print axioms seed_returns
#print axioms seed_all_returns
#print axioms compile_derivation_iff
#print axioms observe_derivation_iff
#print axioms seed_all_derivation_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataCompilationExecution
