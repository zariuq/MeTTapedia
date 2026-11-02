import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls
import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
import Mettapedia.GSLT.LanguageDef.ScopedBindingElaboration

/-!
# Canonical right-hand-side instantiation through retained rule equations

The retained instantiator realizes canonical `Match.applyBindings` on every
Pattern constructor. It traverses ordered children, preserves binder metadata,
eliminates explicit substitution using the canonical bound-variable operations,
and splices a captured collection rest only when its kind agrees and it is closed.
Inserted binding payloads and residual collection elements remain opaque data.

The first-order `PatternPlan.instantiate` interfaces are corollaries of that
single operation. Scoped rule instantiation has separate assignment and
occurrence-argument obligations; the binder-free scoped interface retained here
uses its existing canonical agreement theorem.

The scoped capture operations below realize the existing contextual assignments,
scope checks, substitution, validated recovery, and repeated-value assignment.
The metadata lenses below validate the retained declaration site, occurrence
path and depth, dependency declarations, and occurrence arguments before capture.
They preserve ambient-context metadata and uniqueness-sensitive refusals.
Contextual rewrite authorization remains a separate obligation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval RuleExecutionProgram
open MatchAutomataBindingExecution (bindingsTerm patternOptionTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)

attribute [local simp] a v encoded number patternValue patternsValue

private inductive Traversal where | lift | eliminate
private def Traversal.head : Traversal → String
  | .lift => "gslt:rule:lift-bvars"
  | .eliminate => "gslt:rule:instantiate-bvar-at"
private def Traversal.listHead : Traversal → String
  | .lift => "gslt:rule:lift-bvars-list"
  | .eliminate => "gslt:rule:instantiate-bvar-list-at"
private def Traversal.first : Traversal → String
  | .lift => "cutoff"
  | .eliminate => "depth"
private def Traversal.second : Traversal → String
  | .lift => "shift"
  | .eliminate => "replacement"
private def Traversal.nested : Traversal → String
  | .lift => "replacement"
  | .eliminate => "nested-replacement"
private def Traversal.Parameter : Traversal → Type
  | .lift => Nat
  | .eliminate => Pattern
private def Traversal.parameterTerm : (kind : Traversal) → kind.Parameter → Term
  | .lift, shift => .natural shift
  | .eliminate, replacement => InferenceCettaWire.encodePattern replacement
private def Traversal.result : (kind : Traversal) → Nat → kind.Parameter → Pattern → Pattern
  | .lift, cutoff, shift => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift
  | .eliminate, depth, replacement => Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement

private inductive Form where | pattern | patterns
private def Form.formal : Form → String
  | .pattern => "pattern"
  | .patterns => "patterns"
private def functionHead (kind : Traversal) : Form → String
  | .pattern => kind.head
  | .patterns => kind.listHead
private def equation (kind : Traversal) (form : Form) : SpaceSemantics.Equation :=
  (equations (functionHead kind form))[0]'(by cases kind <;> cases form <;> decide +kernel)
private def environment (kind : Traversal) (form : Form) (first : Nat) (second value : Atom) : Subst :=
  [(form.formal, value), (kind.second, second), (kind.first, number first)]

private theorem helper_clause (kind : Traversal) (form : Form) (first : Nat) (second value : Atom) :
    clauses program (functionHead kind form) [number first, second, value] =
      [.evaluate (environment kind form first second value) (equation kind form).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (functionHead kind form)).filterMap _ = _
  rw [show equations (functionHead kind form) = [equation kind form] from by
    cases kind <;> cases form <;> rfl]
  have formals : (equation kind form).arguments = [v kind.first, v kind.second, v form.formal] := by
    cases kind <;> cases form <;> decide +kernel
  cases kind <;> cases form <;> simp [formals, environment, Traversal.first,
    Traversal.second, Form.formal, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem helper_call (kind : Traversal) (form : Form) (caller : Subst) (state : State)
    (first : Nat) (second value one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [number first, second, value])
    (returned : PureReturns program (environment kind form first second value) state
      (equation kind form).body state answer) :
    PureReturns program caller state (a (functionHead kind form) [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program caller (environment kind form first second value) state state
    (functionHead kind form) [one, two, three] (equation kind form).body answer
    (by cases kind <;> cases form <;> decide)
    (by cases kind <;> cases form <;> decide)
    (by cases kind <;> cases form <;> decide)
    (by cases kind <;> cases form <;> decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> cases kind <;> cases form <;> decide +kernel
  · rw [captured]
    exact helper_clause kind form first second value

private theorem helper_capture (kind : Traversal) (form : Form) (caller : Subst) (state : State)
    (first : Nat) (second value one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [number first, second, value])
    (returned : PureReturns program [] state
      (a (functionHead kind form) [number first, second, value]) state answer) :
    PureReturns program caller state (a (functionHead kind form) [one, two, three]) state answer := by
  apply PureData.raw_capture_returns program [] caller state state (functionHead kind form)
    [number first, second, value] [one, two, three] answer
    (by cases kind <;> cases form <;> decide +kernel) _
    (by cases kind <;> cases form <;> decide) _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> cases kind <;> cases form <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using captured.symm

private def liftIndexBody : Atom :=
  a "if" [a ">=" [v "index", v "cutoff"],
    a "let" [v "next", a "+" [v "index", v "shift"], a "Var" [v "next"]], v "pattern"]
private def eliminateIndexBody : Atom :=
  a "if" [a "<" [v "index", v "depth"], v "pattern",
    a "if" [a "==" [v "index", v "depth"],
      a "gslt:rule:lift-bvars" [number 0, v "depth", v "replacement"],
      a "let" [v "next", a "-" [v "index", number 1], a "Var" [v "next"]]]]

private def applicationBody (kind : Traversal) : Atom :=
  a "let" [v "arguments", a kind.listHead [v kind.first, v kind.second, v "children"],
    a "PApp" [v "head", v "arguments"]]
private def binderBody (kind : Traversal) (many : Bool) : Atom :=
  a "let*" [.expression [
    .expression [v "next", a "+" [v kind.first, if many then v "arity" else number 1]],
    .expression [v "value", a kind.head [v "next", v kind.second, v "body"]]],
    if many then a "PMultiLam" [v "arity", v "binders", v "value"]
      else a "PLam" [v "binder", v "value"]]
private def substitutionBody (kind : Traversal) : Atom :=
  a "let*" [.expression [
    .expression [v "next", a "+" [v kind.first, number 1]],
    .expression [v "value", a kind.head [v "next", v kind.second, v "body"]],
    .expression [v "replacement-value", a kind.head [v kind.first, v kind.second, v kind.nested]]],
    a "PSubst" [v "value", v "replacement-value"]]
private def collectionBody (kind : Traversal) : Atom :=
  a "let" [v "values", a kind.listHead [v kind.first, v kind.second, v "elements"],
    a "PCollection" [v "kind", v "values", v "rest"]]
private def patternCases (kind : Traversal) : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], match kind with | .lift => liftIndexBody | .eliminate => eliminateIndexBody),
   (a "FVar" [v "name"], v "pattern"),
   (a "PApp" [v "head", v "children"], applicationBody kind),
   (a "PLam" [v "binder", v "body"], binderBody kind false),
   (a "PMultiLam" [v "arity", v "binders", v "body"], binderBody kind true),
   (a "PSubst" [v "body", v kind.nested], substitutionBody kind),
   (a "PCollection" [v "kind", v "elements", v "rest"], collectionBody kind)]
private def listBody (kind : Traversal) : Atom :=
  a "let*" [.expression [
    .expression [v "head", a kind.head [v kind.first, v kind.second, v "pattern"]],
    .expression [v "tail", a kind.listHead [v kind.first, v kind.second, v "rest"]]],
    a "LCons" [v "head", v "tail"]]
private def listCases (kind : Traversal) : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "pattern", v "rest"], listBody kind)]
private def cases (kind : Traversal) : Form → SpaceSemantics.Cases
  | .pattern => patternCases kind
  | .patterns => listCases kind

private theorem helper_shape (kind : Traversal) (form : Form) : (equation kind form).body =
    a "case" [v form.formal, .expression ((cases kind form).map fun row => .expression [row.1, row.2])] := by
  cases kind <;> cases form <;> decide +kernel

private theorem helper_case_returns (kind : Traversal) (form : Form) (state : State)
    (first : Nat) (second value : Atom) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (environment kind form first second value) value (cases kind form) =
      some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a (functionHead kind form) [number first, second, value]) state answer := by
  apply helper_call kind form [] state first second value (number first) second value answer
    (by simp only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [helper_shape]
  apply case_returns program (environment kind form first second value) selected state state state
    (v form.formal) value body answer _ (cases kind form) (read_cases_encoded _) _ matched returned
  simpa [environment, applySubst, Subst.lookup] using
    variable_returns program (environment kind form first second value) state form.formal

private inductive Constructor where | bound | app | lam | multiLam | subst | collection | cons
private def Constructor.head : Constructor → String
  | .bound => "Var" | .app => "PApp" | .lam => "PLam" | .multiLam => "PMultiLam"
  | .subst => "PSubst" | .collection => "PCollection" | .cons => "LCons"
private theorem constructor_variables (constructor : Constructor) (names : List String) :
    PureData.Template program (a constructor.head (names.map v)) := by
  apply PureData.Template.constructor constructor.head _
    (by cases constructor <;> decide +kernel) (by cases constructor <;> decide)
  intro argument member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact .captured name

private theorem add_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (capturedFirst : applySubst caller (v first) = number left)
    (capturedSecond : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "+" [v first, v second]) state (number (left + right)) := by
  apply native_variable_call_returns program caller state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, capturedFirst, capturedSecond]
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1


private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have boolean_same : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> decide +kernel
  simpa only [boolean_same] using returned

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom)
    (fresh : Subst.lookup caller name = none)
    (returned : PureReturns program caller state expression state value)
    (continuation : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer returned _ continuation
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem ge_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (capturedFirst : applySubst caller (v first) = number left)
    (capturedSecond : applySubst caller (v second) = number right) :
    PureReturns program caller state (a ">=" [v first, v second]) state
      (Effects.boolean (decide (right ≤ left))) := by
  apply native_variable_call_returns program caller state state ">=" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, capturedFirst, capturedSecond]
  simp [number, encoded, CettaWireAtom.encode]

private theorem lift_index_returns (state : State) (cutoff shift index : Nat) :
    PureReturns program [] state
      (a "gslt:rule:lift-bvars" [number cutoff, number shift, patternValue (.bvar index)]) state
      (patternValue (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift (.bvar index))) := by
  let caller := environment .lift .pattern cutoff (number shift) (patternValue (.bvar index))
  let selected := ("index", number index) :: caller
  apply helper_case_returns .lift .pattern state cutoff (number shift) (patternValue (.bvar index))
    selected liftIndexBody
  · simp [cases, patternCases, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
  · have compared := ge_variables_returns selected state index cutoff "index" "cutoff"
      (by simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
        applySubst, Subst.lookup])
      (by simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
        applySubst, Subst.lookup])
    apply bool_if_returns selected state _ (decide (cutoff ≤ index)) _ _ _ compared
    by_cases lifted : cutoff ≤ index
    · simp only [lifted, decide_true, ite_true,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
      apply named_let_returns selected state "next" _ (number (index + shift)) _ _
      · simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second, Subst.lookup]
      · apply add_variables_returns selected state index shift "index" "shift"
        · simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
            applySubst, Subst.lookup]
        · simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
            applySubst, Subst.lookup]
      · simpa [Constructor.head, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program (("next", number (index + shift)) :: selected) state
            (a "Var" [v "next"]) (constructor_variables .bound ["next"])
    · simp only [lifted, decide_false, Bool.false_eq_true, ite_false,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
      simpa [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
          applySubst, Subst.lookup] using variable_returns program selected state "pattern"

private theorem result_apply (kind : Traversal) (first : Nat) (parameter : kind.Parameter)
    (head : String) (children : List Pattern) :
    kind.result first parameter (.apply head children) =
      .apply head (children.map (kind.result first parameter)) := by
  cases kind with
  | lift =>
      exact congrArg (Pattern.apply head)
        (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map first parameter children)
  | eliminate => exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_3 first parameter head children
private theorem result_lambda (kind : Traversal) (first : Nat) (parameter : kind.Parameter)
    (binder : Option String) (body : Pattern) :
    kind.result first parameter (.lambda binder body) =
      .lambda binder (kind.result (first + 1) parameter body) := by
  cases kind with
  | lift => rfl
  | eliminate => exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_4 first parameter binder body
private theorem result_multiLambda (kind : Traversal) (first : Nat) (parameter : kind.Parameter)
    (arity : Nat) (binders : List String) (body : Pattern) :
    kind.result first parameter (.multiLambda arity binders body) =
      .multiLambda arity binders (kind.result (first + arity) parameter body) := by
  cases kind with
  | lift => rfl
  | eliminate => exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_5 first parameter arity binders body
private theorem result_subst (kind : Traversal) (first : Nat) (parameter : kind.Parameter)
    (body replacement : Pattern) :
    kind.result first parameter (.subst body replacement) =
      .subst (kind.result (first + 1) parameter body) (kind.result first parameter replacement) := by
  cases kind with
  | lift => rfl
  | eliminate => exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_6 first parameter body replacement
private theorem result_collection (kind : Traversal) (first : Nat) (parameter : kind.Parameter)
    (collectionType : CollType) (elements : List Pattern) (rest : Option String) :
    kind.result first parameter (.collection collectionType elements rest) =
      .collection collectionType (elements.map (kind.result first parameter)) rest := by
  cases kind with
  | lift =>
      exact congrArg (fun children => Pattern.collection collectionType children rest)
        (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map first parameter elements)
  | eliminate => exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_7 first parameter collectionType elements rest
private theorem result_fvar (kind : Traversal) (first : Nat) (parameter : kind.Parameter)
    (name : String) : kind.result first parameter (.fvar name) = .fvar name := by
  cases kind with
  | lift => rfl
  | eliminate => exact Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_2 first parameter name

private theorem list_returns_from_elements (kind : Traversal) (parameter : kind.Parameter)
    (state : State) (first : Nat) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a kind.head [number first, encoded (kind.parameterTerm parameter), patternValue pattern]) state
      (patternValue (kind.result first parameter pattern))) :
    PureReturns program [] state
      (a kind.listHead [number first, encoded (kind.parameterTerm parameter), patternsValue patterns]) state
      (patternsValue (patterns.map (kind.result first parameter))) := by
  induction patterns with
  | nil =>
      simp only [patternsValue, encoded, InferenceCettaWire.encodePatterns, List.map_nil, CettaWireAtom.encode]
      apply helper_case_returns kind .patterns state first (encoded (kind.parameterTerm parameter)) (.symbol "LNil")
        (environment kind .patterns first (encoded (kind.parameterTerm parameter)) (.symbol "LNil")) (.symbol "LNil")
      · simp [cases, listCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons pattern patterns ih =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .patterns first second (patternsValue (pattern :: patterns))
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let headValue := patternValue (kind.result first parameter pattern)
      let headBound := ("head", headValue) :: selected
      let tailValue := patternsValue (patterns.map (kind.result first parameter))
      let final := ("tail", tailValue) :: headBound
      have headReturned := helper_capture kind .pattern selected state first second (patternValue pattern)
        (v kind.first) (v kind.second) (v "pattern") headValue
        (by cases kind <;> simp [selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, applySubst, Subst.lookup]) (elements pattern (by simp))
      have tailReturned := helper_capture kind .patterns headBound state first second (patternsValue patterns)
        (v kind.first) (v kind.second) (v "rest") tailValue
        (by cases kind <;> simp [headBound, selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      apply helper_case_returns kind .patterns state first second (patternsValue (pattern :: patterns))
        selected (listBody kind)
      · cases kind <;> simp [cases, listCases, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
      · apply PureData.let_bindings_return
          (pairs := [(v "head", a kind.head [v kind.first, v kind.second, v "pattern"]),
            (v "tail", a kind.listHead [v kind.first, v kind.second, v "rest"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
              matchAtom, Subst.lookup, selected, caller, headBound, environment,
              Form.formal, Traversal.first, Traversal.second]
          · apply PureData.BindingsReturn.cons (bound := final) tailReturned
            · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                matchAtom, Subst.lookup, final, headBound, selected, caller, environment,
                Form.formal, Traversal.first, Traversal.second]
            · exact .nil _ _
        · simpa [Constructor.head, List.map_cons, InferenceCettaWire.encodePatterns,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            final, headBound, headValue, tailValue] using
            PureData.template_return program final state (a "LCons" [v "head", v "tail"])
              (constructor_variables .cons ["head", "tail"])


/-- The two canonical bound-variable operations share these actual source
constructor continuations. Their numeric cases remain separately proved. -/
private theorem traversal_constructors_returns (kind : Traversal) (parameter : kind.Parameter)
    (state : State)
    (indices : ∀ first index, PureReturns program [] state
      (a kind.head [number first, encoded (kind.parameterTerm parameter), patternValue (.bvar index)]) state
      (patternValue (kind.result first parameter (.bvar index))))
    (pattern : Pattern) (first : Nat) :
    PureReturns program [] state
      (a kind.head [number first, encoded (kind.parameterTerm parameter), patternValue pattern]) state
      (patternValue (kind.result first parameter pattern)) := by
  induction pattern using Pattern.inductionOn generalizing first with
  | hbvar index => exact indices first index
  | hfvar name =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .pattern first second (patternValue (.fvar name))
      let selected := ("name", encoded (.string name)) :: caller
      rw [result_fvar]
      apply helper_case_returns kind .pattern state first second (patternValue (.fvar name)) selected (v "pattern")
      · cases kind <;> simp [cases, patternCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
      · simpa [selected, caller, environment, Form.formal, applySubst, Subst.lookup] using
          variable_returns program selected state "pattern"
  | happly head children ih =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .pattern first second (patternValue (.apply head children))
      let selected := ("children", patternsValue children) :: ("head", encoded (.string head)) :: caller
      let results := children.map (kind.result first parameter)
      let final := ("arguments", patternsValue results) :: selected
      rw [result_apply]
      apply helper_case_returns kind .pattern state first second (patternValue (.apply head children))
        selected (applicationBody kind)
      · cases kind <;> simp [cases, patternCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
      · apply named_let_returns selected state "arguments" _ (patternsValue results) _ _
        · cases kind <;> simp [selected, caller, environment, Form.formal,
            Traversal.first, Traversal.second, Subst.lookup]
        · apply helper_capture kind .patterns selected state first second (patternsValue children)
            (v kind.first) (v kind.second) (v "children") _ _
            (list_returns_from_elements kind parameter state first children (fun child member => ih child member first))
          cases kind <;> simp [selected, caller, environment, Form.formal,
            Traversal.first, Traversal.second, applySubst, Subst.lookup]
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, selected, results] using
            PureData.template_return program final state (a "PApp" [v "head", v "arguments"])
              (constructor_variables .app ["head", "arguments"])
  | hlambda binder body ih =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .pattern first second (patternValue (.lambda binder body))
      let selected := ("body", patternValue body) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let nextBound := ("next", number (first + 1)) :: selected
      let value := patternValue (kind.result (first + 1) parameter body)
      let final := ("value", value) :: nextBound
      have nextReturned := add_one_returns selected state first kind.first
        (by cases kind <;> simp [selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, applySubst, Subst.lookup])
      have bodyReturned := helper_capture kind .pattern nextBound state (first + 1) second (patternValue body)
        (v "next") (v kind.second) (v "body") value
        (by cases kind <;> simp [nextBound, selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, applySubst, Subst.lookup]) (ih (first + 1))
      rw [result_lambda]
      apply helper_case_returns kind .pattern state first second (patternValue (.lambda binder body))
        selected (binderBody kind false)
      · cases kind <;> simp [cases, patternCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
      · apply PureData.let_bindings_return
          (pairs := [(v "next", a "+" [v kind.first, number 1]),
            (v "value", a kind.head [v "next", v kind.second, v "body"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
          · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
              matchAtom, Subst.lookup, nextBound, selected, caller, environment,
              Form.formal, Traversal.first, Traversal.second]
          · apply PureData.BindingsReturn.cons (bound := final) bodyReturned
            · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                matchAtom, Subst.lookup, final, nextBound, selected, caller, environment,
                Form.formal, Traversal.first, Traversal.second]
            · exact .nil _ _
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, nextBound, selected, value] using
            PureData.template_return program final state (a "PLam" [v "binder", v "value"])
              (constructor_variables .lam ["binder", "value"])
  | hmultiLambda arity binders body ih =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .pattern first second (patternValue (.multiLambda arity binders body))
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) ::
        ("arity", number arity) :: caller
      let nextBound := ("next", number (first + arity)) :: selected
      let value := patternValue (kind.result (first + arity) parameter body)
      let final := ("value", value) :: nextBound
      have nextReturned := add_variables_returns selected state first arity kind.first "arity"
        (by cases kind <;> simp [selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, applySubst, Subst.lookup])
        (by simp [selected, applySubst, Subst.lookup])
      have bodyReturned := helper_capture kind .pattern nextBound state (first + arity) second (patternValue body)
        (v "next") (v kind.second) (v "body") value
        (by cases kind <;> simp [nextBound, selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, applySubst, Subst.lookup]) (ih (first + arity))
      rw [result_multiLambda]
      apply helper_case_returns kind .pattern state first second (patternValue (.multiLambda arity binders body))
        selected (binderBody kind true)
      · cases kind <;> simp [cases, patternCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
      · apply PureData.let_bindings_return
          (pairs := [(v "next", a "+" [v kind.first, v "arity"]),
            (v "value", a kind.head [v "next", v kind.second, v "body"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
          · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
              matchAtom, Subst.lookup, nextBound, selected, caller, environment,
              Form.formal, Traversal.first, Traversal.second]
          · apply PureData.BindingsReturn.cons (bound := final) bodyReturned
            · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                matchAtom, Subst.lookup, final, nextBound, selected, caller, environment,
                Form.formal, Traversal.first, Traversal.second]
            · exact .nil _ _
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, nextBound, selected, value] using
            PureData.template_return program final state (a "PMultiLam" [v "arity", v "binders", v "value"])
              (constructor_variables .multiLam ["arity", "binders", "value"])
  | hsubst body replacement bodyIH replacementIH =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .pattern first second (patternValue (.subst body replacement))
      let selected := (kind.nested, patternValue replacement) :: ("body", patternValue body) :: caller
      let nextBound := ("next", number (first + 1)) :: selected
      let bodyValue := patternValue (kind.result (first + 1) parameter body)
      let bodyBound := ("value", bodyValue) :: nextBound
      let replacementValue := patternValue (kind.result first parameter replacement)
      let final := ("replacement-value", replacementValue) :: bodyBound
      have nextReturned := add_one_returns selected state first kind.first
        (by cases kind <;> simp [selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, Traversal.nested, applySubst, Subst.lookup])
      have bodyReturned := helper_capture kind .pattern nextBound state (first + 1) second (patternValue body)
        (v "next") (v kind.second) (v "body") bodyValue
        (by cases kind <;> simp [nextBound, selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, Traversal.nested, applySubst, Subst.lookup]) (bodyIH (first + 1))
      have replacementReturned := helper_capture kind .pattern bodyBound state first second (patternValue replacement)
        (v kind.first) (v kind.second) (v kind.nested) replacementValue
        (by cases kind <;> simp [bodyBound, nextBound, selected, caller, environment, Form.formal,
          Traversal.first, Traversal.second, Traversal.nested, applySubst, Subst.lookup]) (replacementIH first)
      rw [result_subst]
      apply helper_case_returns kind .pattern state first second (patternValue (.subst body replacement))
        selected (substitutionBody kind)
      · cases kind <;> simp [cases, patternCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second, Traversal.nested]
      · apply PureData.let_bindings_return
          (pairs := [(v "next", a "+" [v kind.first, number 1]),
            (v "value", a kind.head [v "next", v kind.second, v "body"]),
            (v "replacement-value", a kind.head [v kind.first, v kind.second, v kind.nested])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
          · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
              matchAtom, Subst.lookup, nextBound, selected, caller, environment,
              Form.formal, Traversal.first, Traversal.second, Traversal.nested]
          · apply PureData.BindingsReturn.cons (bound := bodyBound) bodyReturned
            · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                matchAtom, Subst.lookup, bodyBound, nextBound, selected, caller, environment,
                Form.formal, Traversal.first, Traversal.second, Traversal.nested]
            · apply PureData.BindingsReturn.cons (bound := final) replacementReturned
              · cases kind <;> simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                  matchAtom, Subst.lookup, final, bodyBound, nextBound, selected, caller, environment,
                  Form.formal, Traversal.first, Traversal.second, Traversal.nested]
              · exact .nil _ _
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, bodyBound, nextBound, selected, bodyValue, replacementValue] using
            PureData.template_return program final state (a "PSubst" [v "value", v "replacement-value"])
              (constructor_variables .subst ["value", "replacement-value"])
  | hcollection collectionType elements rest ih =>
      let second := encoded (kind.parameterTerm parameter)
      let caller := environment kind .pattern first second (patternValue (.collection collectionType elements rest))
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) ::
        ("kind", encoded (InferenceCettaWire.encodeCollectionType collectionType)) :: caller
      let results := elements.map (kind.result first parameter)
      let final := ("values", patternsValue results) :: selected
      rw [result_collection]
      apply helper_case_returns kind .pattern state first second (patternValue (.collection collectionType elements rest))
        selected (collectionBody kind)
      · cases kind <;> simp [cases, patternCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
      · apply named_let_returns selected state "values" _ (patternsValue results) _ _
        · cases kind <;> simp [selected, caller, environment, Form.formal,
            Traversal.first, Traversal.second, Subst.lookup]
        · apply helper_capture kind .patterns selected state first second (patternsValue elements)
            (v kind.first) (v kind.second) (v "elements") _ _
            (list_returns_from_elements kind parameter state first elements (fun child member => ih child member first))
          cases kind <;> simp [selected, caller, environment, Form.formal,
            Traversal.first, Traversal.second, applySubst, Subst.lookup]
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, selected, results] using
            PureData.template_return program final state (a "PCollection" [v "kind", v "values", v "rest"])
              (constructor_variables .collection ["kind", "values", "rest"])

/-- The source implements canonical bound-variable lifting for every Pattern. -/
theorem lift_bvars_returns (state : State) (cutoff shift : Nat) (pattern : Pattern) :
    PureReturns program [] state
      (a "gslt:rule:lift-bvars" [number cutoff, number shift, patternValue pattern]) state
      (patternValue (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift pattern)) :=
  traversal_constructors_returns .lift shift state (fun cutoff index => lift_index_returns state cutoff shift index)
    pattern cutoff


theorem lift_bvars_captured_returns (caller : Subst) (state : State) (cutoff shift : Nat)
    (pattern : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [number cutoff, number shift, patternValue pattern]) :
    PureReturns program caller state (a "gslt:rule:lift-bvars" [one, two, three]) state
      (patternValue (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift pattern)) :=
  helper_capture .lift .pattern caller state cutoff (number shift) (patternValue pattern) one two three _ captured
    (lift_bvars_returns state cutoff shift pattern)

theorem lift_bvars_list_returns (state : State) (cutoff shift : Nat) (patterns : List Pattern) :
    PureReturns program [] state
      (a "gslt:rule:lift-bvars-list" [number cutoff, number shift, patternsValue patterns]) state
      (patternsValue (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList cutoff shift patterns)) := by
  simpa only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map,
    Traversal.listHead, Traversal.parameterTerm, Traversal.result] using
    list_returns_from_elements .lift shift state cutoff patterns
      (fun pattern _ => lift_bvars_returns state cutoff shift pattern)

theorem lift_bvars_list_captured_returns (caller : Subst) (state : State) (cutoff shift : Nat)
    (patterns : List Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [number cutoff, number shift, patternsValue patterns]) :
    PureReturns program caller state (a "gslt:rule:lift-bvars-list" [one, two, three]) state
      (patternsValue (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList cutoff shift patterns)) :=
  helper_capture .lift .patterns caller state cutoff (number shift) (patternsValue patterns) one two three _ captured
    (lift_bvars_list_returns state cutoff shift patterns)

private theorem lt_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (capturedFirst : applySubst caller (v first) = number left)
    (capturedSecond : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "<" [v first, v second]) state
      (Effects.boolean (decide (left < right))) := by
  apply native_variable_call_returns program caller state state "<" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, capturedFirst, capturedSecond]
  simp [number, encoded, CettaWireAtom.encode]

private theorem subtract_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (positive : 0 < value) (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "-" [v name, number 1]) state (number (value - 1)) := by
  apply native_binary_call_returns program caller state state state state "-"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · have castSubtraction : ((value - 1 : Nat) : Int) = (value : Int) - 1 := by omega
    simpa only [number, encoded, CettaWireAtom.encode, castSubtraction, Int.natCast_one] using
      StdLib.integer_subtraction state (value : Int) 1

private theorem eliminate_index_returns (state : State) (depth index : Nat) (replacement : Pattern) :
    PureReturns program [] state
      (a "gslt:rule:instantiate-bvar-at" [number depth, patternValue replacement, patternValue (.bvar index)]) state
      (patternValue (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement (.bvar index))) := by
  let caller := environment .eliminate .pattern depth (patternValue replacement) (patternValue (.bvar index))
  let selected := ("index", number index) :: caller
  apply helper_case_returns .eliminate .pattern state depth (patternValue replacement) (patternValue (.bvar index))
    selected eliminateIndexBody
  · simp [cases, patternCases, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      Subst.lookup, selected, caller, environment, Form.formal, Traversal.first, Traversal.second]
  · have belowReturned := lt_variables_returns selected state index depth "index" "depth"
      (by simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
        applySubst, Subst.lookup])
      (by simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
        applySubst, Subst.lookup])
    rw [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt.eq_1]
    apply bool_if_returns selected state _ (decide (index < depth)) _ _ _ belowReturned
    by_cases below : index < depth
    · simp only [below, decide_true, ite_true]
      simpa [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
          applySubst, Subst.lookup] using variable_returns program selected state "pattern"
    · simp only [below, decide_false, Bool.false_eq_true, ite_false]
      have equalReturned : PureReturns program selected state (a "==" [v "index", v "depth"]) state
          (Effects.boolean (decide (index = depth))) := by
        simpa only [Term.natural.injEq] using
          CettaWireAtom.equality_captured_returns program selected state (.natural index) (.natural depth) "index" "depth"
            (by simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
              applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
              applySubst, Subst.lookup])
      apply bool_if_returns selected state _ (decide (index = depth)) _ _ _ equalReturned
      by_cases equal : index = depth
      · simp only [equal, decide_true, ite_true]
        apply lift_bvars_captured_returns selected state 0 depth replacement (number 0) (v "depth") (v "replacement")
        simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
          applySubst, Subst.lookup]
      · simp only [equal, decide_false, Bool.false_eq_true, ite_false]
        apply named_let_returns selected state "next" _ (number (index - 1)) _ _
        · simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second, Subst.lookup]
        · apply subtract_one_returns selected state index "index" (by omega)
          simp [selected, caller, environment, Form.formal, Traversal.first, Traversal.second,
            applySubst, Subst.lookup]
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program (("next", number (index - 1)) :: selected) state
              (a "Var" [v "next"]) (constructor_variables .bound ["next"])

/-- Actual substitution eliminates exactly the canonical de Bruijn level. -/
theorem instantiate_bvar_at_returns (state : State) (depth : Nat) (replacement pattern : Pattern) :
    PureReturns program [] state
      (a "gslt:rule:instantiate-bvar-at" [number depth, patternValue replacement, patternValue pattern]) state
      (patternValue (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement pattern)) :=
  traversal_constructors_returns .eliminate replacement state
    (fun depth index => eliminate_index_returns state depth index replacement) pattern depth

theorem instantiate_bvar_at_captured_returns (caller : Subst) (state : State) (depth : Nat)
    (replacement pattern : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [number depth, patternValue replacement, patternValue pattern]) :
    PureReturns program caller state (a "gslt:rule:instantiate-bvar-at" [one, two, three]) state
      (patternValue (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement pattern)) :=
  helper_capture .eliminate .pattern caller state depth (patternValue replacement) (patternValue pattern)
    one two three _ captured (instantiate_bvar_at_returns state depth replacement pattern)

theorem instantiate_bvar_list_at_returns (state : State) (depth : Nat) (replacement : Pattern)
    (patterns : List Pattern) :
    PureReturns program [] state
      (a "gslt:rule:instantiate-bvar-list-at" [number depth, patternValue replacement, patternsValue patterns]) state
      (patternsValue (patterns.map (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement))) :=
  list_returns_from_elements .eliminate replacement state depth patterns
    (fun pattern _ => instantiate_bvar_at_returns state depth replacement pattern)

theorem instantiate_bvar_list_at_captured_returns (caller : Subst) (state : State) (depth : Nat)
    (replacement : Pattern) (patterns : List Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [number depth, patternValue replacement, patternsValue patterns]) :
    PureReturns program caller state (a "gslt:rule:instantiate-bvar-list-at" [one, two, three]) state
      (patternsValue (patterns.map (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement))) :=
  helper_capture .eliminate .patterns caller state depth (patternValue replacement) (patternsValue patterns)
    one two three _ captured (instantiate_bvar_list_at_returns state depth replacement patterns)


private theorem automata_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin RuleExecutionProgram.matcherHead code = true)
    (returned : PureReturns MatchAutomataProgram.program caller before code after answer) :
    PureReturns program caller before code after answer :=
  RuleExecutionProgram.automata_captured_returns supported returned

private abbrev bindingsValue (bindings : Bindings) : Atom :=
  encoded (MatchAutomataBindingExecution.bindingsTerm bindings)
private abbrev optionValue (value : Option Pattern) : Atom :=
  encoded (MatchAutomataBindingExecution.patternOptionTerm value)
private abbrev kindValue (kind : CollType) : Atom := encoded (InferenceCettaWire.encodeCollectionType kind)
private abbrev restValue (rest : Option String) : Atom := encoded (InferenceCettaWire.encodeRest rest)
attribute [local simp] bindingsValue optionValue kindValue restValue

private theorem binding_lookup_returns (caller : Subst) (state : State) (name : String) (bindings : Bindings)
    (captured : [v "name", v "bindings"].map (applySubst caller) =
      [encoded (.string name), bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:automata:binding" [v "name", v "bindings"]) state
      (optionValue (Bindings.lookup bindings name)) :=
  automata_returns (by decide +kernel)
    (MatchAutomataBindingExecution.binding_captured_returns caller state name bindings _ captured)

private theorem append_patterns_returns (caller : Subst) (state : State) (left right : List Pattern)
    (first second : String)
    (captured : [v first, v second].map (applySubst caller) = [patternsValue left, patternsValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v first, v second]) state
      (patternsValue (left ++ right)) := by
  apply automata_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  simpa only [patternsValue, encoded, InferenceCettaWire.encodePatterns_eq_encodeList,
      MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp,
      ← List.map_append] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map InferenceCettaWire.encodePattern) (right.map InferenceCettaWire.encodePattern) (v first) (v second)
      (by simpa only [patternsValue, encoded, InferenceCettaWire.encodePatterns_eq_encodeList,
        MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using captured)

private def collectionEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:instantiate-collection")[0]'(by decide +kernel)
private def collectionEnvironment (kind : CollType) (elements : List Pattern) (rest : Option String)
    (bindings : Bindings) : Subst :=
  [("bindings", bindingsValue bindings), ("rest", restValue rest),
    ("elements", patternsValue elements), ("kind", kindValue kind)]
private def collectionKeep : Atom := a "PCollection" [v "kind", v "elements", v "rest"]
private def collectionClosed : Atom := a "PCollection" [v "kind", v "elements", .symbol "RNone"]
private def collectionSplice : Atom :=
  a "let" [v "all", a "gslt:automata:append" [v "elements", v "bound-elements"],
    a "PCollection" [v "kind", v "all", .symbol "RNone"]]
private def collectionLookupCases : SpaceSemantics.Cases :=
  [(a "Some" [a "PCollection" [v "bound-kind", v "bound-elements", .symbol "RNone"]],
    a "if" [a "==" [v "kind", v "bound-kind"], collectionSplice, collectionKeep]),
   (v "unresolved", collectionKeep)]
private def collectionLookup : Atom := a "case" [a "gslt:automata:binding" [v "name", v "bindings"],
  .expression (collectionLookupCases.map fun row => .expression [row.1, row.2])]
private def collectionCases : SpaceSemantics.Cases :=
  [(.symbol "RNone", collectionClosed), (a "RSome" [v "name"], collectionLookup)]
private theorem collection_shape : collectionEquation.body =
    a "case" [v "rest", .expression (collectionCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem collection_clause (kind : CollType) (elements : List Pattern) (rest : Option String)
    (bindings : Bindings) :
    clauses program "gslt:rule:instantiate-collection" [kindValue kind, patternsValue elements, restValue rest,
      bindingsValue bindings] = [.evaluate (collectionEnvironment kind elements rest bindings) collectionEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:instantiate-collection").filterMap _ = _
  rw [show equations "gslt:rule:instantiate-collection" = [collectionEquation] from rfl]
  have formals : collectionEquation.arguments = [v "kind", v "elements", v "rest", v "bindings"] := by
    decide +kernel
  simp [formals, collectionEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem collection_case_returns (state : State) (kind : CollType) (elements : List Pattern)
    (rest : Option String) (bindings : Bindings) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (collectionEnvironment kind elements rest bindings) (restValue rest)
      collectionCases = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a "gslt:rule:instantiate-collection"
      [kindValue kind, patternsValue elements, restValue rest, bindingsValue bindings]) state answer := by
  apply PureData.raw_authored_call_return program [] (collectionEnvironment kind elements rest bindings) state state
    "gslt:rule:instantiate-collection"
    [kindValue kind, patternsValue elements, restValue rest, bindingsValue bindings]
    collectionEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ _
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl | rfl <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using collection_clause kind elements rest bindings
  · rw [collection_shape]
    apply case_returns program (collectionEnvironment kind elements rest bindings) selected state state state
      (v "rest") (restValue rest) body answer _ collectionCases (read_cases_encoded _) _ matched returned
    simpa [collectionEnvironment, applySubst, Subst.lookup] using
      variable_returns program (collectionEnvironment kind elements rest bindings) state "rest"

private theorem collection_closed_template : PureData.Template program collectionClosed := by
  apply PureData.Template.constructor "PCollection" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · exact .captured _
  · exact .symbol _
private theorem collection_spliced_template :
    PureData.Template program (a "PCollection" [v "kind", v "all", .symbol "RNone"]) := by
  apply PureData.Template.constructor "PCollection" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · exact .captured _
  · exact .symbol _

private theorem applyBindings_collection_lookup (bindings : Bindings) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    applyBindings bindings (.collection kind elements rest) =
      match rest with
      | none => .collection kind (elements.map (applyBindings bindings)) none
      | some name => match Bindings.lookup bindings name with
        | some (.collection boundKind residual none) =>
            if boundKind == kind then .collection kind (elements.map (applyBindings bindings) ++ residual) none
              else .collection kind (elements.map (applyBindings bindings)) (some name)
        | _ => .collection kind (elements.map (applyBindings bindings)) (some name) := by
  rw [applyBindings.eq_def]
  cases rest with
  | none => simp only [List.append_nil]
  | some name =>
      unfold Bindings.lookup
      cases found : bindings.find? (fun entry => entry.1 == name) with
      | none =>
          simp only [found, Option.map_none, List.append_nil]
      | some entry =>
          obtain ⟨key, pattern⟩ := entry
          simp only [found, Option.map_some]
          cases pattern with
          | collection boundKind residual rest =>
              cases rest with
              | some _ => simp only [List.append_nil]
              | none =>
                  cases same : (boundKind == kind) <;>
                    simp only [same, Bool.false_eq_true, ite_false, ite_true, List.append_nil]
          | bvar _ | fvar _ | apply _ _ | lambda _ _ | multiLambda _ _ _ | subst _ _ =>
              simp only [List.append_nil]

private theorem collection_type_encode_eq (left right : CollType) :
    InferenceCettaWire.encodeCollectionType left = InferenceCettaWire.encodeCollectionType right ↔ left = right := by
  constructor
  · intro equal
    have decoded := congrArg InferenceCettaWire.decodeCollectionType equal
    simpa using decoded
  · rintro rfl
    rfl


private theorem collection_keep_returns (caller : Subst) (state : State) (kind : CollType)
    (elements : List Pattern) (rest : Option String)
    (kindCaptured : applySubst caller (v "kind") = kindValue kind)
    (elementsCaptured : applySubst caller (v "elements") = patternsValue elements)
    (restCaptured : applySubst caller (v "rest") = restValue rest) :
    PureReturns program caller state collectionKeep state (patternValue (.collection kind elements rest)) := by
  change (Subst.lookup caller "kind").getD (v "kind") = kindValue kind at kindCaptured
  change (Subst.lookup caller "elements").getD (v "elements") = patternsValue elements at elementsCaptured
  change (Subst.lookup caller "rest").getD (v "rest") = restValue rest at restCaptured
  have answerEq : applySubst caller collectionKeep = patternValue (.collection kind elements rest) := by
    simp [collectionKeep, patternValue, encoded, InferenceCettaWire.encodePattern,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
      kindCaptured, elementsCaptured, restCaptured]
  have returned := PureData.template_return program caller state collectionKeep
    (constructor_variables .collection ["kind", "elements", "rest"])
  rw [answerEq] at returned
  exact returned

private theorem collection_closed_returns (caller : Subst) (state : State) (kind : CollType)
    (elements : List Pattern)
    (kindCaptured : applySubst caller (v "kind") = kindValue kind)
    (elementsCaptured : applySubst caller (v "elements") = patternsValue elements) :
    PureReturns program caller state collectionClosed state (patternValue (.collection kind elements none)) := by
  change (Subst.lookup caller "kind").getD (v "kind") = kindValue kind at kindCaptured
  change (Subst.lookup caller "elements").getD (v "elements") = patternsValue elements at elementsCaptured
  have answerEq : applySubst caller collectionClosed = patternValue (.collection kind elements none) := by
    simp [collectionClosed, patternValue, encoded, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      applySubst, applySubst.applySubstList, kindCaptured, elementsCaptured]
  have returned := PureData.template_return program caller state collectionClosed collection_closed_template
  rw [answerEq] at returned
  exact returned

private theorem matchValue_head_clash (caller : Subst) (left right : String) (patterns values : List Atom)
    (ordinary : left ≠ "cons") (different : left ≠ right) :
    SpaceSemantics.matchValue caller (a left patterns) (a right values) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons caller (.symbol left :: patterns) (.symbol right :: values)]
  · simp only [SpaceSemantics.matchValue.matchValues]
    rw [SpaceSemantics.matchValue_literal (.symbol left) caller (.symbol right)]
    simp [different]
  · intro first rest same
    exact ordinary (by simpa using (List.cons.inj same).1)

private theorem matchValue_some_failure (caller : Subst) (pattern value : Atom)
    (failed : SpaceSemantics.matchValue caller pattern value = none) :
    SpaceSemantics.matchValue caller (a "Some" [pattern]) (a "Some" [value]) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons caller [.symbol "Some", pattern] [.symbol "Some", value]]
  · simp only [SpaceSemantics.matchValue.matchValues]
    rw [SpaceSemantics.matchValue_literal (.symbol "Some") caller (.symbol "Some")]
    simp only [ite_true, bind, Option.bind, failed]
  · intro first rest same
    have heads : ("Some" : String) = "cons" := by simpa using (List.cons.inj same).1
    exact (by decide : ("Some" : String) ≠ "cons") heads

private theorem collection_lookup_failure (kind : CollType) (elements : List Pattern)
    (name : String) (bindings : Bindings)
    (notClosed : ∀ boundKind residual, Bindings.lookup bindings name ≠ some (.collection boundKind residual none)) :
    SpaceSemantics.matchValue
      (("name", encoded (.string name)) :: collectionEnvironment kind elements (some name) bindings)
      (a "Some" [a "PCollection" [v "bound-kind", v "bound-elements", .symbol "RNone"]])
      (optionValue (Bindings.lookup bindings name)) = none := by
  let caller := ("name", encoded (.string name)) :: collectionEnvironment kind elements (some name) bindings
  cases found : Bindings.lookup bindings name with
  | none => simp [optionValue, MatchAutomataBindingExecution.patternOptionTerm,
      CettaWireAtom.encode, SpaceSemantics.matchValue]
  | some pattern =>
      change SpaceSemantics.matchValue caller
        (a "Some" [a "PCollection" [v "bound-kind", v "bound-elements", .symbol "RNone"]])
        (a "Some" [patternValue pattern]) = none
      apply matchValue_some_failure
      cases pattern with
      | collection boundKind residual rest =>
          cases rest with
          | none => exact False.elim (notClosed boundKind residual found)
          | some restName =>
              simp only [patternValue, encoded, InferenceCettaWire.encodePattern,
                InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany]
              rw [SpaceSemantics.matchValue_expression_of_not_cons]
              · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue,
                  matchAtom, caller, collectionEnvironment, Subst.lookup]
              · intro first rest same
                have heads : ("PCollection" : String) = "cons" := by simpa using (List.cons.inj same).1
                exact (by decide : ("PCollection" : String) ≠ "cons") heads
      | bvar _ | fvar _ | apply _ _ | lambda _ _ | multiLambda _ _ _ | subst _ _ =>
          simp only [patternValue, encoded, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany]
          exact matchValue_head_clash caller "PCollection" _ _ _ (by decide) (by decide)

private theorem collection_unresolved_returns (state : State) (kind : CollType) (elements : List Pattern)
    (name : String) (bindings : Bindings)
    (notClosed : ∀ boundKind residual, Bindings.lookup bindings name ≠ some (.collection boundKind residual none)) :
    PureReturns program (("name", encoded (.string name)) :: collectionEnvironment kind elements (some name) bindings)
      state collectionLookup state (patternValue (.collection kind elements (some name))) := by
  let selected := ("name", encoded (.string name)) :: collectionEnvironment kind elements (some name) bindings
  let value := optionValue (Bindings.lookup bindings name)
  let unresolved := ("unresolved", value) :: selected
  have lookedUp := binding_lookup_returns selected state name bindings
    (by simp [selected, collectionEnvironment, applySubst, Subst.lookup])
  apply case_returns program selected unresolved state state state _ value collectionKeep _ _
    collectionLookupCases (read_cases_encoded _) lookedUp _ _
  · apply SpaceSemantics.selectCase_complete
    apply SpaceSemantics.Selected.later (collection_lookup_failure kind elements name bindings notClosed)
    apply SpaceSemantics.Selected.first
    simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
      selected, unresolved, collectionEnvironment, value]
  · apply collection_keep_returns unresolved state kind elements (some name)
    · simp [unresolved, selected, collectionEnvironment, applySubst, Subst.lookup]
    · simp [unresolved, selected, collectionEnvironment, applySubst, Subst.lookup]
    · simp [unresolved, selected, collectionEnvironment, applySubst, Subst.lookup]

private theorem collection_resolved_returns (state : State) (kind : CollType) (elements : List Pattern)
    (name : String) (bindings : Bindings) (boundKind : CollType) (residual : List Pattern)
    (found : Bindings.lookup bindings name = some (.collection boundKind residual none)) :
    PureReturns program (("name", encoded (.string name)) :: collectionEnvironment kind elements (some name) bindings)
      state collectionLookup state
      (patternValue (if boundKind == kind then .collection kind (elements ++ residual) none
        else .collection kind elements (some name))) := by
  let selected := ("name", encoded (.string name)) :: collectionEnvironment kind elements (some name) bindings
  let resolved := ("bound-elements", patternsValue residual) :: ("bound-kind", kindValue boundKind) :: selected
  have lookedUp := binding_lookup_returns selected state name bindings
    (by simp [selected, collectionEnvironment, applySubst, Subst.lookup])
  apply case_returns program selected resolved state state state _ (optionValue (some (.collection boundKind residual none)))
    (a "if" [a "==" [v "kind", v "bound-kind"], collectionSplice, collectionKeep]) _ _
    collectionLookupCases (read_cases_encoded _) _ _ _
  · simpa only [found] using lookedUp
  · simp [collectionLookupCases, optionValue, MatchAutomataBindingExecution.patternOptionTerm,
      InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      Subst.lookup, selected, resolved, collectionEnvironment]
  · have sameReturned : PureReturns program resolved state (a "==" [v "kind", v "bound-kind"]) state
        (Effects.boolean (decide (kind = boundKind))) := by
      simpa only [collection_type_encode_eq] using
        CettaWireAtom.equality_captured_returns program resolved state
          (InferenceCettaWire.encodeCollectionType kind) (InferenceCettaWire.encodeCollectionType boundKind)
          "kind" "bound-kind"
          (by simp [resolved, selected, collectionEnvironment, applySubst, Subst.lookup])
          (by simp [resolved, selected, collectionEnvironment, applySubst, Subst.lookup])
    apply bool_if_returns resolved state _ (decide (kind = boundKind)) _ _ _ sameReturned
    by_cases same : kind = boundKind
    · simp only [same, decide_true, beq_self_eq_true, ite_true]
      let final := ("all", patternsValue (elements ++ residual)) :: resolved
      apply named_let_returns resolved state "all" _ (patternsValue (elements ++ residual)) _ _
      · simp [resolved, selected, collectionEnvironment, Subst.lookup]
      · apply append_patterns_returns resolved state elements residual "elements" "bound-elements"
        simp [resolved, selected, collectionEnvironment, applySubst, Subst.lookup]
      · have constructed := PureData.template_return program final state
          (a "PCollection" [v "kind", v "all", .symbol "RNone"]) collection_spliced_template
        simpa [InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
          Subst.lookup, final, resolved, selected, collectionEnvironment, same] using constructed
    · have different : (boundKind == kind) = false := by simp [Ne.symm same]
      simp only [same, decide_false, Bool.false_eq_true, ite_false, different]
      apply collection_keep_returns resolved state kind elements (some name)
      · simp [resolved, selected, collectionEnvironment, applySubst, Subst.lookup]
      · simp [resolved, selected, collectionEnvironment, applySubst, Subst.lookup]
      · simp [resolved, selected, collectionEnvironment, applySubst, Subst.lookup]

/-- The rest operation consumes the already-instantiated explicit elements.
Captured residual elements are not substituted a second time. -/
theorem instantiate_collection_returns (state : State) (bindings : Bindings) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    PureReturns program [] state (a "gslt:rule:instantiate-collection"
      [kindValue kind, patternsValue (elements.map (applyBindings bindings)), restValue rest, bindingsValue bindings]) state
      (patternValue (applyBindings bindings (.collection kind elements rest))) := by
  let explicit := elements.map (applyBindings bindings)
  rw [applyBindings_collection_lookup]
  cases rest with
  | none =>
      apply collection_case_returns state kind explicit none bindings
        (collectionEnvironment kind explicit none bindings) collectionClosed
      · simp [collectionCases, restValue, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · apply collection_closed_returns _ state kind explicit
        · simp [collectionEnvironment, applySubst, Subst.lookup]
        · simp [collectionEnvironment, applySubst, Subst.lookup]
  | some name =>
      let selected := ("name", encoded (.string name)) :: collectionEnvironment kind explicit (some name) bindings
      apply collection_case_returns state kind explicit (some name) bindings selected collectionLookup
      · simp [collectionCases, restValue, InferenceCettaWire.encodeRest, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, collectionEnvironment]
      · change PureReturns program selected state collectionLookup state
          (patternValue (match Bindings.lookup bindings name with
            | some (.collection boundKind residual none) =>
                if boundKind == kind then .collection kind (explicit ++ residual) none
                  else .collection kind explicit (some name)
            | _ => .collection kind explicit (some name)))
        by_cases closed : ∃ boundKind residual,
            Bindings.lookup bindings name = some (.collection boundKind residual none)
        · obtain ⟨boundKind, residual, found⟩ := closed
          simp only [found]
          exact collection_resolved_returns state kind explicit name bindings boundKind residual found
        · have unresolved : (match Bindings.lookup bindings name with
              | some (Pattern.collection boundKind residual none) =>
                  if boundKind == kind then Pattern.collection kind (explicit ++ residual) none
                    else Pattern.collection kind explicit (some name)
              | _ => Pattern.collection kind explicit (some name)) = Pattern.collection kind explicit (some name) := by
            cases found : Bindings.lookup bindings name with
            | none => rfl
            | some value =>
                cases value with
                | collection boundKind residual rest =>
                    cases rest with
                    | some _ => rfl
                    | none => exact False.elim (closed ⟨boundKind, residual, found⟩)
                | bvar _ | fvar _ | apply _ _ | lambda _ _ | multiLambda _ _ _ | subst _ _ => rfl
          rw [unresolved]
          apply collection_unresolved_returns state kind explicit name bindings
          intro boundKind residual found
          exact closed ⟨boundKind, residual, found⟩



theorem instantiate_collection_captured_returns (caller : Subst) (state : State) (bindings : Bindings)
    (kind : CollType) (elements : List Pattern) (rest : Option String) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [kindValue kind, patternsValue (elements.map (applyBindings bindings)), restValue rest, bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:rule:instantiate-collection" [one, two, three, four]) state
      (patternValue (applyBindings bindings (.collection kind elements rest))) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:rule:instantiate-collection"
    [kindValue kind, patternsValue (elements.map (applyBindings bindings)), restValue rest, bindingsValue bindings]
    [one, two, three, four] _ (by decide +kernel) _ (by decide) _
    (instantiate_collection_returns state bindings kind elements rest)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl | rfl <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using captured.symm

private def instantiationHead : Form → String
  | .pattern => "gslt:rule:instantiate"
  | .patterns => "gslt:rule:instantiate-children"
private def instantiationEquation (form : Form) : SpaceSemantics.Equation :=
  (equations (instantiationHead form))[0]'(by cases form <;> decide +kernel)
private def instantiationEnvironment (form : Form) (value : Atom) (bindings : Bindings) : Subst :=
  [("bindings", bindingsValue bindings), (form.formal, value)]
private def instantiationLookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "pattern"), (a "Some" [v "value"], v "value")]
private def instantiationLookupBody : Atom :=
  a "case" [a "gslt:automata:binding" [v "name", v "bindings"],
    .expression (instantiationLookupCases.map fun row => .expression [row.1, row.2])]
private def instantiationApplicationBody : Atom :=
  a "let" [v "arguments", a "gslt:rule:instantiate-children" [v "children", v "bindings"],
    a "PApp" [v "head", v "arguments"]]
private def instantiationLambdaBody : Atom :=
  a "let" [v "value", a "gslt:rule:instantiate" [v "body", v "bindings"],
    a "PLam" [v "binder", v "value"]]
private def instantiationMultiLambdaBody : Atom :=
  a "let" [v "value", a "gslt:rule:instantiate" [v "body", v "bindings"],
    a "PMultiLam" [v "arity", v "binders", v "value"]]
private def instantiationSubstitutionBody : Atom :=
  a "let*" [.expression [
    .expression [v "value", a "gslt:rule:instantiate" [v "body", v "bindings"]],
    .expression [v "replacement-value", a "gslt:rule:instantiate" [v "replacement", v "bindings"]]],
    a "gslt:rule:instantiate-bvar-at" [number 0, v "replacement-value", v "value"]]
private def instantiationCollectionBody : Atom :=
  a "let" [v "values", a "gslt:rule:instantiate-children" [v "elements", v "bindings"],
    a "gslt:rule:instantiate-collection" [v "kind", v "values", v "rest", v "bindings"]]
private def instantiationCases : SpaceSemantics.Cases :=
  [(a "FVar" [v "name"], instantiationLookupBody), (a "Var" [v "index"], v "pattern"),
   (a "PApp" [v "head", v "children"], instantiationApplicationBody),
   (a "PLam" [v "binder", v "body"], instantiationLambdaBody),
   (a "PMultiLam" [v "arity", v "binders", v "body"], instantiationMultiLambdaBody),
   (a "PSubst" [v "body", v "replacement"], instantiationSubstitutionBody),
   (a "PCollection" [v "kind", v "elements", v "rest"], instantiationCollectionBody)]
private def instantiationListBody : Atom :=
  a "let*" [.expression [
    .expression [v "head", a "gslt:rule:instantiate" [v "pattern", v "bindings"]],
    .expression [v "tail", a "gslt:rule:instantiate-children" [v "rest", v "bindings"]]],
    a "LCons" [v "head", v "tail"]]
private def instantiationListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "pattern", v "rest"], instantiationListBody)]
private def instantiationCaseRows : Form → SpaceSemantics.Cases
  | .pattern => instantiationCases
  | .patterns => instantiationListCases
private theorem instantiation_shape (form : Form) : (instantiationEquation form).body =
    a "case" [v form.formal,
      .expression ((instantiationCaseRows form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private theorem instantiation_clause (form : Form) (value : Atom) (bindings : Bindings) :
    clauses program (instantiationHead form) [value, bindingsValue bindings] =
      [.evaluate (instantiationEnvironment form value bindings) (instantiationEquation form).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations (instantiationHead form)).filterMap _ = _
  rw [show equations (instantiationHead form) = [instantiationEquation form] from by cases form <;> rfl]
  have formals : (instantiationEquation form).arguments = [v form.formal, v "bindings"] := by
    cases form <;> decide +kernel
  cases form <;> simp [formals, instantiationEnvironment, Form.formal,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem instantiation_case_returns (form : Form) (state : State) (value : Atom) (bindings : Bindings)
    (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (instantiationEnvironment form value bindings) value
      (instantiationCaseRows form) = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a (instantiationHead form) [value, bindingsValue bindings]) state answer := by
  apply PureData.raw_authored_call_return program [] (instantiationEnvironment form value bindings) state state
    (instantiationHead form) [value, bindingsValue bindings] (instantiationEquation form).body answer
    (by cases form <;> decide) (by cases form <;> decide) (by cases form <;> decide)
    (by cases form <;> decide +kernel) _ _ _
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> cases form <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using instantiation_clause form value bindings
  · rw [instantiation_shape]
    apply case_returns program (instantiationEnvironment form value bindings) selected state state state
      (v form.formal) value body answer _ (instantiationCaseRows form) (read_cases_encoded _) _ matched returned
    cases form with
    | pattern =>
        simpa [instantiationEnvironment, Form.formal, applySubst, Subst.lookup] using
          variable_returns program (instantiationEnvironment .pattern value bindings) state "pattern"
    | patterns =>
        simpa [instantiationEnvironment, Form.formal, applySubst, Subst.lookup] using
          variable_returns program (instantiationEnvironment .patterns value bindings) state "patterns"

private theorem instantiation_capture (form : Form) (caller : Subst) (state : State) (value : Atom)
    (bindings : Bindings) (one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [value, bindingsValue bindings])
    (returned : PureReturns program [] state (a (instantiationHead form) [value, bindingsValue bindings]) state answer) :
    PureReturns program caller state (a (instantiationHead form) [one, two]) state answer := by
  apply PureData.raw_capture_returns program [] caller state state (instantiationHead form)
    [value, bindingsValue bindings] [one, two] answer (by cases form <;> decide +kernel) _
    (by cases form <;> decide) _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> cases form <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using captured.symm

private theorem applyBindings_fvar_lookup (bindings : Bindings) (name : String) :
    applyBindings bindings (.fvar name) = (Bindings.lookup bindings name).getD (.fvar name) := by
  rw [applyBindings.eq_def]
  simp only
  unfold Bindings.lookup
  cases found : bindings.find? (fun entry => entry.1 == name) with
  | none => rfl
  | some entry => obtain ⟨key, value⟩ := entry; rfl

private theorem instantiation_list_from_elements (state : State) (bindings : Bindings) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a "gslt:rule:instantiate" [patternValue pattern, bindingsValue bindings]) state
      (patternValue (applyBindings bindings pattern))) :
    PureReturns program [] state (a "gslt:rule:instantiate-children" [patternsValue patterns, bindingsValue bindings]) state
      (patternsValue (patterns.map (applyBindings bindings))) := by
  induction patterns with
  | nil =>
      simp only [patternsValue, encoded, InferenceCettaWire.encodePatterns, List.map_nil, CettaWireAtom.encode]
      apply instantiation_case_returns .patterns state (.symbol "LNil") bindings
        (instantiationEnvironment .patterns (.symbol "LNil") bindings) (.symbol "LNil")
      · simp [instantiationCaseRows, instantiationListCases, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons pattern patterns ih =>
      let caller := instantiationEnvironment .patterns (patternsValue (pattern :: patterns)) bindings
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let headValue := patternValue (applyBindings bindings pattern)
      let headBound := ("head", headValue) :: selected
      let tailValue := patternsValue (patterns.map (applyBindings bindings))
      let final := ("tail", tailValue) :: headBound
      have headReturned := instantiation_capture .pattern selected state (patternValue pattern) bindings
        (v "pattern") (v "bindings") headValue
        (by simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup])
        (elements pattern (by simp))
      have tailReturned := instantiation_capture .patterns headBound state (patternsValue patterns) bindings
        (v "rest") (v "bindings") tailValue
        (by simp [headBound, selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup])
        (ih (fun pattern member => elements pattern (List.mem_cons_of_mem _ member)))
      apply instantiation_case_returns .patterns state (patternsValue (pattern :: patterns)) bindings selected instantiationListBody
      · simp [instantiationCaseRows, instantiationListCases, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · apply PureData.let_bindings_return
          (pairs := [(v "head", a "gslt:rule:instantiate" [v "pattern", v "bindings"]),
            (v "tail", a "gslt:rule:instantiate-children" [v "rest", v "bindings"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              selected, caller, headBound, instantiationEnvironment, Form.formal]
          · apply PureData.BindingsReturn.cons (bound := final) tailReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, headBound, selected, caller, instantiationEnvironment, Form.formal]
            · exact .nil _ _
        · simpa [Constructor.head, List.map_cons, InferenceCettaWire.encodePatterns,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, headBound, headValue, tailValue] using
            PureData.template_return program final state (a "LCons" [v "head", v "tail"])
              (constructor_variables .cons ["head", "tail"])


/-- The retained instantiator implements the canonical gradual operation on
all Pattern constructors. Scope-correct rule instantiation has its separate
Assignment and occurrence-argument obligations. -/
theorem apply_bindings_returns (state : State) (bindings : Bindings) (pattern : Pattern) :
    PureReturns program [] state (a "gslt:rule:instantiate" [patternValue pattern, bindingsValue bindings]) state
      (patternValue (applyBindings bindings pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let caller := instantiationEnvironment .pattern (patternValue (.bvar index)) bindings
      let selected := ("index", number index) :: caller
      rw [applyBindings.eq_def]
      apply instantiation_case_returns .pattern state (patternValue (.bvar index)) bindings selected (v "pattern")
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · simpa [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup] using
          variable_returns program selected state "pattern"
  | hfvar name =>
      let caller := instantiationEnvironment .pattern (patternValue (.fvar name)) bindings
      let selected := ("name", encoded (.string name)) :: caller
      have lookedUp := binding_lookup_returns selected state name bindings
        (by simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup])
      rw [applyBindings_fvar_lookup]
      apply instantiation_case_returns .pattern state (patternValue (.fvar name)) bindings selected instantiationLookupBody
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · cases found : Bindings.lookup bindings name with
        | none =>
            apply case_returns program selected selected state state state
              (a "gslt:automata:binding" [v "name", v "bindings"]) (.symbol "None") (v "pattern")
              _ _ instantiationLookupCases (read_cases_encoded _) _ _ _
            · simpa [found, optionValue, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using lookedUp
            · simp [instantiationLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [found, selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup] using
                variable_returns program selected state "pattern"
        | some value =>
            let inserted := ("value", patternValue value) :: selected
            apply case_returns program selected inserted state state state
              (a "gslt:automata:binding" [v "name", v "bindings"]) (a "Some" [patternValue value]) (v "value")
              _ _ instantiationLookupCases (read_cases_encoded _) _ _ _
            · simpa [found, optionValue, MatchAutomataBindingExecution.patternOptionTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookedUp
            · simp [instantiationLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                inserted, selected, caller, instantiationEnvironment, Form.formal]
            · simpa [found, inserted, applySubst, Subst.lookup] using variable_returns program inserted state "value"
  | happly head children ih =>
      let caller := instantiationEnvironment .pattern (patternValue (.apply head children)) bindings
      let selected := ("children", patternsValue children) :: ("head", encoded (.string head)) :: caller
      let results := children.map (applyBindings bindings)
      let final := ("arguments", patternsValue results) :: selected
      rw [applyBindings.eq_def]
      apply instantiation_case_returns .pattern state (patternValue (.apply head children)) bindings selected instantiationApplicationBody
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · apply named_let_returns selected state "arguments" _ (patternsValue results) _ _
        · simp [selected, caller, instantiationEnvironment, Form.formal, Subst.lookup]
        · apply instantiation_capture .patterns selected state (patternsValue children) bindings
            (v "children") (v "bindings") _ _ (instantiation_list_from_elements state bindings children ih)
          simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup]
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, selected, results] using
            PureData.template_return program final state (a "PApp" [v "head", v "arguments"])
              (constructor_variables .app ["head", "arguments"])
  | hlambda binder body ih =>
      let caller := instantiationEnvironment .pattern (patternValue (.lambda binder body)) bindings
      let selected := ("body", patternValue body) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let value := patternValue (applyBindings bindings body)
      let final := ("value", value) :: selected
      rw [applyBindings.eq_def]
      apply instantiation_case_returns .pattern state (patternValue (.lambda binder body)) bindings selected instantiationLambdaBody
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · apply named_let_returns selected state "value" _ value _ _
        · simp [selected, caller, instantiationEnvironment, Form.formal, Subst.lookup]
        · apply instantiation_capture .pattern selected state (patternValue body) bindings
            (v "body") (v "bindings") value _ ih
          simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup]
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, selected, value] using
            PureData.template_return program final state (a "PLam" [v "binder", v "value"])
              (constructor_variables .lam ["binder", "value"])
  | hmultiLambda arity binders body ih =>
      let caller := instantiationEnvironment .pattern (patternValue (.multiLambda arity binders body)) bindings
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", number arity) :: caller
      let value := patternValue (applyBindings bindings body)
      let final := ("value", value) :: selected
      rw [applyBindings.eq_def]
      apply instantiation_case_returns .pattern state (patternValue (.multiLambda arity binders body)) bindings selected instantiationMultiLambdaBody
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · apply named_let_returns selected state "value" _ value _ _
        · simp [selected, caller, instantiationEnvironment, Form.formal, Subst.lookup]
        · apply instantiation_capture .pattern selected state (patternValue body) bindings
            (v "body") (v "bindings") value _ ih
          simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup]
        · simpa [Constructor.head, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
            Subst.lookup, final, selected, value] using
            PureData.template_return program final state (a "PMultiLam" [v "arity", v "binders", v "value"])
              (constructor_variables .multiLam ["arity", "binders", "value"])
  | hsubst body replacement bodyIH replacementIH =>
      let caller := instantiationEnvironment .pattern (patternValue (.subst body replacement)) bindings
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      let bodyValue := patternValue (applyBindings bindings body)
      let bodyBound := ("value", bodyValue) :: selected
      let replacementValue := patternValue (applyBindings bindings replacement)
      let final := ("replacement-value", replacementValue) :: bodyBound
      have bodyReturned := instantiation_capture .pattern selected state (patternValue body) bindings
        (v "body") (v "bindings") bodyValue
        (by simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup]) bodyIH
      have replacementReturned := instantiation_capture .pattern bodyBound state (patternValue replacement) bindings
        (v "replacement") (v "bindings") replacementValue
        (by simp [bodyBound, selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup]) replacementIH
      rw [applyBindings.eq_def]
      apply instantiation_case_returns .pattern state (patternValue (.subst body replacement)) bindings selected instantiationSubstitutionBody
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · apply PureData.let_bindings_return
          (pairs := [(v "value", a "gslt:rule:instantiate" [v "body", v "bindings"]),
            (v "replacement-value", a "gslt:rule:instantiate" [v "replacement", v "bindings"])])
          (final := final)
        · apply PureData.BindingsReturn.cons (bound := bodyBound) bodyReturned
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              bodyBound, selected, caller, instantiationEnvironment, Form.formal]
          · apply PureData.BindingsReturn.cons (bound := final) replacementReturned
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, bodyBound, selected, caller, instantiationEnvironment, Form.formal]
            · exact .nil _ _
        · apply instantiate_bvar_at_captured_returns final state 0
            (applyBindings bindings replacement) (applyBindings bindings body) (number 0) (v "replacement-value") (v "value")
          simp [final, bodyBound, selected, caller, instantiationEnvironment, Form.formal,
            replacementValue, bodyValue, applySubst, Subst.lookup]
  | hcollection kind elements rest ih =>
      let caller := instantiationEnvironment .pattern (patternValue (.collection kind elements rest)) bindings
      let selected := ("rest", restValue rest) :: ("elements", patternsValue elements) :: ("kind", kindValue kind) :: caller
      let values := patternsValue (elements.map (applyBindings bindings))
      let final := ("values", values) :: selected
      apply instantiation_case_returns .pattern state (patternValue (.collection kind elements rest)) bindings selected instantiationCollectionBody
      · simp [instantiationCaseRows, instantiationCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, instantiationEnvironment, Form.formal]
      · apply named_let_returns selected state "values" _ values _ _
        · simp [selected, caller, instantiationEnvironment, Form.formal, Subst.lookup]
        · apply instantiation_capture .patterns selected state (patternsValue elements) bindings
            (v "elements") (v "bindings") values _ (instantiation_list_from_elements state bindings elements ih)
          simp [selected, caller, instantiationEnvironment, Form.formal, applySubst, Subst.lookup]
        · apply instantiate_collection_captured_returns final state bindings kind elements rest
            (v "kind") (v "values") (v "rest") (v "bindings")
          simp [final, selected, caller, instantiationEnvironment, Form.formal, values, applySubst, Subst.lookup]

theorem apply_bindings_captured_returns (caller : Subst) (state : State) (bindings : Bindings)
    (pattern : Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [patternValue pattern, bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:rule:instantiate" [one, two]) state
      (patternValue (applyBindings bindings pattern)) :=
  instantiation_capture .pattern caller state (patternValue pattern) bindings one two _ captured
    (apply_bindings_returns state bindings pattern)

theorem apply_bindings_children_returns (state : State) (bindings : Bindings) (patterns : List Pattern) :
    PureReturns program [] state (a "gslt:rule:instantiate-children" [patternsValue patterns, bindingsValue bindings]) state
      (patternsValue (patterns.map (applyBindings bindings))) :=
  instantiation_list_from_elements state bindings patterns (fun pattern _ => apply_bindings_returns state bindings pattern)

theorem apply_bindings_children_captured_returns (caller : Subst) (state : State) (bindings : Bindings)
    (patterns : List Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [patternsValue patterns, bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:rule:instantiate-children" [one, two]) state
      (patternsValue (patterns.map (applyBindings bindings))) :=
  instantiation_capture .patterns caller state (patternsValue patterns) bindings one two _ captured
    (apply_bindings_children_returns state bindings patterns)

/-- The existing first-order interface is a specialization of the full operation. -/
theorem instantiate_captured_returns (caller : Subst) (state : State) (bindings : Bindings) (plan : PatternPlan)
    (one two : Atom) (captured : [one, two].map (applySubst caller) =
      [patternValue plan.erase, bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:rule:instantiate" [one, two]) state
      (patternValue (plan.instantiate bindings)) := by
  simpa only [instantiate_eq_applyBindings] using
    apply_bindings_captured_returns caller state bindings plan.erase one two captured

theorem instantiate_returns (state : State) (bindings : Bindings) (plan : PatternPlan) :
    PureReturns program [] state
      (a "gslt:rule:instantiate" [patternValue plan.erase, bindingsValue bindings]) state
      (patternValue (plan.instantiate bindings)) := by
  simpa only [instantiate_eq_applyBindings] using apply_bindings_returns state bindings plan.erase

theorem instantiate_children_captured_returns (caller : Subst) (state : State) (bindings : Bindings)
    (plans : List PatternPlan) (one two : Atom) (captured : [one, two].map (applySubst caller) =
      [patternsValue (erasePatterns plans), bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:rule:instantiate-children" [one, two]) state
      (patternsValue (plans.map (PatternPlan.instantiate bindings))) := by
  simpa only [instantiateList_eq_applyBindings] using
    apply_bindings_children_captured_returns caller state bindings (erasePatterns plans) one two captured

theorem instantiate_children_returns (state : State) (bindings : Bindings) (plans : List PatternPlan) :
    PureReturns program [] state
      (a "gslt:rule:instantiate-children" [patternsValue (erasePatterns plans), bindingsValue bindings]) state
      (patternsValue (plans.map (PatternPlan.instantiate bindings))) := by
  simpa only [instantiateList_eq_applyBindings] using
    apply_bindings_children_returns state bindings (erasePatterns plans)

def applyBindingsQuery (bindings : Bindings) (pattern : Pattern) : Atom :=
  a "gslt:rule:instantiate" [patternValue pattern, bindingsValue bindings]

theorem apply_bindings_completed_iff (state : State) (bindings : Bindings) (pattern : Pattern)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (applyBindingsQuery bindings pattern) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [patternValue (applyBindings bindings pattern)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (apply_bindings_returns state bindings pattern)
    after answers input output

theorem apply_bindings_derivation_iff (state : State) (bindings : Bindings) (pattern : Pattern)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (applyBindingsQuery bindings pattern) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [patternValue (applyBindings bindings pattern)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (apply_bindings_returns state bindings pattern)
    after answers input output

/-- The independently defined canonical substitution is the operation realized. -/
theorem instantiate_applyBindings_returns (state : State) (bindings : Bindings) (plan : PatternPlan) :
    PureReturns program [] state
      (a "gslt:rule:instantiate" [patternValue plan.erase, bindingsValue bindings]) state
      (patternValue (applyBindings bindings plan.erase)) := by
  simpa only [instantiate_eq_applyBindings] using instantiate_returns state bindings plan

/-- On this binder-free RHS fragment, the canonical scoped applier agrees as
well, for every authored left-hand side and binding payload. -/
theorem instantiate_scoped_returns (state : State) (lhs : Pattern) (bindings : Bindings) (plan : PatternPlan) :
    PureReturns program [] state
      (a "gslt:rule:instantiate" [patternValue plan.erase, bindingsValue bindings]) state
      (patternValue (applyBindingsScoped lhs bindings 0 plan.erase)) := by
  rw [applyBindingsScoped_zero_of_binderFree lhs bindings plan.erase (binderFree_erase plan)]
  exact instantiate_applyBindings_returns state bindings plan

def instantiateQuery (bindings : Bindings) (plan : PatternPlan) : Atom :=
  a "gslt:rule:instantiate" [patternValue plan.erase, bindingsValue bindings]

theorem instantiate_completed_iff (state : State) (bindings : Bindings) (plan : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (instantiateQuery bindings plan) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [patternValue (plan.instantiate bindings)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (instantiate_returns state bindings plan)
    after answers input output

theorem instantiate_derivation_iff (state : State) (bindings : Bindings) (plan : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (instantiateQuery bindings plan) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [patternValue (plan.instantiate bindings)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (instantiate_returns state bindings plan)
    after answers input output

/-! ## Ordered observations after premise execution -/

private abbrev resultsValue (results : List Bindings) : Atom :=
  encoded (encodeList bindingsTerm results)

private def resultsEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:instantiate-results")[0]'(by decide +kernel)

private def resultsEnvironment (pattern : Pattern) (results : List Bindings) : Subst :=
  [("results", resultsValue results), ("pattern", patternValue pattern)]

private def resultsConsBody : Atom :=
  a "let*" [.expression
    [.expression [v "value", a "gslt:rule:instantiate" [v "pattern", v "bindings"]],
     .expression [v "tail", a "gslt:rule:instantiate-results" [v "pattern", v "rest"]]],
    a "LCons" [v "value", v "tail"]]

private def resultsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "bindings", v "rest"], resultsConsBody)]

private theorem results_shape : resultsEquation.body =
    a "case" [v "results", .expression (resultsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem results_clause (pattern : Pattern) (results : List Bindings) :
    clauses program "gslt:rule:instantiate-results" [patternValue pattern, resultsValue results] =
      [.evaluate (resultsEnvironment pattern results) resultsEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:instantiate-results").filterMap _ = _
  rw [show equations "gslt:rule:instantiate-results" = [resultsEquation] from rfl]
  have formals : resultsEquation.arguments = [v "pattern", v "results"] := by decide +kernel
  simp [formals, resultsEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem results_call (caller : Subst) (state : State) (pattern : Pattern)
    (results : List Bindings) (one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [patternValue pattern, resultsValue results])
    (returned : PureReturns program (resultsEnvironment pattern results) state
      resultsEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:instantiate-results" [one, two]) state answer := by
  apply PureData.raw_authored_call_return program caller (resultsEnvironment pattern results) state state
    "gslt:rule:instantiate-results" [one, two] resultsEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact results_clause pattern results

private theorem results_body_returns (state : State) (pattern : Pattern) (results : List Bindings) :
    PureReturns program (resultsEnvironment pattern results) state resultsEquation.body state
      (patternsValue (results.map (fun bindings => applyBindings bindings pattern))) := by
  induction results with
  | nil =>
      let caller := resultsEnvironment pattern []
      rw [results_shape]
      simp only [List.map_nil, patternsValue, encoded, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "results") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ resultsCases (read_cases_encoded _) _ _ _
      · simpa [caller, resultsEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "results"
      · simp [resultsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons first rest ih =>
      let caller := resultsEnvironment pattern (first :: rest)
      let selected := ("rest", resultsValue rest) :: ("bindings", bindingsValue first) :: caller
      let headValue := patternValue (applyBindings first pattern)
      let headBound := ("value", headValue) :: selected
      let tailValue := patternsValue (rest.map (fun bindings => applyBindings bindings pattern))
      let tailBound := ("tail", tailValue) :: headBound
      rw [results_shape]
      apply case_returns program caller selected state state state (v "results")
        (resultsValue (first :: rest)) resultsConsBody _ _ resultsCases (read_cases_encoded _) _ _ _
      · simpa [caller, resultsEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "results"
      · simp [resultsCases, resultsEnvironment, caller, selected, resultsValue, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have headReturned := apply_bindings_captured_returns selected state first pattern
            (v "pattern") (v "bindings")
            (by simp [selected, caller, resultsEnvironment, applySubst, Subst.lookup])
        have headMatched : SpaceSemantics.matchBinding selected (v "value") headValue = some headBound := by
          simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound,
            selected, caller, resultsEnvironment]
        have tailReturned := results_call headBound state pattern rest (v "pattern") (v "rest") tailValue
            (by simp [headBound, selected, caller, resultsEnvironment, applySubst, Subst.lookup]) ih
        have tailMatched : SpaceSemantics.matchBinding headBound (v "tail") tailValue = some tailBound := by
          simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
            headBound, selected, caller, resultsEnvironment]
        have resultReturned : PureReturns program tailBound state (a "LCons" [v "value", v "tail"]) state
            (patternsValue ((first :: rest).map (fun bindings => applyBindings bindings pattern))) := by
          simpa [Constructor.head, List.map_cons, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
              tailBound, tailValue, headBound, headValue] using
            PureData.template_return program tailBound state _
              (constructor_variables .cons ["value", "tail"])
        have computed := PureData.let_bindings_return
          (PureData.BindingsReturn.cons headReturned headMatched
            (PureData.BindingsReturn.cons tailReturned tailMatched (.nil tailBound state))) state
          (a "LCons" [v "value", v "tail"]) _ resultReturned
        simpa only [resultsConsBody, List.map_cons, List.map_nil] using computed

/-- Ordered instantiation of complete canonical right-hand sides after premise execution. -/
theorem apply_bindings_results_captured_returns (caller : Subst) (state : State)
    (pattern : Pattern) (results : List Bindings) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [patternValue pattern, resultsValue results]) :
    PureReturns program caller state (a "gslt:rule:instantiate-results" [one, two]) state
      (patternsValue (results.map (fun bindings => applyBindings bindings pattern))) :=
  results_call caller state pattern results one two _ captured (results_body_returns state pattern results)

theorem apply_bindings_results_returns (state : State) (pattern : Pattern) (results : List Bindings) :
    PureReturns program [] state
      (a "gslt:rule:instantiate-results" [patternValue pattern, resultsValue results]) state
      (patternsValue (results.map (fun bindings => applyBindings bindings pattern))) :=
  apply_bindings_results_captured_returns [] state pattern results _ _ (by simp)

def applyBindingsResultsQuery (pattern : Pattern) (results : List Bindings) : Atom :=
  a "gslt:rule:instantiate-results" [patternValue pattern, resultsValue results]

theorem apply_bindings_results_derivation_iff (state : State) (pattern : Pattern)
    (results : List Bindings) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (applyBindingsResultsQuery pattern results) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [patternsValue (results.map (fun bindings => applyBindings bindings pattern))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (apply_bindings_results_returns state pattern results)
    after answers input output

/-- Every ordered premise result contributes exactly one RHS observation.
Equal observations from different bindings remain separate occurrences. -/
theorem instantiate_results_captured_returns (caller : Subst) (state : State)
    (plan : PatternPlan) (results : List Bindings) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [patternValue plan.erase, resultsValue results]) :
    PureReturns program caller state (a "gslt:rule:instantiate-results" [one, two]) state
      (patternsValue (results.map (fun bindings => plan.instantiate bindings))) := by
  simpa only [instantiate_eq_applyBindings] using
    apply_bindings_results_captured_returns caller state plan.erase results one two captured

theorem instantiate_results_returns (state : State) (plan : PatternPlan) (results : List Bindings) :
    PureReturns program [] state
      (a "gslt:rule:instantiate-results" [patternValue plan.erase, resultsValue results]) state
      (patternsValue (results.map (fun bindings => plan.instantiate bindings))) :=
  instantiate_results_captured_returns [] state plan results _ _ (by simp)

def instantiateResultsQuery (plan : PatternPlan) (results : List Bindings) : Atom :=
  a "gslt:rule:instantiate-results" [patternValue plan.erase, resultsValue results]

theorem instantiate_results_derivation_iff (state : State) (plan : PatternPlan)
    (results : List Bindings) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (instantiateResultsQuery plan results) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [patternsValue (results.map (fun bindings => plan.instantiate bindings))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (instantiate_results_returns state plan results)
    after answers input output

/-! ## Matching and RHS construction at the root -/

private def rootEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:apply-root")[0]'(by decide +kernel)

private def rootEnvironment (left right subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("right", patternValue right.erase),
   ("left", patternValue left.erase)]

private def rootSomeBody : Atom :=
  a "let" [v "value", a "gslt:rule:instantiate" [v "right", v "bindings"],
    a "LCons" [v "value", .symbol "LNil"]]

private def rootCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "bindings"], rootSomeBody)]

private theorem root_shape : rootEquation.body =
    a "case" [a "gslt:automata:bind" [v "left", v "subject"],
      .expression (rootCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem root_clause (left right subject : PatternPlan) :
    clauses program "gslt:rule:apply-root"
      [patternValue left.erase, patternValue right.erase, patternValue subject.erase] =
      [.evaluate (rootEnvironment left right subject) rootEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:apply-root").filterMap _ = _
  rw [show equations "gslt:rule:apply-root" = [rootEquation] from rfl]
  have formals : rootEquation.arguments = [v "left", v "right", v "subject"] := by decide +kernel
  simp [formals, rootEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem root_body_returns (state : State) (left right subject : PatternPlan) :
    PureReturns program (rootEnvironment left right subject) state rootEquation.body state
      (patternsValue ((matchPattern left.erase subject.erase).map (fun bindings => right.instantiate bindings))) := by
  let caller := rootEnvironment left right subject
  have matched := automata_captured_returns (by decide +kernel)
    (MatchAutomataBindingExecution.bind_captured_returns caller state left subject [v "left", v "subject"]
      (by simp [caller, rootEnvironment, applySubst, Subst.lookup]))
  rw [← MatchAutomataBindingExecution.bind_matches_singleton left subject]
  rw [root_shape]
  cases found : (matchPattern left.erase subject.erase).head? with
  | none =>
      simp only [Option.toList_none, List.map_nil, patternsValue, encoded,
        InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller caller state state state
        (a "gslt:automata:bind" [v "left", v "subject"]) (.symbol "None")
        (.symbol "LNil") (.symbol "LNil") _ rootCases (read_cases_encoded _) _ _ _
      · simpa [found, MatchAutomataBindingExecution.bindingsOptionTerm, CettaWireAtom.encode] using matched
      · simp [rootCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | some bindings =>
      let selected := ("bindings", bindingsValue bindings) :: caller
      let value := patternValue (right.instantiate bindings)
      let bound := ("value", value) :: selected
      simp only [Option.toList_some, List.map_cons, List.map_nil]
      apply case_returns program caller selected state state state
        (a "gslt:automata:bind" [v "left", v "subject"])
        (a "Some" [bindingsValue bindings]) rootSomeBody _ _ rootCases (read_cases_encoded _) _ _ _
      · simpa [found, MatchAutomataBindingExecution.bindingsOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using matched
      · simp [rootCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, caller, rootEnvironment]
      · have instantiated := instantiate_captured_returns selected state bindings right
            (v "right") (v "bindings")
            (by simp [selected, caller, rootEnvironment, applySubst, Subst.lookup])
        apply let_returns program selected bound state state state (v "value") _ _ value _ instantiated _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound,
            selected, caller, rootEnvironment]
        · have template : PureData.Template program (a "LCons" [v "value", .symbol "LNil"]) := by
            apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
            intro argument member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact .captured _
            · exact .symbol _
          simpa [InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup, bound, value] using
            PureData.template_return program bound state _ template

/-- Apply an admitted first-order pattern pair to the root only. A failed
match returns the empty observation list, and a successful match constructs
its contractum through the retained RHS helper. -/
theorem apply_root_captured_returns (caller : Subst) (state : State) (left right subject : PatternPlan)
    (one two three : Atom) (captured : [one, two, three].map (applySubst caller) =
      [patternValue left.erase, patternValue right.erase, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:apply-root" [one, two, three]) state
      (patternsValue ((matchPattern left.erase subject.erase).map (fun bindings => right.instantiate bindings))) := by
  apply PureData.raw_authored_call_return program caller (rootEnvironment left right subject) state state
    "gslt:rule:apply-root" [one, two, three] rootEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ (root_body_returns state left right subject)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact root_clause left right subject

theorem apply_root_returns (state : State) (left right subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:rule:apply-root" [patternValue left.erase, patternValue right.erase, patternValue subject.erase]) state
      (patternsValue ((matchPattern left.erase subject.erase).map (fun bindings => right.instantiate bindings))) :=
  apply_root_captured_returns [] state left right subject _ _ _ (by simp)

/-- The root primitive realizes the existing whole-row plan when its authored
premise list is empty. Conditional rows must execute their premises first. -/
theorem apply_root_rule_returns (state : State) (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (plan : RulePlan) (subject : PatternPlan) (premiseFree : plan.premises = []) :
    PureReturns program [] state
      (a "gslt:rule:apply-root" [patternValue plan.left.erase, patternValue plan.right.erase,
        patternValue subject.erase]) state (patternsValue (plan.run relations language subject.erase)) := by
  simpa only [RulePlan.run, premiseFree, runPremisePlans, List.map_cons, List.map_nil, ← List.map_eq_flatMap,
    run_eq_matchPattern] using apply_root_returns state plan.left plan.right subject

/-- A compiled premise-free source row keeps its full canonical interpreted
rule meaning in the actual target program. -/
theorem apply_root_compiled_returns (state : State)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (source : RewriteRule) (plan : RulePlan)
    (subject : PatternPlan) (accepted : compileRule? source = some plan)
    (premiseFree : source.premises = []) :
    PureReturns program [] state
      (a "gslt:rule:apply-root" [patternValue plan.left.erase, patternValue plan.right.erase,
        patternValue subject.erase]) state
      (patternsValue (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing
        .syntactic (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises relations)
        language recursiveStep source subject.erase)) := by
  have erased := erase_of_compileRule? source plan accepted
  have lengths := congrArg (fun row => row.premises.length) erased
  have empty : plan.premises = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [RulePlan.erase, erasePremisePlans, premiseFree] using lengths
  rw [← run_compileRule?_eq_applyRuleUsing relations language recursiveStep source plan subject.erase accepted]
  exact apply_root_rule_returns state relations language plan subject empty

def applyRootQuery (left right subject : PatternPlan) : Atom :=
  a "gslt:rule:apply-root" [patternValue left.erase, patternValue right.erase, patternValue subject.erase]

theorem apply_root_derivation_iff (state : State) (left right subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (applyRootQuery left right subject) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [patternsValue ((matchPattern left.erase subject.erase).map
          (fun bindings => right.instantiate bindings))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (apply_root_returns state left right subject)
    after answers input output

-- A missing variable stays a variable; absence is not a missing-result value.
example (state : State) :
    PureReturns program [] state (instantiateQuery [] (.metavariable "unbound")) state
      (patternValue (.fvar "unbound")) := by
  simpa [instantiateQuery, PatternPlan.instantiate] using
    instantiate_returns state [] (.metavariable "unbound")

-- The first matching binding wins, and its replacement is inserted once.
example (state : State) :
    PureReturns program [] state
      (instantiateQuery [("x", .fvar "y"), ("x", .apply "later" []), ("y", .apply "resolved" [])]
        (.metavariable "x")) state (patternValue (.fvar "y")) := by
  simpa [instantiateQuery, PatternPlan.instantiate] using
    instantiate_returns state
      [("x", .fvar "y"), ("x", .apply "later" []), ("y", .apply "resolved" [])] (.metavariable "x")

-- Replacement values may themselves contain binders; they remain opaque data.
example (state : State) :
    PureReturns program [] state
      (instantiateQuery [("x", .lambda "bound" (.bvar 0))] (.metavariable "x")) state
      (patternValue (.lambda "bound" (.bvar 0))) := by
  simpa [instantiateQuery, PatternPlan.instantiate] using
    instantiate_returns state [("x", .lambda "bound" (.bvar 0))] (.metavariable "x")

-- Recursive substitution would produce a different observation and is refused.
example (state : State) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (instantiateQuery [("x", .fvar "y"), ("y", .apply "resolved" [])] (.metavariable "x")) }
      (.complete state [patternValue (.apply "resolved" [])] [] []) := by
  intro returned
  have exactOutcome := (instantiate_derivation_iff state
    [("x", .fvar "y"), ("y", .apply "resolved" [])] (.metavariable "x") state _ [] []).mp returned
  have unequal :
      [patternValue (.apply "resolved" [])] ≠
        [patternValue ((PatternPlan.metavariable "x").instantiate
          [("x", .fvar "y"), ("y", .apply "resolved" [])])] := by
    simp [PatternPlan.instantiate, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  exact unequal exactOutcome.2.1

namespace Controls

/-- Reusable inputs; expected payloads come from canonical instantiation. -/
structure Fixture where
  name : String
  plan : PatternPlan
  bindings : Bindings

def unbound : Fixture :=
  ⟨"unbound-variable", .metavariable "x", []⟩

def firstBinding : Fixture :=
  ⟨"duplicate-binding-first-wins", .metavariable "x",
    [("x", .apply "first" []), ("x", .apply "later" [])]⟩

def opaqueReplacement : Fixture :=
  ⟨"replacement-is-not-recursively-substituted", .metavariable "x",
    [("x", .fvar "y"), ("y", .apply "resolved" [])]⟩

def fixtures : List Fixture :=
  [unbound,
   ⟨"bound-index", .bound 3, [("x", .apply "ignored" [])]⟩,
   ⟨"nullary-constructor", .application "unit" [], [("x", .apply "ignored" [])]⟩,
   ⟨"ordered-children", .application "triple" [.metavariable "x", .bound 2, .metavariable "y"],
     [("y", .apply "second" []), ("x", .apply "first" [])]⟩,
   ⟨"nested-repeated-variable", .application "pair"
       [.metavariable "x", .application "wrap" [.metavariable "x"]],
     [("x", .apply "payload" [])]⟩,
   firstBinding,
   opaqueReplacement,
   ⟨"replacement-containing-a-binder", .metavariable "x", [("x", .lambda "bound" (.bvar 0))]⟩]

def Fixture.queryTerm (fixture : Fixture) : Term :=
  .application "gslt:rule:instantiate"
    [InferenceCettaWire.encodePattern fixture.plan.erase, bindingsTerm fixture.bindings]

def Fixture.expectedTerm (fixture : Fixture) : Term :=
  InferenceCettaWire.encodePattern (fixture.plan.instantiate fixture.bindings)

/-- Incorrect observations exercise absence, first-binding priority and opaque
replacement separately from the positive canonical result controls. -/
def incorrectResults : List (Fixture × Pattern) :=
  [(unbound, .apply "unexpected" []),
   (firstBinding, .apply "later" []),
   (opaqueReplacement, .apply "resolved" [])]

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (CettaWireAtom.encode fixture.queryTerm) state
      (CettaWireAtom.encode fixture.expectedTerm) := by
  simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    instantiate_returns state fixture.bindings fixture.plan

/-- Composition controls use the same canonical plans as the public laws. -/
inductive ObservationInput where
  | results (right : PatternPlan) (bindings : List Bindings)
  | root (left right subject : PatternPlan)
  | full (bindings : Bindings) (pattern : Pattern)
  | lift (cutoff shift : Nat) (pattern : Pattern)
  | eliminate (depth : Nat) (replacement body : Pattern)

structure ObservationFixture where
  name : String
  input : ObservationInput

def fullLambda : ObservationFixture :=
  ⟨"full-lambda-preserves-display-and-opaque-binding", .full
    [("x", .fvar "inner"), ("inner", .apply "resolved" [])]
    (.lambda "display" (.apply "body" [.bvar 0, .fvar "x"]))⟩

def fullSubstitution : ObservationFixture :=
  ⟨"full-substitution-eliminates-explicit-node", .full []
    (.subst (.apply "pair" [.bvar 0, .bvar 1]) (.apply "replacement" []))⟩

def fullRestOpaque : ObservationFixture :=
  ⟨"full-rest-residuals-remain-opaque", .full
    [("rest", .collection .vec [.fvar "inner"] none), ("inner", .apply "resolved" [])]
    (.collection .vec [] (some "rest"))⟩

def fullRestDuplicates : ObservationFixture :=
  ⟨"full-rest-retains-order-and-duplicates", .full
    [("rest", .collection .hashBag [.apply "a" [], .apply "a" [], .apply "b" []] none)]
    (.collection .hashBag [.apply "first" []] (some "rest"))⟩

def liftNested : ObservationFixture :=
  ⟨"lift-nested-lambda-cutoff", .lift 0 2
    (.lambda "display" (.apply "pair" [.bvar 0, .bvar 1]))⟩

def eliminateLater : ObservationFixture :=
  ⟨"eliminate-decrements-later-index", .eliminate 1 (.apply "replacement" []) (.bvar 3)⟩

def generalFixtures : List ObservationFixture :=
  [⟨"full-missing-binding-remains-visible", .full [] (.fvar "missing")⟩,
   ⟨"full-first-binding-wins", .full
     [("x", .apply "first" []), ("x", .apply "later" [])] (.fvar "x")⟩,
   fullLambda,
   ⟨"full-multilambda-preserves-arity-and-displays", .full [("x", .apply "payload" [])]
     (.multiLambda 2 ["left", "right"] (.apply "body" [.bvar 1, .fvar "x"]))⟩,
   ⟨"full-multilambda-metadata-is-preserved-verbatim", .full []
     (.multiLambda 2 ["one-display"] (.bvar 1))⟩,
   fullSubstitution,
   ⟨"full-substitution-lifts-replacement-under-lambda", .full []
     (.subst (.lambda "display" (.apply "pair" [.bvar 0, .bvar 1])) (.bvar 0))⟩,
   ⟨"full-substitution-instantiates-both-inputs-first", .full
     [("body", .bvar 0), ("replacement", .apply "payload" [])]
     (.subst (.fvar "body") (.fvar "replacement"))⟩,
   ⟨"full-nested-explicit-substitution", .full []
     (.subst (.subst (.bvar 1) (.apply "inner" [])) (.apply "outer" []))⟩,
   ⟨"full-closed-collection-instantiates-explicit-elements", .full [("x", .apply "payload" [])]
     (.collection .vec [.fvar "x", .bvar 0, .fvar "x"] none)⟩,
   ⟨"full-unbound-rest-retained", .full [] (.collection .vec [.apply "first" []] (some "rest"))⟩,
   fullRestOpaque,
   fullRestDuplicates,
   ⟨"full-wrong-kind-rest-retained", .full
     [("rest", .collection .hashSet [.apply "payload" []] none)]
     (.collection .vec [.apply "first" []] (some "rest"))⟩,
   ⟨"full-open-rest-retained", .full
     [("rest", .collection .vec [.apply "payload" []] (some "nested"))]
     (.collection .vec [.apply "first" []] (some "rest"))⟩,
   ⟨"full-noncollection-rest-retained", .full [("rest", .apply "payload" [])]
     (.collection .vec [] (some "rest"))⟩,
   ⟨"full-first-rest-binding-wins", .full
     [("rest", .collection .vec [.apply "first" []] none),
      ("rest", .collection .vec [.apply "later" []] none)]
     (.collection .vec [] (some "rest"))⟩,
   ⟨"lift-before-cutoff-unchanged", .lift 2 3 (.bvar 1)⟩,
   ⟨"lift-at-cutoff", .lift 2 3 (.bvar 2)⟩,
   ⟨"lift-free-variable-unchanged", .lift 0 3 (.fvar "x")⟩,
   liftNested,
   ⟨"lift-multilambda-cutoff", .lift 0 2
     (.multiLambda 2 ["left", "right"] (.apply "pair" [.bvar 1, .bvar 2]))⟩,
   ⟨"lift-substitution-has-distinct-child-cutoffs", .lift 0 2
     (.subst (.apply "pair" [.bvar 0, .bvar 1]) (.bvar 0))⟩,
   ⟨"lift-collection-retains-rest-metadata", .lift 0 2
     (.collection .vec [.bvar 0] (some "rest"))⟩,
   ⟨"eliminate-earlier-index-unchanged", .eliminate 2 (.apply "replacement" []) (.bvar 1)⟩,
   ⟨"eliminate-at-depth-lifts-replacement", .eliminate 2 (.bvar 0) (.bvar 2)⟩,
   eliminateLater,
   ⟨"eliminate-under-lambda", .eliminate 0 (.bvar 0)
     (.lambda "display" (.apply "pair" [.bvar 0, .bvar 1]))⟩,
   ⟨"eliminate-under-multilambda", .eliminate 0 (.bvar 0)
     (.multiLambda 2 ["left", "right"] (.apply "pair" [.bvar 1, .bvar 2]))⟩,
   ⟨"eliminate-retains-nested-substitution-level", .eliminate 0 (.apply "replacement" [])
     (.subst (.bvar 1) (.bvar 0))⟩,
   ⟨"eliminate-collection-retains-rest-metadata", .eliminate 0 (.apply "replacement" [])
     (.collection .vec [.bvar 0, .bvar 1] (some "rest"))⟩]

def observationFixtures : List ObservationFixture :=
  [⟨"results-empty", .results (.metavariable "x") []⟩,
   ⟨"results-singleton", .results (.application "out" [.metavariable "x"])
     [[("x", .apply "a" [])]]⟩,
   ⟨"results-retain-duplicates", .results (.metavariable "x")
     [[("x", .apply "a" [])], [("x", .apply "a" [])], [("x", .apply "b" [])]]⟩,
   ⟨"results-retain-order-and-opaque-payload", .results (.metavariable "x")
     [[("x", .fvar "inner"), ("inner", .apply "resolved" [])],
      [("x", .apply "last" [])]]⟩,
   ⟨"root-nullary-hit", .root (.application "a" []) (.application "b" []) (.application "a" [])⟩,
   ⟨"root-nullary-miss", .root (.application "a" []) (.application "b" []) (.application "c" [])⟩,
   ⟨"root-repeated-variable-hit", .root
     (.application "pair" [.metavariable "x", .metavariable "x"])
     (.application "out" [.metavariable "x"])
     (.application "pair" [.application "a" [], .application "a" []])⟩,
   ⟨"root-repeated-variable-conflict", .root
     (.application "pair" [.metavariable "x", .metavariable "x"])
     (.application "out" [.metavariable "x"])
     (.application "pair" [.application "a" [], .application "b" []])⟩,
   ⟨"root-nested-rhs", .root (.application "wrap" [.metavariable "x"])
     (.application "pair" [.metavariable "x", .application "wrap" [.metavariable "x"]])
     (.application "wrap" [.application "payload" []])⟩,
   ⟨"root-child-match-grants-no-permission", .root
     (.application "a" []) (.application "b" [])
     (.application "wrap" [.application "a" []])⟩,
   ⟨"root-unbound-rhs-variable-remains-visible", .root
     (.application "a" []) (.metavariable "unbound") (.application "a" [])⟩]

def ObservationFixture.queryTerm (fixture : ObservationFixture) : Term :=
  match fixture.input with
  | .results right bindings => .application "gslt:rule:instantiate-results"
      [InferenceCettaWire.encodePattern right.erase, encodeList bindingsTerm bindings]
  | .root left right subject => .application "gslt:rule:apply-root"
      [InferenceCettaWire.encodePattern left.erase, InferenceCettaWire.encodePattern right.erase,
       InferenceCettaWire.encodePattern subject.erase]
  | .full bindings pattern => .application "gslt:rule:instantiate"
      [InferenceCettaWire.encodePattern pattern, bindingsTerm bindings]
  | .lift cutoff shift pattern => .application "gslt:rule:lift-bvars"
      [.natural cutoff, .natural shift, InferenceCettaWire.encodePattern pattern]
  | .eliminate depth replacement body => .application "gslt:rule:instantiate-bvar-at"
      [.natural depth, InferenceCettaWire.encodePattern replacement, InferenceCettaWire.encodePattern body]

def ObservationFixture.expectedTerm (fixture : ObservationFixture) : Term :=
  match fixture.input with
  | .results right bindings => InferenceCettaWire.encodePatterns (bindings.map (right.instantiate ·))
  | .root left right subject =>
      InferenceCettaWire.encodePatterns ((matchPattern left.erase subject.erase).map (right.instantiate ·))
  | .full bindings pattern => InferenceCettaWire.encodePattern (applyBindings bindings pattern)
  | .lift cutoff shift pattern =>
      InferenceCettaWire.encodePattern (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift pattern)
  | .eliminate depth replacement body =>
      InferenceCettaWire.encodePattern
        (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth replacement body)

theorem ObservationFixture.returns (fixture : ObservationFixture) (state : State) :
    PureReturns program [] state (CettaWireAtom.encode fixture.queryTerm) state
      (CettaWireAtom.encode fixture.expectedTerm) := by
  rcases fixture with ⟨name, input⟩
  cases input with
  | results right bindings =>
      simpa [ObservationFixture.queryTerm, ObservationFixture.expectedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, resultsValue] using
        instantiate_results_returns state right bindings
  | root left right subject =>
      simpa [ObservationFixture.queryTerm, ObservationFixture.expectedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        apply_root_returns state left right subject
  | full bindings pattern =>
      simpa [ObservationFixture.queryTerm, ObservationFixture.expectedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using apply_bindings_returns state bindings pattern
  | lift cutoff shift pattern =>
      simpa [ObservationFixture.queryTerm, ObservationFixture.expectedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using lift_bvars_returns state cutoff shift pattern
  | eliminate depth replacement body =>
      simpa [ObservationFixture.queryTerm, ObservationFixture.expectedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using instantiate_bvar_at_returns state depth replacement body

def incorrectGeneralResults : List (ObservationFixture × Pattern) :=
  [(fullLambda, .lambda "wrong-display" (.apply "body" [.bvar 0, .fvar "inner"])),
   (fullSubstitution, .subst (.apply "pair" [.bvar 0, .bvar 1]) (.apply "replacement" [])),
   (fullRestOpaque, .collection .vec [.apply "resolved" []] none),
   (fullRestDuplicates, .collection .hashBag [.apply "first" [], .apply "a" [], .apply "b" []] none),
   (liftNested, .lambda "display" (.apply "pair" [.bvar 0, .bvar 1])),
   (eliminateLater, .bvar 3)]

theorem incorrect_general_results_are_distinct :
    ∀ result ∈ incorrectGeneralResults,
      InferenceCettaWire.encodePattern result.2 ≠ result.1.expectedTerm := by
  decide +kernel


end Controls

namespace RowLookup

private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev listValue (values : List Term) : Atom := encoded (encodeList id values)
private def optionTerm : Option Term → Term
  | none => .symbol "None"
  | some value => .application "Some" [value]
private abbrev optionValue (value : Option Term) : Atom := encoded (optionTerm value)

private def rowAtEquation : SpaceSemantics.Equation :=
  (RuleExecutionProgram.equations "gslt:rule:row-at")[0]'(by decide +kernel)

private def rowAtEnvironment (index : Nat) (values : List Term) : Subst :=
  [("rewrites", listValue values), ("index", number index)]

private def rowAtNextBody : Atom :=
  a "let" [v "previous", a "-" [v "index", number 1],
    a "gslt:rule:row-at" [v "previous", v "rest"]]

private def rowAtConsBody : Atom :=
  a "if" [a "==" [v "index", number 0], a "Some" [v "row"], rowAtNextBody]

private def rowAtCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"), (a "LCons" [v "row", v "rest"], rowAtConsBody)]

private theorem rowAt_shape : rowAtEquation.body =
    a "case" [v "rewrites", .expression (rowAtCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem rowAt_clause (index : Nat) (values : List Term) :
    clauses program "gslt:rule:row-at" [number index, listValue values] =
      [.evaluate (rowAtEnvironment index values) rowAtEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have filtered : program.equations.filter (fun row => row.head == "gslt:rule:row-at") =
      RuleExecutionProgram.equations "gslt:rule:row-at" := by rfl
  rw [filtered]
  rw [show RuleExecutionProgram.equations "gslt:rule:row-at" = [rowAtEquation] from rfl]
  have formals : rowAtEquation.arguments = [v "index", v "rewrites"] := by decide +kernel
  simp [formals, rowAtEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem rowAt_call (caller : Subst) (state : State) (index : Nat) (values : List Term)
    (one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, listValue values])
    (returned : PureReturns program (rowAtEnvironment index values) state rowAtEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state answer := by
  apply PureData.raw_authored_call_return program caller (rowAtEnvironment index values) state state
    "gslt:rule:row-at" [one, two] rowAtEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact rowAt_clause index values

private theorem rowAt_body_returns (state : State) (index : Nat) (values : List Term) :
    PureReturns program (rowAtEnvironment index values) state rowAtEquation.body state
      (optionValue values[index]?) := by
  induction values generalizing index with
  | nil =>
      let caller := rowAtEnvironment index []
      rw [rowAt_shape]
      apply case_returns program caller caller state state state (v "rewrites") (.symbol "LNil")
        (.symbol "None") (.symbol "None") _ rowAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, rowAtEnvironment, listValue, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "rewrites"
      · simp [rowAtCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "None"
  | cons value values ih =>
      let caller := rowAtEnvironment index (value :: values)
      let selected := ("rest", listValue values) :: ("row", encoded value) :: caller
      have tested := CettaWireAtom.equality_evaluated_returns program selected state (.natural index) (.natural 0)
        (v "index") (number 0) (by decide +kernel) (by decide +kernel)
        (by simpa [selected, caller, rowAtEnvironment, applySubst, Subst.lookup] using
          variable_returns program selected state "index")
        (grounded_returns program selected state (.int 0))
      rw [rowAt_shape]
      apply case_returns program caller selected state state state (v "rewrites")
        (listValue (value :: values)) rowAtConsBody _ _ rowAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, rowAtEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "rewrites"
      · simp [rowAtCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, rowAtEnvironment]
      · unfold rowAtConsBody
        apply if_returns program selected state state state _ _ _ _ _ tested
        cases index with
        | zero =>
            simp only [decide_true]
            rw [show (Effects.boolean true == Effects.boolean true) = true from by decide +kernel]
            simp only [↓reduceIte, List.getElem?_cons_zero]
            change PureReturns program selected state (a "Some" [v "row"]) state
              (a "Some" [encoded value])
            simpa [applySubst, Subst.lookup, selected] using
              constructor_variables_return program selected state "Some" ["row"]
                (by decide +kernel) (by decide)
        | succ index =>
            simp only [Term.natural.injEq, Nat.add_one_ne_zero, decide_false]
            rw [show (Effects.boolean false == Effects.boolean true) = false from by decide +kernel]
            simp only [Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_succ]
            let bound := ("previous", number index) :: selected
            have previous : PureReturns program selected state (a "-" [v "index", number 1]) state (number index) := by
              apply native_binary_call_returns program selected state state state state "-"
                (v "index") (number 1) (number (index + 1)) (number 1) (number index)
                (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
              · simpa [selected, caller, rowAtEnvironment, applySubst, Subst.lookup] using
                  variable_returns program selected state "index"
              · exact grounded_returns program selected state (.int 1)
              · change (Except.ok (state, [Atom.grounded (.int (((index + 1 : Nat) : Int) - 1))]) :
                    Effects.Result) = Except.ok (state, [.grounded (.int (index : Int))])
                simp
            unfold rowAtNextBody
            apply let_returns program selected bound state state state (v "previous") _ _ _ _ previous _ _
            · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound,
                selected, caller, rowAtEnvironment]
            · exact rowAt_call bound state index values (v "previous") (v "rest") _
                (by simp [bound, selected, caller, rowAtEnvironment, applySubst, Subst.lookup]) (ih index)

theorem row_at_captured_returns (caller : Subst) (state : State) (index : Nat) (values : List Term)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [CettaWireAtom.encode (.natural index), CettaWireAtom.encode (encodeList id values)]) :
    PureReturns program caller state (.expression [.symbol "gslt:rule:row-at", one, two]) state
      (CettaWireAtom.encode (MatchAutomataBindingExecution.payloadOptionTerm values[index]?)) := by
  have returned := rowAt_call caller state index values one two _ captured (rowAt_body_returns state index values)
  cases found : values[index]? <;>
    simpa [found, optionValue, optionTerm, MatchAutomataBindingExecution.payloadOptionTerm] using returned

theorem row_at_returns (state : State) (index : Nat) (values : List Term) :
    PureReturns program [] state
      (.expression [.symbol "gslt:rule:row-at", CettaWireAtom.encode (.natural index),
        CettaWireAtom.encode (encodeList id values)]) state
      (CettaWireAtom.encode (MatchAutomataBindingExecution.payloadOptionTerm values[index]?)) :=
  row_at_captured_returns [] state index values _ _ (by simp)

end RowLookup

/-! ## Scoped capture and contextual-value operations

These retained equations realize the existing RuleBinding recovery and
occurrence assignments, ContextSubstitution, and ScopedRuleMatching.assign.
The finite descriptors denote exactly those canonical assignments. Their
substitution operation preserves explicit substitution nodes; RHS
applyBindings above uses its distinct canonical elimination operation.
These local operations do not validate declaration sites or authorize rewrites.
-/

namespace ScopedCapture

open Mettapedia.OSLF.MeTTaIL
open scoped ProgramQuotation

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)

attribute [local simp] a v encoded number patternValue patternsValue

private inductive Helper where
  | scoped | scopedList | index | spine | assignment | substitute | substituteList
  | instantiate | recover | assign

private abbrev Helper.head : Helper → String
  | .scoped => "gslt:rule:scope-well-scoped"
  | .scopedList => "gslt:rule:scope-well-scoped-list"
  | .index => "gslt:rule:scope-index"
  | .spine => "gslt:rule:scope-variable-spine"
  | .assignment => "gslt:rule:scope-assignment"
  | .substitute => "gslt:rule:scope-substitute"
  | .substituteList => "gslt:rule:scope-substitute-list"
  | .instantiate => "gslt:rule:scope-instantiate-value"
  | .recover => "gslt:rule:scope-recover-value"
  | .assign => "gslt:rule:scope-assign"

private def Helper.names : Helper → List String
  | .scoped => ["depth", "pattern"]
  | .scopedList => ["depth", "patterns"]
  | .index => ["index", "indices"]
  | .spine => ["depth", "arguments"]
  | .assignment => ["assignment", "index"]
  | .substitute => ["assignment", "prefix", "pattern"]
  | .substituteList => ["assignment", "prefix", "patterns"]
  | .instantiate => ["value", "ambient", "depth", "arguments"]
  | .recover => ["dependencies", "ambient", "depth", "arguments", "target"]
  | .assign => ["assignment", "name", "value"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  ((program.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel))

private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  have rows : program.equations.filter (fun row => row.head == helper.head) = [equation helper] := by
    cases helper <;> rfl
  rw [rows]
  have arguments : (equation helper).arguments = helper.names.map v := by
    cases helper <;> decide +kernel
  simp only [List.filterMap_cons, List.filterMap_nil, arguments]
  rw [PureData.match_variable_values helper.names values []
    (by cases helper <;> decide) length (by intro name member; rfl)]
  simp [environment]

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl <;> first | omega | decide +kernel

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem add_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "+" [v first, v second]) state (number (left + right)) := by
  apply native_variable_call_returns program caller state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

private theorem lt_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "<" [v first, v second]) state
      (Effects.boolean (decide (left < right))) := by
  apply native_variable_call_returns program caller state state "<" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simp [number, encoded, CettaWireAtom.encode]

private inductive ScopeForm where | pattern | patterns

private def ScopeForm.helper : ScopeForm → Helper
  | .pattern => .scoped
  | .patterns => .scopedList

private def ScopeForm.formal : ScopeForm → String
  | .pattern => "pattern"
  | .patterns => "patterns"

attribute [local simp] ScopeForm.helper ScopeForm.formal

private def scopeBinderBody (many : Bool) : Atom :=
  a "let" [v "next", a "+" [v "depth", if many then v "arity" else number 1],
    a Helper.scoped.head [v "next", v "body"]]

private def scopeSubstBody : Atom :=
  a "let" [v "next", a "+" [v "depth", number 1],
    a "if" [a Helper.scoped.head [v "next", v "body"],
      a Helper.scoped.head [v "depth", v "replacement"], (Effects.boolean false)]]

private def scopeListBody : Atom :=
  a "if" [a Helper.scoped.head [v "depth", v "pattern"],
    a Helper.scopedList.head [v "depth", v "rest"], (Effects.boolean false)]

private def scopeCases : ScopeForm → SpaceSemantics.Cases
  | .pattern =>
      [(a "Var" [v "index"], a "<" [v "index", v "depth"]),
       (a "FVar" [v "name"], (Effects.boolean true)),
       (a "PApp" [v "head", v "children"], a Helper.scopedList.head [v "depth", v "children"]),
       (a "PLam" [v "binder", v "body"], scopeBinderBody false),
       (a "PMultiLam" [v "arity", v "binders", v "body"], scopeBinderBody true),
       (a "PSubst" [v "body", v "replacement"], scopeSubstBody),
       (a "PCollection" [v "kind", v "elements", v "rest"],
         a Helper.scopedList.head [v "depth", v "elements"]),
       (v "invalid", (Effects.boolean false))]
  | .patterns =>
      [(.symbol "LNil", (Effects.boolean true)),
       (a "LCons" [v "pattern", v "rest"], scopeListBody),
       (v "invalid", (Effects.boolean false))]

private theorem scope_shape (form : ScopeForm) : (equation form.helper).body =
    a "case" [v form.formal,
      .expression ((scopeCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private theorem scope_case_returns (form : ScopeForm) (state : State) (depth : Nat)
    (value : Atom) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (environment form.helper [number depth, value])
      value (scopeCases form) = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a form.helper.head [number depth, value]) state answer := by
  apply helper_call form.helper [] state [number depth, value] [number depth, value] answer
    (by cases form <;> rfl) (by simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [scope_shape]
  apply case_returns program (environment form.helper [number depth, value]) selected state state state
    (v form.formal) value body answer _ (scopeCases form) (read_cases_encoded _) _ matched returned
  cases form with
  | pattern =>
      simpa [environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns program (environment .scoped [number depth, value]) state "pattern"
  | patterns =>
      simpa [environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns program (environment .scopedList [number depth, value]) state "patterns"

private theorem scope_capture (form : ScopeForm) (caller : Subst) (state : State)
    (depth : Nat) (value one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [number depth, value])
    (returned : PureReturns program [] state (a form.helper.head [number depth, value]) state answer) :
    PureReturns program caller state (a form.helper.head [one, two]) state answer :=
  helper_capture form.helper caller state [one, two] [number depth, value] answer
    (by cases form <;> rfl) captured returned

private theorem scope_list_from_elements (state : State) (depth : Nat) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a Helper.scoped.head [number depth, patternValue pattern]) state
      (Effects.boolean (pattern.isWellScopedAt depth))) :
    PureReturns program [] state (a Helper.scopedList.head [number depth, patternsValue patterns]) state
      (Effects.boolean (Pattern.isWellScopedListAt depth patterns)) := by
  induction patterns with
  | nil =>
      simp only [patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
        Pattern.isWellScopedListAt]
      change PureReturns program [] state (a Helper.scopedList.head [number depth, .symbol "LNil"])
        state (Effects.boolean true)
      apply scope_case_returns .patterns state depth (.symbol "LNil")
        (environment .scopedList [number depth, .symbol "LNil"]) ((Effects.boolean true))
      · simp [scopeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program _ state (.bool true)
  | cons pattern patterns ih =>
      let caller := environment .scopedList [number depth, patternsValue (pattern :: patterns)]
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      apply scope_case_returns .patterns state depth (patternsValue (pattern :: patterns))
        selected scopeListBody
      · simp [scopeCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · apply bool_if_returns selected state _ (pattern.isWellScopedAt depth) _ _ _
        · exact scope_capture .pattern selected state depth (patternValue pattern) (v "depth")
            (v "pattern") _ (by simp [selected, caller, environment, Helper.names, applySubst,
              Subst.lookup]) (elements pattern (by simp))
        · cases scopeResult : pattern.isWellScopedAt depth with
          | false =>
              simpa [Effects.boolean, scopeListBody, scopeResult, Pattern.isWellScopedListAt] using
                grounded_returns program selected state (.bool false)
          | true =>
              simpa [Effects.boolean, scopeListBody, scopeResult, Pattern.isWellScopedListAt] using
                scope_capture .patterns selected state depth (patternsValue patterns) (v "depth")
                  (v "rest") _ (by simp [selected, caller, environment, Helper.names, applySubst,
                    Subst.lookup]) (ih (fun child member => elements child (List.mem_cons_of_mem _ member)))

theorem well_scoped_returns (state : State) (pattern : Pattern) (depth : Nat) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-well-scoped" :: [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePattern pattern)])) state
      (Effects.boolean (pattern.isWellScopedAt depth)) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      let caller := environment .scoped [number depth, patternValue (.bvar index)]
      let selected := ("index", number index) :: caller
      apply scope_case_returns .pattern state depth (patternValue (.bvar index)) selected
        (a "<" [v "index", v "depth"])
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · exact lt_variables_returns selected state index depth "index" "depth"
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
  | hfvar name =>
      let caller := environment .scoped [number depth, patternValue (.fvar name)]
      let selected := ("name", encoded (.string name)) :: caller
      apply scope_case_returns .pattern state depth (patternValue (.fvar name)) selected ((Effects.boolean true))
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · exact grounded_returns program selected state (.bool true)
  | happly head children ih =>
      let caller := environment .scoped [number depth, patternValue (.apply head children)]
      let selected := ("children", patternsValue children) :: ("head", encoded (.string head)) :: caller
      apply scope_case_returns .pattern state depth (patternValue (.apply head children)) selected
        (a Helper.scopedList.head [v "depth", v "children"])
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · exact scope_capture .patterns selected state depth (patternsValue children) (v "depth")
          (v "children") _ (by simp [selected, caller, environment, Helper.names, applySubst,
            Subst.lookup]) (scope_list_from_elements state depth children (fun child member => ih child member depth))
  | hlambda binder body ih =>
      let caller := environment .scoped [number depth, patternValue (.lambda binder body)]
      let selected := ("body", patternValue body) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let bound := ("next", number (depth + 1)) :: selected
      apply scope_case_returns .pattern state depth (patternValue (.lambda binder body)) selected
        (scopeBinderBody false)
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · apply named_let_returns selected state "next" _ (number (depth + 1))
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · exact add_one_returns selected state depth "depth"
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        · exact scope_capture .pattern bound state (depth + 1) (patternValue body)
            (v "next") (v "body") _ (by simp [bound, selected, caller, environment, Helper.names,
              applySubst, Subst.lookup]) (ih (depth + 1))
  | hmultiLambda arity binders body ih =>
      let caller := environment .scoped [number depth, patternValue (.multiLambda arity binders body)]
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", number arity) :: caller
      let bound := ("next", number (depth + arity)) :: selected
      apply scope_case_returns .pattern state depth (patternValue (.multiLambda arity binders body)) selected
        (scopeBinderBody true)
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · apply named_let_returns selected state "next" _ (number (depth + arity))
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · exact add_variables_returns selected state depth arity "depth" "arity"
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        · exact scope_capture .pattern bound state (depth + arity) (patternValue body)
            (v "next") (v "body") _ (by simp [bound, selected, caller, environment, Helper.names,
              applySubst, Subst.lookup]) (ih (depth + arity))
  | hsubst body replacement bodyIH replacementIH =>
      let caller := environment .scoped [number depth, patternValue (.subst body replacement)]
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      let bound := ("next", number (depth + 1)) :: selected
      apply scope_case_returns .pattern state depth (patternValue (.subst body replacement)) selected scopeSubstBody
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · apply named_let_returns selected state "next" _ (number (depth + 1))
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · exact add_one_returns selected state depth "depth"
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        · apply bool_if_returns bound state _ (body.isWellScopedAt (depth + 1))
          · exact scope_capture .pattern bound state (depth + 1) (patternValue body)
              (v "next") (v "body") _ (by simp [bound, selected, caller, environment, Helper.names,
                applySubst, Subst.lookup]) (bodyIH (depth + 1))
          · cases scopeResult : body.isWellScopedAt (depth + 1) with
            | false =>
                simpa [Effects.boolean, scopeResult, Pattern.isWellScopedAt] using grounded_returns program bound state (.bool false)
            | true =>
                simpa [Effects.boolean, scopeResult, Pattern.isWellScopedAt] using
                  scope_capture .pattern bound state depth (patternValue replacement)
                    (v "depth") (v "replacement") _
                    (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                    (replacementIH depth)
  | hcollection kind elements rest ih =>
      let caller := environment .scoped [number depth, patternValue (.collection kind elements rest)]
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      apply scope_case_returns .pattern state depth (patternValue (.collection kind elements rest)) selected
        (a Helper.scopedList.head [v "depth", v "elements"])
      · simp [scopeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          environment, Helper.names]
      · exact scope_capture .patterns selected state depth (patternsValue elements) (v "depth")
          (v "elements") _ (by simp [selected, caller, environment, Helper.names, applySubst,
            Subst.lookup]) (scope_list_from_elements state depth elements (fun child member => ih child member depth))

theorem well_scoped_list_returns (state : State) (patterns : List Pattern) (depth : Nat) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-well-scoped-list" :: [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns patterns)])) state
      (Effects.boolean (Pattern.isWellScopedListAt depth patterns)) :=
  scope_list_from_elements state depth patterns (fun pattern _ => well_scoped_returns state pattern depth)

theorem well_scoped_captured_returns (caller : Subst) (state : State) (pattern : Pattern) (depth : Nat)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePattern pattern)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-well-scoped" :: [one, two])) state
      (Effects.boolean (pattern.isWellScopedAt depth)) :=
  scope_capture .pattern caller state depth (patternValue pattern) one two _ captured
    (well_scoped_returns state pattern depth)

theorem well_scoped_list_captured_returns (caller : Subst) (state : State) (patterns : List Pattern) (depth : Nat)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns patterns)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-well-scoped-list" :: [one, two])) state
      (Effects.boolean (Pattern.isWellScopedListAt depth patterns)) :=
  scope_capture .patterns caller state depth (patternsValue patterns) one two _ captured
    (well_scoped_list_returns state patterns depth)

def naturalOptionTerm : Option Nat → Term
  | none => .symbol "None"
  | some value => .application "Some" [.natural value]

private abbrev indicesValue (indices : List Nat) : Atom :=
  encoded (InferenceCettaWire.encodeList Term.natural indices)

attribute [local simp] indicesValue

private def indexResult (index : Nat) (indices : List Nat) : Option Nat :=
  if index ∈ indices then some (indices.idxOf index) else none

private theorem index_result_cons (index first : Nat) (indices : List Nat) :
    indexResult index (first :: indices) =
      if index = first then some 0 else (indexResult index indices).map (· + 1) := by
  by_cases same : index = first
  · subst first; simp [indexResult]
  · by_cases member : index ∈ indices
    · simp [indexResult, same, member, Ne.symm same]
    · simp [indexResult, same, member]

private theorem some_returns (caller : Subst) (state : State) (code value : Atom)
    (returned : PureReturns program caller state code state value) :
    PureReturns program caller state (a "Some" [code]) state (a "Some" [value]) := by
  apply PureData.constructor_return program caller state "Some" [code] [value]
    (by decide +kernel) (by decide)
  exact .cons returned .nil

private def indexNextBody : Atom :=
  a "let" [v "next", a "+" [v "position", number 1], a "Some" [v "next"]]

private def indexResultCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "position"], indexNextBody)]

private def indexConsBody : Atom :=
  a "if" [a "==" [v "index", v "first"], a "Some" [number 0],
    a "case" [a Helper.index.head [v "index", v "rest"],
      .expression (indexResultCases.map fun row => .expression [row.1, row.2])]]

private def indexCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"),
   (a "LCons" [v "first", v "rest"], indexConsBody), (v "invalid", .symbol "None")]

private theorem index_shape : (equation .index).body =
    a "case" [v "indices", .expression (indexCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem index_returns (state : State) (index : Nat) (indices : List Nat) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-index" :: [CettaWireAtom.encode (.natural index), CettaWireAtom.encode (InferenceCettaWire.encodeList Term.natural indices)])) state
      (CettaWireAtom.encode (naturalOptionTerm (if index ∈ indices then some (indices.idxOf index) else none))) := by
  change PureReturns program [] state
    (a Helper.index.head [number index, indicesValue indices]) state
    (encoded (naturalOptionTerm (indexResult index indices)))
  induction indices with
  | nil =>
      apply helper_call .index [] state [number index, indicesValue []] [number index, indicesValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
      rw [index_shape]
      let caller := environment .index [number index, indicesValue []]
      apply case_returns program caller caller state state state (v "indices") (.symbol "LNil")
        (.symbol "None") _ _ indexCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, InferenceCettaWire.encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "indices"
      · simp [indexCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "None"
  | cons first indices ih =>
      let caller := environment .index [number index, indicesValue (first :: indices)]
      let selected := ("rest", indicesValue indices) :: ("first", number first) :: caller
      apply helper_call .index [] state [number index, indicesValue (first :: indices)]
        [number index, indicesValue (first :: indices)] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
      rw [index_shape]
      apply case_returns program caller selected state state state (v "indices")
        (indicesValue (first :: indices)) indexConsBody _ _ indexCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "indices"
      · simp [indexCases, InferenceCettaWire.encodeList, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · have compared : PureReturns program selected state (a "==" [v "index", v "first"]) state
            (Effects.boolean (decide (index = first))) := by
          simpa only [Term.natural.injEq] using
            CettaWireAtom.equality_captured_returns program selected state (.natural index) (.natural first)
              "index" "first"
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              (by simp [selected, applySubst, Subst.lookup])
        apply bool_if_returns selected state _ (decide (index = first)) _ _ _ compared
        rw [index_result_cons]
        by_cases same : index = first
        · simpa [same, naturalOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            some_returns selected state (number 0) (number 0)
              (grounded_returns program selected state (.int 0))
        · simp only [same, decide_false, Bool.false_eq_true, ite_false]
          have recursive := helper_capture .index selected state [v "index", v "rest"]
            [number index, indicesValue indices] _ rfl
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
          cases found : indexResult index indices with
          | none =>
              apply case_returns program selected selected state state state
                (a Helper.index.head [v "index", v "rest"]) (.symbol "None") (.symbol "None")
                _ _ indexResultCases (read_cases_encoded _)
              · simpa [found, naturalOptionTerm, CettaWireAtom.encode] using recursive
              · simp [indexResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · exact symbol_returns program selected state "None"
          | some position =>
              let bound := ("position", number position) :: selected
              let final := ("next", number (position + 1)) :: bound
              apply case_returns program selected bound state state state
                (a Helper.index.head [v "index", v "rest"]) (a "Some" [number position]) indexNextBody
                _ _ indexResultCases (read_cases_encoded _)
              · simpa [found, naturalOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using recursive
              · simp [indexResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, selected, caller,
                  environment, Helper.names]
              · apply named_let_returns bound state "next" _ (number (position + 1))
                · simp [bound, selected, caller, environment, Helper.names, Subst.lookup]
                · exact add_one_returns bound state position "position"
                    (by simp [bound, applySubst, Subst.lookup])
                · simpa [found, naturalOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    final, applySubst, Subst.lookup] using
                    some_returns final state (v "next") (number (position + 1))
                      (by simpa [final, applySubst, Subst.lookup] using variable_returns program final state "next")

theorem index_captured_returns (caller : Subst) (state : State) (index : Nat) (indices : List Nat)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode (.natural index), CettaWireAtom.encode (InferenceCettaWire.encodeList Term.natural indices)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-index" :: [one, two])) state
      (CettaWireAtom.encode (naturalOptionTerm (if index ∈ indices then some (indices.idxOf index) else none))) :=
  helper_capture .index caller state [one, two] [number index, indicesValue indices] _ rfl captured
    (index_returns state index indices)

def spineOptionTerm : Option (List Nat) → Term
  | none => .symbol "None"
  | some indices => .application "Some" [InferenceCettaWire.encodeList Term.natural indices]

private theorem variable_spine_nil (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth [] = some [] := by
  simp [Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine?]

private theorem variable_spine_cons (depth index : Nat) (arguments : List Pattern) :
    Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth (.bvar index :: arguments) =
      if index < depth then
        (Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth arguments).bind fun indices =>
          if index ∈ indices then none else some (index :: indices)
      else none := by
  simp only [Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine?, List.mapM_cons]
  by_cases bounded : index < depth
  · simp only [bounded, ite_true, Option.bind_eq_bind, Option.pure_def,
      Option.bind_assoc, Option.bind_some]
    congr 1
    funext indices
    by_cases distinct : indices.Nodup
    · by_cases member : index ∈ indices <;> simp [List.nodup_cons, distinct, member]
    · simp [List.nodup_cons, distinct]
  · simp [bounded]

private theorem variable_spine_nonvariable (depth : Nat) (pattern : Pattern) (arguments : List Pattern)
    (notVariable : ∀ index, pattern ≠ .bvar index) :
    Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth (pattern :: arguments) = none := by
  cases pattern with
  | bvar index => exact False.elim (notVariable index rfl)
  | fvar | apply | lambda | multiLambda | subst | collection =>
      simp [Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine?, List.mapM_cons]

private theorem member_indices_returns (caller : Subst) (state : State) (index : Nat) (indices : List Nat)
    (first second : String)
    (indexCaptured : applySubst caller (v first) = number index)
    (indicesCaptured : applySubst caller (v second) = indicesValue indices) :
    PureReturns program caller state (a "gslt:automata:member" [v first, v second]) state
      (Effects.boolean (decide (index ∈ indices))) := by
  have closed : PureReturns MatchAutomataProgram.program [] state
      (a "gslt:automata:member" [number index, indicesValue indices]) state
        (Effects.boolean (decide (index ∈ indices))) := by
    simpa only [a, number, indicesValue, encoded, InferenceCettaWire.encodeList,
      MatchAutomataSourceExecution.listValue, encodeList_map,
      Function.comp_def, id_eq, List.mem_map, Term.natural.injEq, exists_eq_right] using
      MatchAutomataSourceExecution.member_returns state (.natural index) (indices.map Term.natural)
  have captured : PureReturns MatchAutomataProgram.program caller state
      (a "gslt:automata:member" [v first, v second]) state
        (Effects.boolean (decide (index ∈ indices))) := by
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] caller state state
      "gslt:automata:member" [number index, indicesValue indices] [v first, v second] _
      (by decide +kernel) _ (by decide) _ closed
    · intro position bounded
      have small : position = 0 ∨ position = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl <;> decide +kernel
    · simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil,
        indexCaptured, indicesCaptured]
  exact RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead]) captured

private def spineSomeBody : Atom :=
  a "if" [a "gslt:automata:member" [v "index", v "indices"], .symbol "None",
    a "let" [v "all", a "LCons" [v "index", v "indices"], a "Some" [v "all"]]]

private def spineResultCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "indices"], spineSomeBody)]

private def spineVarBody : Atom :=
  a "if" [a "<" [v "index", v "depth"],
    a "case" [a Helper.spine.head [v "depth", v "rest"],
      .expression (spineResultCases.map fun row => .expression [row.1, row.2])], .symbol "None"]

private def spineArgumentCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], spineVarBody), (v "nonvariable", .symbol "None")]

private def spineConsBody : Atom :=
  a "case" [v "argument", .expression (spineArgumentCases.map fun row => .expression [row.1, row.2])]

private def spineCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [.symbol "LNil"]),
   (a "LCons" [v "argument", v "rest"], spineConsBody), (v "invalid", .symbol "None")]

private theorem spine_shape : (equation .spine).body =
    a "case" [v "arguments", .expression (spineCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem encoded_nonvariable_refuses (caller : Subst) (pattern : Pattern)
    (notVariable : ∀ index, pattern ≠ .bvar index) :
    SpaceSemantics.matchValue caller (a "Var" [v "index"]) (patternValue pattern) = none := by
  cases pattern with
  | bvar index => exact False.elim (notVariable index rfl)
  | fvar | apply | lambda | multiLambda | subst | collection =>
      simp [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]

private theorem spine_argument_nonvariable_returns (caller : Subst) (state : State) (pattern : Pattern)
    (notVariable : ∀ index, pattern ≠ .bvar index)
    (captured : applySubst caller (v "argument") = patternValue pattern)
    (fresh : Subst.lookup caller "nonvariable" = none) :
    PureReturns program caller state spineConsBody state (.symbol "None") := by
  let rejected := ("nonvariable", patternValue pattern) :: caller
  apply case_returns program caller rejected state state state (v "argument") (patternValue pattern)
    (.symbol "None") (.symbol "None") _ spineArgumentCases (read_cases_encoded _)
  · simpa only [captured] using variable_returns program caller state "argument"
  · simp [spineArgumentCases, SpaceSemantics.selectCase, encoded_nonvariable_refuses caller pattern notVariable,
      SpaceSemantics.matchValue, matchAtom, fresh, rejected]
  · exact symbol_returns program rejected state "None"

private theorem spine_cons_case (state : State) (depth : Nat) (pattern : Pattern) (arguments : List Pattern)
    (answer : Atom)
    (returned : PureReturns program
      (("rest", patternsValue arguments) :: ("argument", patternValue pattern) ::
        environment .spine [number depth, patternsValue (pattern :: arguments)]) state spineConsBody state answer) :
    PureReturns program [] state (a Helper.spine.head [number depth, patternsValue (pattern :: arguments)])
      state answer := by
  apply helper_call .spine [] state [number depth, patternsValue (pattern :: arguments)]
    [number depth, patternsValue (pattern :: arguments)] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [spine_shape]
  let caller := environment .spine [number depth, patternsValue (pattern :: arguments)]
  let selected := ("rest", patternsValue arguments) :: ("argument", patternValue pattern) :: caller
  apply case_returns program caller selected state state state (v "arguments") (patternsValue (pattern :: arguments))
    spineConsBody answer _ spineCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "arguments"
  · simp [spineCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
  · exact returned

theorem variable_spine_returns (state : State) (depth : Nat) (arguments : List Pattern) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-variable-spine" :: [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns arguments)])) state
      (CettaWireAtom.encode (spineOptionTerm (Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth arguments))) := by
  induction arguments with
  | nil =>
      rw [variable_spine_nil]
      apply helper_call .spine [] state [number depth, patternsValue []] [number depth, patternsValue []] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
      rw [spine_shape]
      let caller := environment .spine [number depth, patternsValue []]
      apply case_returns program caller caller state state state (v "arguments") (.symbol "LNil")
        (a "Some" [.symbol "LNil"]) _ _ spineCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "arguments"
      · simp [spineCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact some_returns caller state (.symbol "LNil") (.symbol "LNil")
          (symbol_returns program caller state "LNil")
  | cons pattern arguments ih =>
      let caller := environment .spine [number depth, patternsValue (pattern :: arguments)]
      let selected := ("rest", patternsValue arguments) :: ("argument", patternValue pattern) :: caller
      apply spine_cons_case state depth pattern arguments _ ?_
      cases pattern with
      | bvar index =>
          let bound := ("index", number index) :: selected
          apply case_returns program selected bound state state state (v "argument") (patternValue (.bvar index))
            spineVarBody _ _ spineArgumentCases (read_cases_encoded _)
          · simpa [selected, applySubst, Subst.lookup] using variable_returns program selected state "argument"
          · simp [spineArgumentCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, selected, caller,
              environment, Helper.names]
          · have compared := lt_variables_returns bound state index depth "index" "depth"
              (by simp [bound, applySubst, Subst.lookup])
              (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            apply bool_if_returns bound state _ (decide (index < depth)) _ _ _ compared
            rw [variable_spine_cons]
            by_cases bounded : index < depth
            · simp only [bounded, decide_true, ite_true]
              have recursive := helper_capture .spine bound state [v "depth", v "rest"]
                [number depth, patternsValue arguments] _ rfl
                (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
              cases tail : Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth arguments with
              | none =>
                  apply case_returns program bound bound state state state
                    (a Helper.spine.head [v "depth", v "rest"]) (.symbol "None") (.symbol "None")
                    _ _ spineResultCases (read_cases_encoded _)
                  · simpa [tail, spineOptionTerm, CettaWireAtom.encode] using recursive
                  · simp [spineResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · exact symbol_returns program bound state "None"
              | some indices =>
                  let found := ("indices", indicesValue indices) :: bound
                  let allBound := ("all", indicesValue (index :: indices)) :: found
                  apply case_returns program bound found state state state
                    (a Helper.spine.head [v "depth", v "rest"]) (a "Some" [indicesValue indices])
                    spineSomeBody _ _ spineResultCases (read_cases_encoded _)
                  · simpa [tail, spineOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using recursive
                  · simp [spineResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, found, bound, selected,
                      caller, environment, Helper.names]
                  · apply bool_if_returns found state _ (decide (index ∈ indices))
                    · exact member_indices_returns found state index indices "index" "indices"
                        (by simp [found, bound, applySubst, Subst.lookup])
                        (by simp [found, applySubst, Subst.lookup])
                    · by_cases member : index ∈ indices
                      · simpa [member, tail, spineOptionTerm, CettaWireAtom.encode] using
                          symbol_returns program found state "None"
                      · simp only [member, decide_false, Bool.false_eq_true, ite_false]
                        apply named_let_returns found state "all" _ (indicesValue (index :: indices))
                        · simp [found, bound, selected, caller, environment, Helper.names, Subst.lookup]
                        · simpa [InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                            found, bound, applySubst, Subst.lookup] using
                            constructor_variables_return program found state "LCons" ["index", "indices"]
                              (by decide +kernel) (by decide)
                        · simpa [tail, member, spineOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                            allBound, applySubst, Subst.lookup] using
                            some_returns allBound state (v "all") (indicesValue (index :: indices))
                              (by simpa [allBound, applySubst, Subst.lookup] using variable_returns program allBound state "all")
            · simpa [bounded, spineOptionTerm, CettaWireAtom.encode] using symbol_returns program bound state "None"
      | fvar name =>
          rw [variable_spine_nonvariable depth (.fvar name) arguments (by intro index; simp)]
          exact spine_argument_nonvariable_returns selected state (.fvar name)
            (by intro index; simp)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, Subst.lookup])
      | apply head children =>
          rw [variable_spine_nonvariable depth (.apply head children) arguments (by intro index; simp)]
          exact spine_argument_nonvariable_returns selected state (.apply head children)
            (by intro index; simp)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, Subst.lookup])
      | lambda binder body =>
          rw [variable_spine_nonvariable depth (.lambda binder body) arguments (by intro index; simp)]
          exact spine_argument_nonvariable_returns selected state (.lambda binder body)
            (by intro index; simp)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, Subst.lookup])
      | multiLambda arity binders body =>
          rw [variable_spine_nonvariable depth (.multiLambda arity binders body) arguments (by intro index; simp)]
          exact spine_argument_nonvariable_returns selected state (.multiLambda arity binders body)
            (by intro index; simp)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, Subst.lookup])
      | subst body replacement =>
          rw [variable_spine_nonvariable depth (.subst body replacement) arguments (by intro index; simp)]
          exact spine_argument_nonvariable_returns selected state (.subst body replacement)
            (by intro index; simp)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, Subst.lookup])
      | collection kind elements rest =>
          rw [variable_spine_nonvariable depth (.collection kind elements rest) arguments (by intro index; simp)]
          exact spine_argument_nonvariable_returns selected state (.collection kind elements rest)
            (by intro index; simp)
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, Subst.lookup])

theorem variable_spine_captured_returns (caller : Subst) (state : State) (depth : Nat) (arguments : List Pattern)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns arguments)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-variable-spine" :: [one, two])) state
      (CettaWireAtom.encode (spineOptionTerm (Mettapedia.OSLF.MeTTaIL.RuleBinding.variableSpine? depth arguments))) :=
  helper_capture .spine caller state [one, two] [number depth, patternsValue arguments] _ rfl captured
    (variable_spine_returns state depth arguments)


/-- Finite source data denoting exactly the two canonical scoped assignments. -/
inductive AssignmentDescriptor where
  | occurrence (dependencies depth : Nat) (arguments : List Pattern)
  | recovery (depth dependencies ambient : Nat) (indices : List Nat)

/-- Descriptor interpretation reuses the original context-variable assignments. -/
def AssignmentDescriptor.interpret : AssignmentDescriptor → Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment
  | .occurrence dependencies depth arguments =>
      Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceAssignment dependencies depth arguments
  | .recovery depth dependencies ambient indices =>
      Mettapedia.OSLF.MeTTaIL.RuleBinding.recoveryAssignment depth dependencies ambient indices

def AssignmentDescriptor.term : AssignmentDescriptor → Term
  | .occurrence dependencies depth arguments => .application "OccurrenceAssignment"
      [.natural dependencies, .natural depth, InferenceCettaWire.encodePatterns arguments]
  | .recovery depth dependencies ambient indices => .application "RecoveryAssignment"
      [.natural depth, .natural dependencies, .natural ambient,
        InferenceCettaWire.encodeList Term.natural indices]

private abbrev descriptorValue (descriptor : AssignmentDescriptor) : Atom := encoded descriptor.term
attribute [local simp] descriptorValue

private theorem subtract_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String) (bounded : right ≤ left)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "-" [v first, v second]) state (number (left - right)) := by
  apply native_variable_call_returns program caller state state "-" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  have castSubtraction : ((left - right : Nat) : Int) = (left : Int) - (right : Int) := by omega
  simpa only [number, encoded, CettaWireAtom.encode, castSubtraction] using
    StdLib.integer_subtraction state (left : Int) (right : Int)

private def shiftedAssignmentBody (base shift : String) : Atom :=
  a "let*" [.expression
    [.expression [v "offset", a "-" [v "index", v base]],
     .expression [v "shifted", a "+" [v shift, v "offset"]]],
    a "Var" [v "shifted"]]

private def occurrenceAssignmentCases : SpaceSemantics.Cases :=
  [(.symbol "None", a "Var" [number 0]), (a "Some" [v "value"], v "value")]

private def occurrenceAssignmentBody : Atom :=
  a "if" [a "<" [v "index", v "dependencies"],
    a "case" [a "gslt:rule:row-at" [v "index", v "arguments"],
      .expression (occurrenceAssignmentCases.map fun row => .expression [row.1, row.2])],
    shiftedAssignmentBody "dependencies" "depth"]

private def recoveryAssignmentCases : SpaceSemantics.Cases :=
  [(.symbol "None", a "let" [v "outside", a "+" [v "dependencies", v "ambient"], a "Var" [v "outside"]]),
   (a "Some" [v "position"], a "Var" [v "position"])]

private def recoveryAssignmentBody : Atom :=
  a "if" [a "<" [v "index", v "depth"],
    a "case" [a Helper.index.head [v "index", v "indices"],
      .expression (recoveryAssignmentCases.map fun row => .expression [row.1, row.2])],
    shiftedAssignmentBody "depth" "dependencies"]

private def assignmentCases : SpaceSemantics.Cases :=
  [(a "OccurrenceAssignment" [v "dependencies", v "depth", v "arguments"], occurrenceAssignmentBody),
   (a "RecoveryAssignment" [v "depth", v "dependencies", v "ambient", v "indices"], recoveryAssignmentBody),
   (v "invalid", .symbol "None")]

private theorem assignment_shape : (equation .assignment).body =
    a "case" [v "assignment", .expression (assignmentCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem shifted_assignment_returns (caller : Subst) (state : State) (index base shift : Nat)
    (baseName shiftName : String) (bounded : base ≤ index)
    (indexCaptured : applySubst caller (v "index") = number index)
    (baseCaptured : applySubst caller (v baseName) = number base)
    (shiftCaptured : applySubst caller (v shiftName) = number shift)
    (offsetFresh : Subst.lookup caller "offset" = none)
    (shiftedFresh : Subst.lookup caller "shifted" = none)
    (shiftNotOffset : shiftName ≠ "offset") :
    PureReturns program caller state (shiftedAssignmentBody baseName shiftName) state
      (patternValue (.bvar (shift + (index - base)))) := by
  let offsetBound := ("offset", number (index - base)) :: caller
  let final := ("shifted", number (shift + (index - base))) :: offsetBound
  have offsetReturned := subtract_variables_returns caller state index base "index" baseName bounded
    indexCaptured baseCaptured
  have shiftedFreshAtOffset : Subst.lookup offsetBound "shifted" = none := by
    simpa [offsetBound, Subst.lookup] using shiftedFresh
  have shiftReturned := add_variables_returns offsetBound state shift (index - base) shiftName "offset"
    (by simpa [offsetBound, applySubst, Subst.lookup, shiftNotOffset, Ne.symm shiftNotOffset] using shiftCaptured)
    (by simp [offsetBound, applySubst, Subst.lookup])
  unfold shiftedAssignmentBody
  apply PureData.let_bindings_return
    (pairs := [(v "offset", a "-" [v "index", v baseName]),
      (v "shifted", a "+" [v shiftName, v "offset"])]) (final := final)
  · apply PureData.BindingsReturn.cons (bound := offsetBound) offsetReturned
    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, offsetFresh, offsetBound]
    · apply PureData.BindingsReturn.cons (bound := final) shiftReturned
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, shiftedFreshAtOffset, final]
      · exact .nil _ _
  · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      final, offsetBound, applySubst, Subst.lookup] using
      constructor_variables_return program final state "Var" ["shifted"] (by decide +kernel) (by decide)

private theorem patterns_as_list (patterns : List Pattern) :
    patternsValue patterns = MatchAutomataSourceExecution.listValue
      (patterns.map InferenceCettaWire.encodePattern) := by
  rw [patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList]
  simp [MatchAutomataSourceExecution.listValue, encodeList_map]

private theorem row_at_patterns_returns (caller : Subst) (state : State) (index : Nat) (arguments : List Pattern)
    (captured : [v "index", v "arguments"].map (applySubst caller) = [number index, patternsValue arguments]) :
    PureReturns program caller state (a "gslt:rule:row-at" [v "index", v "arguments"]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm (arguments[index]?.map InferenceCettaWire.encodePattern))) := by
  have returned := RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index
    (arguments.map InferenceCettaWire.encodePattern) (v "index") (v "arguments")
    (by simpa only [patterns_as_list] using captured)
  cases found : arguments[index]? <;>
    simpa [List.getElem?_map, found, MatchAutomataBindingExecution.payloadOptionTerm] using returned

theorem assignment_returns (state : State) (descriptor : AssignmentDescriptor) (index : Nat) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-assignment" :: [CettaWireAtom.encode descriptor.term, CettaWireAtom.encode (.natural index)])) state
      (CettaWireAtom.encode (InferenceCettaWire.encodePattern (descriptor.interpret index))) := by
  apply helper_call .assignment [] state [descriptorValue descriptor, number index]
    [descriptorValue descriptor, number index] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [assignment_shape]
  let caller := environment .assignment [descriptorValue descriptor, number index]
  cases descriptor with
  | occurrence dependencies depth arguments =>
      let selected := ("arguments", patternsValue arguments) :: ("depth", number depth) ::
        ("dependencies", number dependencies) :: caller
      apply case_returns program caller selected state state state (v "assignment")
        (descriptorValue (.occurrence dependencies depth arguments)) occurrenceAssignmentBody _ _
        assignmentCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "assignment"
      · simp [assignmentCases, AssignmentDescriptor.term, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold occurrenceAssignmentBody
        apply bool_if_returns selected state _ (decide (index < dependencies))
        · exact lt_variables_returns selected state index dependencies "index" "dependencies"
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        · by_cases bounded : index < dependencies
          · simp only [bounded, decide_true, ↓reduceIte]
            have lookup := row_at_patterns_returns selected state index arguments
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            cases found : arguments[index]? with
            | none =>
                apply case_returns program selected selected state state state
                  (a "gslt:rule:row-at" [v "index", v "arguments"]) (.symbol "None") (a "Var" [number 0])
                  _ _ occurrenceAssignmentCases (read_cases_encoded _)
                · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using lookup
                · simp [occurrenceAssignmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · simpa [AssignmentDescriptor.interpret, Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceAssignment,
                    bounded, List.getD_eq_getElem?_getD, found, InferenceCettaWire.encodePattern,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    unary_constructor_of_returns program selected state state "Var" (number 0) (number 0)
                      (by decide +kernel) (by decide) (grounded_returns program selected state (.int 0))
            | some value =>
                let final := ("value", patternValue value) :: selected
                apply case_returns program selected final state state state
                  (a "gslt:rule:row-at" [v "index", v "arguments"]) (a "Some" [patternValue value]) (v "value")
                  _ _ occurrenceAssignmentCases (read_cases_encoded _)
                · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookup
                · simp [occurrenceAssignmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, final, selected,
                    caller, environment, Helper.names]
                · simpa [AssignmentDescriptor.interpret, Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceAssignment,
                    bounded, List.getD_eq_getElem?_getD, found, final, applySubst, Subst.lookup] using
                    variable_returns program final state "value"
          · simpa [AssignmentDescriptor.interpret, Mettapedia.OSLF.MeTTaIL.RuleBinding.occurrenceAssignment, bounded] using
              shifted_assignment_returns selected state index dependencies depth "dependencies" "depth" (by omega)
                (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
                (by simp [selected, caller, environment, Helper.names, Subst.lookup])
                (by simp [selected, caller, environment, Helper.names, Subst.lookup]) (by decide)
  | recovery depth dependencies ambient indices =>
      let selected := ("indices", indicesValue indices) :: ("ambient", number ambient) ::
        ("dependencies", number dependencies) :: ("depth", number depth) :: caller
      apply case_returns program caller selected state state state (v "assignment")
        (descriptorValue (.recovery depth dependencies ambient indices)) recoveryAssignmentBody _ _
        assignmentCases (read_cases_encoded _)
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "assignment"
      · simp [assignmentCases, AssignmentDescriptor.term, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold recoveryAssignmentBody
        apply bool_if_returns selected state _ (decide (index < depth))
        · exact lt_variables_returns selected state index depth "index" "depth"
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [selected, applySubst, Subst.lookup])
        · by_cases bounded : index < depth
          · simp only [bounded, decide_true, ↓reduceIte]
            have lookup := index_captured_returns selected state index indices (v "index") (v "indices")
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            by_cases member : index ∈ indices
            · let final := ("position", number (indices.idxOf index)) :: selected
              apply case_returns program selected final state state state
                (a Helper.index.head [v "index", v "indices"]) (a "Some" [number (indices.idxOf index)])
                (a "Var" [v "position"]) _ _ recoveryAssignmentCases (read_cases_encoded _)
              · simpa [indexResult, member, naturalOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookup
              · simp [recoveryAssignmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, final, selected, caller,
                  environment, Helper.names]
              · simpa [AssignmentDescriptor.interpret, Mettapedia.OSLF.MeTTaIL.RuleBinding.recoveryAssignment,
                  bounded, member, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  final, applySubst, Subst.lookup] using
                  constructor_variables_return program final state "Var" ["position"] (by decide +kernel) (by decide)
            · let final := ("outside", number (dependencies + ambient)) :: selected
              apply case_returns program selected selected state state state
                (a Helper.index.head [v "index", v "indices"]) (.symbol "None")
                (a "let" [v "outside", a "+" [v "dependencies", v "ambient"], a "Var" [v "outside"]])
                _ _ recoveryAssignmentCases (read_cases_encoded _)
              · simpa [indexResult, member, naturalOptionTerm, CettaWireAtom.encode] using lookup
              · simp [recoveryAssignmentCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · apply named_let_returns selected state "outside" _ (number (dependencies + ambient))
                · simp [selected, caller, environment, Helper.names, Subst.lookup]
                · exact add_variables_returns selected state dependencies ambient "dependencies" "ambient"
                    (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
                · simpa [AssignmentDescriptor.interpret, Mettapedia.OSLF.MeTTaIL.RuleBinding.recoveryAssignment,
                    bounded, member, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    final, applySubst, Subst.lookup] using
                    constructor_variables_return program final state "Var" ["outside"] (by decide +kernel) (by decide)
          · simpa [AssignmentDescriptor.interpret, Mettapedia.OSLF.MeTTaIL.RuleBinding.recoveryAssignment, bounded] using
              shifted_assignment_returns selected state index depth dependencies "depth" "dependencies" (by omega)
                (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                (by simp [selected, applySubst, Subst.lookup]) (by simp [selected, applySubst, Subst.lookup])
                (by simp [selected, caller, environment, Helper.names, Subst.lookup])
                (by simp [selected, caller, environment, Helper.names, Subst.lookup]) (by decide)

theorem assignment_captured_returns (caller : Subst) (state : State) (descriptor : AssignmentDescriptor) (index : Nat)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode descriptor.term, CettaWireAtom.encode (.natural index)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-assignment" :: [one, two])) state
      (CettaWireAtom.encode (InferenceCettaWire.encodePattern (descriptor.interpret index))) :=
  helper_capture .assignment caller state [one, two] [descriptorValue descriptor, number index] _ rfl captured
    (assignment_returns state descriptor index)

open Mettapedia.OSLF.MeTTaIL

private abbrev substitutionResult (descriptor : AssignmentDescriptor) (binderPrefix : Nat) (pattern : Pattern) : Pattern :=
  Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix descriptor.interpret) pattern

private abbrev substitutionListResult (descriptor : AssignmentDescriptor) (binderPrefix : Nat)
    (patterns : List Pattern) : List Pattern :=
  Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix descriptor.interpret) patterns

private theorem substitution_result_lambda (descriptor : AssignmentDescriptor) (binderPrefix : Nat)
    (binder : Option String) (body : Pattern) :
    substitutionResult descriptor binderPrefix (.lambda binder body) =
      .lambda binder (substitutionResult descriptor (binderPrefix + 1) body) := by
  simp [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]

private theorem substitution_result_multiLambda (descriptor : AssignmentDescriptor) (binderPrefix arity : Nat)
    (binders : List String) (body : Pattern) :
    substitutionResult descriptor binderPrefix (.multiLambda arity binders body) =
      .multiLambda arity binders (substitutionResult descriptor (binderPrefix + arity) body) := by
  simp [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]

private theorem substitution_result_subst (descriptor : AssignmentDescriptor) (binderPrefix : Nat)
    (body replacement : Pattern) :
    substitutionResult descriptor binderPrefix (.subst body replacement) =
      .subst (substitutionResult descriptor (binderPrefix + 1) body) (substitutionResult descriptor binderPrefix replacement) := by
  simp [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]

private inductive SubstitutionForm where | pattern | patterns
private def SubstitutionForm.helper : SubstitutionForm → Helper
  | .pattern => .substitute | .patterns => .substituteList
private def SubstitutionForm.formal : SubstitutionForm → String
  | .pattern => "pattern" | .patterns => "patterns"
attribute [local simp] SubstitutionForm.helper SubstitutionForm.formal

private def substituteBvarBody : Atom :=
  a "if" [a "<" [v "index", v "prefix"], v "pattern",
    a "let*" [.expression
      [.expression [v "original", a "-" [v "index", v "prefix"]],
       .expression [v "image", a Helper.assignment.head [v "assignment", v "original"]]],
      a "gslt:rule:lift-bvars" [number 0, v "prefix", v "image"]]]

private def substituteAppBody : Atom :=
  a "let" [v "values", a Helper.substituteList.head [v "assignment", v "prefix", v "children"],
    a "PApp" [v "head", v "values"]]

private def substituteBinderBody (many : Bool) : Atom :=
  a "let*" [.expression
    [.expression [v "next", a "+" [v "prefix", if many then v "arity" else number 1]],
     .expression [v "value", a Helper.substitute.head [v "assignment", v "next", v "body"]]],
    if many then a "PMultiLam" [v "arity", v "binders", v "value"] else a "PLam" [v "binder", v "value"]]

private def substituteSubstBody : Atom :=
  a "let*" [.expression
    [.expression [v "next", a "+" [v "prefix", number 1]],
     .expression [v "value", a Helper.substitute.head [v "assignment", v "next", v "body"]],
     .expression [v "replacement-value", a Helper.substitute.head [v "assignment", v "prefix", v "replacement"]]],
    a "PSubst" [v "value", v "replacement-value"]]

private def substituteCollectionBody : Atom :=
  a "let" [v "values", a Helper.substituteList.head [v "assignment", v "prefix", v "elements"],
    a "PCollection" [v "kind", v "values", v "rest"]]

private def substituteConsBody : Atom :=
  a "let*" [.expression
    [.expression [v "head", a Helper.substitute.head [v "assignment", v "prefix", v "pattern"]],
     .expression [v "tail", a Helper.substituteList.head [v "assignment", v "prefix", v "rest"]]],
    a "LCons" [v "head", v "tail"]]

private def substitutionCases : SubstitutionForm → SpaceSemantics.Cases
  | .pattern =>
      [(a "Var" [v "index"], substituteBvarBody), (a "FVar" [v "name"], v "pattern"),
       (a "PApp" [v "head", v "children"], substituteAppBody),
       (a "PLam" [v "binder", v "body"], substituteBinderBody false),
       (a "PMultiLam" [v "arity", v "binders", v "body"], substituteBinderBody true),
       (a "PSubst" [v "body", v "replacement"], substituteSubstBody),
       (a "PCollection" [v "kind", v "elements", v "rest"], substituteCollectionBody),
       (v "invalid", .symbol "None")]
  | .patterns =>
      [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "pattern", v "rest"], substituteConsBody),
       (v "invalid", .symbol "None")]

private theorem substitution_shape (form : SubstitutionForm) : (equation form.helper).body =
    a "case" [v form.formal, .expression ((substitutionCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private theorem substitution_case_returns (form : SubstitutionForm) (state : State)
    (descriptor : AssignmentDescriptor) (binderPrefix : Nat) (value : Atom) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (environment form.helper [descriptorValue descriptor, number binderPrefix, value])
      value (substitutionCases form) = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a form.helper.head [descriptorValue descriptor, number binderPrefix, value]) state answer := by
  apply helper_call form.helper [] state [descriptorValue descriptor, number binderPrefix, value]
    [descriptorValue descriptor, number binderPrefix, value] answer (by cases form <;> rfl)
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [substitution_shape]
  apply case_returns program (environment form.helper [descriptorValue descriptor, number binderPrefix, value])
    selected state state state (v form.formal) value body answer _ (substitutionCases form) (read_cases_encoded _)
    _ matched returned
  cases form with
  | pattern => simpa [environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (environment .substitute [descriptorValue descriptor, number binderPrefix, value]) state "pattern"
  | patterns => simpa [environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program (environment .substituteList [descriptorValue descriptor, number binderPrefix, value]) state "patterns"

private theorem substitution_capture (form : SubstitutionForm) (caller : Subst) (state : State)
    (descriptor : AssignmentDescriptor) (binderPrefix : Nat) (value one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [descriptorValue descriptor, number binderPrefix, value])
    (returned : PureReturns program [] state (a form.helper.head [descriptorValue descriptor, number binderPrefix, value]) state answer) :
    PureReturns program caller state (a form.helper.head [one, two, three]) state answer :=
  helper_capture form.helper caller state [one, two, three] [descriptorValue descriptor, number binderPrefix, value]
    answer (by cases form <;> rfl) captured returned

private theorem substitution_list_from_elements (state : State) (descriptor : AssignmentDescriptor)
    (binderPrefix : Nat) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a Helper.substitute.head [descriptorValue descriptor, number binderPrefix, patternValue pattern]) state
      (patternValue (substitutionResult descriptor binderPrefix pattern))) :
    PureReturns program [] state
      (a Helper.substituteList.head [descriptorValue descriptor, number binderPrefix, patternsValue patterns]) state
      (patternsValue (substitutionListResult descriptor binderPrefix patterns)) := by
  induction patterns with
  | nil =>
      apply substitution_case_returns .patterns state descriptor binderPrefix (patternsValue [])
        (environment .substituteList [descriptorValue descriptor, number binderPrefix, patternsValue []]) (.symbol "LNil")
      · simp [substitutionCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [substitutionListResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode] using symbol_returns program _ state "LNil"
  | cons pattern patterns ih =>
      let caller := environment .substituteList [descriptorValue descriptor, number binderPrefix, patternsValue (pattern :: patterns)]
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      let headBound := ("head", patternValue (substitutionResult descriptor binderPrefix pattern)) :: selected
      let final := ("tail", patternsValue (substitutionListResult descriptor binderPrefix patterns)) :: headBound
      apply substitution_case_returns .patterns state descriptor binderPrefix (patternsValue (pattern :: patterns)) selected substituteConsBody
      · simp [substitutionCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteConsBody
        apply PureData.let_bindings_return
          (pairs := [(v "head", a Helper.substitute.head [v "assignment", v "prefix", v "pattern"]),
            (v "tail", a Helper.substituteList.head [v "assignment", v "prefix", v "rest"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := headBound)
          · exact substitution_capture .pattern selected state descriptor binderPrefix (patternValue pattern)
              (v "assignment") (v "prefix") (v "pattern") _
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              (elements pattern (by simp))
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              headBound, selected, caller, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final)
            · exact substitution_capture .patterns headBound state descriptor binderPrefix (patternsValue patterns)
                (v "assignment") (v "prefix") (v "rest") _
                (by simp [headBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                (ih (fun child member => elements child (List.mem_cons_of_mem _ member)))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, headBound, selected, caller, environment, Helper.names]
            · exact .nil _ _
        · simpa [substitutionListResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList, InferenceCettaWire.encodePatterns,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, final, headBound, selected, applySubst, Subst.lookup] using
            constructor_variables_return program final state "LCons" ["head", "tail"] (by decide +kernel) (by decide)

theorem substitute_returns (state : State) (descriptor : AssignmentDescriptor) (pattern : Pattern) (binderPrefix : Nat) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-substitute" :: [CettaWireAtom.encode descriptor.term, CettaWireAtom.encode (.natural binderPrefix), CettaWireAtom.encode (InferenceCettaWire.encodePattern pattern)])) state
      (CettaWireAtom.encode (InferenceCettaWire.encodePattern (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix (descriptor).interpret) pattern))) := by
  change PureReturns program [] state
    (a Helper.substitute.head [descriptorValue descriptor, number binderPrefix, patternValue pattern]) state
    (patternValue (substitutionResult descriptor binderPrefix pattern))
  induction pattern using Pattern.inductionOn generalizing binderPrefix with
  | hbvar index =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.bvar index)]
      let selected := ("index", number index) :: caller
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.bvar index)) selected substituteBvarBody
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteBvarBody
        apply bool_if_returns selected state _ (decide (index < binderPrefix))
        · exact lt_variables_returns selected state index binderPrefix "index" "prefix"
            (by simp [selected, applySubst, Subst.lookup])
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        · by_cases bounded : index < binderPrefix
          · simpa [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, bounded,
              selected, caller, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns program selected state "pattern"
          · simp only [bounded, decide_false, Bool.false_eq_true, ite_false]
            let originalBound := ("original", number (index - binderPrefix)) :: selected
            let final := ("image", patternValue (descriptor.interpret (index - binderPrefix))) :: originalBound
            apply PureData.let_bindings_return
              (pairs := [(v "original", a "-" [v "index", v "prefix"]),
                (v "image", a Helper.assignment.head [v "assignment", v "original"])]) (final := final)
            · apply PureData.BindingsReturn.cons (bound := originalBound)
              · exact subtract_variables_returns selected state index binderPrefix "index" "prefix" (by omega)
                  (by simp [selected, applySubst, Subst.lookup])
                  (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                  originalBound, selected, caller, environment, Helper.names]
              · apply PureData.BindingsReturn.cons (bound := final)
                · exact assignment_captured_returns originalBound state descriptor (index - binderPrefix)
                    (v "assignment") (v "original")
                    (by simp [originalBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                    final, originalBound, selected, caller, environment, Helper.names]
                · exact .nil _ _
            · simpa [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, bounded] using
                RuleInstantiationExecution.lift_bvars_captured_returns final state 0 binderPrefix
                  (descriptor.interpret (index - binderPrefix)) (number 0) (v "prefix") (v "image")
                  (by simp [final, originalBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
  | hfvar name =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.fvar name)]
      let selected := ("name", encoded (.string name)) :: caller
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.fvar name)) selected (v "pattern")
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · simpa [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, selected, caller, environment, Helper.names,
          applySubst, Subst.lookup] using variable_returns program selected state "pattern"
  | happly head children ih =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.apply head children)]
      let selected := ("children", patternsValue children) :: ("head", encoded (.string head)) :: caller
      let final := ("values", patternsValue (substitutionListResult descriptor binderPrefix children)) :: selected
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.apply head children)) selected substituteAppBody
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteAppBody
        apply named_let_returns selected state "values" _ (patternsValue (substitutionListResult descriptor binderPrefix children))
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · exact substitution_capture .patterns selected state descriptor binderPrefix (patternsValue children)
            (v "assignment") (v "prefix") (v "children") _
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (substitution_list_from_elements state descriptor binderPrefix children (fun child member => ih child member binderPrefix))
        · simpa [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, substitutionListResult,
            InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany, final, selected,
            applySubst, Subst.lookup] using
            constructor_variables_return program final state "PApp" ["head", "values"] (by decide +kernel) (by decide)
  | hlambda binder body ih =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.lambda binder body)]
      let selected := ("body", patternValue body) :: ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let nextBound := ("next", number (binderPrefix + 1)) :: selected
      let final := ("value", patternValue (substitutionResult descriptor (binderPrefix + 1) body)) :: nextBound
      rw [substitution_result_lambda]
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.lambda binder body)) selected (substituteBinderBody false)
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteBinderBody
        simp only [Bool.false_eq_true, ite_false]
        apply PureData.let_bindings_return
          (pairs := [(v "next", a "+" [v "prefix", number 1]),
            (v "value", a Helper.substitute.head [v "assignment", v "next", v "body"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound)
          · exact add_one_returns selected state binderPrefix "prefix"
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, selected, caller, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final)
            · exact substitution_capture .pattern nextBound state descriptor (binderPrefix + 1) (patternValue body)
                (v "assignment") (v "next") (v "body") _
                (by simp [nextBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih (binderPrefix + 1))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, nextBound, selected, caller, environment, Helper.names]
            · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            final, nextBound, selected, applySubst, Subst.lookup] using
            constructor_variables_return program final state "PLam" ["binder", "value"] (by decide +kernel) (by decide)
  | hmultiLambda arity binders body ih =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.multiLambda arity binders body)]
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", number arity) :: caller
      let nextBound := ("next", number (binderPrefix + arity)) :: selected
      let final := ("value", patternValue (substitutionResult descriptor (binderPrefix + arity) body)) :: nextBound
      rw [substitution_result_multiLambda]
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.multiLambda arity binders body)) selected (substituteBinderBody true)
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteBinderBody
        simp only [ite_true]
        apply PureData.let_bindings_return
          (pairs := [(v "next", a "+" [v "prefix", v "arity"]),
            (v "value", a Helper.substitute.head [v "assignment", v "next", v "body"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound)
          · exact add_variables_returns selected state binderPrefix arity "prefix" "arity"
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              (by simp [selected, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, selected, caller, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := final)
            · exact substitution_capture .pattern nextBound state descriptor (binderPrefix + arity) (patternValue body)
                (v "assignment") (v "next") (v "body") _
                (by simp [nextBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih (binderPrefix + arity))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, nextBound, selected, caller, environment, Helper.names]
            · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            final, nextBound, selected, applySubst, Subst.lookup] using
            constructor_variables_return program final state "PMultiLam" ["arity", "binders", "value"] (by decide +kernel) (by decide)
  | hsubst body replacement ihBody ihReplacement =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.subst body replacement)]
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      let nextBound := ("next", number (binderPrefix + 1)) :: selected
      let valueBound := ("value", patternValue (substitutionResult descriptor (binderPrefix + 1) body)) :: nextBound
      let final := ("replacement-value", patternValue (substitutionResult descriptor binderPrefix replacement)) :: valueBound
      rw [substitution_result_subst]
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.subst body replacement)) selected substituteSubstBody
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteSubstBody
        apply PureData.let_bindings_return
          (pairs := [(v "next", a "+" [v "prefix", number 1]),
            (v "value", a Helper.substitute.head [v "assignment", v "next", v "body"]),
            (v "replacement-value", a Helper.substitute.head [v "assignment", v "prefix", v "replacement"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := nextBound)
          · exact add_one_returns selected state binderPrefix "prefix"
              (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              nextBound, selected, caller, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := valueBound)
            · exact substitution_capture .pattern nextBound state descriptor (binderPrefix + 1) (patternValue body)
                (v "assignment") (v "next") (v "body") _
                (by simp [nextBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ihBody (binderPrefix + 1))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                valueBound, nextBound, selected, caller, environment, Helper.names]
            · apply PureData.BindingsReturn.cons (bound := final)
              · exact substitution_capture .pattern valueBound state descriptor binderPrefix (patternValue replacement)
                  (v "assignment") (v "prefix") (v "replacement") _
                  (by simp [valueBound, nextBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ihReplacement binderPrefix)
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                  final, valueBound, nextBound, selected, caller, environment, Helper.names]
              · exact .nil _ _
        · simpa [InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            final, valueBound, nextBound, applySubst, Subst.lookup] using
            constructor_variables_return program final state "PSubst" ["value", "replacement-value"] (by decide +kernel) (by decide)
  | hcollection kind elements rest ih =>
      let caller := environment .substitute [descriptorValue descriptor, number binderPrefix, patternValue (.collection kind elements rest)]
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) :: ("elements", patternsValue elements) ::
        ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      let final := ("values", patternsValue (substitutionListResult descriptor binderPrefix elements)) :: selected
      apply substitution_case_returns .pattern state descriptor binderPrefix (patternValue (.collection kind elements rest)) selected substituteCollectionBody
      · simp [substitutionCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold substituteCollectionBody
        apply named_let_returns selected state "values" _ (patternsValue (substitutionListResult descriptor binderPrefix elements))
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · exact substitution_capture .patterns selected state descriptor binderPrefix (patternsValue elements)
            (v "assignment") (v "prefix") (v "elements") _
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (substitution_list_from_elements state descriptor binderPrefix elements (fun child member => ih child member binderPrefix))
        · simpa [substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, substitutionListResult,
            InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany, final, selected,
            applySubst, Subst.lookup] using
            constructor_variables_return program final state "PCollection" ["kind", "values", "rest"] (by decide +kernel) (by decide)

theorem substitute_captured_returns (caller : Subst) (state : State) (descriptor : AssignmentDescriptor)
    (binderPrefix : Nat) (pattern : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [CettaWireAtom.encode descriptor.term, CettaWireAtom.encode (.natural binderPrefix), CettaWireAtom.encode (InferenceCettaWire.encodePattern pattern)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-substitute" :: [one, two, three])) state
      (CettaWireAtom.encode (InferenceCettaWire.encodePattern (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix (descriptor).interpret) pattern))) :=
  substitution_capture .pattern caller state descriptor binderPrefix (patternValue pattern) one two three _ captured
    (substitute_returns state descriptor pattern binderPrefix)

theorem substitute_list_returns (state : State) (descriptor : AssignmentDescriptor) (binderPrefix : Nat) (patterns : List Pattern) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-substitute-list" :: [CettaWireAtom.encode descriptor.term, CettaWireAtom.encode (.natural binderPrefix), CettaWireAtom.encode (InferenceCettaWire.encodePatterns patterns)])) state
      (CettaWireAtom.encode (InferenceCettaWire.encodePatterns (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix (descriptor).interpret) patterns))) :=
  substitution_list_from_elements state descriptor binderPrefix patterns (fun pattern _ => substitute_returns state descriptor pattern binderPrefix)

theorem substitute_list_captured_returns (caller : Subst) (state : State) (descriptor : AssignmentDescriptor)
    (binderPrefix : Nat) (patterns : List Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [CettaWireAtom.encode descriptor.term, CettaWireAtom.encode (.natural binderPrefix), CettaWireAtom.encode (InferenceCettaWire.encodePatterns patterns)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-substitute-list" :: [one, two, three])) state
      (CettaWireAtom.encode (InferenceCettaWire.encodePatterns (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix (descriptor).interpret) patterns))) :=
  substitution_capture .patterns caller state descriptor binderPrefix (patternsValue patterns) one two three _ captured
    (substitute_list_returns state descriptor binderPrefix patterns)

open InferenceCettaWire.AuthoredRule (contextualValueTerm contextualValueTerm_injective)

private abbrev valueWire (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue) : Atom := encoded (contextualValueTerm value)

/-- The original assignment rows use the retained opaque payload binding wire. -/
def scopedAssignmentTerm (assignment : ScopedRuleMatching.Assignment) : Term :=
  MatchAutomataBindingExecution.payloadBindingsTerm
    (assignment.map fun entry => (entry.1, contextualValueTerm entry.2))

def scopedAssignmentOptionTerm (result : Option ScopedRuleMatching.Assignment) : Term :=
  MatchAutomataBindingExecution.payloadOptionTerm (result.map scopedAssignmentTerm)

private abbrev assignmentWire (assignment : ScopedRuleMatching.Assignment) : Atom := encoded (scopedAssignmentTerm assignment)
attribute [local simp] valueWire assignmentWire

/-- The shared opaque binding wire retains the original contextual value and
first-occurrence lookup. Premise execution uses this same assignment wire. -/
theorem scoped_lookup_wire (assignment : ScopedRuleMatching.Assignment) (name : String) :
    MatchAutomataBindingExecution.payloadLookup
      (assignment.map fun entry => (entry.1, contextualValueTerm entry.2)) name =
        (ScopedRuleMatching.lookup assignment name).map contextualValueTerm := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : key = name
      · subst key
        simp [MatchAutomataBindingExecution.payloadLookup, ScopedRuleMatching.lookup]
      · simpa [MatchAutomataBindingExecution.payloadLookup, ScopedRuleMatching.lookup, List.find?_cons,
          same, Ne.symm same] using ih

private theorem contextual_binding_returns (caller : Subst) (state : State)
    (assignment : ScopedRuleMatching.Assignment) (name : String)
    (captured : [v "name", v "assignment"].map (applySubst caller) = [encoded (.string name), assignmentWire assignment]) :
    PureReturns program caller state (a "gslt:automata:binding" [v "name", v "assignment"]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm
        ((ScopedRuleMatching.lookup assignment name).map contextualValueTerm))) := by
  apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
  simpa only [scoped_lookup_wire] using
    MatchAutomataBindingExecution.payload_binding_captured_returns caller state name
      (assignment.map fun entry => (entry.1, contextualValueTerm entry.2)) [v "name", v "assignment"]
      (by simpa only [assignmentWire, scopedAssignmentTerm] using captured)

private def assignMissingBody : Atom :=
  a "let*" [.expression
    [.expression [v "entry", a "Binding" [v "name", v "value"]],
     .expression [v "extended", a "LCons" [v "entry", v "assignment"]]],
    a "Some" [v "extended"]]

private def assignRepeatBody : Atom :=
  a "if" [a "==" [v "prior", v "value"], a "Some" [v "assignment"], .symbol "None"]

private def assignCases : SpaceSemantics.Cases :=
  [(.symbol "None", assignMissingBody), (a "Some" [v "prior"], assignRepeatBody)]

private theorem assign_shape : (equation .assign).body =
    a "case" [a "gslt:automata:binding" [v "name", v "assignment"],
      .expression (assignCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem assign_returns (state : State) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue) :
    PureReturns program [] state (Atom.expression (Atom.symbol "gslt:rule:scope-assign" :: [CettaWireAtom.encode (scopedAssignmentTerm assignment), CettaWireAtom.encode (.string name), CettaWireAtom.encode (contextualValueTerm value)])) state
      (CettaWireAtom.encode (scopedAssignmentOptionTerm (ScopedRuleMatching.assign assignment name value))) := by
  apply helper_call .assign [] state [assignmentWire assignment, encoded (.string name), valueWire value]
    [assignmentWire assignment, encoded (.string name), valueWire value] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [assign_shape]
  let caller := environment .assign [assignmentWire assignment, encoded (.string name), valueWire value]
  have looked := contextual_binding_returns caller state assignment name
    (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
  cases found : ScopedRuleMatching.lookup assignment name with
  | none =>
      let entryBound := ("entry", encoded (MatchAutomataBindingExecution.payloadBindingTerm (name, contextualValueTerm value))) :: caller
      let final := ("extended", assignmentWire ((name, value) :: assignment)) :: entryBound
      apply case_returns program caller caller state state state
        (a "gslt:automata:binding" [v "name", v "assignment"]) (.symbol "None") assignMissingBody _ _
        assignCases (read_cases_encoded _)
      · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using looked
      · simp [assignCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · unfold assignMissingBody
        apply PureData.let_bindings_return
          (pairs := [(v "entry", a "Binding" [v "name", v "value"]),
            (v "extended", a "LCons" [v "entry", v "assignment"])]) (final := final)
        · apply PureData.BindingsReturn.cons (bound := entryBound)
          · simpa [MatchAutomataBindingExecution.payloadBindingTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              caller, environment, Helper.names, applySubst, Subst.lookup] using
              constructor_variables_return program caller state "Binding" ["name", "value"] (by decide +kernel) (by decide)
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              entryBound, caller, environment, Helper.names, MatchAutomataBindingExecution.payloadBindingTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · apply PureData.BindingsReturn.cons (bound := final)
            · simpa [scopedAssignmentTerm, MatchAutomataBindingExecution.payloadBindingsTerm, List.map_cons,
                encodeList, MatchAutomataBindingExecution.payloadBindingTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                entryBound, caller, environment, Helper.names, applySubst, Subst.lookup] using
                constructor_variables_return program entryBound state "LCons" ["entry", "assignment"] (by decide +kernel) (by decide)
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                final, entryBound, caller, environment, Helper.names, scopedAssignmentTerm,
                MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
                encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · exact .nil _ _
        · simpa [ScopedRuleMatching.assign, found, scopedAssignmentOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, final, applySubst, Subst.lookup] using
            constructor_variables_return program final state "Some" ["extended"] (by decide +kernel) (by decide)
  | some prior =>
      let selected := ("prior", valueWire prior) :: caller
      apply case_returns program caller selected state state state
        (a "gslt:automata:binding" [v "name", v "assignment"]) (a "Some" [valueWire prior]) assignRepeatBody _ _
        assignCases (read_cases_encoded _)
      · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using looked
      · simp [assignCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · have compared := CettaWireAtom.equality_captured_returns program selected state
          (contextualValueTerm prior) (contextualValueTerm value) "prior" "value"
          (by simp [selected, applySubst, Subst.lookup])
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        unfold assignRepeatBody
        apply bool_if_returns selected state _ (decide (prior = value))
        · simpa only [contextualValueTerm_injective.eq_iff] using compared
        · by_cases same : prior = value
          · subst prior
            simpa [ScopedRuleMatching.assign, found, scopedAssignmentOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, caller, environment, Helper.names,
              applySubst, Subst.lookup] using
              constructor_variables_return program selected state "Some" ["assignment"] (by decide +kernel) (by decide)
          · simpa [same, ScopedRuleMatching.assign, found, scopedAssignmentOptionTerm,
              MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using
              symbol_returns program selected state "None"

theorem assign_captured_returns (caller : Subst) (state : State) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [CettaWireAtom.encode (scopedAssignmentTerm assignment), CettaWireAtom.encode (.string name), CettaWireAtom.encode (contextualValueTerm value)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-assign" :: [one, two, three])) state
      (CettaWireAtom.encode (scopedAssignmentOptionTerm (ScopedRuleMatching.assign assignment name value))) :=
  helper_capture .assign caller state [one, two, three] [assignmentWire assignment, encoded (.string name), valueWire value]
    _ rfl captured (assign_returns state assignment name value)

private abbrev dependenciesWire (dependencies : List TypeExpr) : Atom :=
  encoded (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies)
attribute [local simp] dependenciesWire

private theorem dependencies_as_list (dependencies : List TypeExpr) :
    dependenciesWire dependencies = MatchAutomataSourceExecution.listValue
      (dependencies.map InferenceCettaWire.AuthoredRule.typeTerm) := by
  simp [MatchAutomataSourceExecution.listValue, InferenceCettaWire.encodeList, encodeList_map]

private theorem length_list_returns (caller : Subst) (state : State) (values : List Term) (name : String)
    (captured : applySubst caller (v name) = MatchAutomataSourceExecution.listValue values) :
    PureReturns program caller state (a "gslt:automata:length" [v name]) state (number values.length) := by
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  exact MatchAutomataSourceExecution.length_captured_returns caller state values (v name) captured

private theorem equal_numbers_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "==" [v first, v second]) state
      (Effects.boolean (decide (left = right))) := by
  simpa only [Term.natural.injEq] using
    CettaWireAtom.equality_captured_returns program caller state (.natural left) (.natural right)
      first second leftCaptured rightCaptured

private theorem scoped_list_all (depth : Nat) (patterns : List Pattern) :
    Pattern.isWellScopedListAt depth patterns = patterns.all (fun pattern => pattern.isWellScopedAt depth) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp only [Pattern.isWellScopedListAt, List.all_cons, ih]

private theorem instantiate_value_equation (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue) (ambient depth : Nat) (arguments : List Pattern) :
    RuleBinding.instantiateValue? value ambient depth arguments =
      if value.ambient = ambient then
        if arguments.length = value.dependencies.length then
          if value.body.isWellScopedAt (value.dependencies.length + ambient) then
            if Pattern.isWellScopedListAt (depth + ambient) arguments then
              let result := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
                (RuleBinding.occurrenceAssignment value.dependencies.length depth arguments) value.body
              if result.isWellScopedAt (depth + ambient) then some result else none
            else none
          else none
        else none
      else none := by
  by_cases context : value.ambient = ambient
  · by_cases arity : arguments.length = value.dependencies.length
    · cases bodyScoped : value.body.isWellScopedAt (value.dependencies.length + ambient) <;>
        cases argumentsScoped : Pattern.isWellScopedListAt (depth + ambient) arguments <;>
        simp [RuleBinding.instantiateValue?, context, arity, bodyScoped, ← scoped_list_all, argumentsScoped]
    · simp [RuleBinding.instantiateValue?, context, arity]
  · simp [RuleBinding.instantiateValue?, context]

private def instantiateResultBody : Atom :=
  a "if" [a Helper.scoped.head [v "target-depth", v "result"], a "Some" [v "result"], .symbol "None"]
private def instantiateSubstitutionBody : Atom :=
  a "let*" [.expression
    [.expression [v "assignment", a "OccurrenceAssignment" [v "arity", v "depth", v "arguments"]],
     .expression [v "result", a Helper.substitute.head [v "assignment", number 0, v "body"]]],
    instantiateResultBody]
private def instantiateArgumentsBody : Atom :=
  a "if" [a Helper.scopedList.head [v "target-depth", v "arguments"], instantiateSubstitutionBody, .symbol "None"]
private def instantiateSourceBody : Atom :=
  a "if" [a Helper.scoped.head [v "source-depth", v "body"], instantiateArgumentsBody, .symbol "None"]
private def instantiateDepthBody : Atom :=
  a "let*" [.expression
    [.expression [v "source-depth", a "+" [v "arity", v "ambient"]],
     .expression [v "target-depth", a "+" [v "depth", v "ambient"]]], instantiateSourceBody]
private def instantiateArityBody : Atom :=
  a "if" [a "==" [v "supplied", v "arity"], instantiateDepthBody, .symbol "None"]
private def instantiateLengthsBody : Atom :=
  a "let*" [.expression
    [.expression [v "arity", a "gslt:automata:length" [v "dependencies"]],
     .expression [v "supplied", a "gslt:automata:length" [v "arguments"]]], instantiateArityBody]
private def instantiateBody : Atom :=
  a "if" [a "==" [v "stored-ambient", v "ambient"], instantiateLengthsBody, .symbol "None"]
private def instantiateCases : SpaceSemantics.Cases :=
  [(a "ContextualValue" [v "dependencies", v "stored-ambient", v "body"], instantiateBody),
   (v "invalid", .symbol "None")]
private theorem instantiate_shape : (equation .instantiate).body =
    a "case" [v "value", .expression (instantiateCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private abbrev patternOptionValue (value : Option Pattern) : Atom :=
  encoded (MatchAutomataBindingExecution.patternOptionTerm value)

theorem instantiate_value_returns (state : State) (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) :
    PureReturns program [] state
      (Atom.expression (Atom.symbol "gslt:rule:scope-instantiate-value" :: [CettaWireAtom.encode (contextualValueTerm value), CettaWireAtom.encode (.natural ambient), CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns arguments)])) state
      (CettaWireAtom.encode (MatchAutomataBindingExecution.patternOptionTerm (RuleBinding.instantiateValue? value ambient depth arguments))) := by
  rw [instantiate_value_equation]
  apply helper_call .instantiate [] state
    [valueWire value, number ambient, number depth, patternsValue arguments]
    [valueWire value, number ambient, number depth, patternsValue arguments] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [instantiate_shape]
  let caller := environment .instantiate [valueWire value, number ambient, number depth, patternsValue arguments]
  let selected := ("body", patternValue value.body) :: ("stored-ambient", number value.ambient) ::
    ("dependencies", dependenciesWire value.dependencies) :: caller
  apply case_returns program caller selected state state state (v "value") (valueWire value)
    instantiateBody _ _ instantiateCases (read_cases_encoded _)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "value"
  · simp [instantiateCases, valueWire, contextualValueTerm, dependenciesWire,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      selected, caller, environment, Helper.names]
  · unfold instantiateBody
    apply bool_if_returns selected state _ (decide (value.ambient = ambient))
    · exact equal_numbers_returns selected state value.ambient ambient "stored-ambient" "ambient"
        (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
    · by_cases context : value.ambient = ambient
      · simp only [context, ite_true, decide_true]
        unfold instantiateLengthsBody
        let arityBound := ("arity", number value.dependencies.length) :: selected
        let lengthsBound := ("supplied", number arguments.length) :: arityBound
        apply PureData.let_bindings_return
          (pairs := [(v "arity", a "gslt:automata:length" [v "dependencies"]),
            (v "supplied", a "gslt:automata:length" [v "arguments"])]) (final := lengthsBound)
        · apply PureData.BindingsReturn.cons (bound := arityBound)
          · simpa only [List.length_map] using
              length_list_returns selected state (value.dependencies.map InferenceCettaWire.AuthoredRule.typeTerm) "dependencies"
                (by simpa only [dependencies_as_list] using
                  (show applySubst selected (v "dependencies") = dependenciesWire value.dependencies by
                    simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]))
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
              arityBound, selected, caller, environment, Helper.names]
          · apply PureData.BindingsReturn.cons (bound := lengthsBound)
            · simpa only [List.length_map] using
                length_list_returns arityBound state (arguments.map InferenceCettaWire.encodePattern) "arguments"
                  (by simpa only [patterns_as_list] using
                    (show applySubst arityBound (v "arguments") = patternsValue arguments by
                      simp [arityBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]))
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                lengthsBound, arityBound, selected, caller, environment, Helper.names]
            · exact .nil _ _
        · unfold instantiateArityBody
          apply bool_if_returns lengthsBound state _ (decide (arguments.length = value.dependencies.length))
          · exact equal_numbers_returns lengthsBound state arguments.length value.dependencies.length "supplied" "arity"
              (by simp [lengthsBound, arityBound, applySubst, Subst.lookup])
              (by simp [lengthsBound, arityBound, applySubst, Subst.lookup])
          · by_cases arity : arguments.length = value.dependencies.length
            · simp only [arity, ite_true, decide_true]
              unfold instantiateDepthBody
              let sourceBound := ("source-depth", number (value.dependencies.length + ambient)) :: lengthsBound
              let depthBound := ("target-depth", number (depth + ambient)) :: sourceBound
              apply PureData.let_bindings_return
                (pairs := [(v "source-depth", a "+" [v "arity", v "ambient"]),
                  (v "target-depth", a "+" [v "depth", v "ambient"])]) (final := depthBound)
              · apply PureData.BindingsReturn.cons (bound := sourceBound)
                · exact add_variables_returns lengthsBound state value.dependencies.length ambient "arity" "ambient"
                    (by simp [lengthsBound, arityBound, applySubst, Subst.lookup])
                    (by simp [lengthsBound, arityBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                    sourceBound, lengthsBound, arityBound, selected, caller, environment, Helper.names]
                · apply PureData.BindingsReturn.cons (bound := depthBound)
                  · exact add_variables_returns sourceBound state depth ambient "depth" "ambient"
                      (by simp [sourceBound, lengthsBound, arityBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                      (by simp [sourceBound, lengthsBound, arityBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                      depthBound, sourceBound, lengthsBound, arityBound, selected, caller, environment, Helper.names]
                  · exact .nil _ _
              · unfold instantiateSourceBody
                apply bool_if_returns depthBound state _ (value.body.isWellScopedAt (value.dependencies.length + ambient))
                · exact well_scoped_captured_returns depthBound state value.body (value.dependencies.length + ambient)
                    (v "source-depth") (v "body")
                    (by simp [depthBound, sourceBound, lengthsBound, arityBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                · cases bodyScoped : value.body.isWellScopedAt (value.dependencies.length + ambient) with
                  | false =>
                      simpa [bodyScoped, patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                        CettaWireAtom.encode] using symbol_returns program depthBound state "None"
                  | true =>
                      simp only [ite_true]
                      unfold instantiateArgumentsBody
                      apply bool_if_returns depthBound state _ (Pattern.isWellScopedListAt (depth + ambient) arguments)
                      · exact well_scoped_list_captured_returns depthBound state arguments (depth + ambient)
                          (v "target-depth") (v "arguments")
                          (by simp [depthBound, sourceBound, lengthsBound, arityBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                      · cases argumentsScoped : Pattern.isWellScopedListAt (depth + ambient) arguments with
                        | false =>
                            simpa [argumentsScoped, patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                              CettaWireAtom.encode] using symbol_returns program depthBound state "None"
                        | true =>
                            simp only [ite_true]
                            unfold instantiateSubstitutionBody
                            let descriptor := AssignmentDescriptor.occurrence value.dependencies.length depth arguments
                            let assignmentBound := ("assignment", descriptorValue descriptor) :: depthBound
                            let result := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute descriptor.interpret value.body
                            let resultBound := ("result", patternValue result) :: assignmentBound
                            apply PureData.let_bindings_return
                              (pairs := [(v "assignment", a "OccurrenceAssignment" [v "arity", v "depth", v "arguments"]),
                                (v "result", a Helper.substitute.head [v "assignment", number 0, v "body"])]) (final := resultBound)
                            · apply PureData.BindingsReturn.cons (bound := assignmentBound)
                              · simpa [descriptorValue, descriptor, AssignmentDescriptor.term, CettaWireAtom.encode,
                                  CettaWireAtom.encodeMany, depthBound, sourceBound, lengthsBound, arityBound, selected,
                                  caller, environment, Helper.names, applySubst, Subst.lookup] using
                                  constructor_variables_return program depthBound state "OccurrenceAssignment" ["arity", "depth", "arguments"]
                                    (by decide +kernel) (by decide)
                              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                                  assignmentBound, descriptor, AssignmentDescriptor.term, CettaWireAtom.encode,
                                  CettaWireAtom.encodeMany, depthBound, sourceBound, lengthsBound, arityBound, selected,
                                  caller, environment, Helper.names]
                              · apply PureData.BindingsReturn.cons (bound := resultBound)
                                · simpa only [result, substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] using
                                    substitute_captured_returns assignmentBound state descriptor 0 value.body
                                      (v "assignment") (number 0) (v "body")
                                      (by simp [assignmentBound, depthBound, sourceBound, lengthsBound, arityBound, selected,
                                        caller, environment, Helper.names, applySubst, Subst.lookup])
                                · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                                    resultBound, result, assignmentBound, depthBound, sourceBound, lengthsBound, arityBound, selected,
                                    caller, environment, Helper.names]
                                · exact .nil _ _
                            · change PureReturns program resultBound state instantiateResultBody state
                                (patternOptionValue (if result.isWellScopedAt (depth + ambient) then some result else none))
                              unfold instantiateResultBody
                              apply bool_if_returns resultBound state _ (result.isWellScopedAt (depth + ambient))
                              · exact well_scoped_captured_returns resultBound state result (depth + ambient)
                                  (v "target-depth") (v "result")
                                  (by simp [resultBound, assignmentBound, depthBound, sourceBound, lengthsBound, arityBound,
                                    selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                              · cases resultScoped : result.isWellScopedAt (depth + ambient) with
                                | false =>
                                    simp only [Bool.false_eq_true, ite_false]
                                    simpa [patternOptionValue,
                                      MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                                      symbol_returns program resultBound state "None"
                                | true =>
                                    simp only [ite_true]
                                    simpa [patternOptionValue,
                                      MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                                      resultBound, applySubst, Subst.lookup] using
                                      constructor_variables_return program resultBound state "Some" ["result"] (by decide +kernel) (by decide)
            · simpa [arity, patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
                CettaWireAtom.encode] using symbol_returns program lengthsBound state "None"
      · simpa [context, patternOptionValue, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode] using symbol_returns program selected state "None"

theorem instantiate_value_captured_returns (caller : Subst) (state : State) (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue)
    (ambient depth : Nat) (arguments : List Pattern) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [CettaWireAtom.encode (contextualValueTerm value), CettaWireAtom.encode (.natural ambient), CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns arguments)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-instantiate-value" :: [one, two, three, four])) state
      (CettaWireAtom.encode (MatchAutomataBindingExecution.patternOptionTerm (RuleBinding.instantiateValue? value ambient depth arguments))) :=
  helper_capture .instantiate caller state [one, two, three, four]
    [valueWire value, number ambient, number depth, patternsValue arguments] _ rfl captured
    (instantiate_value_returns state value ambient depth arguments)

def contextualValueOptionTerm (value : Option Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue) : Term :=
  MatchAutomataBindingExecution.payloadOptionTerm (value.map contextualValueTerm)

private theorem recover_value_equation (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) :
    RuleBinding.recoverValue? dependencies ambient depth arguments target =
      if target.isWellScopedAt (depth + ambient) then
        match RuleBinding.variableSpine? depth arguments with
        | none => none
        | some indices =>
            if indices.length = dependencies.length then
              let value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue := ⟨dependencies, ambient,
                Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
                  (RuleBinding.recoveryAssignment depth dependencies.length ambient indices) target⟩
              if RuleBinding.instantiateValue? value ambient depth arguments = some target then some value else none
            else none
      else none := by
  cases targetScoped : target.isWellScopedAt (depth + ambient) with
  | false => simp [RuleBinding.recoverValue?, targetScoped]
  | true =>
      cases spine : RuleBinding.variableSpine? depth arguments with
      | none => simp [RuleBinding.recoverValue?, targetScoped, spine]
      | some indices =>
          by_cases arity : indices.length = dependencies.length
          · simp [RuleBinding.recoverValue?, targetScoped, spine, arity, beq_iff_eq]
          · simp [RuleBinding.recoverValue?, targetScoped, spine, arity]

private def recoverResultBody : Atom :=
  a "if" [a "==" [v "forward", a "Some" [v "target"]], a "Some" [v "value"], .symbol "None"]
private def recoverSubstitutionBody : Atom :=
  a "let*" [.expression
    [.expression [v "assignment", a "RecoveryAssignment" [v "depth", v "arity", v "ambient", v "indices"]],
     .expression [v "body", a Helper.substitute.head [v "assignment", number 0, v "target"]],
     .expression [v "value", a "ContextualValue" [v "dependencies", v "ambient", v "body"]],
     .expression [v "forward", a Helper.instantiate.head [v "value", v "ambient", v "depth", v "arguments"]]],
    recoverResultBody]
private def recoverArityBody : Atom :=
  a "if" [a "==" [v "supplied", v "arity"], recoverSubstitutionBody, .symbol "None"]
private def recoverLengthsBody : Atom :=
  a "let*" [.expression
    [.expression [v "arity", a "gslt:automata:length" [v "dependencies"]],
     .expression [v "supplied", a "gslt:automata:length" [v "indices"]]], recoverArityBody]
private def recoverSpineCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "indices"], recoverLengthsBody)]
private def recoverScopeBody : Atom :=
  a "if" [a Helper.scoped.head [v "target-depth", v "target"],
    a "case" [a Helper.spine.head [v "depth", v "arguments"],
      .expression (recoverSpineCases.map fun row => .expression [row.1, row.2])], .symbol "None"]
private theorem recover_shape : (equation .recover).body =
    a "let" [v "target-depth", a "+" [v "depth", v "ambient"], recoverScopeBody] := by
  decide +kernel

theorem recover_value_returns (state : State) (dependencies : List TypeExpr) (ambient depth : Nat)
    (arguments : List Pattern) (target : Pattern) :
    PureReturns program [] state
      (Atom.expression (Atom.symbol "gslt:rule:scope-recover-value" :: [CettaWireAtom.encode (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies), CettaWireAtom.encode (.natural ambient), CettaWireAtom.encode (.natural depth),
        CettaWireAtom.encode (InferenceCettaWire.encodePatterns arguments), CettaWireAtom.encode (InferenceCettaWire.encodePattern target)])) state
      (CettaWireAtom.encode (contextualValueOptionTerm (RuleBinding.recoverValue? dependencies ambient depth arguments target))) := by
  rw [recover_value_equation]
  apply helper_call .recover [] state
    [dependenciesWire dependencies, number ambient, number depth, patternsValue arguments, patternValue target]
    [dependenciesWire dependencies, number ambient, number depth, patternsValue arguments, patternValue target] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [recover_shape]
  let caller := environment .recover [dependenciesWire dependencies, number ambient, number depth,
    patternsValue arguments, patternValue target]
  let depthBound := ("target-depth", number (depth + ambient)) :: caller
  apply named_let_returns caller state "target-depth" _ (number (depth + ambient))
  · simp [caller, environment, Helper.names, Subst.lookup]
  · exact add_variables_returns caller state depth ambient "depth" "ambient"
      (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
  · unfold recoverScopeBody
    apply bool_if_returns depthBound state _ (target.isWellScopedAt (depth + ambient))
    · exact well_scoped_captured_returns depthBound state target (depth + ambient) (v "target-depth") (v "target")
        (by simp [depthBound, caller, environment, Helper.names, applySubst, Subst.lookup])
    · cases targetScoped : target.isWellScopedAt (depth + ambient) with
      | false =>
          simpa [targetScoped, contextualValueOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
            CettaWireAtom.encode] using symbol_returns program depthBound state "None"
      | true =>
          simp only [ite_true]
          have spineReturned := variable_spine_captured_returns depthBound state depth arguments (v "depth") (v "arguments")
            (by simp [depthBound, caller, environment, Helper.names, applySubst, Subst.lookup])
          cases spine : RuleBinding.variableSpine? depth arguments with
          | none =>
              apply case_returns program depthBound depthBound state state state
                (a Helper.spine.head [v "depth", v "arguments"]) (.symbol "None") (.symbol "None") _ _
                recoverSpineCases (read_cases_encoded _)
              · simpa [spine, spineOptionTerm, CettaWireAtom.encode] using spineReturned
              · simp [recoverSpineCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [contextualValueOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
                  CettaWireAtom.encode] using symbol_returns program depthBound state "None"
          | some indices =>
              let selected := ("indices", indicesValue indices) :: depthBound
              apply case_returns program depthBound selected state state state
                (a Helper.spine.head [v "depth", v "arguments"]) (a "Some" [indicesValue indices]) recoverLengthsBody _ _
                recoverSpineCases (read_cases_encoded _)
              · simpa [spine, spineOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using spineReturned
              · simp [recoverSpineCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                  selected, depthBound, caller, environment, Helper.names]
              · unfold recoverLengthsBody
                let arityBound := ("arity", number dependencies.length) :: selected
                let lengthsBound := ("supplied", number indices.length) :: arityBound
                apply PureData.let_bindings_return
                  (pairs := [(v "arity", a "gslt:automata:length" [v "dependencies"]),
                    (v "supplied", a "gslt:automata:length" [v "indices"])]) (final := lengthsBound)
                · apply PureData.BindingsReturn.cons (bound := arityBound)
                  · simpa only [List.length_map] using
                      length_list_returns selected state (dependencies.map InferenceCettaWire.AuthoredRule.typeTerm) "dependencies"
                        (by simpa only [dependencies_as_list] using
                          (show applySubst selected (v "dependencies") = dependenciesWire dependencies by
                            simp [selected, depthBound, caller, environment, Helper.names, applySubst, Subst.lookup]))
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                      arityBound, selected, depthBound, caller, environment, Helper.names]
                  · apply PureData.BindingsReturn.cons (bound := lengthsBound)
                    · simpa only [List.length_map] using
                        length_list_returns arityBound state (indices.map Term.natural) "indices"
                          (by simp [arityBound, selected, indicesValue, MatchAutomataSourceExecution.listValue,
                            InferenceCettaWire.encodeList, encodeList_map, applySubst, Subst.lookup])
                    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                        lengthsBound, arityBound, selected, depthBound, caller, environment, Helper.names]
                    · exact .nil _ _
                · unfold recoverArityBody
                  apply bool_if_returns lengthsBound state _ (decide (indices.length = dependencies.length))
                  · exact equal_numbers_returns lengthsBound state indices.length dependencies.length "supplied" "arity"
                      (by simp [lengthsBound, arityBound, applySubst, Subst.lookup])
                      (by simp [lengthsBound, arityBound, applySubst, Subst.lookup])
                  · by_cases arity : indices.length = dependencies.length
                    · simp only [arity, ite_true, decide_true]
                      unfold recoverSubstitutionBody
                      let descriptor := AssignmentDescriptor.recovery depth dependencies.length ambient indices
                      let body := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute descriptor.interpret target
                      let value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue := ⟨dependencies, ambient, body⟩
                      let forward := RuleBinding.instantiateValue? value ambient depth arguments
                      let assignmentBound := ("assignment", descriptorValue descriptor) :: lengthsBound
                      let bodyBound := ("body", patternValue body) :: assignmentBound
                      let valueBound := ("value", valueWire value) :: bodyBound
                      let forwardBound := ("forward", patternOptionValue forward) :: valueBound
                      apply PureData.let_bindings_return
                        (pairs := [(v "assignment", a "RecoveryAssignment" [v "depth", v "arity", v "ambient", v "indices"]),
                          (v "body", a Helper.substitute.head [v "assignment", number 0, v "target"]),
                          (v "value", a "ContextualValue" [v "dependencies", v "ambient", v "body"]),
                          (v "forward", a Helper.instantiate.head [v "value", v "ambient", v "depth", v "arguments"])])
                        (final := forwardBound)
                      · apply PureData.BindingsReturn.cons (bound := assignmentBound)
                        · simpa [descriptorValue, descriptor, AssignmentDescriptor.term, CettaWireAtom.encode,
                            CettaWireAtom.encodeMany, lengthsBound, arityBound, selected, depthBound, caller,
                            environment, Helper.names, applySubst, Subst.lookup] using
                            constructor_variables_return program lengthsBound state "RecoveryAssignment"
                              ["depth", "arity", "ambient", "indices"] (by decide +kernel) (by decide)
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                            assignmentBound, descriptor, AssignmentDescriptor.term, CettaWireAtom.encode,
                            CettaWireAtom.encodeMany, lengthsBound, arityBound, selected, depthBound, caller, environment, Helper.names]
                        · apply PureData.BindingsReturn.cons (bound := bodyBound)
                          · simpa only [body, substitutionResult, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] using
                              substitute_captured_returns assignmentBound state descriptor 0 target
                                (v "assignment") (number 0) (v "target")
                                (by simp [assignmentBound, lengthsBound, arityBound, selected, depthBound, caller,
                                  environment, Helper.names, applySubst, Subst.lookup])
                          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                              bodyBound, body, assignmentBound, lengthsBound, arityBound, selected, depthBound, caller, environment, Helper.names]
                          · apply PureData.BindingsReturn.cons (bound := valueBound)
                            · simpa [value, valueWire, contextualValueTerm, dependenciesWire,
                                CettaWireAtom.encode, CettaWireAtom.encodeMany, bodyBound, assignmentBound,
                                lengthsBound, arityBound, selected, depthBound, caller, environment, Helper.names,
                                applySubst, Subst.lookup] using
                                constructor_variables_return program bodyBound state "ContextualValue"
                                  ["dependencies", "ambient", "body"] (by decide +kernel) (by decide)
                            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                                valueBound, value, valueWire, contextualValueTerm, dependenciesWire,
                                CettaWireAtom.encode, CettaWireAtom.encodeMany, bodyBound, assignmentBound,
                                lengthsBound, arityBound, selected, depthBound, caller, environment, Helper.names]
                            · apply PureData.BindingsReturn.cons (bound := forwardBound)
                              · exact instantiate_value_captured_returns valueBound state value ambient depth arguments
                                  (v "value") (v "ambient") (v "depth") (v "arguments")
                                  (by simp [valueBound, bodyBound, assignmentBound, lengthsBound, arityBound, selected,
                                    depthBound, caller, environment, Helper.names, applySubst, Subst.lookup])
                              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                                  forwardBound, forward, valueBound, bodyBound, assignmentBound, lengthsBound, arityBound, selected,
                                  depthBound, caller, environment, Helper.names]
                              · exact .nil _ _
                      · change PureReturns program forwardBound state recoverResultBody state
                          (encoded (contextualValueOptionTerm (if forward = some target then some value else none)))
                        unfold recoverResultBody
                        apply bool_if_returns forwardBound state _ (decide (forward = some target))
                        · have tested := CettaWireAtom.equality_evaluated_returns program forwardBound state
                            (MatchAutomataBindingExecution.patternOptionTerm forward)
                            (MatchAutomataBindingExecution.patternOptionTerm (some target))
                            (v "forward") (a "Some" [v "target"]) (by decide +kernel) (by decide +kernel)
                            (by simpa [forwardBound, applySubst, Subst.lookup] using variable_returns program forwardBound state "forward")
                            (by simpa [MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode,
                                CettaWireAtom.encodeMany, forwardBound, valueBound, bodyBound, assignmentBound,
                                lengthsBound, arityBound, selected, depthBound, caller, environment, Helper.names,
                                applySubst, Subst.lookup] using
                                constructor_variables_return program forwardBound state "Some" ["target"] (by decide +kernel) (by decide))
                          simpa only [MatchAutomataBindingExecution.patternOptionTerm_injective.eq_iff] using tested
                        · by_cases valid : forward = some target
                          · simp only [valid, ite_true, decide_true]
                            simpa [
                              contextualValueOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
                              CettaWireAtom.encode, CettaWireAtom.encodeMany, forwardBound, valueBound, applySubst, Subst.lookup] using
                              constructor_variables_return program forwardBound state "Some" ["value"] (by decide +kernel) (by decide)
                          · simp only [valid, ite_false, decide_false, Bool.false_eq_true]
                            simpa [
                              contextualValueOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
                              CettaWireAtom.encode] using symbol_returns program forwardBound state "None"
                    · simpa [arity, contextualValueOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
                        CettaWireAtom.encode] using symbol_returns program lengthsBound state "None"

theorem recover_value_captured_returns (caller : Subst) (state : State) (dependencies : List TypeExpr)
    (ambient depth : Nat) (arguments : List Pattern) (target : Pattern) (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [CettaWireAtom.encode (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies), CettaWireAtom.encode (.natural ambient), CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns arguments), CettaWireAtom.encode (InferenceCettaWire.encodePattern target)]) :
    PureReturns program caller state (Atom.expression (Atom.symbol "gslt:rule:scope-recover-value" :: [one, two, three, four, five])) state
      (CettaWireAtom.encode (contextualValueOptionTerm (RuleBinding.recoverValue? dependencies ambient depth arguments target))) :=
  helper_capture .recover caller state [one, two, three, four, five]
    [dependenciesWire dependencies, number ambient, number depth, patternsValue arguments, patternValue target]
    _ rfl captured (recover_value_returns state dependencies ambient depth arguments target)

namespace Controls

inductive Input where
  | wellScoped (depth : Nat) (pattern : Pattern)
  | wellScopedList (depth : Nat) (patterns : List Pattern)
  | index (index : Nat) (indices : List Nat)
  | spine (depth : Nat) (arguments : List Pattern)
  | assignment (descriptor : AssignmentDescriptor) (index : Nat)
  | substitute (descriptor : AssignmentDescriptor) (binderPrefix : Nat) (pattern : Pattern)
  | substituteList (descriptor : AssignmentDescriptor) (binderPrefix : Nat) (patterns : List Pattern)
  | instantiate (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue) (ambient depth : Nat) (arguments : List Pattern)
  | recover (dependencies : List TypeExpr) (ambient depth : Nat) (arguments : List Pattern) (target : Pattern)
  | assign (assignment : ScopedRuleMatching.Assignment) (name : String) (value : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue)

def Input.queryTerm : Input → Term
  | .wellScoped depth pattern => .application "if"
      [.application "gslt:rule:scope-well-scoped" [.natural depth, InferenceCettaWire.encodePattern pattern],
       .symbol "ScopedYes", .symbol "ScopedNo"]
  | .wellScopedList depth patterns => .application "if"
      [.application "gslt:rule:scope-well-scoped-list" [.natural depth, InferenceCettaWire.encodePatterns patterns],
       .symbol "ScopedYes", .symbol "ScopedNo"]
  | .index requested indices => .application "gslt:rule:scope-index"
      [.natural requested, InferenceCettaWire.encodeList Term.natural indices]
  | .spine depth arguments => .application "gslt:rule:scope-variable-spine"
      [.natural depth, InferenceCettaWire.encodePatterns arguments]
  | .assignment descriptor ordinal => .application "gslt:rule:scope-assignment" [descriptor.term, .natural ordinal]
  | .substitute descriptor binderPrefix pattern => .application "gslt:rule:scope-substitute"
      [descriptor.term, .natural binderPrefix, InferenceCettaWire.encodePattern pattern]
  | .substituteList descriptor binderPrefix patterns => .application "gslt:rule:scope-substitute-list"
      [descriptor.term, .natural binderPrefix, InferenceCettaWire.encodePatterns patterns]
  | .instantiate value ambient depth arguments => .application "gslt:rule:scope-instantiate-value"
      [contextualValueTerm value, .natural ambient, .natural depth, InferenceCettaWire.encodePatterns arguments]
  | .recover dependencies ambient depth arguments target => .application "gslt:rule:scope-recover-value"
      [InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies,
       .natural ambient, .natural depth, InferenceCettaWire.encodePatterns arguments, InferenceCettaWire.encodePattern target]
  | .assign saved name value => .application "gslt:rule:scope-assign"
      [scopedAssignmentTerm saved, .string name, contextualValueTerm value]

def Input.expectedTerm : Input → Term
  | .wellScoped depth pattern => if pattern.isWellScopedAt depth then .symbol "ScopedYes" else .symbol "ScopedNo"
  | .wellScopedList depth patterns => if Pattern.isWellScopedListAt depth patterns then .symbol "ScopedYes" else .symbol "ScopedNo"
  | .index requested indices => naturalOptionTerm (if requested ∈ indices then some (indices.idxOf requested) else none)
  | .spine depth arguments => spineOptionTerm (RuleBinding.variableSpine? depth arguments)
  | .assignment descriptor ordinal => InferenceCettaWire.encodePattern (descriptor.interpret ordinal)
  | .substitute descriptor binderPrefix pattern => InferenceCettaWire.encodePattern
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix descriptor.interpret) pattern)
  | .substituteList descriptor binderPrefix patterns => InferenceCettaWire.encodePatterns
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift binderPrefix descriptor.interpret) patterns)
  | .instantiate value ambient depth arguments => MatchAutomataBindingExecution.patternOptionTerm
      (RuleBinding.instantiateValue? value ambient depth arguments)
  | .recover dependencies ambient depth arguments target => contextualValueOptionTerm
      (RuleBinding.recoverValue? dependencies ambient depth arguments target)
  | .assign saved name value => scopedAssignmentOptionTerm (ScopedRuleMatching.assign saved name value)

theorem Input.returns (input : Input) (state : State) :
    PureReturns program [] state (CettaWireAtom.encode input.queryTerm) state (CettaWireAtom.encode input.expectedTerm) := by
  cases input with
  | wellScoped depth pattern =>
      change PureReturns program [] state (a "if" [a Helper.scoped.head [number depth, patternValue pattern],
        .symbol "ScopedYes", .symbol "ScopedNo"]) state _
      apply bool_if_returns [] state _ (pattern.isWellScopedAt depth)
      · exact well_scoped_returns state pattern depth
      · cases checked : pattern.isWellScopedAt depth with
        | false => simpa [Input.expectedTerm, checked, CettaWireAtom.encode] using symbol_returns program [] state "ScopedNo"
        | true => simpa [Input.expectedTerm, checked, CettaWireAtom.encode] using symbol_returns program [] state "ScopedYes"
  | wellScopedList depth patterns =>
      change PureReturns program [] state (a "if" [a Helper.scopedList.head [number depth, patternsValue patterns],
        .symbol "ScopedYes", .symbol "ScopedNo"]) state _
      apply bool_if_returns [] state _ (Pattern.isWellScopedListAt depth patterns)
      · exact well_scoped_list_returns state patterns depth
      · cases checked : Pattern.isWellScopedListAt depth patterns with
        | false => simpa [Input.expectedTerm, checked, CettaWireAtom.encode] using symbol_returns program [] state "ScopedNo"
        | true => simpa [Input.expectedTerm, checked, CettaWireAtom.encode] using symbol_returns program [] state "ScopedYes"
  | index requested indices =>
      simpa [Input.queryTerm, Input.expectedTerm, indexResult, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        index_returns state requested indices
  | spine depth arguments =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        variable_spine_returns state depth arguments
  | assignment descriptor ordinal =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        assignment_returns state descriptor ordinal
  | substitute descriptor binderPrefix pattern =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, substitutionResult, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        substitute_returns state descriptor pattern binderPrefix
  | substituteList descriptor binderPrefix patterns =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, substitutionListResult, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        substitute_list_returns state descriptor binderPrefix patterns
  | instantiate value ambient depth arguments =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, patternOptionValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        instantiate_value_returns state value ambient depth arguments
  | recover dependencies ambient depth arguments target =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        recover_value_returns state dependencies ambient depth arguments target
  | assign saved name value =>
      simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        assign_returns state saved name value

structure Fixture where
  name : String
  input : Input

def Fixture.queryTerm (fixture : Fixture) : Term := fixture.input.queryTerm
def Fixture.expectedTerm (fixture : Fixture) : Term := fixture.input.expectedTerm

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (CettaWireAtom.encode fixture.queryTerm) state (CettaWireAtom.encode fixture.expectedTerm) :=
  fixture.input.returns state

theorem Fixture.completed_iff (fixture : Fixture) (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded fixture.queryTerm) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded fixture.expectedTerm] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (fixture.returns state) after answers input output

theorem Fixture.derivation_iff (fixture : Fixture) (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded fixture.queryTerm) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded fixture.expectedTerm] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (fixture.returns state) after answers input output

def capturedBody : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue := ⟨[TypeExpr.term], 0, .apply "body" [.bvar 0]⟩
def alternateBody : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue := ⟨[TypeExpr.term], 0, .apply "other" [.bvar 0]⟩
def zeroSpine : Fixture :=
  ⟨"recover-zero-local-spine", .recover [TypeExpr.term] 0 2 [.bvar 0] (.apply "body" [.bvar 0])⟩
def oneSpine : Fixture :=
  ⟨"recover-different-local-spine-same-body", .recover [TypeExpr.term] 0 2 [.bvar 1] (.apply "body" [.bvar 1])⟩
def preservedSubstitution : Fixture :=
  ⟨"scope-substitution-preserves-explicit-node", .substitute (.occurrence 1 2 [.bvar 1]) 0
    (.subst (.apply "pair" [.bvar 0, .bvar 1]) (.bvar 0))⟩
def repeatedAssignment : Fixture :=
  ⟨"scope-assign-retains-first-identical-value-and-order",
    .assign [("first", capturedBody), ("x", capturedBody), ("x", alternateBody)] "x" capturedBody⟩

def fixtures : List Fixture :=
  [⟨"scope-local-index", .wellScoped 1 (.bvar 0)⟩,
   ⟨"scope-outside-index-refused", .wellScoped 1 (.bvar 1)⟩,
   ⟨"scope-free-variable-is-opaque", .wellScoped 0 (.fvar "opaque")⟩,
   ⟨"scope-application-checks-every-child", .wellScoped 1 (.apply "pair" [.bvar 0, .bvar 1])⟩,
   ⟨"scope-lambda-extends-context", .wellScoped 1 (.lambda "display" (.bvar 1))⟩,
   ⟨"scope-multilambda-extends-context", .wellScoped 0 (.multiLambda 2 ["a", "b"] (.bvar 1))⟩,
   ⟨"scope-substitution-has-distinct-child-contexts", .wellScoped 1 (.subst (.bvar 1) (.bvar 0))⟩,
   ⟨"scope-collection-preserves-rest-metadata", .wellScoped 1 (.collection .hashBag [.bvar 0, .bvar 0] (some "rest"))⟩,
   ⟨"scope-ordered-list", .wellScopedList 1 [.bvar 0, .lambda none (.bvar 1)]⟩,
   ⟨"scope-list-refuses-invalid-member", .wellScopedList 1 [.bvar 0, .bvar 1]⟩,
   ⟨"scope-index-first-duplicate", .index 4 [9, 4, 4]⟩,
   ⟨"scope-index-missing", .index 4 [9, 8]⟩,
   ⟨"scope-spine-empty", .spine 0 []⟩,
   ⟨"scope-spine-retains-authored-order", .spine 3 [.bvar 2, .bvar 0]⟩,
   ⟨"scope-spine-refuses-duplicate-variable", .spine 2 [.bvar 0, .bvar 0]⟩,
   ⟨"scope-spine-refuses-nonvariable", .spine 2 [.apply "constructor" []]⟩,
   ⟨"scope-spine-refuses-ambient-variable", .spine 2 [.bvar 2]⟩,
   ⟨"occurrence-assignment-supplies-opaque-argument", .assignment (.occurrence 1 2 [.fvar "opaque"]) 0⟩,
   ⟨"occurrence-assignment-fallback-is-exact", .assignment (.occurrence 1 2 []) 0⟩,
   ⟨"occurrence-assignment-shifts-ambient-index", .assignment (.occurrence 1 3 [.bvar 0]) 2⟩,
   ⟨"recovery-assignment-selects-spine-position", .assignment (.recovery 3 2 1 [2, 0]) 0⟩,
   ⟨"recovery-assignment-marks-unselected-local", .assignment (.recovery 3 2 1 [2, 0]) 1⟩,
   ⟨"scope-substitution-lifts-image-under-lambda", .substitute (.occurrence 1 2 [.bvar 1]) 0
      (.lambda "display" (.apply "pair" [.bvar 0, .bvar 1]))⟩,
   preservedSubstitution,
   ⟨"scope-substitution-collection-order-and-rest", .substitute (.occurrence 1 2 [.bvar 1]) 0
      (.collection .hashBag [.bvar 0, .bvar 0] (some "rest"))⟩,
   ⟨"scope-substitution-list-preserves-order", .substituteList (.recovery 3 2 1 [2, 0]) 0 [.bvar 2, .bvar 3, .fvar "opaque"]⟩,
   ⟨"instantiate-value-local-argument", .instantiate capturedBody 0 2 [.bvar 1]⟩,
   ⟨"instantiate-value-allows-nonvariable-argument", .instantiate capturedBody 0 0 [.apply "closed" []]⟩,
   ⟨"instantiate-value-refuses-ambient-mismatch", .instantiate capturedBody 1 2 [.bvar 1]⟩,
   ⟨"instantiate-value-refuses-arity-mismatch", .instantiate capturedBody 0 2 []⟩,
   ⟨"instantiate-value-refuses-unscoped-body", .instantiate ⟨[TypeExpr.term], 0, .bvar 1⟩ 0 2 [.bvar 0]⟩,
   ⟨"instantiate-value-refuses-unscoped-argument", .instantiate capturedBody 0 2 [.bvar 2]⟩,
   zeroSpine,
   oneSpine,
   ⟨"recover-retains-ambient-context-segment", .recover [TypeExpr.term] 1 2 [.bvar 1] (.bvar 2)⟩,
   ⟨"recover-under-lambda", .recover [TypeExpr.term] 0 2 [.bvar 1]
      (.lambda "display" (.apply "pair" [.bvar 0, .bvar 2]))⟩,
   ⟨"recover-refuses-unselected-local-dependence", .recover [TypeExpr.term] 0 2 [.bvar 1] (.bvar 0)⟩,
   ⟨"recover-refuses-duplicate-spine", .recover [TypeExpr.term, TypeExpr.term] 0 2 [.bvar 0, .bvar 0] (.bvar 0)⟩,
   ⟨"recover-refuses-nonvariable-spine", .recover [TypeExpr.term] 0 2 [.apply "a" []] (.bvar 0)⟩,
   ⟨"recover-refuses-arity-mismatch", .recover [TypeExpr.term] 0 2 [] (.apply "a" [])⟩,
   ⟨"recover-refuses-unscoped-target", .recover [TypeExpr.term] 0 2 [.bvar 1] (.bvar 2)⟩,
   ⟨"scope-assign-introduces-new-value", .assign [] "x" capturedBody⟩,
   repeatedAssignment,
   ⟨"scope-assign-refuses-repeated-body-conflict", .assign [("x", capturedBody)] "x" alternateBody⟩,
   ⟨"scope-assign-refuses-dependency-context-conflict", .assign [("x", capturedBody)] "x"
      ⟨[.base "Other"], 0, capturedBody.body⟩⟩,
   ⟨"scope-assign-refuses-ambient-context-conflict", .assign [("x", capturedBody)] "x"
      ⟨capturedBody.dependencies, 1, capturedBody.body⟩⟩]

theorem different_spines_recover_same_body :
    zeroSpine.expectedTerm = contextualValueOptionTerm (some capturedBody) ∧
    oneSpine.expectedTerm = contextualValueOptionTerm (some capturedBody) := by
  decide +kernel

def incorrectResults : List (Fixture × Term) :=
  [(zeroSpine, contextualValueOptionTerm none),
   (oneSpine, contextualValueOptionTerm (some alternateBody)),
   (preservedSubstitution, InferenceCettaWire.encodePattern (.apply "pair" [.bvar 1, .bvar 2])),
   (repeatedAssignment, scopedAssignmentOptionTerm (some [("x", capturedBody)]))]

theorem incorrect_results_are_distinct :
    ∀ result ∈ incorrectResults, result.2 ≠ result.1.expectedTerm := by
  decide +kernel

theorem incorrect_results_refused (state : State) :
    ∀ result ∈ incorrectResults,
      ¬ DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded result.1.queryTerm) }
        (.complete state [encoded result.2] [] []) := by
  intro result member computed
  have exactOutcome := (result.1.derivation_iff state state [encoded result.2] [] []).mp computed
  have same := (List.cons.inj exactOutcome.2.1).1
  exact incorrect_results_are_distinct result member (CettaWireAtom.encode_injective _ _ same)

end Controls

#print axioms helper_call
#print axioms well_scoped_returns
#print axioms well_scoped_list_captured_returns
#print axioms index_captured_returns
#print axioms variable_spine_captured_returns
#print axioms assignment_captured_returns
#print axioms substitute_captured_returns
#print axioms substitute_list_captured_returns
#print axioms assign_captured_returns
#print axioms instantiate_value_captured_returns
#print axioms recover_value_captured_returns
#print axioms Controls.Fixture.returns
#print axioms Controls.Fixture.derivation_iff
#print axioms Controls.different_spines_recover_same_body
#print axioms Controls.incorrect_results_are_distinct
#print axioms Controls.incorrect_results_refused


end ScopedCapture

#print axioms RowLookup.row_at_returns
#print axioms RowLookup.row_at_captured_returns

#print axioms lift_bvars_returns
#print axioms lift_bvars_list_returns
#print axioms instantiate_bvar_at_returns
#print axioms instantiate_bvar_list_at_returns
#print axioms instantiate_collection_returns
#print axioms apply_bindings_returns
#print axioms apply_bindings_captured_returns
#print axioms apply_bindings_children_returns
#print axioms apply_bindings_derivation_iff
#print axioms apply_bindings_results_returns
#print axioms apply_bindings_results_derivation_iff
#print axioms Controls.ObservationFixture.returns
#print axioms Controls.incorrect_general_results_are_distinct
#print axioms instantiate_returns
#print axioms instantiate_children_returns
#print axioms instantiate_applyBindings_returns
#print axioms instantiate_scoped_returns
#print axioms instantiate_derivation_iff
#print axioms instantiate_results_returns
#print axioms instantiate_results_derivation_iff
#print axioms apply_root_returns
#print axioms apply_root_compiled_returns
#print axioms apply_root_derivation_iff

section MetadataExecution

set_option maxHeartbeats 1200000

namespace ScopedCapture

open Mettapedia.OSLF.MeTTaIL

theorem scopedAssignmentTerm_injective :
    Function.Injective RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm := by
  let entryTerm : String × RuleBinding.ContextualValue → Term := fun entry =>
    .application "Binding" [.string entry.1, InferenceCettaWire.AuthoredRule.contextualValueTerm entry.2]
  have entryInjective : Function.Injective entryTerm := by
    intro first second same
    have arguments := (Term.application.inj same).2
    apply Prod.ext
    · exact Term.string.inj (List.cons.inj arguments).1
    · exact InferenceCettaWire.AuthoredRule.contextualValueTerm_injective
        (List.cons.inj (List.cons.inj arguments).2).1
  have sameWire (assignment : ScopedRuleMatching.Assignment) :
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment = encodeList entryTerm assignment := by
    simp only [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, encodeList_map,
      Function.comp_def, MatchAutomataBindingExecution.payloadBindingTerm, entryTerm]
  intro first second same
  apply encodeList_injective entryTerm entryInjective
  simpa only [sameWire] using same

theorem scopedAssignmentOptionTerm_injective :
    Function.Injective RuleInstantiationExecution.ScopedCapture.scopedAssignmentOptionTerm := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [RuleInstantiationExecution.ScopedCapture.scopedAssignmentOptionTerm,
      MatchAutomataBindingExecution.payloadOptionTerm, scopedAssignmentTerm_injective.eq_iff]


#print axioms scopedAssignmentTerm_injective
#print axioms scopedAssignmentOptionTerm_injective

end ScopedCapture

/-! ## Authored metadata lookup and occurrence capture

These equations inspect the lossless authored rule wire and realize the existing
RuleBinding site, dependency, and argument operations. Capture computes its
actual occurrence depth before reusing canonical recovery and assignment.
The typed occurrence bridge fixes ambient sorts independently; metadata lookup
and successful capture do not supply contextual rewrite permission.
-/

namespace ScopedMetadata

open Mettapedia.OSLF.MeTTaIL

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)

attribute [local simp] a v encoded number patternValue patternsValue

private inductive Helper where
  | dependencyRows | dependencies | occurrenceRows | quantifiedBody | sitePremise
  | premisePattern | premiseDepth | sitePattern | siteDepth | occurrenceName
  | occurrenceDepth | depthAtSite | occurrenceDeclared | arguments | capture | captureRest

private def Helper.head : Helper → String
  | .dependencyRows => "gslt:rule:scope-metadata-dependency-rows"
  | .dependencies => "gslt:rule:scope-metadata-dependencies"
  | .occurrenceRows => "gslt:rule:scope-metadata-occurrence-rows"
  | .quantifiedBody => "gslt:rule:scope-metadata-quantified-body"
  | .sitePremise => "gslt:rule:scope-metadata-site-premise"
  | .premisePattern => "gslt:rule:scope-metadata-premise-pattern"
  | .premiseDepth => "gslt:rule:scope-metadata-premise-depth"
  | .sitePattern => "gslt:rule:scope-metadata-site-pattern"
  | .siteDepth => "gslt:rule:scope-metadata-site-depth"
  | .occurrenceName => "gslt:rule:scope-metadata-occurrence-name"
  | .occurrenceDepth => "gslt:rule:scope-metadata-occurrence-depth"
  | .depthAtSite => "gslt:rule:scope-metadata-occurrence-depth-at-site"
  | .occurrenceDeclared => "gslt:rule:scope-metadata-occurrence-declared"
  | .arguments => "gslt:rule:scope-metadata-arguments"
  | .capture => "gslt:rule:scope-metadata-capture"
  | .captureRest => "gslt:rule:scope-metadata-capture-rest"

private def Helper.names : Helper → List String
  | .dependencyRows => ["rows", "name"]
  | .dependencies => ["spec", "name"]
  | .occurrenceRows => ["rows", "name", "site", "path"]
  | .quantifiedBody => ["count", "premise"]
  | .sitePremise => ["rule", "index", "quantifiers"]
  | .premisePattern => ["premise", "argument"]
  | .premiseDepth => ["premise", "argument"]
  | .sitePattern => ["rule", "site"]
  | .siteDepth => ["rule", "site"]
  | .occurrenceName => ["pattern", "path"]
  | .occurrenceDepth => ["pattern", "path", "depth"]
  | .depthAtSite => ["rule", "site", "path"]
  | .occurrenceDeclared => ["rule", "occurrence"]
  | .arguments => ["rule", "spec", "name", "site", "path"]
  | .capture => ["rule", "ambient", "site", "path", "assignment", "name", "target"]
  | .captureRest => ["rule", "ambient", "site", "path", "assignment", "name", "kind", "elements"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  ((program.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel))

private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] := by
  apply PureData.named_equation_clause program helper.head (equation helper) helper.names values
  · cases helper <;> rfl
  · cases helper <;> decide +kernel
  · cases helper <;> decide
  · exact length

private theorem lookup_cons (caller : Subst) (name query : String) (value : Atom) :
    Subst.lookup ((name, value) :: caller) query =
      if name == query then some value else Subst.lookup caller query := by
  simp only [Subst.lookup, List.find?_cons]
  cases same : (name == query) <;> simp

private theorem variable_cons (caller : Subst) (name query : String) (value : Atom) :
    applySubst ((name, value) :: caller) (v query) =
      if name == query then value else applySubst caller (v query) := by
  simp only [applySubst, lookup_cons]
  cases same : (name == query) <;> simp

attribute [local simp] lookup_cons variable_cons

private theorem captured_closed (values : List Atom) :
    values.map (applySubst []) = values := by
  induction values with
  | nil => rfl
  | cons first rest ih => rw [List.map_cons, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ih]

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw program helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem add_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "+" [v first, v second]) state (number (left + right)) := by
  apply native_variable_call_returns program caller state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

private theorem lt_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "<" [v first, v second]) state
      (Effects.boolean (decide (left < right))) := by
  apply native_variable_call_returns program caller state state "<" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simp [number, encoded, CettaWireAtom.encode]


private abbrev stringValue (name : String) : Atom := encoded (.string name)
private abbrev typeListValue (sorts : List TypeExpr) : Atom := encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm sorts)
private abbrev dependencyRowsValue (rows : List (String × List TypeExpr)) : Atom :=
  encoded (encodeList InferenceCettaWire.AuthoredRule.dependencyTerm rows)
private abbrev occurrenceRowsValue (rows : List MetavariableOccurrence) : Atom :=
  encoded (encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows)
private abbrev specValue (spec : RuleBindingSpec) : Atom := encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)
private abbrev siteValue (site : RulePatternSite) : Atom := encoded (InferenceCettaWire.AuthoredRule.siteTerm site)
private abbrev pathValue (path : List Nat) : Atom := encoded (encodeList Term.natural path)
private abbrev ruleValue (rule : RewriteRule) : Atom := encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
private abbrev premiseValue (premise : Premise) : Atom := encoded (InferenceCettaWire.AuthoredRule.premiseTerm premise)

private theorem some_returns (caller : Subst) (state : State) (code value : Atom)
    (returned : PureReturns program caller state code state value) :
    PureReturns program caller state (a "Some" [code]) state (a "Some" [value]) := by
  apply PureData.constructor_return program caller state "Some" [code] [value]
    (by decide +kernel) (by decide)
  exact .cons returned .nil

private def dependencyConsBody : Atom :=
  a "let" [v "tail", a Helper.dependencyRows.head [v "rest", v "name"],
    a "if" [a "==" [v "name", v "declared"],
      a "LCons" [a "RuleDependency" [v "declared", v "sorts"], v "tail"], v "tail"]]

private def dependencyCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "RuleDependency" [v "declared", v "sorts"], v "rest"], dependencyConsBody),
   (v "invalid", .symbol "LNil")]

private theorem dependency_rows_shape : (equation .dependencyRows).body =
    a "case" [v "rows", .expression (dependencyCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem dependency_cons_template : PureData.Template program
    (a "LCons" [a "RuleDependency" [v "declared", v "sorts"], v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro child member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "RuleDependency" _ (by decide +kernel) (by decide)
    intro child member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

theorem dependency_rows_returns (state : State) (rows : List (String × List TypeExpr)) (name : String) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-dependency-rows" [dependencyRowsValue rows, stringValue name]) state
      (dependencyRowsValue (rows.filter (fun row => row.1 == name))) := by
  induction rows with
  | nil =>
      let caller := environment .dependencyRows [dependencyRowsValue [], stringValue name]
      apply helper_call .dependencyRows [] state _
        [dependencyRowsValue [], stringValue name] _ rfl
        (captured_closed _)
      rw [dependency_rows_shape]
      apply case_returns program caller caller state state state (v "rows") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ dependencyCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, dependencyRowsValue, applySubst, Subst.lookup]
          using variable_returns program caller state "rows"
      · simp [dependencyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons first rows ih =>
      rcases first with ⟨declared, sorts⟩
      let caller := environment .dependencyRows [dependencyRowsValue ((declared, sorts) :: rows), stringValue name]
      let selected := ("rest", dependencyRowsValue rows) :: ("sorts", typeListValue sorts) ::
        ("declared", stringValue declared) :: caller
      let tail := rows.filter (fun row => row.1 == name)
      let bound := ("tail", dependencyRowsValue tail) :: selected
      apply helper_call .dependencyRows [] state _
        [dependencyRowsValue ((declared, sorts) :: rows), stringValue name] _ rfl
        (captured_closed _)
      rw [dependency_rows_shape]
      apply case_returns program caller selected state state state (v "rows")
        (dependencyRowsValue ((declared, sorts) :: rows)) dependencyConsBody _ _ dependencyCases
        (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
          using variable_returns program caller state "rows"
      · simp [dependencyCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, dependencyRowsValue, typeListValue,
          InferenceCettaWire.AuthoredRule.dependencyTerm, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, environment, Helper.names, Subst.lookup]
      · apply named_let_returns selected state "tail" _ (dependencyRowsValue tail) _ _
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · exact helper_capture .dependencyRows selected state [v "rest", v "name"]
            [dependencyRowsValue rows, stringValue name] _ rfl
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
        · apply bool_if_returns bound state _ (decide (name = declared)) _ _ _
          · simpa only [Term.string.injEq] using CettaWireAtom.equality_captured_returns program bound state
              (.string name) (.string declared) "name" "declared"
              (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          · by_cases same : name = declared
            · subst declared
              simpa [dependencyRowsValue, typeListValue, InferenceCettaWire.encodeList, InferenceCettaWire.AuthoredRule.dependencyTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                bound, selected, caller, environment, Helper.names, Subst.lookup, tail] using
                PureData.template_return program bound state _ dependency_cons_template
            · simpa [same, Ne.symm same, dependencyRowsValue, bound, selected, caller,
                environment, Helper.names, applySubst, Subst.lookup, tail] using
                variable_returns program bound state "tail"

theorem dependency_rows_captured_returns (caller : Subst) (state : State)
    (rows : List (String × List TypeExpr)) (name : String) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [dependencyRowsValue rows, stringValue name]) :
    PureReturns program caller state
      (a "gslt:rule:scope-metadata-dependency-rows" [one, two]) state
      (dependencyRowsValue (rows.filter (fun row => row.1 == name))) :=
  helper_capture .dependencyRows caller state [one, two] [dependencyRowsValue rows, stringValue name]
    _ rfl captured (dependency_rows_returns state rows name)

def dependencyOptionTerm : Option (List TypeExpr) → Term
  | none => .symbol "None"
  | some sorts => .application "Some" [encodeList InferenceCettaWire.AuthoredRule.typeTerm sorts]

private def dependencyResultCases : SpaceSemantics.Cases :=
  [(a "LCons" [a "RuleDependency" [v "declared", v "sorts"], .symbol "LNil"],
      a "Some" [v "sorts"]),
   (v "other", .symbol "None")]

private def dependenciesBody : Atom := a "case"
  [a Helper.dependencyRows.head [v "dependencies", v "name"],
    .expression (dependencyResultCases.map fun row => .expression [row.1, row.2])]

private def dependenciesCases : SpaceSemantics.Cases :=
  [(a "RuleBindingSpec" [v "dependencies", v "occurrences"], dependenciesBody),
   (v "invalid", .symbol "None")]

private theorem dependencies_shape : (equation .dependencies).body = a "case"
    [v "spec", .expression (dependenciesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem dependencies_returns (state : State) (spec : RuleBindingSpec) (name : String) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-dependencies" [specValue spec, stringValue name]) state
      (encoded (dependencyOptionTerm (RuleBinding.dependencies? spec name))) := by
  let caller := environment .dependencies [specValue spec, stringValue name]
  let selected := ("occurrences", occurrenceRowsValue spec.occurrences) ::
    ("dependencies", dependencyRowsValue spec.dependencies) :: caller
  let matching := spec.dependencies.filter (fun row => row.1 == name)
  have computed := dependency_rows_captured_returns selected state spec.dependencies name
    (v "dependencies") (v "name")
    (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
  change PureReturns program selected state
    (a Helper.dependencyRows.head [v "dependencies", v "name"]) state (dependencyRowsValue matching) at computed
  apply helper_call .dependencies [] state _ [specValue spec, stringValue name] _ rfl
    (captured_closed _)
  rw [dependencies_shape]
  apply case_returns program caller selected state state state (v "spec") (specValue spec)
    dependenciesBody _ _ dependenciesCases (read_cases_encoded _) _ _ _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "spec"
  · simp [dependenciesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, specValue,
      InferenceCettaWire.AuthoredRule.bindingSpecTerm, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      occurrenceRowsValue, dependencyRowsValue, selected, caller, environment, Helper.names, Subst.lookup]
  · cases result : matching with
    | nil =>
        have output : RuleBinding.dependencies? spec name = none := by
          have physical : spec.dependencies.filter (fun row => row.1 == name) = [] := result
          simp only [RuleBinding.dependencies?, physical]
        rw [output]
        apply case_returns program selected (("other", .symbol "LNil") :: selected)
          state state state _ (.symbol "LNil") (.symbol "None") (.symbol "None")
          _ dependencyResultCases (read_cases_encoded _) _ _ _
        · simpa only [result, dependencyRowsValue, encodeList, CettaWireAtom.encode] using computed
        · simp [dependencyResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom,
            selected, caller, environment, Helper.names, Subst.lookup]
        · exact symbol_returns program _ state "None"
    | cons row rest =>
        rcases row with ⟨declared, sorts⟩
        cases rest with
        | nil =>
            have output : RuleBinding.dependencies? spec name = some sorts := by
              have physical : spec.dependencies.filter (fun row => row.1 == name) = [(declared, sorts)] := result
              simp only [RuleBinding.dependencies?, physical]
            rw [output]
            let bound := ("sorts", typeListValue sorts) :: ("declared", stringValue declared) :: selected
            apply case_returns program selected bound state state state _
              (dependencyRowsValue [(declared, sorts)]) (a "Some" [v "sorts"])
              (encoded (dependencyOptionTerm (some sorts))) _ dependencyResultCases
              (read_cases_encoded _) _ _ _
            · simpa only [result] using computed
            · simp [dependencyResultCases, dependencyRowsValue, typeListValue,
                InferenceCettaWire.AuthoredRule.dependencyTerm, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, bound, selected, caller,
                environment, Helper.names, Subst.lookup]
            · apply some_returns bound state (v "sorts") (typeListValue sorts)
              simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "sorts"
        | cons next rest =>
            have output : RuleBinding.dependencies? spec name = none := by
              have physical : spec.dependencies.filter (fun row => row.1 == name) = (declared, sorts) :: next :: rest := result
              simp only [RuleBinding.dependencies?, physical]
            rw [output]
            apply case_returns program selected
              (("other", dependencyRowsValue ((declared, sorts) :: next :: rest)) :: selected)
              state state state _ (dependencyRowsValue ((declared, sorts) :: next :: rest))
              (.symbol "None") (.symbol "None") _ dependencyResultCases (read_cases_encoded _) _ _ _
            · simpa only [result] using computed
            · rcases next with ⟨otherName, otherSorts⟩
              simp [dependencyResultCases, dependencyRowsValue,
                InferenceCettaWire.AuthoredRule.dependencyTerm, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller,
                environment, Helper.names, Subst.lookup]
            · exact symbol_returns program _ state "None"

theorem dependencies_captured_returns (caller : Subst) (state : State)
    (spec : RuleBindingSpec) (name : String) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [specValue spec, stringValue name]) :
    PureReturns program caller state
      (a "gslt:rule:scope-metadata-dependencies" [one, two]) state
      (encoded (dependencyOptionTerm (RuleBinding.dependencies? spec name))) :=
  helper_capture .dependencies caller state [one, two] [specValue spec, stringValue name]
    _ rfl captured (dependencies_returns state spec name)

private theorem site_wire_eq (first second : RulePatternSite) :
    InferenceCettaWire.AuthoredRule.siteTerm first = InferenceCettaWire.AuthoredRule.siteTerm second ↔ first = second := by
  constructor
  · intro same
    have decoded := congrArg InferenceCettaWire.AuthoredRule.decodeSite? same
    simpa using decoded
  · exact congrArg InferenceCettaWire.AuthoredRule.siteTerm

private theorem path_wire_eq (first second : List Nat) :
    encodeList Term.natural first = encodeList Term.natural second ↔ first = second := by
  constructor
  · intro same
    exact encodeList_injective Term.natural (fun _ _ same => Term.natural.inj same) same
  · exact congrArg (encodeList Term.natural)

private def occurrenceKeep : Atom := a "LCons"
  [a "RuleOccurrence" [v "declared", v "actual-site", v "actual-path", v "arguments"], v "tail"]

private def occurrenceConsBody : Atom :=
  a "let" [v "tail", a Helper.occurrenceRows.head [v "rest", v "name", v "site", v "path"],
    a "if" [a "==" [v "name", v "declared"],
      a "if" [a "==" [v "site", v "actual-site"],
        a "if" [a "==" [v "path", v "actual-path"], occurrenceKeep, v "tail"],
        v "tail"], v "tail"]]

private def occurrenceCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "RuleOccurrence" [v "declared", v "actual-site", v "actual-path", v "arguments"],
      v "rest"], occurrenceConsBody),
   (v "invalid", .symbol "LNil")]

private theorem occurrence_rows_shape : (equation .occurrenceRows).body =
    a "case" [v "rows", .expression (occurrenceCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem occurrence_keep_template : PureData.Template program occurrenceKeep := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro child member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "RuleOccurrence" _ (by decide +kernel) (by decide)
    intro child member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact .captured _
  · exact .captured _

theorem occurrence_rows_returns (state : State) (rows : List MetavariableOccurrence)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-occurrence-rows"
        [occurrenceRowsValue rows, stringValue name, siteValue site, pathValue path]) state
      (occurrenceRowsValue (rows.filter (fun row => row.name == name && row.site == site && row.path == path))) := by
  induction rows with
  | nil =>
      let values := [occurrenceRowsValue [], stringValue name, siteValue site, pathValue path]
      let caller := environment .occurrenceRows values
      apply helper_call .occurrenceRows [] state _ values _ rfl
        (captured_closed _)
      rw [occurrence_rows_shape]
      apply case_returns program caller caller state state state (v "rows") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ occurrenceCases (read_cases_encoded _) _ _ _
      · simpa [caller, values, environment, Helper.names, occurrenceRowsValue, applySubst, Subst.lookup]
          using variable_returns program caller state "rows"
      · simp [occurrenceCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons first rows ih =>
      rcases first with ⟨declared, actualSite, actualPath, arguments⟩
      let values := [occurrenceRowsValue (⟨declared, actualSite, actualPath, arguments⟩ :: rows),
        stringValue name, siteValue site, pathValue path]
      let caller := environment .occurrenceRows values
      let selected := ("rest", occurrenceRowsValue rows) :: ("arguments", patternsValue arguments) ::
        ("actual-path", pathValue actualPath) :: ("actual-site", siteValue actualSite) ::
        ("declared", stringValue declared) :: caller
      let tail := rows.filter (fun row => row.name == name && row.site == site && row.path == path)
      let bound := ("tail", occurrenceRowsValue tail) :: selected
      apply helper_call .occurrenceRows [] state _ values _ rfl
        (captured_closed _)
      rw [occurrence_rows_shape]
      apply case_returns program caller selected state state state (v "rows")
        (occurrenceRowsValue (⟨declared, actualSite, actualPath, arguments⟩ :: rows)) occurrenceConsBody _
        _ occurrenceCases (read_cases_encoded _) _ _ _
      · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup]
          using variable_returns program caller state "rows"
      · simp [occurrenceCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, occurrenceRowsValue, patternsValue,
          siteValue, pathValue, InferenceCettaWire.encodeList, InferenceCettaWire.AuthoredRule.occurrenceTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, caller, values, environment, Helper.names, Subst.lookup]
      · apply named_let_returns selected state "tail" _ (occurrenceRowsValue tail) _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · exact helper_capture .occurrenceRows selected state
            [v "rest", v "name", v "site", v "path"]
            [occurrenceRowsValue rows, stringValue name, siteValue site, pathValue path] _ rfl
            (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup]) ih
        · apply bool_if_returns bound state _ (decide (name = declared)) _ _ _
          · simpa only [Term.string.injEq] using CettaWireAtom.equality_captured_returns program bound state
              (.string name) (.string declared) "name" "declared"
              (by simp [bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
              (by simp [bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
          · by_cases sameName : name = declared
            · subst declared
              simp only [decide_true, ↓reduceIte]
              apply bool_if_returns bound state _ (decide (site = actualSite)) _ _ _
              · simpa only [site_wire_eq] using CettaWireAtom.equality_captured_returns program bound state
                  (InferenceCettaWire.AuthoredRule.siteTerm site) (InferenceCettaWire.AuthoredRule.siteTerm actualSite)
                  "site" "actual-site"
                  (by simp [bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                  (by simp [bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
              · by_cases sameSite : site = actualSite
                · subst actualSite
                  simp only [decide_true, ↓reduceIte]
                  apply bool_if_returns bound state _ (decide (path = actualPath)) _ _ _
                  · simpa only [path_wire_eq] using CettaWireAtom.equality_captured_returns program bound state
                      (encodeList Term.natural path) (encodeList Term.natural actualPath) "path" "actual-path"
                      (by simp [bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                      (by simp [bound, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
                  · by_cases samePath : path = actualPath
                    · subst actualPath
                      simpa [occurrenceKeep, occurrenceRowsValue, siteValue, pathValue, InferenceCettaWire.encodeList, InferenceCettaWire.AuthoredRule.occurrenceTerm,
                        CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
                        bound, selected, caller, values, environment, Helper.names, Subst.lookup, tail]
                        using PureData.template_return program bound state _ occurrence_keep_template
                    · simpa [samePath, Ne.symm samePath, occurrenceRowsValue, bound, selected, caller,
                        values, environment, Helper.names, applySubst, Subst.lookup, tail]
                        using variable_returns program bound state "tail"
                · simpa [sameSite, Ne.symm sameSite, occurrenceRowsValue, bound, selected, caller,
                    values, environment, Helper.names, applySubst, Subst.lookup, tail]
                    using variable_returns program bound state "tail"
            · simpa [sameName, Ne.symm sameName, occurrenceRowsValue, bound, selected, caller,
                values, environment, Helper.names, applySubst, Subst.lookup, tail]
                using variable_returns program bound state "tail"

theorem occurrence_rows_captured_returns (caller : Subst) (state : State)
    (rows : List MetavariableOccurrence) (name : String) (site : RulePatternSite) (path : List Nat)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [occurrenceRowsValue rows, stringValue name, siteValue site, pathValue path]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-rows" [one, two, three, four]) state
      (occurrenceRowsValue (rows.filter (fun row => row.name == name && row.site == site && row.path == path))) :=
  helper_capture .occurrenceRows caller state [one, two, three, four]
    [occurrenceRowsValue rows, stringValue name, siteValue site, pathValue path] _ rfl captured
    (occurrence_rows_returns state rows name site path)

private theorem option_case_returns (caller : Subst) (state : State) (code : Atom)
    (value : Option Term) (name fallback : String) (yes no answer : Atom)
    (freshName : Subst.lookup caller name = none)
    (freshFallback : Subst.lookup caller fallback = none)
    (computed : PureReturns program caller state code state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm value)))
    (stopped : value = none → PureReturns program ((fallback, .symbol "None") :: caller)
      state no state answer)
    (continued : ∀ payload, value = some payload →
      PureReturns program ((name, encoded payload) :: caller) state yes state answer) :
    PureReturns program caller state (a "case" [code,
      .expression [.expression [a "Some" [v name], yes], .expression [v fallback, no]]]) state answer := by
  cases value with
  | none =>
      apply case_returns program caller ((fallback, .symbol "None") :: caller) state state state
        code (.symbol "None") no answer _ [(a "Some" [v name], yes), (v fallback, no)]
        (read_cases_encoded _) computed _ (stopped rfl)
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, freshFallback]
  | some payload =>
      apply case_returns program caller ((name, encoded payload) :: caller) state state state
        code (a "Some" [encoded payload]) yes answer _ [(a "Some" [v name], yes), (v fallback, no)]
        (read_cases_encoded _) computed _ (continued payload rfl)
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, freshName]

private theorem equal_zero_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "==" [v name, number 0]) state
      (Effects.boolean (decide (value = 0))) := by
  simpa only [Term.natural.injEq] using CettaWireAtom.equality_evaluated_returns program caller state
    (.natural value) (.natural 0) (v name) (number 0) (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns program caller state name)
    (grounded_returns program caller state (.int 0))

private theorem subtract_one_returns (caller : Subst) (state : State) (value : Nat)
    (name : String) (positive : 0 < value) (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "-" [v name, number 1]) state (number (value - 1)) := by
  apply native_binary_call_returns program caller state state state state "-"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.ofNat_sub positive, Int.natCast_one] using
      StdLib.integer_subtraction state (value : Int) 1

def premiseOptionTerm (result : Option Premise) : Term :=
  MatchAutomataBindingExecution.payloadOptionTerm (result.map InferenceCettaWire.AuthoredRule.premiseTerm)

private def quantifiedBodyNext : Atom := a "let"
  [v "previous", a "-" [v "count", number 1], a Helper.quantifiedBody.head [v "previous", v "body"]]

private def quantifiedBodyCases : SpaceSemantics.Cases :=
  [(a "ForAll" [v "collection", v "parameter", v "body"], quantifiedBodyNext),
   (v "other", .symbol "None")]

private theorem quantified_body_shape : (equation .quantifiedBody).body =
    a "if" [a "==" [v "count", number 0], a "Some" [v "premise"],
      a "case" [v "premise", .expression (quantifiedBodyCases.map fun row => .expression [row.1, row.2])]] := by
  decide +kernel

theorem quantified_body_returns (state : State) (count : Nat) (premise : Premise) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-quantified-body" [number count, premiseValue premise]) state
      (encoded (premiseOptionTerm (RuleBinding.quantifiedBody? count premise))) := by
  induction count generalizing premise with
  | zero =>
      let caller := environment .quantifiedBody [number 0, premiseValue premise]
      apply helper_call .quantifiedBody [] state _ [number 0, premiseValue premise] _ rfl
        (captured_closed _)
      rw [quantified_body_shape]
      apply bool_if_returns caller state _ true _ _ _
      · simpa only [decide_true] using equal_zero_returns caller state 0 "count"
          (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      · apply some_returns caller state (v "premise") (premiseValue premise)
        simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
          using variable_returns program caller state "premise"
  | succ count ih =>
      let caller := environment .quantifiedBody [number (count + 1), premiseValue premise]
      apply helper_call .quantifiedBody [] state _ [number (count + 1), premiseValue premise] _ rfl
        (captured_closed _)
      rw [quantified_body_shape]
      apply bool_if_returns caller state _ false _ _ _
      · simpa only [Nat.add_one_ne_zero, decide_false] using
          equal_zero_returns caller state (count + 1) "count"
            (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      · cases premise with
        | forAll collection parameter body =>
            let selected := ("body", premiseValue body) :: ("parameter", stringValue parameter) ::
              ("collection", stringValue collection) :: caller
            let bound := ("previous", number count) :: selected
            apply case_returns program caller selected state state state (v "premise")
              (premiseValue (.forAll collection parameter body)) quantifiedBodyNext _
              _ quantifiedBodyCases (read_cases_encoded _) _ _ _
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
                using variable_returns program caller state "premise"
            · simp [quantifiedBodyCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                selected, caller, environment, Helper.names, Subst.lookup]
            · apply named_let_returns selected state "previous" _ (number count) _ _
              · simp [selected, caller, environment, Helper.names, Subst.lookup]
              · simpa only [Nat.add_sub_cancel] using subtract_one_returns selected state (count + 1)
                  "count" (by omega)
                  (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              · exact helper_capture .quantifiedBody bound state [v "previous", v "body"]
                  [number count, premiseValue body] _ rfl
                  (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih body)
        | freshness condition =>
            apply case_returns program caller (("other", premiseValue (.freshness condition)) :: caller)
              state state state (v "premise") (premiseValue (.freshness condition)) (.symbol "None")
              (.symbol "None") _ quantifiedBodyCases (read_cases_encoded _) _ _ _
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
                using variable_returns program caller state "premise"
            · simp [quantifiedBodyCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, caller, environment, Helper.names, Subst.lookup]
            · exact symbol_returns program _ state "None"
        | congruence source target =>
            apply case_returns program caller (("other", premiseValue (.congruence source target)) :: caller)
              state state state (v "premise") (premiseValue (.congruence source target)) (.symbol "None")
              (.symbol "None") _ quantifiedBodyCases (read_cases_encoded _) _ _ _
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
                using variable_returns program caller state "premise"
            · simp [quantifiedBodyCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, caller, environment, Helper.names, Subst.lookup]
            · exact symbol_returns program _ state "None"
        | scopedStep step =>
            apply case_returns program caller (("other", premiseValue (.scopedStep step)) :: caller)
              state state state (v "premise") (premiseValue (.scopedStep step)) (.symbol "None")
              (.symbol "None") _ quantifiedBodyCases (read_cases_encoded _) _ _ _
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
                using variable_returns program caller state "premise"
            · simp [quantifiedBodyCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, caller, environment, Helper.names, Subst.lookup]
            · exact symbol_returns program _ state "None"
        | relationQuery relation arguments =>
            apply case_returns program caller (("other", premiseValue (.relationQuery relation arguments)) :: caller)
              state state state (v "premise") (premiseValue (.relationQuery relation arguments)) (.symbol "None")
              (.symbol "None") _ quantifiedBodyCases (read_cases_encoded _) _ _ _
            · simpa [caller, environment, Helper.names, applySubst, Subst.lookup]
                using variable_returns program caller state "premise"
            · simp [quantifiedBodyCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, caller, environment, Helper.names, Subst.lookup]
            · exact symbol_returns program _ state "None"

theorem quantified_body_captured_returns (caller : Subst) (state : State)
    (count : Nat) (premise : Premise) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number count, premiseValue premise]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-quantified-body" [one, two]) state
      (encoded (premiseOptionTerm (RuleBinding.quantifiedBody? count premise))) :=
  helper_capture .quantifiedBody caller state [one, two] [number count, premiseValue premise]
    _ rfl captured (quantified_body_returns state count premise)

private theorem environment_fresh (helper : Helper) (values : List Atom) (name : String)
    (missing : name ∉ helper.names) : Subst.lookup (environment helper values) name = none := by
  unfold environment Subst.lookup
  have absent : ((helper.names.zip values).reverse.find? (fun entry => entry.1 == name)) = none := by
    apply List.find?_eq_none.mpr
    intro entry member equal
    have declared := (List.of_mem_zip (List.mem_reverse.mp member)).1
    have same : entry.1 = name := by simpa using equal
    exact missing (same ▸ declared)
  rw [absent]
  rfl

private def rulePatternCode : Atom := a "ScopedRewriteRuleV1"
  [v "rule-name", v "context", v "premises", v "left", v "right", v "bindings"]

private def ruleCases (body invalid : Atom) : SpaceSemantics.Cases :=
  [(rulePatternCode, body), (v "invalid", invalid)]

private def ruleSelected (helper : Helper) (values : List Atom) (rule : RewriteRule) : Subst :=
  [("bindings", encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)),
   ("right", patternValue rule.right), ("left", patternValue rule.left),
   ("premises", encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)),
   ("context", encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext)),
   ("rule-name", stringValue rule.name)] ++ environment helper values

private theorem rule_selected_match (helper : Helper) (values : List Atom)
    (rule : RewriteRule) (body invalid : Atom) :
    SpaceSemantics.selectCase (environment helper values) (ruleValue rule) (ruleCases body invalid) =
      some (ruleSelected helper values rule, body) := by
  let names := ["rule-name", "context", "premises", "left", "right", "bindings"]
  let fields := [stringValue rule.name,
    encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext),
    encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises),
    patternValue rule.left, patternValue rule.right,
    encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)]
  have fieldsMatched := PureData.match_variable_values names fields (environment helper values)
    (by decide) rfl (by
      intro name member
      apply environment_fresh helper values name
      simp only [names, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> cases helper <;> decide)
  have matched : SpaceSemantics.matchValue (environment helper values) rulePatternCode (ruleValue rule) =
      some (ruleSelected helper values rule) := by
    change SpaceSemantics.matchValue (environment helper values)
      (.expression (.symbol "ScopedRewriteRuleV1" :: names.map v))
      (.expression (.symbol "ScopedRewriteRuleV1" :: fields)) = some (ruleSelected helper values rule)
    rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by intro first rest; simp [names])]
    rw [SpaceSemantics.matchValue.matchValues]
    change (SpaceSemantics.matchValue (environment helper values) (.symbol "ScopedRewriteRuleV1")
      (.symbol "ScopedRewriteRuleV1")).bind (fun bound =>
        SpaceSemantics.matchValue.matchValues bound (names.map v) fields) =
          some (ruleSelected helper values rule)
    have root : SpaceSemantics.matchValue (environment helper values) (.symbol "ScopedRewriteRuleV1")
        (.symbol "ScopedRewriteRuleV1") = some (environment helper values) := by
      simp [SpaceSemantics.matchValue, matchAtom]
    rw [root]
    simpa [names, fields, ruleSelected] using fieldsMatched
  simp only [ruleCases, SpaceSemantics.selectCase, matched]

private theorem retained_row_returns (caller : Subst) (state : State) (index : Nat)
    (values : List Term) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [number index, encoded (encodeList id values)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [v one, v two]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm values[index]?)) := by
  exact RowLookup.row_at_captured_returns caller state index values (v one) (v two) captured

private def sitePremiseBody : Atom := a "case" [a "gslt:rule:row-at" [v "index", v "premises"],
  .expression [.expression [a "Some" [v "premise"], a Helper.quantifiedBody.head [v "quantifiers", v "premise"]],
    .expression [v "other", .symbol "None"]]]

private theorem site_premise_shape : (equation .sitePremise).body =
    a "case" [v "rule", .expression ((ruleCases sitePremiseBody (.symbol "None")).map
      fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem site_premise_returns (state : State) (rule : RewriteRule) (index quantifiers : Nat) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-site-premise" [ruleValue rule, number index, number quantifiers]) state
      (encoded (premiseOptionTerm (rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers)))) := by
  let values := [ruleValue rule, number index, number quantifiers]
  let caller := environment .sitePremise values
  let selected := ruleSelected .sitePremise values rule
  have computed := retained_row_returns selected state index
    (rule.premises.map InferenceCettaWire.AuthoredRule.premiseTerm) "index" "premises"
    (by simp [selected, ruleSelected, values, environment, Helper.names, applySubst,
      Subst.lookup, encodeList_map])
  have lookup : (rule.premises.map InferenceCettaWire.AuthoredRule.premiseTerm)[index]? =
      rule.premises[index]?.map InferenceCettaWire.AuthoredRule.premiseTerm := List.getElem?_map
  rw [lookup] at computed
  apply helper_call .sitePremise [] state _ values _ rfl (captured_closed _)
  rw [site_premise_shape]
  apply case_returns program caller selected state state state (v "rule") (ruleValue rule) sitePremiseBody _
    _ (ruleCases sitePremiseBody (.symbol "None")) (read_cases_encoded _) _ _ _
  · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "rule"
  · exact rule_selected_match .sitePremise values rule _ _
  · apply option_case_returns selected state _ _ "premise" "other" _ _ _
    · simp [selected, ruleSelected, values, environment, Helper.names, Subst.lookup]
    · simp [selected, ruleSelected, values, environment, Helper.names, Subst.lookup]
    · exact computed
    · intro stopped
      have missing : rule.premises[index]? = none := by
        cases found : rule.premises[index]? <;> simp_all
      simpa [missing, premiseOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm,
        CettaWireAtom.encode] using symbol_returns program _ state "None"
    · intro payload present
      cases found : rule.premises[index]? with
      | none => simp [found] at present
      | some premise =>
          have same : payload = InferenceCettaWire.AuthoredRule.premiseTerm premise := by
            simpa [found] using present.symm
          subst payload
          simpa only [Helper.head, found, Option.bind_some] using quantified_body_captured_returns
            (("premise", premiseValue premise) :: selected) state quantifiers premise
            (v "quantifiers") (v "premise")
            (by simp [selected, ruleSelected, values, environment, Helper.names, applySubst, Subst.lookup])

theorem site_premise_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (index quantifiers : Nat) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [ruleValue rule, number index, number quantifiers]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-site-premise" [one, two, three]) state
      (encoded (premiseOptionTerm (rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers)))) :=
  helper_capture .sitePremise caller state [one, two, three]
    [ruleValue rule, number index, number quantifiers] _ rfl captured
    (site_premise_returns state rule index quantifiers)

private def selectedPremisePattern (premise : Premise) (argument : Nat) : Option Pattern :=
  match premise with
  | .freshness condition => if argument == 0 then some condition.term else none
  | .congruence source target => if argument == 0 then some source else if argument == 1 then some target else none
  | .scopedStep step => if argument == 0 then some step.source else if argument == 1 then some step.target else none
  | .relationQuery _ arguments => arguments[argument]?
  | .forAll _ _ _ => none

private def selectedPremiseDepth (premise : Premise) (argument : Nat) : Option Nat :=
  match premise with
  | .freshness _ => if argument == 0 then some 0 else none
  | .congruence _ _ => if argument < 2 then some 0 else none
  | .scopedStep step => if argument < 2 then some step.binders.length else none
  | .relationQuery _ arguments => if argument < arguments.length then some 0 else none
  | .forAll _ _ _ => none

private theorem site_pattern_given (rule : RewriteRule) (index quantifiers argument : Nat)
    (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise) :
    RuleBinding.sitePattern? rule (.premise index quantifiers argument) = selectedPremisePattern premise argument := by
  cases lookup : rule.premises[index]? with
  | none => simp [lookup] at found
  | some original =>
      have picked : RuleBinding.quantifiedBody? quantifiers original = some premise := by
        simpa [lookup] using found
      simp [RuleBinding.sitePattern?, lookup, picked, selectedPremisePattern]
      cases premise <;> rfl

private theorem site_depth_given (rule : RewriteRule) (index quantifiers argument : Nat)
    (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise) :
    RuleBinding.siteBinderDepth? rule (.premise index quantifiers argument) = selectedPremiseDepth premise argument := by
  cases lookup : rule.premises[index]? with
  | none => simp [lookup] at found
  | some original =>
      have picked : RuleBinding.quantifiedBody? quantifiers original = some premise := by
        simpa [lookup] using found
      simp [RuleBinding.siteBinderDepth?, lookup, picked, selectedPremiseDepth]
      cases premise <;> rfl

private theorem equal_number_returns (caller : Subst) (state : State) (value constant : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "==" [v name, number constant]) state
      (Effects.boolean (decide (value = constant))) := by
  simpa only [Term.natural.injEq] using CettaWireAtom.equality_evaluated_returns program caller state
    (.natural value) (.natural constant) (v name) (number constant) (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns program caller state name)
    (grounded_returns program caller state (.int constant))

private inductive PremiseLens where | pattern | depth
private def PremiseLens.helper : PremiseLens → Helper
  | .pattern => .premisePattern
  | .depth => .premiseDepth

private def premiseEndpoints : Atom := a "if" [a "==" [v "argument", number 0], a "Some" [v "source"],
  a "if" [a "==" [v "argument", number 1], a "Some" [v "target"], .symbol "None"]]

private def premiseLensCases : PremiseLens → SpaceSemantics.Cases
  | .pattern =>
      [(a "Freshness" [v "name", v "pattern"],
          a "if" [a "==" [v "argument", number 0], a "Some" [v "pattern"], .symbol "None"]),
       (a "Congruence" [v "source", v "target"], premiseEndpoints),
       (a "ScopedStep" [v "binders", v "sort", v "source", v "target"], premiseEndpoints),
       (a "RelationQuery" [v "relation", v "arguments"], a "gslt:rule:row-at" [v "argument", v "arguments"]),
       (v "other", .symbol "None")]
  | .depth =>
      [(a "Freshness" [v "name", v "pattern"],
          a "if" [a "==" [v "argument", number 0], a "Some" [number 0], .symbol "None"]),
       (a "Congruence" [v "source", v "target"],
          a "if" [a "<" [v "argument", number 2], a "Some" [number 0], .symbol "None"]),
       (a "ScopedStep" [v "binders", v "sort", v "source", v "target"],
          a "if" [a "<" [v "argument", number 2],
            a "let" [v "depth", a "gslt:automata:length" [v "binders"], a "Some" [v "depth"]], .symbol "None"]),
       (a "RelationQuery" [v "relation", v "arguments"],
          a "let" [v "length", a "gslt:automata:length" [v "arguments"],
            a "if" [a "<" [v "argument", v "length"], a "Some" [number 0], .symbol "None"]]),
       (v "other", .symbol "None")]

private theorem premise_lens_shape (form : PremiseLens) : (equation form.helper).body =
    a "case" [v "premise", .expression ((premiseLensCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private def premiseCaller (premise : Premise) (argument : Nat) : Subst :=
  [("argument", number argument), ("premise", premiseValue premise)]

private theorem premise_case_returns (form : PremiseLens) (state : State)
    (premise : Premise) (argument : Nat) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (premiseCaller premise argument)
      (premiseValue premise) (premiseLensCases form) = some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a form.helper.head [premiseValue premise, number argument]) state answer := by
  apply helper_call form.helper [] state _ [premiseValue premise, number argument] _
    (by cases form <;> rfl) (captured_closed _)
  rw [premise_lens_shape]
  have caller : environment form.helper [premiseValue premise, number argument] =
      premiseCaller premise argument := by cases form <;> rfl
  rw [caller]
  apply case_returns program (premiseCaller premise argument) selected state state state (v "premise")
    (premiseValue premise) body answer _ (premiseLensCases form) (read_cases_encoded _) _ matched returned
  simpa [premiseCaller, applySubst, Subst.lookup]
    using variable_returns program (premiseCaller premise argument) state "premise"

private theorem premise_endpoints_returns (caller : Subst) (state : State)
    (argument : Nat) (source target : Pattern)
    (argumentCaptured : applySubst caller (v "argument") = number argument)
    (sourceCaptured : applySubst caller (v "source") = patternValue source)
    (targetCaptured : applySubst caller (v "target") = patternValue target) :
    PureReturns program caller state premiseEndpoints state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (if argument == 0 then some source else if argument == 1 then some target else none))) := by
  apply bool_if_returns caller state _ (decide (argument = 0)) _ _ _
    (equal_zero_returns caller state argument "argument" argumentCaptured)
  by_cases zero : argument = 0
  · subst argument
    apply some_returns caller state (v "source") (patternValue source)
    simpa only [sourceCaptured] using variable_returns program caller state "source"
  · simp only [zero, decide_false, Bool.false_eq_true, ite_false]
    apply bool_if_returns caller state _ (decide (argument = 1)) _ _ _
      (equal_number_returns caller state argument 1 "argument" argumentCaptured)
    by_cases one : argument = 1
    · subst argument
      apply some_returns caller state (v "target") (patternValue target)
      simpa only [targetCaptured] using variable_returns program caller state "target"
    · simpa [zero, one, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode]
        using symbol_returns program caller state "None"

theorem premise_pattern_returns (state : State) (rule : RewriteRule) (index quantifiers argument : Nat)
    (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-premise-pattern" [premiseValue premise, number argument]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (RuleBinding.sitePattern? rule (.premise index quantifiers argument)))) := by
  rw [site_pattern_given rule index quantifiers argument premise found]
  simp only [selectedPremisePattern]
  cases premise with
  | freshness condition =>
      let caller := premiseCaller (.freshness condition) argument
      let selected := ("pattern", patternValue condition.term) :: ("name", stringValue condition.varName) :: caller
      apply premise_case_returns .pattern state (.freshness condition) argument selected
        (a "if" [a "==" [v "argument", number 0], a "Some" [v "pattern"], .symbol "None"])
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply bool_if_returns selected state _ (decide (argument = 0)) _ _ _
        · apply equal_zero_returns selected state argument "argument"
          simp [selected, caller, premiseCaller, applySubst, Subst.lookup]
        · by_cases zero : argument = 0
          · subst argument
            apply some_returns selected state (v "pattern") (patternValue condition.term)
            simpa [selected, applySubst, Subst.lookup] using variable_returns program selected state "pattern"
          · simpa [zero, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode]
              using symbol_returns program selected state "None"
  | congruence source target =>
      let caller := premiseCaller (.congruence source target) argument
      let selected := ("target", patternValue target) :: ("source", patternValue source) :: caller
      apply premise_case_returns .pattern state (.congruence source target) argument selected premiseEndpoints
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply premise_endpoints_returns selected state argument source target <;>
          simp [selected, caller, premiseCaller, applySubst, Subst.lookup]
  | scopedStep step =>
      let caller := premiseCaller (.scopedStep step) argument
      let selected := ("target", patternValue step.target) :: ("source", patternValue step.source) ::
        ("sort", encoded (InferenceCettaWire.AuthoredRule.typeTerm step.resultType)) ::
        ("binders", typeListValue step.binders) :: caller
      apply premise_case_returns .pattern state (.scopedStep step) argument selected premiseEndpoints
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply premise_endpoints_returns selected state argument step.source step.target <;>
          simp [selected, caller, premiseCaller, applySubst, Subst.lookup]
  | relationQuery relation arguments =>
      let caller := premiseCaller (.relationQuery relation arguments) argument
      let selected := ("arguments", patternsValue arguments) :: ("relation", stringValue relation) :: caller
      apply premise_case_returns .pattern state (.relationQuery relation arguments) argument selected
        (a "gslt:rule:row-at" [v "argument", v "arguments"])
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · have returned := retained_row_returns selected state argument
          (arguments.map InferenceCettaWire.encodePattern) "argument" "arguments"
          (by simp [selected, caller, premiseCaller, applySubst, Subst.lookup, encodeList_map,
            InferenceCettaWire.encodePatterns_eq_encodeList])
        rw [List.getElem?_map] at returned
        cases selectedArgument : arguments[argument]? <;>
          simpa [selectedArgument, MatchAutomataBindingExecution.patternOptionTerm,
            MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
  | forAll collection parameter body =>
      let caller := premiseCaller (.forAll collection parameter body) argument
      let selected := ("other", premiseValue (.forAll collection parameter body)) :: caller
      apply premise_case_returns .pattern state (.forAll collection parameter body) argument selected (.symbol "None")
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · exact symbol_returns program selected state "None"

theorem premise_pattern_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (index quantifiers argument : Nat) (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [premiseValue premise, number argument]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-premise-pattern" [one, two]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (RuleBinding.sitePattern? rule (.premise index quantifiers argument)))) :=
  helper_capture .premisePattern caller state [one, two] [premiseValue premise, number argument] _ rfl captured
    (premise_pattern_returns state rule index quantifiers argument premise found)

private theorem lt_number_returns (caller : Subst) (state : State) (value constant : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "<" [v name, number constant]) state
      (Effects.boolean (decide (value < constant))) := by
  apply native_binary_call_returns program caller state state state state "<"
    (v name) (number constant) (number value) (number constant) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int constant)
  · simp [number, encoded, CettaWireAtom.encode]

private theorem retained_length_returns (caller : Subst) (state : State)
    (values : List Term) (name : String)
    (captured : applySubst caller (v name) = encoded (encodeList id values)) :
    PureReturns program caller state (a "gslt:automata:length" [v name]) state (number values.length) := by
  apply RuleExecutionProgram.automata_captured_returns (by
    simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  exact MatchAutomataSourceExecution.length_captured_returns caller state values (v name) captured

private theorem depth_zero_returns (caller : Subst) (state : State) :
    PureReturns program caller state (a "Some" [number 0]) state
      (encoded (ScopedCapture.naturalOptionTerm (some 0))) :=
  some_returns caller state (number 0) (number 0) (grounded_returns program caller state (.int 0))

private theorem constant_depth_returns (caller : Subst) (state : State)
    (argument : Nat) (captured : applySubst caller (v "argument") = number argument) :
    PureReturns program caller state
      (a "if" [a "<" [v "argument", number 2], a "Some" [number 0], .symbol "None"]) state
      (encoded (ScopedCapture.naturalOptionTerm
        (if argument < 2 then some 0 else none))) := by
  apply bool_if_returns caller state _ (decide (argument < 2)) _ _ _
    (lt_number_returns caller state argument 2 "argument" captured)
  by_cases bounded : argument < 2
  · simpa only [bounded, decide_true, ite_true] using depth_zero_returns caller state
  · simpa [bounded, ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
      using symbol_returns program caller state "None"

theorem premise_depth_returns (state : State) (rule : RewriteRule) (index quantifiers argument : Nat)
    (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-premise-depth" [premiseValue premise, number argument]) state
      (encoded (ScopedCapture.naturalOptionTerm
        (RuleBinding.siteBinderDepth? rule (.premise index quantifiers argument)))) := by
  rw [site_depth_given rule index quantifiers argument premise found]
  simp only [selectedPremiseDepth]
  cases premise with
  | freshness condition =>
      let caller := premiseCaller (.freshness condition) argument
      let selected := ("pattern", patternValue condition.term) :: ("name", stringValue condition.varName) :: caller
      apply premise_case_returns .depth state (.freshness condition) argument selected
        (a "if" [a "==" [v "argument", number 0], a "Some" [number 0], .symbol "None"])
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply bool_if_returns selected state _ (decide (argument = 0)) _ _ _
        · apply equal_zero_returns selected state argument "argument"
          simp [selected, caller, premiseCaller, applySubst, Subst.lookup]
        · by_cases zero : argument = 0
          · subst argument
            exact depth_zero_returns selected state
          · simpa [zero, ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
              using symbol_returns program selected state "None"
  | congruence source target =>
      let caller := premiseCaller (.congruence source target) argument
      let selected := ("target", patternValue target) :: ("source", patternValue source) :: caller
      apply premise_case_returns .depth state (.congruence source target) argument selected
        (a "if" [a "<" [v "argument", number 2], a "Some" [number 0], .symbol "None"])
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply constant_depth_returns selected state argument
        simp [selected, caller, premiseCaller, applySubst, Subst.lookup]
  | scopedStep step =>
      let caller := premiseCaller (.scopedStep step) argument
      let selected := ("target", patternValue step.target) :: ("source", patternValue step.source) ::
        ("sort", encoded (InferenceCettaWire.AuthoredRule.typeTerm step.resultType)) ::
        ("binders", typeListValue step.binders) :: caller
      apply premise_case_returns .depth state (.scopedStep step) argument selected
        (a "if" [a "<" [v "argument", number 2],
          a "let" [v "depth", a "gslt:automata:length" [v "binders"], a "Some" [v "depth"]], .symbol "None"])
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply bool_if_returns selected state _ (decide (argument < 2)) _ _ _
        · apply lt_number_returns selected state argument 2 "argument"
          simp [selected, caller, premiseCaller, applySubst, Subst.lookup]
        · by_cases bounded : argument < 2
          · simp only [bounded, decide_true, ite_true]
            let bound := ("depth", number step.binders.length) :: selected
            apply named_let_returns selected state "depth" _ (number step.binders.length) _ _
            · simp [selected, caller, premiseCaller, Subst.lookup]
            · have returned := retained_length_returns selected state
                (step.binders.map InferenceCettaWire.AuthoredRule.typeTerm) "binders"
                (by simp [selected, typeListValue, applySubst, Subst.lookup, encodeList_map])
              simpa only [List.length_map] using returned
            · apply some_returns bound state (v "depth") (number step.binders.length)
              simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "depth"
          · simpa [bounded, ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
              using symbol_returns program selected state "None"
  | relationQuery relation arguments =>
      let caller := premiseCaller (.relationQuery relation arguments) argument
      let selected := ("arguments", patternsValue arguments) :: ("relation", stringValue relation) :: caller
      let bound := ("length", number arguments.length) :: selected
      apply premise_case_returns .depth state (.relationQuery relation arguments) argument selected
        (a "let" [v "length", a "gslt:automata:length" [v "arguments"],
          a "if" [a "<" [v "argument", v "length"], a "Some" [number 0], .symbol "None"]])
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · apply named_let_returns selected state "length" _ (number arguments.length) _ _
        · simp [selected, caller, premiseCaller, Subst.lookup]
        · have returned := retained_length_returns selected state (arguments.map InferenceCettaWire.encodePattern) "arguments"
            (by simp [selected, patternsValue, applySubst, Subst.lookup,
              InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map])
          simpa only [List.length_map] using returned
        · apply bool_if_returns bound state _ (decide (argument < arguments.length)) _ _ _
          · apply lt_variables_returns bound state argument arguments.length "argument" "length" <;>
              simp [bound, selected, caller, premiseCaller, applySubst, Subst.lookup]
          · by_cases bounded : argument < arguments.length
            · simpa only [bounded, decide_true, ite_true] using depth_zero_returns bound state
            · simpa [bounded, ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
                using symbol_returns program bound state "None"
  | forAll collection parameter body =>
      let caller := premiseCaller (.forAll collection parameter body) argument
      let selected := ("other", premiseValue (.forAll collection parameter body)) :: caller
      apply premise_case_returns .depth state (.forAll collection parameter body) argument selected (.symbol "None")
      · simp [premiseLensCases, premiseValue, InferenceCettaWire.AuthoredRule.premiseTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, premiseCaller, Subst.lookup]
      · exact symbol_returns program selected state "None"

theorem premise_depth_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (index quantifiers argument : Nat) (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [premiseValue premise, number argument]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-premise-depth" [one, two]) state
      (encoded (ScopedCapture.naturalOptionTerm
        (RuleBinding.siteBinderDepth? rule (.premise index quantifiers argument)))) :=
  helper_capture .premiseDepth caller state [one, two] [premiseValue premise, number argument] _ rfl captured
    (premise_depth_returns state rule index quantifiers argument premise found)

private inductive SiteLens where | pattern | depth
private def SiteLens.helper : SiteLens → Helper
  | .pattern => .sitePattern
  | .depth => .siteDepth
private def SiteLens.result (form : SiteLens) (rule : RewriteRule) (site : RulePatternSite) : Term :=
  match form with
  | .pattern => MatchAutomataBindingExecution.patternOptionTerm (RuleBinding.sitePattern? rule site)
  | .depth => ScopedCapture.naturalOptionTerm (RuleBinding.siteBinderDepth? rule site)
private def SiteLens.premiseHelper : SiteLens → Helper
  | .pattern => .premisePattern
  | .depth => .premiseDepth
private def siteLensPremiseBody (form : SiteLens) : Atom :=
  a "case" [a Helper.sitePremise.head [v "rule", v "index", v "quantifiers"],
    .expression [.expression [a "Some" [v "premise"],
      a form.premiseHelper.head [v "premise", v "argument"]],
      .expression [v "other", .symbol "None"]]]
private def SiteLens.leftBody : SiteLens → Atom
  | .pattern => a "Some" [v "left"]
  | .depth => a "Some" [number 0]
private def SiteLens.rightBody : SiteLens → Atom
  | .pattern => a "Some" [v "right"]
  | .depth => a "Some" [number 0]
private def siteLensCases (form : SiteLens) : SpaceSemantics.Cases :=
  [(.symbol "RuleLeft", form.leftBody),
   (.symbol "RuleRight", form.rightBody),
   (a "RulePremise" [v "index", v "quantifiers", v "argument"], siteLensPremiseBody form),
   (v "unknown", .symbol "None")]
private def siteLensBody (form : SiteLens) : Atom :=
  a "case" [v "site", .expression ((siteLensCases form).map fun row => .expression [row.1, row.2])]
private theorem site_lens_shape (form : SiteLens) : (equation form.helper).body =
    (match form with
    | .pattern => a "case" [v "rule", .expression ((ruleCases (siteLensBody form) (.symbol "None")).map
        fun row => .expression [row.1, row.2])]
    | .depth => siteLensBody form) := by
  cases form <;> decide +kernel

private theorem site_none (form : SiteLens) (rule : RewriteRule) (index quantifiers argument : Nat)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = none) :
    form.result rule (.premise index quantifiers argument) = .symbol "None" := by
  cases lookup : rule.premises[index]? with
  | none =>
      cases form <;> simp [SiteLens.result, RuleBinding.sitePattern?, RuleBinding.siteBinderDepth?, lookup,
        MatchAutomataBindingExecution.patternOptionTerm, ScopedCapture.naturalOptionTerm]
  | some original =>
      have picked : RuleBinding.quantifiedBody? quantifiers original = none := by simpa [lookup] using found
      cases form <;> simp [SiteLens.result, RuleBinding.sitePattern?, RuleBinding.siteBinderDepth?, lookup, picked,
        MatchAutomataBindingExecution.patternOptionTerm, ScopedCapture.naturalOptionTerm]

private theorem premise_lens_captured_returns (form : SiteLens) (caller : Subst) (state : State)
    (rule : RewriteRule) (index quantifiers argument : Nat) (premise : Premise)
    (found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = some premise)
    (captured : [v "premise", v "argument"].map (applySubst caller) = [premiseValue premise, number argument]) :
    PureReturns program caller state (a form.premiseHelper.head [v "premise", v "argument"]) state
      (encoded (form.result rule (.premise index quantifiers argument))) := by
  cases form with
  | pattern =>
      exact premise_pattern_captured_returns caller state rule index quantifiers argument premise found
        (v "premise") (v "argument") captured
  | depth =>
      exact premise_depth_captured_returns caller state rule index quantifiers argument premise found
        (v "premise") (v "argument") captured

private theorem site_lens_given_returns (form : SiteLens) (caller : Subst) (state : State)
    (rule : RewriteRule) (site : RulePatternSite)
    (ruleCaptured : applySubst caller (v "rule") = ruleValue rule)
    (siteCaptured : applySubst caller (v "site") = siteValue site)
    (leftCaptured : form = .pattern → applySubst caller (v "left") = patternValue rule.left)
    (rightCaptured : form = .pattern → applySubst caller (v "right") = patternValue rule.right)
    (fresh : ∀ name ∈ ["index", "quantifiers", "argument", "premise", "other", "unknown"],
      Subst.lookup caller name = none) :
    PureReturns program caller state (siteLensBody form) state (encoded (form.result rule site)) := by
  unfold siteLensBody
  cases site with
  | left =>
      apply case_returns program caller caller state state state (v "site") (siteValue .left) form.leftBody _ _
        (siteLensCases form) (read_cases_encoded _) _ _ _
      · simpa only [siteCaptured] using variable_returns program caller state "site"
      · simp [siteLensCases, siteValue, InferenceCettaWire.AuthoredRule.siteTerm, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · cases form with
        | pattern =>
            apply some_returns caller state (v "left") (patternValue rule.left)
            simpa only [leftCaptured rfl] using variable_returns program caller state "left"
        | depth => exact depth_zero_returns caller state
  | right =>
      apply case_returns program caller caller state state state (v "site") (siteValue .right) form.rightBody _ _
        (siteLensCases form) (read_cases_encoded _) _ _ _
      · simpa only [siteCaptured] using variable_returns program caller state "site"
      · simp [siteLensCases, siteValue, InferenceCettaWire.AuthoredRule.siteTerm, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · cases form with
        | pattern =>
            apply some_returns caller state (v "right") (patternValue rule.right)
            simpa only [rightCaptured rfl] using variable_returns program caller state "right"
        | depth => exact depth_zero_returns caller state
  | premise index quantifiers argument =>
      let selected := ("argument", number argument) :: ("quantifiers", number quantifiers) ::
        ("index", number index) :: caller
      apply case_returns program caller selected state state state (v "site")
        (siteValue (.premise index quantifiers argument)) (siteLensPremiseBody form) _ _
        (siteLensCases form) (read_cases_encoded _) _ _ _
      · simpa only [siteCaptured] using variable_returns program caller state "site"
      · simp [siteLensCases, siteValue, InferenceCettaWire.AuthoredRule.siteTerm, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, lookup_cons,
          fresh "index" (by simp), fresh "quantifiers" (by simp), fresh "argument" (by simp)]
      · apply option_case_returns selected state _ _ "premise" "other" _ _ _
        · simp [selected, fresh "premise" (by simp)]
        · simp [selected, fresh "other" (by simp)]
        · exact site_premise_captured_returns selected state rule index quantifiers
            (v "rule") (v "index") (v "quantifiers")
            (by simp [selected, ruleCaptured])
        · intro stopped
          have missing : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) = none := by
            cases found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) with
            | none => rfl
            | some premise => simp [found] at stopped
          simpa [site_none form rule index quantifiers argument missing, CettaWireAtom.encode]
            using symbol_returns program _ state "None"
        · intro payload present
          cases found : rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers) with
          | none => simp [found] at present
          | some premise =>
              have same : payload = InferenceCettaWire.AuthoredRule.premiseTerm premise := by
                simpa [premiseOptionTerm, found] using present.symm
              subst payload
              exact premise_lens_captured_returns form (("premise", premiseValue premise) :: selected)
                state rule index quantifiers argument premise found
                (by simp [selected])

theorem site_pattern_returns (state : State) (rule : RewriteRule) (site : RulePatternSite) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-site-pattern" [ruleValue rule, siteValue site]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm (RuleBinding.sitePattern? rule site))) := by
  let values := [ruleValue rule, siteValue site]
  let caller := environment .sitePattern values
  let selected := ruleSelected .sitePattern values rule
  apply helper_call .sitePattern [] state _ values _ rfl (captured_closed _)
  rw [show (equation .sitePattern).body = _ from site_lens_shape .pattern]
  apply case_returns program caller selected state state state (v "rule") (ruleValue rule)
    (siteLensBody .pattern) _ _ (ruleCases (siteLensBody .pattern) (.symbol "None"))
    (read_cases_encoded _) _ (rule_selected_match .sitePattern values rule _ _) _
  · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "rule"
  · apply site_lens_given_returns .pattern selected state rule site
    · simp [selected, ruleSelected, values, environment, Helper.names, applySubst, Subst.lookup]
    · simp [selected, ruleSelected, values, environment, Helper.names, applySubst, Subst.lookup]
    · intro _; simp [selected, ruleSelected, applySubst, Subst.lookup]
    · intro _; simp [selected, ruleSelected, applySubst, Subst.lookup]
    · intro name member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [selected, ruleSelected, values, environment, Helper.names, Subst.lookup]

theorem site_pattern_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (site : RulePatternSite) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [ruleValue rule, siteValue site]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-site-pattern" [one, two]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm (RuleBinding.sitePattern? rule site))) :=
  helper_capture .sitePattern caller state [one, two] [ruleValue rule, siteValue site] _ rfl captured
    (site_pattern_returns state rule site)

theorem site_depth_returns (state : State) (rule : RewriteRule) (site : RulePatternSite) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-site-depth" [ruleValue rule, siteValue site]) state
      (encoded (ScopedCapture.naturalOptionTerm (RuleBinding.siteBinderDepth? rule site))) := by
  let values := [ruleValue rule, siteValue site]
  let caller := environment .siteDepth values
  apply helper_call .siteDepth [] state _ values _ rfl (captured_closed _)
  rw [show (equation .siteDepth).body = _ from site_lens_shape .depth]
  apply site_lens_given_returns .depth caller state rule site
  · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · simp [caller, values, environment, Helper.names, applySubst, Subst.lookup]
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro name member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [caller, values, environment, Helper.names, Subst.lookup]

theorem site_depth_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (site : RulePatternSite) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [ruleValue rule, siteValue site]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-site-depth" [one, two]) state
      (encoded (ScopedCapture.naturalOptionTerm (RuleBinding.siteBinderDepth? rule site))) :=
  helper_capture .siteDepth caller state [one, two] [ruleValue rule, siteValue site] _ rfl captured
    (site_depth_returns state rule site)

private inductive OccurrenceLens where | name | depth
private def OccurrenceLens.helper : OccurrenceLens → Helper
  | .name => .occurrenceName
  | .depth => .occurrenceDepth
private def OccurrenceLens.arguments (form : OccurrenceLens) (pattern path depth : Atom) : List Atom :=
  match form with
  | .name => [pattern, path]
  | .depth => [pattern, path, depth]
private def OccurrenceLens.result (form : OccurrenceLens) (pattern : Pattern) (path : List Nat) (depth : Nat) : Term :=
  match form with
  | .name => MatchAutomataBindingExecution.payloadOptionTerm
      ((RuleBinding.occurrenceAt? pattern path).map Term.string)
  | .depth => ScopedCapture.naturalOptionTerm
      (RuleBinding.occurrenceDepthAt? pattern path depth)
private def occurrenceCall (form : OccurrenceLens) (pattern path depth : Atom) : Atom :=
  a form.helper.head (form.arguments pattern path depth)
private def OccurrenceLens.payload : OccurrenceLens → Atom
  | .name => v "name"
  | .depth => v "depth"
private def occurrenceNilBody (form : OccurrenceLens) : Atom :=
  a "case" [v "pattern", .expression [
    .expression [a "FVar" [v "name"],
      a "Some" [form.payload]],
    .expression [v "other", .symbol "None"]]]
private def occurrenceChildrenBody (form : OccurrenceLens) (children : String) : Atom :=
  a "case" [a "gslt:rule:row-at" [v "index", v children], .expression [
    .expression [a "Some" [v "child"], occurrenceCall form (v "child") (v "rest") (v "depth")],
    .expression [v "missing", .symbol "None"]]]
private def occurrenceBinderBody (form : OccurrenceLens) (amount : Atom) : Atom :=
  match form with
  | .name => occurrenceCall form (v "body") (v "rest") (v "depth")
  | .depth => a "let" [v "next", a "+" [v "depth", amount],
      occurrenceCall form (v "body") (v "rest") (v "next")]
private def occurrenceRestBody (form : OccurrenceLens) : Atom :=
  a "case" [v "rest", .expression [
    .expression [.symbol "LNil", a "case" [v "tail", .expression [
      .expression [a "RSome" [v "name"],
        a "Some" [form.payload]],
      .expression [v "missing", .symbol "None"]]]],
    .expression [v "remaining", .symbol "None"]]]
private def occurrenceCollectionBody (form : OccurrenceLens) : Atom :=
  a "let" [v "length", a "gslt:automata:length" [v "elements"],
    a "if" [a "<" [v "index", v "length"], occurrenceChildrenBody form "elements",
      a "if" [a "==" [v "index", v "length"], occurrenceRestBody form, .symbol "None"]]]
private def occurrencePatternCases (form : OccurrenceLens) : SpaceSemantics.Cases :=
  [(a "PApp" [v "head", v "arguments"], occurrenceChildrenBody form "arguments"),
   (a "PLam" [v "binder", v "body"],
      a "if" [a "==" [v "index", number 0], occurrenceBinderBody form (number 1), .symbol "None"]),
   (a "PMultiLam" [v "arity", v "binders", v "body"],
      a "if" [a "==" [v "index", number 0], occurrenceBinderBody form (v "arity"), .symbol "None"]),
   (a "PSubst" [v "body", v "replacement"],
      a "if" [a "==" [v "index", number 0], occurrenceBinderBody form (number 1),
        a "if" [a "==" [v "index", number 1],
          occurrenceCall form (v "replacement") (v "rest") (v "depth"), .symbol "None"]]),
   (a "PCollection" [v "kind", v "elements", v "tail"], occurrenceCollectionBody form),
   (v "other", .symbol "None")]
private def occurrencePathCases (form : OccurrenceLens) : SpaceSemantics.Cases :=
  [(.symbol "LNil", occurrenceNilBody form),
   (a "LCons" [v "index", v "rest"],
      a "case" [v "pattern", .expression ((occurrencePatternCases form).map
        fun row => .expression [row.1, row.2])]),
   (v "invalid", .symbol "None")]
private theorem occurrence_lens_shape (form : OccurrenceLens) : (equation form.helper).body =
    a "case" [v "path", .expression ((occurrencePathCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private theorem occurrence_capture (form : OccurrenceLens) (caller : Subst) (state : State)
    (pattern : Pattern) (path : List Nat) (depth : Nat) (one two three : Atom)
    (captured : (form.arguments one two three).map (applySubst caller) =
      form.arguments (patternValue pattern) (pathValue path) (number depth))
    (returned : PureReturns program [] state
      (occurrenceCall form (patternValue pattern) (pathValue path) (number depth)) state
      (encoded (form.result pattern path depth))) :
    PureReturns program caller state (occurrenceCall form one two three) state
      (encoded (form.result pattern path depth)) := by
  apply helper_capture form.helper caller state (form.arguments one two three)
    (form.arguments (patternValue pattern) (pathValue path) (number depth)) _
    (by cases form <;> rfl) captured returned

private theorem occurrence_nil_returns (form : OccurrenceLens) (caller : Subst) (state : State)
    (pattern : Pattern) (depth : Nat)
    (captured : applySubst caller (v "pattern") = patternValue pattern)
    (depthCaptured : form = .depth → applySubst caller (v "depth") = number depth)
    (fresh : Subst.lookup caller "name" = none ∧ Subst.lookup caller "other" = none) :
    PureReturns program caller state (occurrenceNilBody form) state
      (encoded (form.result pattern [] depth)) := by
  cases pattern
  case fvar name =>
    let selected := ("name", stringValue name) :: caller
    apply case_returns program caller selected state state state (v "pattern") (patternValue (.fvar name))
      (a "Some" [form.payload]) _ _
      [(a "FVar" [v "name"], a "Some" [form.payload]), (v "other", .symbol "None")]
      (read_cases_encoded _) _ _ _
    · simpa only [captured] using variable_returns program caller state "pattern"
    · simp [selected, patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, fresh.1]
    · cases form with
      | name =>
          apply some_returns selected state (v "name") (stringValue name)
          simpa [selected] using variable_returns program selected state "name"
      | depth =>
          apply some_returns selected state (v "depth") (number depth)
          simpa [selected, depthCaptured rfl] using variable_returns program selected state "depth"
  all_goals
    let selected := ("other", applySubst caller (v "pattern")) :: caller
    apply case_returns program caller selected state state state (v "pattern") (applySubst caller (v "pattern"))
      (.symbol "None") _ _ [(a "FVar" [v "name"], a "Some" [form.payload]), (v "other", .symbol "None")]
      (read_cases_encoded _) (variable_returns program caller state "pattern") _ _
    · simp [selected, captured, patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, fresh.2]
    · cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
        MatchAutomataBindingExecution.payloadOptionTerm, ScopedCapture.naturalOptionTerm,
        CettaWireAtom.encode] using symbol_returns program selected state "None"

private theorem occurrence_children_returns (form : OccurrenceLens) (caller : Subst) (state : State)
    (patterns : List Pattern) (index : Nat) (path : List Nat) (depth : Nat) (children : String)
    (childrenCaptured : applySubst caller (v children) = patternsValue patterns)
    (indexCaptured : applySubst caller (v "index") = number index)
    (pathCaptured : applySubst caller (v "rest") = pathValue path)
    (depthCaptured : form = .depth → applySubst caller (v "depth") = number depth)
    (fresh : Subst.lookup caller "child" = none ∧ Subst.lookup caller "missing" = none)
    (earlier : ∀ child ∈ patterns, PureReturns program [] state
      (occurrenceCall form (patternValue child) (pathValue path) (number depth)) state
      (encoded (form.result child path depth))) :
    PureReturns program caller state (occurrenceChildrenBody form children) state
      (encoded (match form with
        | .name => MatchAutomataBindingExecution.payloadOptionTerm
          ((patterns[index]?.bind (RuleBinding.occurrenceAt? · path)).map Term.string)
        | .depth => ScopedCapture.naturalOptionTerm
          (patterns[index]?.bind (RuleBinding.occurrenceDepthAt? · path depth)))) := by
  have computed := retained_row_returns caller state index
    (patterns.map InferenceCettaWire.encodePattern) "index" children
    (by simp [indexCaptured, childrenCaptured, patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList,
      encodeList_map])
  rw [List.getElem?_map] at computed
  apply option_case_returns caller state _ _ "child" "missing" _ _ _ fresh.1 fresh.2 computed
  · intro stopped
    have missing : patterns[index]? = none := by
      cases found : patterns[index]? with
      | none => rfl
      | some child => simp [found] at stopped
    cases form <;> simpa [missing, OccurrenceLens.result, MatchAutomataBindingExecution.payloadOptionTerm,
      ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
      using symbol_returns program _ state "None"
  · intro payload present
    cases found : patterns[index]? with
    | none => simp [found] at present
    | some child =>
        have same : payload = InferenceCettaWire.encodePattern child := by simpa [found] using present.symm
        subst payload
        have member : child ∈ patterns := List.mem_of_getElem? found
        have returned := occurrence_capture form (("child", patternValue child) :: caller) state child path depth
          (v "child") (v "rest") (v "depth")
          (by
            cases form with
            | name => simp [OccurrenceLens.arguments, pathCaptured]
            | depth => simp [OccurrenceLens.arguments, pathCaptured, depthCaptured rfl])
          (earlier child member)
        cases form <;> simpa [found, OccurrenceLens.result] using returned

private theorem occurrence_binder_returns (form : OccurrenceLens) (caller : Subst) (state : State)
    (body : Pattern) (path : List Nat) (depth amount : Nat) (amountCode : Atom)
    (bodyCaptured : applySubst caller (v "body") = patternValue body)
    (pathCaptured : applySubst caller (v "rest") = pathValue path)
    (fresh : Subst.lookup caller "next" = none)
    (added : form = .depth → PureReturns program caller state
      (a "+" [v "depth", amountCode]) state (number (depth + amount)))
    (earlier : PureReturns program [] state
      (occurrenceCall form (patternValue body) (pathValue path) (number (depth + amount))) state
      (encoded (form.result body path (depth + amount)))) :
    PureReturns program caller state (occurrenceBinderBody form amountCode) state
      (encoded (form.result body path (depth + amount))) := by
  cases form with
  | name =>
      exact occurrence_capture .name caller state body path (depth + amount)
        (v "body") (v "rest") (v "depth")
        (by simp [OccurrenceLens.arguments, bodyCaptured, pathCaptured]) earlier
  | depth =>
      let bound := ("next", number (depth + amount)) :: caller
      apply named_let_returns caller state "next" _ (number (depth + amount)) _ _ fresh (added rfl)
      exact occurrence_capture .depth bound state body path (depth + amount)
        (v "body") (v "rest") (v "next")
        (by simp [bound, OccurrenceLens.arguments, bodyCaptured, pathCaptured]) earlier

private theorem equal_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (v first) = number left)
    (rightCaptured : applySubst caller (v second) = number right) :
    PureReturns program caller state (a "==" [v first, v second]) state
      (Effects.boolean (decide (left = right))) := by
  simpa only [Term.natural.injEq] using CettaWireAtom.equality_captured_returns program caller state
    (.natural left) (.natural right) first second leftCaptured rightCaptured

private theorem occurrence_rest_returns (form : OccurrenceLens) (caller : Subst) (state : State)
    (kind : CollType) (elements : List Pattern) (tail : Option String) (path : List Nat) (depth : Nat)
    (pathCaptured : applySubst caller (v "rest") = pathValue path)
    (tailCaptured : applySubst caller (v "tail") = encoded (InferenceCettaWire.encodeRest tail))
    (depthCaptured : form = .depth → applySubst caller (v "depth") = number depth)
    (fresh : ∀ name ∈ ["name", "missing", "remaining"], Subst.lookup caller name = none) :
    PureReturns program caller state (occurrenceRestBody form) state
      (encoded (form.result (.collection kind elements tail) (elements.length :: path) depth)) := by
  cases path with
  | nil =>
      apply case_returns program caller caller state state state (v "rest") (pathValue [])
        (a "case" [v "tail", .expression [
          .expression [a "RSome" [v "name"], a "Some" [form.payload]],
          .expression [v "missing", .symbol "None"]]]) _ _
        [(.symbol "LNil", a "case" [v "tail", .expression [
          .expression [a "RSome" [v "name"], a "Some" [form.payload]],
          .expression [v "missing", .symbol "None"]]]), (v "remaining", .symbol "None")]
        (read_cases_encoded _) _ _ _
      · simpa only [pathCaptured] using variable_returns program caller state "rest"
      · simp [pathValue, encodeList, CettaWireAtom.encode, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · cases tail with
        | none =>
            let selected := ("missing", .symbol "RNone") :: caller
            apply case_returns program caller selected state state state (v "tail") (.symbol "RNone")
              (.symbol "None") _ _ [(a "RSome" [v "name"], a "Some" [form.payload]), (v "missing", .symbol "None")]
              (read_cases_encoded _) _ _ _
            · simpa only [tailCaptured, InferenceCettaWire.encodeRest, CettaWireAtom.encode]
                using variable_returns program caller state "tail"
            · simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, selected,
                fresh "missing" (by simp)]
            · cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
                MatchAutomataBindingExecution.payloadOptionTerm, ScopedCapture.naturalOptionTerm,
                CettaWireAtom.encode] using symbol_returns program selected state "None"
        | some name =>
            let selected := ("name", stringValue name) :: caller
            apply case_returns program caller selected state state state (v "tail")
              (encoded (InferenceCettaWire.encodeRest (some name))) (a "Some" [form.payload]) _ _
              [(a "RSome" [v "name"], a "Some" [form.payload]), (v "missing", .symbol "None")]
              (read_cases_encoded _) _ _ _
            · simpa only [tailCaptured] using variable_returns program caller state "tail"
            · simp [InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, selected, fresh "name" (by simp)]
            · cases form with
              | name =>
                  have returned := some_returns selected state (v "name") (stringValue name)
                    (by simpa [selected] using variable_returns program selected state "name")
                  simpa [OccurrenceLens.result, OccurrenceLens.payload, RuleBinding.occurrenceAt?,
                    MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using returned
              | depth =>
                  have returned := some_returns selected state (v "depth") (number depth)
                    (by simpa [selected, depthCaptured rfl] using variable_returns program selected state "depth")
                  simpa [OccurrenceLens.result, OccurrenceLens.payload, RuleBinding.occurrenceDepthAt?,
                    ScopedCapture.naturalOptionTerm, CettaWireAtom.encode] using returned
  | cons index path =>
      let selected := ("remaining", pathValue (index :: path)) :: caller
      apply case_returns program caller selected state state state (v "rest") (pathValue (index :: path))
        (.symbol "None") _ _ [(.symbol "LNil", a "case" [v "tail", .expression [
          .expression [a "RSome" [v "name"], a "Some" [form.payload]],
          .expression [v "missing", .symbol "None"]]]), (v "remaining", .symbol "None")]
        (read_cases_encoded _) _ _ _
      · simpa only [pathCaptured] using variable_returns program caller state "rest"
      · simp [pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, selected,
          fresh "remaining" (by simp)]
      · cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
          MatchAutomataBindingExecution.payloadOptionTerm, ScopedCapture.naturalOptionTerm,
          CettaWireAtom.encode] using symbol_returns program selected state "None"

private theorem occurrence_collection_returns (form : OccurrenceLens) (caller : Subst) (state : State)
    (kind : CollType) (elements : List Pattern) (tail : Option String) (index : Nat) (path : List Nat) (depth : Nat)
    (elementsCaptured : applySubst caller (v "elements") = patternsValue elements)
    (tailCaptured : applySubst caller (v "tail") = encoded (InferenceCettaWire.encodeRest tail))
    (indexCaptured : applySubst caller (v "index") = number index)
    (pathCaptured : applySubst caller (v "rest") = pathValue path)
    (depthCaptured : form = .depth → applySubst caller (v "depth") = number depth)
    (fresh : ∀ name ∈ ["length", "child", "missing", "name", "remaining"], Subst.lookup caller name = none)
    (earlier : ∀ child ∈ elements, PureReturns program [] state
      (occurrenceCall form (patternValue child) (pathValue path) (number depth)) state
      (encoded (form.result child path depth))) :
    PureReturns program caller state (occurrenceCollectionBody form) state
      (encoded (form.result (.collection kind elements tail) (index :: path) depth)) := by
  let bound := ("length", number elements.length) :: caller
  apply named_let_returns caller state "length" _ (number elements.length) _ _
    (fresh "length" (by simp))
  · have returned := retained_length_returns caller state
      (elements.map InferenceCettaWire.encodePattern) "elements"
      (by simpa [patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList,
        encodeList_map, Function.comp_def] using elementsCaptured)
    simpa only [List.length_map] using returned
  · apply bool_if_returns bound state _ (decide (index < elements.length)) _ _ _
    · apply lt_variables_returns bound state index elements.length "index" "length" <;>
        simp [bound, indexCaptured]
    · by_cases bounded : index < elements.length
      · simp only [bounded, decide_true, ite_true]
        have returned := occurrence_children_returns form bound state elements index path depth "elements"
          (by simp [bound, elementsCaptured]) (by simp [bound, indexCaptured]) (by simp [bound, pathCaptured])
          (by intro same; simp [bound, depthCaptured same])
          (by simp [bound, fresh "child" (by simp), fresh "missing" (by simp)]) earlier
        cases form <;> simpa only [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
          bounded, ite_true] using returned
      · simp only [bounded, decide_false, Bool.false_eq_true, ite_false]
        apply bool_if_returns bound state _ (decide (index = elements.length)) _ _ _
        · apply equal_variables_returns bound state index elements.length "index" "length" <;>
            simp [bound, indexCaptured]
        · by_cases same : index = elements.length
          · subst index
            simp only [decide_true, ite_true]
            apply occurrence_rest_returns form bound state kind elements tail path depth
            · simp [bound, pathCaptured]
            · simp [bound, tailCaptured]
            · intro isDepth; simp [bound, depthCaptured isDepth]
            · intro name member
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
              rcases member with rfl | rfl | rfl <;> simp [bound, fresh]
          · cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
              bounded, same, MatchAutomataBindingExecution.payloadOptionTerm,
              ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
              using symbol_returns program bound state "None"

private def occurrenceCaller (form : OccurrenceLens) (pattern : Pattern) (path : List Nat) (depth : Nat) : Subst :=
  environment form.helper (form.arguments (patternValue pattern) (pathValue path) (number depth))
private def occurrenceConsCaller (form : OccurrenceLens) (pattern : Pattern) (index : Nat)
    (path : List Nat) (depth : Nat) : Subst :=
  [("rest", pathValue path), ("index", number index)] ++ occurrenceCaller form pattern (index :: path) depth
private def occurrencePatternBody (form : OccurrenceLens) : Atom :=
  a "case" [v "pattern", .expression ((occurrencePatternCases form).map fun row => .expression [row.1, row.2])]

private theorem occurrence_empty_returns (form : OccurrenceLens) (state : State) (pattern : Pattern) (depth : Nat) :
    PureReturns program [] state (occurrenceCall form (patternValue pattern) (pathValue []) (number depth)) state
      (encoded (form.result pattern [] depth)) := by
  let values := form.arguments (patternValue pattern) (pathValue []) (number depth)
  let caller := occurrenceCaller form pattern [] depth
  apply helper_call form.helper [] state _ values _ (by cases form <;> rfl) (captured_closed _)
  rw [occurrence_lens_shape]
  apply case_returns program caller caller state state state (v "path") (pathValue [])
    (occurrenceNilBody form) _ _ (occurrencePathCases form) (read_cases_encoded _) _ _ _
  · cases form <;> simpa [caller, values, occurrenceCaller, environment, OccurrenceLens.arguments,
      OccurrenceLens.helper, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "path"
  · simp [occurrencePathCases, pathValue, encodeList, CettaWireAtom.encode,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · apply occurrence_nil_returns form caller state pattern depth
    · cases form <;> simp [caller, occurrenceCaller, environment, OccurrenceLens.arguments,
        OccurrenceLens.helper, Helper.names, applySubst, Subst.lookup]
    · intro same; subst form
      simp [caller, occurrenceCaller, environment, OccurrenceLens.arguments,
        OccurrenceLens.helper, Helper.names, applySubst, Subst.lookup]
    · cases form <;> simp [caller, occurrenceCaller, environment, OccurrenceLens.arguments,
        OccurrenceLens.helper, Helper.names, Subst.lookup]

private theorem occurrence_cons_returns (form : OccurrenceLens) (state : State) (pattern : Pattern)
    (index : Nat) (path : List Nat) (depth : Nat)
    (returned : PureReturns program (occurrenceConsCaller form pattern index path depth) state
      (occurrencePatternBody form) state (encoded (form.result pattern (index :: path) depth))) :
    PureReturns program [] state
      (occurrenceCall form (patternValue pattern) (pathValue (index :: path)) (number depth)) state
      (encoded (form.result pattern (index :: path) depth)) := by
  let values := form.arguments (patternValue pattern) (pathValue (index :: path)) (number depth)
  let caller := occurrenceCaller form pattern (index :: path) depth
  apply helper_call form.helper [] state _ values _ (by cases form <;> rfl) (captured_closed _)
  rw [occurrence_lens_shape]
  apply case_returns program caller (occurrenceConsCaller form pattern index path depth) state state state
    (v "path") (pathValue (index :: path)) (occurrencePatternBody form) _ _
    (occurrencePathCases form) (read_cases_encoded _) _ _ returned
  · cases form <;> simpa [caller, values, occurrenceCaller, environment, OccurrenceLens.arguments,
      OccurrenceLens.helper, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "path"
  · cases form <;> simp [caller, occurrenceConsCaller, occurrenceCaller, environment, OccurrenceLens.arguments,
      OccurrenceLens.helper, Helper.names, pathValue, encodeList, occurrencePathCases, occurrencePatternBody, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem occurrence_lens_returns (form : OccurrenceLens) (state : State)
    (pattern : Pattern) (path : List Nat) (depth : Nat) :
    PureReturns program [] state
      (occurrenceCall form (patternValue pattern) (pathValue path) (number depth)) state
      (encoded (form.result pattern path depth)) := by
  induction path generalizing pattern depth with
  | nil => exact occurrence_empty_returns form state pattern depth
  | cons index path ih =>
      apply occurrence_cons_returns form state pattern index path depth
      let caller := occurrenceConsCaller form pattern index path depth
      cases pattern
      case apply head arguments =>
        let selected := ("arguments", patternsValue arguments) :: ("head", stringValue head) :: caller
        apply case_returns program caller selected state state state (v "pattern")
          (patternValue (.apply head arguments)) (occurrenceChildrenBody form "arguments") _ _
          (occurrencePatternCases form) (read_cases_encoded _) _ _ _
        · cases form <;> simpa [caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
            using variable_returns program caller state "pattern"
        · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup,
            occurrencePatternCases, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
        · have returned := occurrence_children_returns form selected state arguments index path depth "arguments"
            (by simp [selected])
            (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
            (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
            (by intro isDepth; subst form
                simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
            (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup])
            (by intro child _; exact ih child depth)
          cases form <;> simpa only [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?]
            using returned
      case lambda binder body =>
        let selected := ("body", patternValue body) :: ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
        apply case_returns program caller selected state state state (v "pattern")
          (patternValue (.lambda binder body))
          (a "if" [a "==" [v "index", number 0], occurrenceBinderBody form (number 1), .symbol "None"])
          _ _ (occurrencePatternCases form) (read_cases_encoded _) _ _ _
        · cases form <;> simpa [caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
            using variable_returns program caller state "pattern"
        · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup,
            occurrencePatternCases, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
        · apply bool_if_returns selected state _ (decide (index = 0)) _ _ _
          · apply equal_zero_returns selected state index "index"
            cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
          · by_cases zero : index = 0
            · subst index
              simp only [decide_true, ite_true]
              have returned := occurrence_binder_returns form selected state body path depth 1 (number 1)
                (by simp [selected])
                (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup])
                (by intro isDepth; subst form
                    apply add_one_returns selected state depth "depth"
                    simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                      OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                (ih body (depth + 1))
              cases form <;> simpa only [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?]
                using returned
            · cases index with
              | zero => exact False.elim (zero rfl)
              | succ index =>
                  cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
                    MatchAutomataBindingExecution.payloadOptionTerm,
                    ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
                    using symbol_returns program selected state "None"
      case multiLambda arity binders body =>
        let selected := ("body", patternValue body) ::
          ("binders", encoded (encodeList Term.string binders)) :: ("arity", number arity) :: caller
        apply case_returns program caller selected state state state (v "pattern")
          (patternValue (.multiLambda arity binders body))
          (a "if" [a "==" [v "index", number 0], occurrenceBinderBody form (v "arity"), .symbol "None"])
          _ _ (occurrencePatternCases form) (read_cases_encoded _) _ _ _
        · cases form <;> simpa [caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
            using variable_returns program caller state "pattern"
        · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup,
            occurrencePatternCases, patternValue, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeList,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
        · apply bool_if_returns selected state _ (decide (index = 0)) _ _ _
          · apply equal_zero_returns selected state index "index"
            cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
          · by_cases zero : index = 0
            · subst index
              simp only [decide_true, ite_true]
              have returned := occurrence_binder_returns form selected state body path depth arity (v "arity")
                (by simp [selected])
                (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup])
                (by intro isDepth; subst form
                    apply add_variables_returns selected state depth arity "depth" "arity" <;>
                      simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                        OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                (ih body (depth + arity))
              cases form <;> simpa only [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?]
                using returned
            · cases index with
              | zero => exact False.elim (zero rfl)
              | succ index =>
                  cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
                    MatchAutomataBindingExecution.payloadOptionTerm,
                    ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
                    using symbol_returns program selected state "None"
      case subst body replacement =>
        let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
        apply case_returns program caller selected state state state (v "pattern")
          (patternValue (.subst body replacement))
          (a "if" [a "==" [v "index", number 0], occurrenceBinderBody form (number 1),
            a "if" [a "==" [v "index", number 1],
              occurrenceCall form (v "replacement") (v "rest") (v "depth"), .symbol "None"]])
          _ _ (occurrencePatternCases form) (read_cases_encoded _) _ _ _
        · cases form <;> simpa [caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
            using variable_returns program caller state "pattern"
        · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup,
            occurrencePatternCases, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
        · apply bool_if_returns selected state _ (decide (index = 0)) _ _ _
          · apply equal_zero_returns selected state index "index"
            cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
          · by_cases zero : index = 0
            · subst index
              simp only [decide_true, ite_true]
              have returned := occurrence_binder_returns form selected state body path depth 1 (number 1)
                (by simp [selected])
                (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup])
                (by intro isDepth; subst form
                    apply add_one_returns selected state depth "depth"
                    simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                      OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                (ih body (depth + 1))
              cases form <;> simpa only [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?]
                using returned
            · simp only [zero, decide_false, Bool.false_eq_true, ite_false]
              apply bool_if_returns selected state _ (decide (index = 1)) _ _ _
              · apply equal_number_returns selected state index 1 "index"
                cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                  OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
              · by_cases one : index = 1
                · subst index
                  simp only [decide_true, ite_true]
                  have returned := occurrence_capture form selected state replacement path depth
                    (v "replacement") (v "rest") (v "depth")
                    (by cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                      OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup])
                    (ih replacement depth)
                  cases form <;> simpa only [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?]
                    using returned
                · cases index with
                  | zero => exact False.elim (zero rfl)
                  | succ index =>
                      cases index with
                      | zero => exact False.elim (one rfl)
                      | succ index =>
                          cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
                            MatchAutomataBindingExecution.payloadOptionTerm,
                            ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
                            using symbol_returns program selected state "None"
      case collection kind elements tail =>
        let selected := ("tail", encoded (InferenceCettaWire.encodeRest tail)) :: ("elements", patternsValue elements) ::
          ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
        apply case_returns program caller selected state state state (v "pattern")
          (patternValue (.collection kind elements tail)) (occurrenceCollectionBody form)
          _ _ (occurrencePatternCases form) (read_cases_encoded _) _ _ _
        · cases form <;> simpa [caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
            using variable_returns program caller state "pattern"
        · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup,
            occurrencePatternCases, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
        · apply occurrence_collection_returns form selected state kind elements tail index path depth
          · simp [selected]
          · simp [selected]
          · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
          · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
          · intro isDepth; subst form
            simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
              OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, applySubst, Subst.lookup]
          · intro name member
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl <;> cases form <;>
              simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
                OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup]
          · intro child _; exact ih child depth
      all_goals
        let selected := ("other", applySubst caller (v "pattern")) :: caller
        apply case_returns program caller selected state state state (v "pattern") (applySubst caller (v "pattern"))
          (.symbol "None") _ _ (occurrencePatternCases form) (read_cases_encoded _)
          (variable_returns program caller state "pattern") _ _
        · cases form <;> simp [selected, caller, occurrenceConsCaller, occurrenceCaller, environment,
            OccurrenceLens.helper, OccurrenceLens.arguments, Helper.names, Subst.lookup,
            occurrencePatternCases, applySubst, patternValue, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
        · cases form <;> simpa [OccurrenceLens.result, RuleBinding.occurrenceAt?, RuleBinding.occurrenceDepthAt?,
            MatchAutomataBindingExecution.payloadOptionTerm, ScopedCapture.naturalOptionTerm,
            CettaWireAtom.encode] using symbol_returns program selected state "None"

theorem occurrence_name_returns (state : State) (pattern : Pattern) (path : List Nat) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-occurrence-name" [patternValue pattern, pathValue path]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm
        ((RuleBinding.occurrenceAt? pattern path).map Term.string))) :=
  occurrence_lens_returns .name state pattern path 0

theorem occurrence_name_captured_returns (caller : Subst) (state : State)
    (pattern : Pattern) (path : List Nat) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [patternValue pattern, pathValue path]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-name" [one, two]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm
        ((RuleBinding.occurrenceAt? pattern path).map Term.string))) :=
  occurrence_capture .name caller state pattern path 0 one two (number 0) captured
    (occurrence_name_returns state pattern path)

theorem occurrence_depth_returns (state : State) (pattern : Pattern) (path : List Nat) (depth : Nat) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-occurrence-depth" [patternValue pattern, pathValue path, number depth]) state
      (encoded (ScopedCapture.naturalOptionTerm
        (RuleBinding.occurrenceDepthAt? pattern path depth))) :=
  occurrence_lens_returns .depth state pattern path depth

theorem occurrence_depth_captured_returns (caller : Subst) (state : State)
    (pattern : Pattern) (path : List Nat) (depth : Nat) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [patternValue pattern, pathValue path, number depth]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-depth" [one, two, three]) state
      (encoded (ScopedCapture.naturalOptionTerm
        (RuleBinding.occurrenceDepthAt? pattern path depth))) :=
  occurrence_capture .depth caller state pattern path depth one two three captured
    (occurrence_depth_returns state pattern path depth)

private theorem natural_option_wire (value : Option Nat) :
    MatchAutomataBindingExecution.payloadOptionTerm (value.map Term.natural) =
      ScopedCapture.naturalOptionTerm value := by
  cases value <;> rfl

private def depthAtSiteBody : Atom :=
  a "case" [a Helper.sitePattern.head [v "rule", v "site"],
    .expression [.expression [a "Some" [v "pattern"],
      a "case" [a Helper.siteDepth.head [v "rule", v "site"],
        .expression [.expression [a "Some" [v "depth"],
          a Helper.occurrenceDepth.head [v "pattern", v "path", v "depth"]],
          .expression [v "no-depth", .symbol "None"]]]],
      .expression [v "no-pattern", .symbol "None"]]]
private theorem depth_at_site_shape : (equation .depthAtSite).body = depthAtSiteBody := by decide +kernel

theorem depth_at_site_returns (state : State) (rule : RewriteRule) (site : RulePatternSite) (path : List Nat) :
    PureReturns program [] state
      (a "gslt:rule:scope-metadata-occurrence-depth-at-site" [ruleValue rule, siteValue site, pathValue path]) state
      (encoded (ScopedCapture.naturalOptionTerm (RuleBinding.occurrenceDepthAtSite? rule site path))) := by
  let values := [ruleValue rule, siteValue site, pathValue path]
  let caller := environment .depthAtSite values
  apply helper_call .depthAtSite [] state _ values _ rfl (captured_closed _)
  rw [depth_at_site_shape]
  apply option_case_returns caller state _ ((RuleBinding.sitePattern? rule site).map InferenceCettaWire.encodePattern)
    "pattern" "no-pattern" _ _ _
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · have returned := site_pattern_captured_returns caller state rule site (v "rule") (v "site")
      (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
    cases found : RuleBinding.sitePattern? rule site <;>
      simpa only [Helper.head, found, MatchAutomataBindingExecution.patternOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map_none, Option.map_some] using returned
  · intro stopped
    have missing : RuleBinding.sitePattern? rule site = none := by
      cases found : RuleBinding.sitePattern? rule site with
      | none => rfl
      | some pattern => simp [found] at stopped
    simpa [RuleBinding.occurrenceDepthAtSite?, missing, ScopedCapture.naturalOptionTerm,
      CettaWireAtom.encode] using symbol_returns program _ state "None"
  · intro payload present
    cases found : RuleBinding.sitePattern? rule site with
    | none => simp [found] at present
    | some pattern =>
        have same : payload = InferenceCettaWire.encodePattern pattern := by simpa [found] using present.symm
        subst payload
        let selected := ("pattern", patternValue pattern) :: caller
        apply option_case_returns selected state _ ((RuleBinding.siteBinderDepth? rule site).map Term.natural)
          "depth" "no-depth" _ _ _
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
        · rw [natural_option_wire]
          exact site_depth_captured_returns selected state rule site (v "rule") (v "site")
            (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
        · intro stopped
          have missing : RuleBinding.siteBinderDepth? rule site = none := by
            cases depthFound : RuleBinding.siteBinderDepth? rule site with
            | none => rfl
            | some depth => simp [depthFound] at stopped
          simpa [RuleBinding.occurrenceDepthAtSite?, found, missing,
            ScopedCapture.naturalOptionTerm, CettaWireAtom.encode]
            using symbol_returns program _ state "None"
        · intro payload present
          cases depthFound : RuleBinding.siteBinderDepth? rule site with
          | none => simp [depthFound] at present
          | some depth =>
              have same : payload = Term.natural depth := by simpa [depthFound] using present.symm
              subst payload
              have returned := occurrence_depth_captured_returns (("depth", number depth) :: selected)
                state pattern path depth (v "pattern") (v "path") (v "depth")
                (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
              simpa [RuleBinding.occurrenceDepthAtSite?, found, depthFound, Helper.head] using returned

theorem depth_at_site_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (site : RulePatternSite) (path : List Nat) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) = [ruleValue rule, siteValue site, pathValue path]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-depth-at-site" [one, two, three]) state
      (encoded (ScopedCapture.naturalOptionTerm (RuleBinding.occurrenceDepthAtSite? rule site path))) :=
  helper_capture .depthAtSite caller state [one, two, three] [ruleValue rule, siteValue site, pathValue path] _ rfl captured
    (depth_at_site_returns state rule site path)

private theorem name_option_same (value : Option String) (name : String) :
    MatchAutomataBindingExecution.payloadOptionTerm (value.map Term.string) =
      Term.application "Some" [Term.string name] ↔ value = some name := by
  cases value <;> simp [MatchAutomataBindingExecution.payloadOptionTerm, Term.application.injEq, Term.string.injEq]

private theorem name_option_boolean (value : Option String) (name : String) :
    decide (MatchAutomataBindingExecution.payloadOptionTerm (value.map Term.string) =
      Term.application "Some" [Term.string name]) = (value == some name) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  exact name_option_same value name

private def declaredContinueBody : Atom :=
  a "let" [v "observed", a Helper.occurrenceName.head [v "pattern", v "path"],
    a "==" [v "observed", a "Some" [v "name"]]]
private def declaredPatternBody : Atom :=
  a "case" [a Helper.sitePattern.head [v "rule", v "site"], .expression [
    .expression [a "Some" [v "pattern"], declaredContinueBody], .expression [v "other", Effects.boolean false]]]
private def declaredCases : SpaceSemantics.Cases :=
  [(a "RuleOccurrence" [v "name", v "site", v "path", v "arguments"], declaredPatternBody),
   (v "invalid", Effects.boolean false)]
private theorem declared_shape : (equation .occurrenceDeclared).body =
    a "case" [v "occurrence", .expression (declaredCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem occurrence_declared_returns (state : State) (rule : RewriteRule) (occurrence : MetavariableOccurrence) :
    PureReturns program [] state (a "gslt:rule:scope-metadata-occurrence-declared"
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence)]) state
      (Effects.boolean (RuleBinding.occurrenceDeclared rule occurrence)) := by
  let values := [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence)]
  let caller := environment .occurrenceDeclared values
  let selected := ("arguments", patternsValue occurrence.arguments) :: ("path", pathValue occurrence.path) ::
    ("site", siteValue occurrence.site) :: ("name", stringValue occurrence.name) :: caller
  apply helper_call .occurrenceDeclared [] state _ values _ rfl (captured_closed _)
  rw [declared_shape]
  apply case_returns program caller selected state state state (v "occurrence")
    (encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence)) declaredPatternBody _ _ declaredCases
    (read_cases_encoded _) _ _ _
  · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "occurrence"
  · simp [declaredCases, InferenceCettaWire.AuthoredRule.occurrenceTerm, InferenceCettaWire.encodeList,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      selected, caller, values, environment, Helper.names, Subst.lookup, patternsValue, pathValue, siteValue]
  · apply option_case_returns selected state _ ((RuleBinding.sitePattern? rule occurrence.site).map InferenceCettaWire.encodePattern)
      "pattern" "other" _ _ _
    · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
    · simp [selected, caller, values, environment, Helper.names, Subst.lookup]
    · have returned := site_pattern_captured_returns selected state rule occurrence.site (v "rule") (v "site")
        (by simp [selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
      cases found : RuleBinding.sitePattern? rule occurrence.site <;>
        simpa only [Helper.head, found, MatchAutomataBindingExecution.patternOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm, Option.map_none, Option.map_some] using returned
    · intro stopped
      have missing : RuleBinding.sitePattern? rule occurrence.site = none := by
        cases found : RuleBinding.sitePattern? rule occurrence.site with
        | none => rfl
        | some pattern => simp [found] at stopped
      simpa [RuleBinding.occurrenceDeclared, missing, Effects.boolean]
        using grounded_returns program _ state (.bool false)
    · intro payload present
      cases found : RuleBinding.sitePattern? rule occurrence.site with
      | none => simp [found] at present
      | some pattern =>
          have same : payload = InferenceCettaWire.encodePattern pattern := by simpa [found] using present.symm
          subst payload
          let captured := ("pattern", patternValue pattern) :: selected
          let observed := MatchAutomataBindingExecution.payloadOptionTerm
            ((RuleBinding.occurrenceAt? pattern occurrence.path).map Term.string)
          let bound := ("observed", encoded observed) :: captured
          apply named_let_returns captured state "observed" _ (encoded observed) _ _
          · simp [captured, selected, caller, values, environment, Helper.names, Subst.lookup]
          · exact occurrence_name_captured_returns captured state pattern occurrence.path (v "pattern") (v "path")
              (by simp [captured, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
          · have first : PureReturns program bound state (v "observed") state (encoded observed) := by
              simpa [bound] using variable_returns program bound state "observed"
            have second := some_returns bound state (v "name") (stringValue occurrence.name)
              (by simpa [bound, captured, selected] using variable_returns program bound state "name")
            have returned := CettaWireAtom.equality_evaluated_returns program bound state observed
              (.application "Some" [.string occurrence.name]) (v "observed") (a "Some" [v "name"])
              (by decide +kernel) (by decide +kernel) first second
            simpa only [observed, name_option_boolean, RuleBinding.occurrenceDeclared, found, Option.bind_some]
              using returned

theorem occurrence_declared_captured_returns (caller : Subst) (state : State)
    (rule : RewriteRule) (occurrence : MetavariableOccurrence) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence)]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-occurrence-declared" [one, two]) state
      (Effects.boolean (RuleBinding.occurrenceDeclared rule occurrence)) :=
  helper_capture .occurrenceDeclared caller state [one, two]
    [ruleValue rule, encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence)] _ rfl captured
    (occurrence_declared_returns state rule occurrence)

private abbrev argumentsValue (value : Option (List Pattern)) : Atom :=
  encoded (MatchAutomataBindingExecution.payloadOptionTerm (value.map InferenceCettaWire.encodePatterns))
private def argumentsLengthBody : Atom :=
  a "let*" [.expression [
    .expression [v "arity", a "gslt:automata:length" [v "dependencies"]],
    .expression [v "supplied", a "gslt:automata:length" [v "arguments"]]],
    a "if" [a "==" [v "supplied", v "arity"], a "Some" [v "arguments"], .symbol "None"]]
private def argumentsSingletonBody : Atom :=
  a "if" [a Helper.occurrenceDeclared.head [v "rule", a "RuleOccurrence"
    [v "actual-name", v "actual-site", v "actual-path", v "arguments"]], argumentsLengthBody, .symbol "None"]
private def argumentsResultCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "if" [a "==" [v "dependencies", .symbol "LNil"], a "Some" [.symbol "LNil"], .symbol "None"]),
   (a "LCons" [a "RuleOccurrence" [v "actual-name", v "actual-site", v "actual-path", v "arguments"], .symbol "LNil"],
     argumentsSingletonBody), (v "ambiguous", .symbol "None")]
private def argumentsRowsBody : Atom :=
  a "case" [a Helper.occurrenceRows.head [v "occurrences", v "name", v "site", v "path"],
    .expression (argumentsResultCases.map fun row => .expression [row.1, row.2])]
private def argumentsSpecBody : Atom :=
  a "case" [v "spec", .expression [
    .expression [a "RuleBindingSpec" [v "dependency-rows", v "occurrences"], argumentsRowsBody],
    .expression [v "invalid", .symbol "None"]]]
private def argumentsDeclaredBody : Atom :=
  a "if" [a Helper.occurrenceDeclared.head [v "rule", a "RuleOccurrence"
    [v "name", v "site", v "path", .symbol "LNil"]], argumentsSpecBody, .symbol "None"]
private theorem arguments_shape : (equation .arguments).body =
    a "case" [a Helper.dependencies.head [v "spec", v "name"], .expression [
      .expression [a "Some" [v "dependencies"], argumentsDeclaredBody],
      .expression [v "unknown", .symbol "None"]]] := by decide +kernel

theorem arguments_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    PureReturns program [] state (a "gslt:rule:scope-metadata-arguments"
      [ruleValue rule, specValue spec, stringValue name, siteValue site, pathValue path]) state
      (argumentsValue (RuleBinding.arguments? rule spec name site path)) := by
  let values := [ruleValue rule, specValue spec, stringValue name, siteValue site, pathValue path]
  let caller := environment .arguments values
  let declaration : MetavariableOccurrence := ⟨name, site, path, []⟩
  apply helper_call .arguments [] state _ values _ rfl (captured_closed _)
  rw [arguments_shape]
  apply option_case_returns caller state _ ((RuleBinding.dependencies? spec name).map
    (encodeList InferenceCettaWire.AuthoredRule.typeTerm)) "dependencies" "unknown" _ _ _
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · simp [caller, values, environment, Helper.names, Subst.lookup]
  · have returned := dependencies_captured_returns caller state spec name (v "spec") (v "name")
      (by simp [caller, values, environment, Helper.names, applySubst, Subst.lookup])
    cases found : RuleBinding.dependencies? spec name <;>
      simpa only [Helper.head, found, dependencyOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm, Option.map_none, Option.map_some] using returned
  · intro stopped
    have missing : RuleBinding.dependencies? spec name = none := by
      cases found : RuleBinding.dependencies? spec name with
      | none => rfl
      | some dependencies => simp [found] at stopped
    simpa [RuleBinding.arguments?, missing, argumentsValue, MatchAutomataBindingExecution.payloadOptionTerm,
      CettaWireAtom.encode] using symbol_returns program _ state "None"
  · intro payload present
    cases depsFound : RuleBinding.dependencies? spec name with
    | none => simp [depsFound] at present
    | some dependencies =>
        have same : payload = encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies := by
          simpa [depsFound] using present.symm
        subst payload
        let depsCaller := ("dependencies", typeListValue dependencies) :: caller
        apply bool_if_returns depsCaller state _ (RuleBinding.occurrenceDeclared rule declaration) _ _ _
        · exact occurrence_declared_captured_returns depsCaller state rule declaration (v "rule")
            (a "RuleOccurrence" [v "name", v "site", v "path", .symbol "LNil"])
            (by simp [declaration, depsCaller, caller, values, environment, Helper.names, applySubst,
              applySubst.applySubstList, Subst.lookup, InferenceCettaWire.AuthoredRule.occurrenceTerm,
              InferenceCettaWire.encodePatterns, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany])
        · cases declared : RuleBinding.occurrenceDeclared rule declaration with
          | false =>
              simpa [RuleBinding.arguments?, depsFound, declaration, declared, argumentsValue,
                MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                using symbol_returns program depsCaller state "None"
          | true =>
              simp only [ite_true]
              let specCaller := ("occurrences", occurrenceRowsValue spec.occurrences) ::
                ("dependency-rows", dependencyRowsValue spec.dependencies) :: depsCaller
              have computed := occurrence_rows_captured_returns specCaller state spec.occurrences name site path
                (v "occurrences") (v "name") (v "site") (v "path")
                (by simp [specCaller, depsCaller, caller, values, environment, Helper.names, applySubst, Subst.lookup])
              let matching := spec.occurrences.filter (fun row => row.name == name && row.site == site && row.path == path)
              change PureReturns program specCaller state
                (a Helper.occurrenceRows.head [v "occurrences", v "name", v "site", v "path"]) state
                (occurrenceRowsValue matching) at computed
              apply case_returns program depsCaller specCaller state state state (v "spec") (specValue spec)
                argumentsRowsBody _ _
                [(a "RuleBindingSpec" [v "dependency-rows", v "occurrences"], argumentsRowsBody),
                  (v "invalid", .symbol "None")] (read_cases_encoded _) _ _ _
              · simpa [depsCaller, caller, values, environment, Helper.names, applySubst, Subst.lookup]
                  using variable_returns program depsCaller state "spec"
              · simp [specValue, InferenceCettaWire.AuthoredRule.bindingSpecTerm, InferenceCettaWire.encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                  SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
                  specCaller, depsCaller, caller, values, environment, Helper.names, Subst.lookup,
                  occurrenceRowsValue, dependencyRowsValue]
              · cases rowsFound : matching with
                | nil =>
                    have physical : spec.occurrences.filter
                        (fun row => row.name == name && row.site == site && row.path == path) = [] := rowsFound
                    apply case_returns program specCaller specCaller state state state
                      (a Helper.occurrenceRows.head [v "occurrences", v "name", v "site", v "path"])
                      (.symbol "LNil")
                      (a "if" [a "==" [v "dependencies", .symbol "LNil"], a "Some" [.symbol "LNil"], .symbol "None"])
                      _ _ argumentsResultCases (read_cases_encoded _) _ _ _
                    · simpa [rowsFound, occurrenceRowsValue, encodeList, CettaWireAtom.encode] using computed
                    · simp [argumentsResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                    · cases dependencies with
                      | nil =>
                          apply bool_if_returns specCaller state _ true _ _ _
                          · simpa using CettaWireAtom.equality_evaluated_returns program specCaller state
                              (.symbol "LNil") (.symbol "LNil") (v "dependencies") (.symbol "LNil")
                              (by decide +kernel) (by decide +kernel)
                              (by simpa [specCaller, depsCaller, typeListValue, encodeList, CettaWireAtom.encode]
                                using variable_returns program specCaller state "dependencies")
                              (symbol_returns program specCaller state "LNil")
                          · have returned := some_returns specCaller state (.symbol "LNil") (.symbol "LNil")
                              (symbol_returns program specCaller state "LNil")
                            simpa [RuleBinding.arguments?, depsFound, declaration, declared, physical,
                              argumentsValue, MatchAutomataBindingExecution.payloadOptionTerm,
                              InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using returned
                      | cons sort dependencies =>
                          apply bool_if_returns specCaller state _ false _ _ _
                          · have returned := CettaWireAtom.equality_evaluated_returns program specCaller state
                              (encodeList InferenceCettaWire.AuthoredRule.typeTerm (sort :: dependencies))
                              (.symbol "LNil") (v "dependencies") (.symbol "LNil")
                              (by decide +kernel) (by decide +kernel)
                              (by simpa [specCaller, depsCaller] using variable_returns program specCaller state "dependencies")
                              (symbol_returns program specCaller state "LNil")
                            simpa [encodeList] using returned
                          · simpa [RuleBinding.arguments?, depsFound, declaration, declared, physical,
                              argumentsValue, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                              using symbol_returns program specCaller state "None"
                | cons occurrence remaining =>
                    cases remaining with
                    | nil =>
                        have physical : spec.occurrences.filter
                            (fun row => row.name == name && row.site == site && row.path == path) = [occurrence] := rowsFound
                        let selected := ("arguments", patternsValue occurrence.arguments) ::
                          ("actual-path", pathValue occurrence.path) :: ("actual-site", siteValue occurrence.site) ::
                          ("actual-name", stringValue occurrence.name) :: specCaller
                        apply case_returns program specCaller selected state state state
                          (a Helper.occurrenceRows.head [v "occurrences", v "name", v "site", v "path"])
                          (occurrenceRowsValue [occurrence]) argumentsSingletonBody _ _ argumentsResultCases
                          (read_cases_encoded _) _ _ _
                        · simpa only [rowsFound] using computed
                        · simp [argumentsResultCases, occurrenceRowsValue, encodeList, InferenceCettaWire.AuthoredRule.occurrenceTerm,
                            InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                            matchAtom, selected, specCaller, depsCaller, caller, values, environment, Helper.names,
                            Subst.lookup, patternsValue, pathValue, siteValue]
                        · apply bool_if_returns selected state _ (RuleBinding.occurrenceDeclared rule occurrence) _ _ _
                          · exact occurrence_declared_captured_returns selected state rule occurrence (v "rule")
                              (a "RuleOccurrence" [v "actual-name", v "actual-site", v "actual-path", v "arguments"])
                              (by simp [selected, specCaller, depsCaller, caller, values, environment, Helper.names,
                                applySubst, applySubst.applySubstList, Subst.lookup,
                                InferenceCettaWire.AuthoredRule.occurrenceTerm, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany])
                          · cases actualDeclared : RuleBinding.occurrenceDeclared rule occurrence with
                            | false =>
                                simpa [RuleBinding.arguments?, depsFound, declaration, declared, physical, actualDeclared,
                                  argumentsValue, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                                  using symbol_returns program selected state "None"
                            | true =>
                                simp only [ite_true]
                                let arityCaller := ("arity", number dependencies.length) :: selected
                                let suppliedCaller := ("supplied", number occurrence.arguments.length) :: arityCaller
                                apply PureData.let_bindings_return (pairs :=
                                  [(v "arity", a "gslt:automata:length" [v "dependencies"]),
                                   (v "supplied", a "gslt:automata:length" [v "arguments"])])
                                  (final := suppliedCaller) (middle := state)
                                · apply PureData.BindingsReturn.cons (value := number dependencies.length) (bound := arityCaller)
                                  · have returned := retained_length_returns selected state
                                      (dependencies.map InferenceCettaWire.AuthoredRule.typeTerm) "dependencies"
                                      (by simp [selected, specCaller, depsCaller, typeListValue, encodeList_map])
                                    simpa only [List.length_map] using returned
                                  · simp [arityCaller, selected, specCaller, depsCaller, caller, values, environment,
                                      Helper.names, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                                      matchAtom, Subst.lookup]
                                  · apply PureData.BindingsReturn.cons (value := number occurrence.arguments.length)
                                      (bound := suppliedCaller)
                                    · have returned := retained_length_returns arityCaller state
                                        (occurrence.arguments.map InferenceCettaWire.encodePattern) "arguments"
                                        (by simp [arityCaller, selected, patternsValue,
                                          InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map])
                                      simpa only [List.length_map] using returned
                                    · simp [suppliedCaller, arityCaller, selected, specCaller, depsCaller, caller, values,
                                        environment, Helper.names, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
                                        matchAtom, Subst.lookup]
                                    · exact PureData.BindingsReturn.nil suppliedCaller state
                                · apply bool_if_returns suppliedCaller state _
                                    (decide (occurrence.arguments.length = dependencies.length)) _ _ _
                                  · apply equal_variables_returns suppliedCaller state occurrence.arguments.length
                                      dependencies.length "supplied" "arity" <;> simp [suppliedCaller, arityCaller]
                                  · by_cases arity : occurrence.arguments.length = dependencies.length
                                    · have returned := some_returns suppliedCaller state (v "arguments")
                                        (patternsValue occurrence.arguments)
                                        (by simpa [suppliedCaller, arityCaller, selected]
                                          using variable_returns program suppliedCaller state "arguments")
                                      simpa [RuleBinding.arguments?, depsFound, declaration, declared, physical,
                                        actualDeclared, arity, argumentsValue, MatchAutomataBindingExecution.payloadOptionTerm,
                                        CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
                                    · simpa [RuleBinding.arguments?, depsFound, declaration, declared, physical,
                                        actualDeclared, arity, argumentsValue, MatchAutomataBindingExecution.payloadOptionTerm,
                                        CettaWireAtom.encode] using symbol_returns program suppliedCaller state "None"
                    | cons next rest =>
                        have physical : spec.occurrences.filter
                            (fun row => row.name == name && row.site == site && row.path == path) = occurrence :: next :: rest := rowsFound
                        let selected := ("ambiguous", occurrenceRowsValue (occurrence :: next :: rest)) :: specCaller
                        apply case_returns program specCaller selected state state state
                          (a Helper.occurrenceRows.head [v "occurrences", v "name", v "site", v "path"])
                          (occurrenceRowsValue (occurrence :: next :: rest)) (.symbol "None") _ _ argumentsResultCases
                          (read_cases_encoded _) _ _ _
                        · simpa only [rowsFound] using computed
                        · simp [argumentsResultCases, occurrenceRowsValue, encodeList, InferenceCettaWire.AuthoredRule.occurrenceTerm,
                            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            SpaceSemantics.matchValue.matchValues, matchAtom, selected, specCaller, depsCaller, caller, values,
                            environment, Helper.names, Subst.lookup]
                        · simpa [RuleBinding.arguments?, depsFound, declaration, declared, physical, argumentsValue,
                            MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                            using symbol_returns program selected state "None"

theorem arguments_captured_returns (caller : Subst) (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (name : String) (site : RulePatternSite) (path : List Nat) (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [ruleValue rule, specValue spec, stringValue name, siteValue site, pathValue path]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-arguments" [one, two, three, four, five]) state
      (argumentsValue (RuleBinding.arguments? rule spec name site path)) :=
  helper_capture .arguments caller state [one, two, three, four, five]
    [ruleValue rule, specValue spec, stringValue name, siteValue site, pathValue path] _ rfl captured
    (arguments_returns state rule spec name site path)

private def captureAssignBody : Atom :=
  a "gslt:rule:scope-assign" [v "assignment", v "name", v "value"]
private def captureRecoverBody : Atom :=
  a "case" [a "gslt:rule:scope-recover-value" [v "dependencies", v "ambient", v "depth", v "arguments", v "target"],
    .expression [.expression [a "Some" [v "value"], captureAssignBody], .expression [v "failed", .symbol "None"]]]
private def captureArgumentsBody : Atom :=
  a "case" [a Helper.arguments.head [v "rule", v "spec", v "name", v "site", v "path"],
    .expression [.expression [a "Some" [v "arguments"], captureRecoverBody], .expression [v "no-arguments", .symbol "None"]]]
private def captureDependenciesBody : Atom :=
  a "case" [a Helper.dependencies.head [v "spec", v "name"],
    .expression [.expression [a "Some" [v "dependencies"], captureArgumentsBody], .expression [v "no-dependencies", .symbol "None"]]]
private def captureDepthBody : Atom :=
  a "case" [a Helper.depthAtSite.head [v "rule", v "site", v "path"],
    .expression [.expression [a "Some" [v "depth"], captureDependenciesBody], .expression [v "no-depth", .symbol "None"]]]
private def captureBindingsCases : SpaceSemantics.Cases :=
  [(a "RuleBindingSome" [v "spec"], captureDepthBody), (v "no-spec", .symbol "None")]
private def captureBindingBody : Atom :=
  a "case" [v "bindings", .expression (captureBindingsCases.map fun row => .expression [row.1, row.2])]
private def captureCases : SpaceSemantics.Cases :=
  [(a "ScopedRewriteRuleV1" [v "rule-name", v "context", v "premises", v "left", v "right", v "bindings"], captureBindingBody),
    (v "invalid", .symbol "None")]
private theorem capture_shape : (equation .capture).body =
    a "case" [v "rule", .expression (captureCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

/-- The capture endpoint reads the attached metadata and the actual occurrence
address before calling the original recovery and assignment operations. -/
theorem capture_returns (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) :
    PureReturns program [] state (a "gslt:rule:scope-metadata-capture"
      [ruleValue rule, number ambient, siteValue site, pathValue path,
        encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name, patternValue target]) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
          ScopedRuleMatching.capture? rule spec ambient depth site path assignment name target))) := by
  let values := [ruleValue rule, number ambient, siteValue site, pathValue path,
    encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name, patternValue target]
  let caller := environment .capture values
  let selected := ("bindings", encoded (InferenceCettaWire.AuthoredRule.optionalBindingTerm rule.bindings)) ::
    ("right", patternValue rule.right) :: ("left", patternValue rule.left) ::
    ("premises", encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)) ::
    ("context", encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext)) ::
    ("rule-name", stringValue rule.name) :: caller
  apply helper_call .capture [] state _ values _ rfl (captured_closed _)
  rw [capture_shape]
  apply case_returns program caller selected state state state (v "rule") (ruleValue rule)
    captureBindingBody _ _ captureCases (read_cases_encoded _) _ _ _
  · simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup]
      using variable_returns program caller state "rule"
  · simp [captureCases, ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
      InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, caller, values, environment, Helper.names, Subst.lookup]
  · cases bindingsFound : rule.bindings with
    | none =>
        let missing := ("no-spec", .symbol "RuleBindingNone") :: selected
        apply case_returns program selected missing state state state (v "bindings") (.symbol "RuleBindingNone")
          (.symbol "None") _ _ captureBindingsCases (read_cases_encoded _) _ _ _
        · simpa [selected, bindingsFound, InferenceCettaWire.AuthoredRule.optionalBindingTerm,
            CettaWireAtom.encode] using variable_returns program selected state "bindings"
        · simp [captureBindingsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            matchAtom, missing, selected, caller, values, environment, Helper.names, Subst.lookup]
        · simpa [bindingsFound, ScopedCapture.scopedAssignmentOptionTerm,
            MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
            using symbol_returns program missing state "None"
    | some spec =>
        let specCaller := ("spec", specValue spec) :: selected
        apply case_returns program selected specCaller state state state (v "bindings")
          (a "RuleBindingSome" [specValue spec]) captureDepthBody _ _ captureBindingsCases
          (read_cases_encoded _) _ _ _
        · simpa [selected, bindingsFound, InferenceCettaWire.AuthoredRule.optionalBindingTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany]
            using variable_returns program selected state "bindings"
        · simp [captureBindingsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, specCaller, selected, caller, values,
            environment, Helper.names, Subst.lookup]
        · apply option_case_returns specCaller state _
            ((RuleBinding.occurrenceDepthAtSite? rule site path).map Term.natural)
            "depth" "no-depth" _ _ _
          · simp [specCaller, selected, caller, values, environment, Helper.names, Subst.lookup]
          · simp [specCaller, selected, caller, values, environment, Helper.names, Subst.lookup]
          · have returned := depth_at_site_captured_returns specCaller state rule site path
              (v "rule") (v "site") (v "path")
              (by simp [specCaller, selected, caller, values, environment, Helper.names, applySubst, Subst.lookup])
            cases found : RuleBinding.occurrenceDepthAtSite? rule site path <;>
              simpa only [Helper.head, found, ScopedCapture.naturalOptionTerm,
                MatchAutomataBindingExecution.payloadOptionTerm, Option.map_none, Option.map_some] using returned
          · intro stopped
            have missing : RuleBinding.occurrenceDepthAtSite? rule site path = none := by
              cases found : RuleBinding.occurrenceDepthAtSite? rule site path with
              | none => rfl
              | some depth => simp [found] at stopped
            simpa [bindingsFound, missing, ScopedCapture.scopedAssignmentOptionTerm,
              MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
              using symbol_returns program _ state "None"
          · intro payload present
            cases depthFound : RuleBinding.occurrenceDepthAtSite? rule site path with
            | none => simp [depthFound] at present
            | some depth =>
                have same : payload = Term.natural depth := by simpa [depthFound] using present.symm
                subst payload
                let depthCaller := ("depth", number depth) :: specCaller
                apply option_case_returns depthCaller state _
                  ((RuleBinding.dependencies? spec name).map (encodeList InferenceCettaWire.AuthoredRule.typeTerm))
                  "dependencies" "no-dependencies" _ _ _
                · simp [depthCaller, specCaller, selected, caller, values, environment, Helper.names, Subst.lookup]
                · simp [depthCaller, specCaller, selected, caller, values, environment, Helper.names, Subst.lookup]
                · have returned := dependencies_captured_returns depthCaller state spec name (v "spec") (v "name")
                    (by simp [depthCaller, specCaller, selected, caller, values, environment, Helper.names,
                      applySubst, Subst.lookup])
                  cases found : RuleBinding.dependencies? spec name <;>
                    simpa only [Helper.head, found, dependencyOptionTerm,
                      MatchAutomataBindingExecution.payloadOptionTerm, Option.map_none, Option.map_some] using returned
                · intro stopped
                  have missing : RuleBinding.dependencies? spec name = none := by
                    cases found : RuleBinding.dependencies? spec name with
                    | none => rfl
                    | some dependencies => simp [found] at stopped
                  simpa [bindingsFound, depthFound, ScopedRuleMatching.capture?, missing,
                    ScopedCapture.scopedAssignmentOptionTerm,
                    MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                    using symbol_returns program _ state "None"
                · intro payload present
                  cases depsFound : RuleBinding.dependencies? spec name with
                  | none => simp [depsFound] at present
                  | some dependencies =>
                      have same : payload = encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies := by
                        simpa [depsFound] using present.symm
                      subst payload
                      let depsCaller := ("dependencies", typeListValue dependencies) :: depthCaller
                      apply option_case_returns depsCaller state _
                        ((RuleBinding.arguments? rule spec name site path).map InferenceCettaWire.encodePatterns)
                        "arguments" "no-arguments" _ _ _
                      · simp [depsCaller, depthCaller, specCaller, selected, caller, values, environment,
                          Helper.names, Subst.lookup]
                      · simp [depsCaller, depthCaller, specCaller, selected, caller, values, environment,
                          Helper.names, Subst.lookup]
                      · simpa only [Helper.head, argumentsValue] using arguments_captured_returns depsCaller state rule spec name site path
                          (v "rule") (v "spec") (v "name") (v "site") (v "path")
                          (by simp [depsCaller, depthCaller, specCaller, selected, caller, values,
                            environment, Helper.names, applySubst, Subst.lookup])
                      · intro stopped
                        have missing : RuleBinding.arguments? rule spec name site path = none := by
                          cases found : RuleBinding.arguments? rule spec name site path with
                          | none => rfl
                          | some arguments => simp [found] at stopped
                        simpa [bindingsFound, depthFound, ScopedRuleMatching.capture?, depsFound, missing,
                          ScopedCapture.scopedAssignmentOptionTerm,
                          MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                          using symbol_returns program _ state "None"
                      · intro payload present
                        cases argsFound : RuleBinding.arguments? rule spec name site path with
                        | none => simp [argsFound] at present
                        | some arguments =>
                            have same : payload = InferenceCettaWire.encodePatterns arguments := by
                              simpa [argsFound] using present.symm
                            subst payload
                            let argsCaller := ("arguments", patternsValue arguments) :: depsCaller
                            apply option_case_returns argsCaller state _
                              ((RuleBinding.recoverValue? dependencies ambient depth arguments target).map
                                InferenceCettaWire.AuthoredRule.contextualValueTerm)
                              "value" "failed" _ _ _
                            · simp [argsCaller, depsCaller, depthCaller, specCaller, selected, caller,
                                values, environment, Helper.names, Subst.lookup]
                            · simp [argsCaller, depsCaller, depthCaller, specCaller, selected, caller,
                                values, environment, Helper.names, Subst.lookup]
                            · have returned := ScopedCapture.recover_value_captured_returns
                                argsCaller state dependencies ambient depth arguments target
                                (v "dependencies") (v "ambient") (v "depth") (v "arguments") (v "target")
                                (by simp [argsCaller, depsCaller, depthCaller, specCaller, selected, caller,
                                  values, environment, Helper.names, applySubst, Subst.lookup,
                                  InferenceCettaWire.encodeList])
                              have lifted := returned
                              simpa only [ScopedCapture.contextualValueOptionTerm] using lifted
                            · intro stopped
                              have missing : RuleBinding.recoverValue? dependencies ambient depth arguments target = none := by
                                cases found : RuleBinding.recoverValue? dependencies ambient depth arguments target with
                                | none => rfl
                                | some value => simp [found] at stopped
                              simpa [bindingsFound, depthFound, ScopedRuleMatching.capture?, depsFound, argsFound, missing,
                                ScopedCapture.scopedAssignmentOptionTerm,
                                MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode]
                                using symbol_returns program _ state "None"
                            · intro payload present
                              cases recoveryFound : RuleBinding.recoverValue? dependencies ambient depth arguments target with
                              | none => simp [recoveryFound] at present
                              | some value =>
                                  have same : payload = InferenceCettaWire.AuthoredRule.contextualValueTerm value := by
                                    simpa [recoveryFound] using present.symm
                                  subst payload
                                  let valueCaller := ("value", encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm value)) :: argsCaller
                                  have returned := ScopedCapture.assign_captured_returns
                                    valueCaller state assignment name value (v "assignment") (v "name") (v "value")
                                    (by simp [valueCaller, argsCaller, depsCaller, depthCaller, specCaller, selected,
                                      caller, values, environment, Helper.names, applySubst, Subst.lookup])
                                  have lifted := returned
                                  simpa [bindingsFound, depthFound, ScopedRuleMatching.capture?, depsFound,
                                    argsFound, recoveryFound, captureAssignBody, valueCaller] using lifted

theorem capture_captured_returns (caller : Subst) (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (one two three four five six seven : Atom)
    (captured : [one, two, three, four, five, six, seven].map (applySubst caller) =
      [ruleValue rule, number ambient, siteValue site, pathValue path,
        encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name, patternValue target]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-capture" [one, two, three, four, five, six, seven]) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
          ScopedRuleMatching.capture? rule spec ambient depth site path assignment name target))) :=
  helper_capture .capture caller state [one, two, three, four, five, six, seven]
    [ruleValue rule, number ambient, siteValue site, pathValue path,
      encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name, patternValue target]
    _ rfl captured (capture_returns state rule ambient site path assignment name target)

private theorem capture_rest_shape : (equation .captureRest).body =
    a Helper.capture.head [v "rule", v "ambient", v "site", v "path", v "assignment", v "name",
      a "PCollection" [v "kind", v "elements", .symbol "RNone"]] := by decide +kernel

theorem capture_rest_returns (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (kind : CollType) (elements : List Pattern) :
    PureReturns program [] state (a "gslt:rule:scope-metadata-capture-rest"
      [ruleValue rule, number ambient, siteValue site, pathValue path,
        encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name,
        encoded (InferenceCettaWire.encodeCollectionType kind), patternsValue elements]) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
          ScopedRuleMatching.captureRest? rule spec ambient depth site path assignment name kind elements))) := by
  let values := [ruleValue rule, number ambient, siteValue site, pathValue path,
    encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name,
    encoded (InferenceCettaWire.encodeCollectionType kind), patternsValue elements]
  let caller := environment .captureRest values
  apply helper_call .captureRest [] state _ values _ rfl (captured_closed _)
  rw [capture_rest_shape]
  simpa only [Helper.head, ScopedRuleMatching.captureRest?] using
    capture_captured_returns caller state rule ambient site path assignment name (.collection kind elements none)
      (v "rule") (v "ambient") (v "site") (v "path") (v "assignment") (v "name")
      (a "PCollection" [v "kind", v "elements", .symbol "RNone"])
      (by simp [caller, values, environment, Helper.names, applySubst, applySubst.applySubstList,
        Subst.lookup, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany])

theorem capture_rest_captured_returns (caller : Subst) (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (kind : CollType) (elements : List Pattern) (one two three four five six seven eight : Atom)
    (captured : [one, two, three, four, five, six, seven, eight].map (applySubst caller) =
      [ruleValue rule, number ambient, siteValue site, pathValue path,
        encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name,
        encoded (InferenceCettaWire.encodeCollectionType kind), patternsValue elements]) :
    PureReturns program caller state (a "gslt:rule:scope-metadata-capture-rest" [one, two, three, four, five, six, seven, eight]) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
          ScopedRuleMatching.captureRest? rule spec ambient depth site path assignment name kind elements))) :=
  helper_capture .captureRest caller state [one, two, three, four, five, six, seven, eight]
    [ruleValue rule, number ambient, siteValue site, pathValue path,
      encoded (ScopedCapture.scopedAssignmentTerm assignment), stringValue name,
      encoded (InferenceCettaWire.encodeCollectionType kind), patternsValue elements]
    _ rfl captured (capture_rest_returns state rule ambient site path assignment name kind elements)

/-- Query wire for the attached-metadata capture endpoint. -/
def captureTerm (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (name : String) (target : Pattern) : Term :=
  .application "gslt:rule:scope-metadata-capture"
    [InferenceCettaWire.AuthoredRule.rewriteTerm rule, .natural ambient,
      InferenceCettaWire.AuthoredRule.siteTerm site, encodeList Term.natural path,
      ScopedCapture.scopedAssignmentTerm assignment, .string name,
      InferenceCettaWire.encodePattern target]


theorem capture_term_returns (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) :
    PureReturns program [] state (encoded (captureTerm rule ambient site path assignment name target)) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
          ScopedRuleMatching.capture? rule spec ambient depth site path assignment name target))) := by
  simpa only [captureTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    capture_returns state rule ambient site path assignment name target

/-- Every completed machine observation includes the original store and
empty I/O; no assumption about a selected evaluation fuel is needed. -/
theorem capture_completed_iff (state after : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (captureTerm rule ambient site path assignment name target)) } =
      .complete after answers input output) ↔
    after = state ∧ answers = [encoded (ScopedCapture.scopedAssignmentOptionTerm
      (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
        ScopedRuleMatching.capture? rule spec ambient depth site path assignment name target))] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (capture_term_returns state rule ambient site path assignment name target) after answers input output

theorem capture_derivation_iff (state after : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (captureTerm rule ambient site path assignment name target)) }
      (.complete after answers input output) ↔
    after = state ∧ answers = [encoded (ScopedCapture.scopedAssignmentOptionTerm
      (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
        ScopedRuleMatching.capture? rule spec ambient depth site path assignment name target))] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (capture_term_returns state rule ambient site path assignment name target) after answers input output

/-- The wire distinguishes refusal from every full assignment, including
ambient and dependency metadata in repeated captures. -/
theorem capture_success_iff (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (initial final : ScopedRuleMatching.Assignment)
    (name : String) (target : Pattern) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (captureTerm rule ambient site path initial name target)) } =
      .complete state [encoded (ScopedCapture.scopedAssignmentOptionTerm (some final))] [] []) ↔
      (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
        ScopedRuleMatching.capture? rule spec ambient depth site path initial name target) = some final := by
  rw [capture_completed_iff]
  simp only [true_and, and_true, List.cons.injEq, CettaWireAtom.encode_eq_encode,
    ScopedCapture.scopedAssignmentOptionTerm_injective.eq_iff, eq_comm]

namespace TypedOccurrence

open BindingSyntax BindingSyntax.ScopedElaboration
open BindingSyntax.ScopedElaboration.TargetReification BindingSyntax.ScopedElaboration.InputRecovery
open Mettapedia.OSLF.Binding

/-- The compiled occurrence earns both attachment and its actual local
binder depth from the authored rule. Numeric ambient length remains a
projection of the independently fixed typed ambient context. -/
theorem compiled_capture_returns {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (state : State) (initial : ScopedRuleMatching.Assignment)
    (target : Mettapedia.OSLF.Binding.Term (BindingSyntax.signatureOf language) (locals ++ ambient) sort) :
    PureReturns program [] state (encoded (captureTerm rule ambient.length site path initial name (erase target))) state
      (encoded (ScopedCapture.scopedAssignmentOptionTerm
        (ScopedRuleMatching.capture? rule spec ambient.length locals.length site path initial name (erase target)))) := by
  simpa only [input.attached, input.depth, Option.bind_some] using
    capture_term_returns state rule ambient.length site path initial name (erase target)

/-- Acceptance at this compiled occurrence is exactly the original typed
contextual action and assignment update. The canonical target restriction is
provided by the existing typed boundary, not inferred from the raw wire. -/
theorem compiled_capture_canonical_iff {language : LanguageDef} {rule : RewriteRule} {spec : RuleBindingSpec}
    {locals ambient : List TypeExpr} {site : RulePatternSite} {path : List Nat} {name : String} {sort : TypeExpr}
    (input : CompiledInputOccurrence language rule spec locals site path name sort)
    (state : State) (initial final : ScopedRuleMatching.Assignment)
    (target : Mettapedia.OSLF.Binding.Term (BindingSyntax.signatureOf language) (locals ++ ambient) sort)
    (canonical : CanonicalObject target) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (captureTerm rule ambient.length site path initial name (erase target))) } =
      .complete state [encoded (ScopedCapture.scopedAssignmentOptionTerm (some final))] [] []) ↔
      ∃ body : Mettapedia.OSLF.Binding.Term (BindingSyntax.signatureOf language) (input.dependencies ++ ambient) sort,
        CanonicalObject body ∧ bind (occurrenceSubstitution
          (appendAmbientArguments input.compiled.arguments ambient)) body = target ∧
        ScopedRuleMatching.assign initial name (contextualValue body) = some final := by
  rw [capture_success_iff]
  simpa only [input.attached, input.depth, Option.bind_some] using
    AmbientCorrespondence.input_capture_canonical_iff input initial final target canonical

end TypedOccurrence

namespace Controls

inductive Input where
  | dependencyRows (rows : List (String × List TypeExpr)) (name : String)
  | dependencies (spec : RuleBindingSpec) (name : String)
  | occurrenceRows (rows : List MetavariableOccurrence) (name : String) (site : RulePatternSite) (path : List Nat)
  | quantified (count : Nat) (premise : Premise)
  | sitePremise (rule : RewriteRule) (index quantifiers : Nat)
  | sitePattern (rule : RewriteRule) (site : RulePatternSite)
  | siteDepth (rule : RewriteRule) (site : RulePatternSite)
  | occurrenceName (pattern : Pattern) (path : List Nat)
  | occurrenceDepth (pattern : Pattern) (path : List Nat) (depth : Nat)
  | depthAtSite (rule : RewriteRule) (site : RulePatternSite) (path : List Nat)
  | declared (rule : RewriteRule) (occurrence : MetavariableOccurrence)
  | arguments (rule : RewriteRule) (spec : RuleBindingSpec) (name : String) (site : RulePatternSite) (path : List Nat)
  | capture (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
      (assignment : ScopedRuleMatching.Assignment) (name : String) (target : Pattern)
  | captureRest (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
      (assignment : ScopedRuleMatching.Assignment) (name : String) (kind : CollType) (elements : List Pattern)

def Input.queryTerm : Input → Term
  | .dependencyRows rows name => .application Helper.dependencyRows.head
      [encodeList InferenceCettaWire.AuthoredRule.dependencyTerm rows, .string name]
  | .dependencies spec name => .application Helper.dependencies.head
      [InferenceCettaWire.AuthoredRule.bindingSpecTerm spec, .string name]
  | .occurrenceRows rows name site path => .application Helper.occurrenceRows.head
      [encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm rows, .string name,
        InferenceCettaWire.AuthoredRule.siteTerm site, encodeList Term.natural path]
  | .quantified count premise => .application Helper.quantifiedBody.head
      [.natural count, InferenceCettaWire.AuthoredRule.premiseTerm premise]
  | .sitePremise rule index quantifiers => .application Helper.sitePremise.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, .natural index, .natural quantifiers]
  | .sitePattern rule site => .application Helper.sitePattern.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, InferenceCettaWire.AuthoredRule.siteTerm site]
  | .siteDepth rule site => .application Helper.siteDepth.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, InferenceCettaWire.AuthoredRule.siteTerm site]
  | .occurrenceName pattern path => .application Helper.occurrenceName.head
      [InferenceCettaWire.encodePattern pattern, encodeList Term.natural path]
  | .occurrenceDepth pattern path depth => .application Helper.occurrenceDepth.head
      [InferenceCettaWire.encodePattern pattern, encodeList Term.natural path, .natural depth]
  | .depthAtSite rule site path => .application Helper.depthAtSite.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, InferenceCettaWire.AuthoredRule.siteTerm site, encodeList Term.natural path]
  | .declared rule occurrence => .application "if"
      [.application Helper.occurrenceDeclared.head
        [InferenceCettaWire.AuthoredRule.rewriteTerm rule, InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence],
        .symbol "DeclaredYes", .symbol "DeclaredNo"]
  | .arguments rule spec name site path => .application Helper.arguments.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, InferenceCettaWire.AuthoredRule.bindingSpecTerm spec,
        .string name, InferenceCettaWire.AuthoredRule.siteTerm site, encodeList Term.natural path]
  | .capture rule ambient site path assignment name target => .application Helper.capture.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, .natural ambient, InferenceCettaWire.AuthoredRule.siteTerm site,
        encodeList Term.natural path, ScopedCapture.scopedAssignmentTerm assignment,
        .string name, InferenceCettaWire.encodePattern target]
  | .captureRest rule ambient site path assignment name kind elements => .application Helper.captureRest.head
      [InferenceCettaWire.AuthoredRule.rewriteTerm rule, .natural ambient, InferenceCettaWire.AuthoredRule.siteTerm site,
        encodeList Term.natural path, ScopedCapture.scopedAssignmentTerm assignment,
        .string name, InferenceCettaWire.encodeCollectionType kind, InferenceCettaWire.encodePatterns elements]

def Input.expectedTerm : Input → Term
  | .dependencyRows rows name => encodeList InferenceCettaWire.AuthoredRule.dependencyTerm (rows.filter fun row => row.1 == name)
  | .dependencies spec name => dependencyOptionTerm (RuleBinding.dependencies? spec name)
  | .occurrenceRows rows name site path => encodeList InferenceCettaWire.AuthoredRule.occurrenceTerm
      (rows.filter fun row => row.name == name && row.site == site && row.path == path)
  | .quantified count premise => premiseOptionTerm (RuleBinding.quantifiedBody? count premise)
  | .sitePremise rule index quantifiers => premiseOptionTerm (rule.premises[index]?.bind (RuleBinding.quantifiedBody? quantifiers))
  | .sitePattern rule site => MatchAutomataBindingExecution.patternOptionTerm (RuleBinding.sitePattern? rule site)
  | .siteDepth rule site => ScopedCapture.naturalOptionTerm (RuleBinding.siteBinderDepth? rule site)
  | .occurrenceName pattern path => MatchAutomataBindingExecution.payloadOptionTerm ((RuleBinding.occurrenceAt? pattern path).map Term.string)
  | .occurrenceDepth pattern path depth => ScopedCapture.naturalOptionTerm
      (RuleBinding.occurrenceDepthAt? pattern path depth)
  | .depthAtSite rule site path => ScopedCapture.naturalOptionTerm (RuleBinding.occurrenceDepthAtSite? rule site path)
  | .declared rule occurrence => if RuleBinding.occurrenceDeclared rule occurrence then .symbol "DeclaredYes" else .symbol "DeclaredNo"
  | .arguments rule spec name site path => MatchAutomataBindingExecution.payloadOptionTerm
      ((RuleBinding.arguments? rule spec name site path).map InferenceCettaWire.encodePatterns)
  | .capture rule ambient site path assignment name target => ScopedCapture.scopedAssignmentOptionTerm
      (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
        ScopedRuleMatching.capture? rule spec ambient depth site path assignment name target)
  | .captureRest rule ambient site path assignment name kind elements => ScopedCapture.scopedAssignmentOptionTerm
      (rule.bindings.bind fun spec => (RuleBinding.occurrenceDepthAtSite? rule site path).bind fun depth =>
        ScopedRuleMatching.captureRest? rule spec ambient depth site path assignment name kind elements)

theorem Input.returns (input : Input) (state : State) :
    PureReturns program [] state (encoded input.queryTerm) state (encoded input.expectedTerm) := by
  cases input with
  | dependencyRows rows name => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using dependency_rows_returns state rows name
  | dependencies spec name => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using dependencies_returns state spec name
  | occurrenceRows rows name site path => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using occurrence_rows_returns state rows name site path
  | quantified count premise => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using quantified_body_returns state count premise
  | sitePremise rule index quantifiers => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using site_premise_returns state rule index quantifiers
  | sitePattern rule site => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using site_pattern_returns state rule site
  | siteDepth rule site => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using site_depth_returns state rule site
  | occurrenceName pattern path => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using occurrence_name_returns state pattern path
  | occurrenceDepth pattern path depth => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using occurrence_depth_returns state pattern path depth
  | depthAtSite rule site path => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using depth_at_site_returns state rule site path
  | declared rule occurrence =>
      change PureReturns program [] state (a "if" [a Helper.occurrenceDeclared.head [ruleValue rule,
        encoded (InferenceCettaWire.AuthoredRule.occurrenceTerm occurrence)], .symbol "DeclaredYes", .symbol "DeclaredNo"]) state _
      apply bool_if_returns [] state _ (RuleBinding.occurrenceDeclared rule occurrence) _ _ _
      · exact occurrence_declared_returns state rule occurrence
      · cases checked : RuleBinding.occurrenceDeclared rule occurrence with
        | false => simpa [Input.expectedTerm, checked, CettaWireAtom.encode] using symbol_returns program [] state "DeclaredNo"
        | true => simpa [Input.expectedTerm, checked, CettaWireAtom.encode] using symbol_returns program [] state "DeclaredYes"
  | arguments rule spec name site path => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using arguments_returns state rule spec name site path
  | capture rule ambient site path assignment name target => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using capture_returns state rule ambient site path assignment name target
  | captureRest rule ambient site path assignment name kind elements => simpa [Input.queryTerm, Input.expectedTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using capture_rest_returns state rule ambient site path assignment name kind elements

structure Fixture where
  name : String
  input : Input

def Fixture.queryTerm (fixture : Fixture) : Term := fixture.input.queryTerm
def Fixture.expectedTerm (fixture : Fixture) : Term := fixture.input.expectedTerm

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (encoded fixture.queryTerm) state (encoded fixture.expectedTerm) := fixture.input.returns state

private def nameSort : TypeExpr := .base "Name"
private def procSort : TypeExpr := .base "Proc"

def binderSpec (arguments : List Pattern) (dependencies : List TypeExpr := [nameSort]) : RuleBindingSpec :=
  ⟨[("body", dependencies)], [⟨"body", .left, [0], arguments⟩]⟩

def binderRule (arguments : List Pattern := [.bvar 1]) (dependencies : List TypeExpr := [nameSort]) : RewriteRule where
  name := "metadata-capture"
  premises := []
  typeContext := [("body", .arrow nameSort procSort)]
  left := .multiLambda 2 ["x", "y"] (.fvar "body")
  right := .fvar "body"
  bindings := some (binderSpec arguments dependencies)

def quantifiedRule : RewriteRule where
  name := "quantified-site"
  typeContext := [("body", .arrow nameSort procSort)]
  premises := [.forAll "parts" "part" (.forAll "more" "next" (.scopedStep
    ⟨[nameSort, nameSort], procSort, .fvar "body", .fvar "result"⟩))]
  left := .apply "start" []
  right := .apply "done" []
  bindings := some ⟨[("body", [nameSort])], [⟨"body", .premise 0 2 0, [], [.bvar 1]⟩]⟩

def restRule : RewriteRule where
  name := "collection-rest-site"
  typeContext := []
  premises := []
  left := .collection .hashBag [.apply "fixed" []] (some "tail")
  right := .fvar "tail"
  bindings := some ⟨[("tail", [])], []⟩

private def capturedBody : RuleBinding.ContextualValue := ⟨[nameSort], 0, .bvar 0⟩
private def duplicateDependencies : RuleBindingSpec := ⟨[("body", [nameSort]), ("body", [nameSort])], (binderSpec [.bvar 1]).occurrences⟩
private def duplicateOccurrences : RuleBindingSpec := ⟨[("body", [nameSort])],
  [⟨"body", .left, [0], [.bvar 1]⟩, ⟨"body", .left, [0], [.bvar 1]⟩]⟩
private def noOccurrenceSpec : RuleBindingSpec := ⟨[("body", [nameSort])], []⟩
private def wrongAritySpec : RuleBindingSpec := binderSpec []

def fixtures : List Fixture :=
  [⟨"dependency-filter-retains-authored-order", .dependencyRows [("body", [nameSort]), ("other", []), ("body", [])] "body"⟩,
   ⟨"dependencies-exact-singleton", .dependencies (binderSpec [.bvar 1]) "body"⟩,
   ⟨"refuse-unknown-dependency", .dependencies (binderSpec [.bvar 1]) "missing"⟩,
   ⟨"refuse-duplicate-dependency-declaration", .dependencies duplicateDependencies "body"⟩,
   ⟨"occurrence-filter-preserves-identical-duplicates", .occurrenceRows duplicateOccurrences.occurrences "body" .left [0]⟩,
   ⟨"quantified-body-two-local-scopes", .quantified 2 (quantifiedRule.premises[0]'(by decide +kernel))⟩,
   ⟨"refuse-quantifier-past-authored-body", .quantified 3 (quantifiedRule.premises[0]'(by decide +kernel))⟩,
   ⟨"premise-physical-row-and-quantifiers", .sitePremise quantifiedRule 0 2⟩,
   ⟨"refuse-future-premise-row", .sitePremise quantifiedRule 1 0⟩,
   ⟨"premise-scoped-source-pattern", .sitePattern quantifiedRule (.premise 0 2 0)⟩,
   ⟨"premise-scoped-target-pattern", .sitePattern quantifiedRule (.premise 0 2 1)⟩,
   ⟨"refuse-premise-argument-outside-shape", .sitePattern quantifiedRule (.premise 0 2 2)⟩,
   ⟨"scoped-premise-binder-depth", .siteDepth quantifiedRule (.premise 0 2 0)⟩,
   ⟨"refuse-quantified-wrong-level", .siteDepth quantifiedRule (.premise 0 1 0)⟩,
   ⟨"occurrence-nested-lambda-address", .occurrenceName (.lambda "x" (.apply "box" [.fvar "body"])) [0, 0]⟩,
   ⟨"refuse-occurrence-wrong-child", .occurrenceName (.lambda "x" (.fvar "body")) [1]⟩,
   ⟨"occurrence-rest-slot-name", .occurrenceName restRule.left [1]⟩,
   ⟨"refuse-rest-descendant", .occurrenceName restRule.left [1, 0]⟩,
   ⟨"multi-binder-occurrence-depth", .occurrenceDepth (binderRule []).left [0] 3⟩,
   ⟨"substitution-body-increases-depth", .occurrenceDepth (.subst (.fvar "body") (.fvar "replacement")) [0] 2⟩,
   ⟨"substitution-replacement-retains-depth", .occurrenceDepth (.subst (.fvar "body") (.fvar "replacement")) [1] 2⟩,
   ⟨"rest-slot-occurrence-depth", .occurrenceDepth restRule.left [1] 4⟩,
   ⟨"site-plus-pattern-binder-depth", .depthAtSite (binderRule []) .left [0]⟩,
   ⟨"quantified-site-depth", .depthAtSite quantifiedRule (.premise 0 2 0) []⟩,
   ⟨"declared-occurrence-exact-address", .declared (binderRule []) ⟨"body", .left, [0], []⟩⟩,
   ⟨"refuse-declared-wrong-name", .declared (binderRule []) ⟨"other", .left, [0], []⟩⟩,
   ⟨"arguments-preserve-declared-spine", .arguments (binderRule []) (binderSpec [.bvar 1]) "body" .left [0]⟩,
   ⟨"refuse-duplicate-occurrence-declaration", .arguments (binderRule []) duplicateOccurrences "body" .left [0]⟩,
   ⟨"refuse-missing-nonempty-spine", .arguments (binderRule []) noOccurrenceSpec "body" .left [0]⟩,
   ⟨"refuse-wrong-spine-arity", .arguments (binderRule []) wrongAritySpec "body" .left [0]⟩,
   ⟨"infer-declared-empty-spine", .arguments (binderRule [] []) ⟨[("body", [])], []⟩ "body" .left [0]⟩,
   ⟨"capture-computed-address-spine-one", .capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"capture-computed-address-spine-zero", .capture (binderRule [.bvar 0]) 0 .left [0] [] "body" (.bvar 0)⟩,
   ⟨"capture-repeated-body-agreement", .capture (binderRule [.bvar 0]) 0 .left [0] [("body", capturedBody)] "body" (.bvar 0)⟩,
   ⟨"refuse-repeated-body-conflict", .capture (binderRule [.bvar 0]) 0 .left [0] [("body", ⟨[nameSort], 0, .apply "different" []⟩)] "body" (.bvar 0)⟩,
   ⟨"refuse-repeated-ambient-metadata-conflict", .capture (binderRule [.bvar 0]) 0 .left [0] [("body", ⟨[nameSort], 1, .bvar 0⟩)] "body" (.bvar 0)⟩,
   ⟨"refuse-unselected-local-dependence", .capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 0)⟩,
   ⟨"refuse-duplicate-local-spine", .capture (binderRule [.bvar 1, .bvar 1] [nameSort, nameSort]) 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"refuse-non-variable-spine", .capture (binderRule [.apply "not-variable" []]) 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"refuse-outside-local-spine", .capture (binderRule [.bvar 2]) 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"refuse-target-outside-ambient", .capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 2)⟩,
   ⟨"capture-retains-admitted-ambient-index", .capture (binderRule [.bvar 1]) 1 .left [0] [] "body" (.bvar 2)⟩,
   ⟨"refuse-wrong-capture-name", .capture (binderRule [.bvar 1]) 0 .left [0] [] "missing" (.bvar 1)⟩,
   ⟨"refuse-wrong-capture-address", .capture (binderRule [.bvar 1]) 0 .left [1] [] "body" (.bvar 1)⟩,
   ⟨"refuse-duplicate-capture-dependencies", .capture { binderRule [.bvar 1] with bindings := some duplicateDependencies } 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"refuse-duplicate-capture-occurrences", .capture { binderRule [.bvar 1] with bindings := some duplicateOccurrences } 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"refuse-omitted-capture-metadata", .capture { binderRule [.bvar 1] with bindings := none } 0 .left [0] [] "body" (.bvar 1)⟩,
   ⟨"capture-quantified-scoped-premise", .capture quantifiedRule 0 (.premise 0 2 0) [] [] "body" (.bvar 1)⟩,
   ⟨"capture-rest-tag-order-and-duplicates", .captureRest restRule 0 .left [1] [] "tail" .hashBag [.apply "a" [], .apply "a" [], .apply "b" []]⟩,
   ⟨"refuse-wrong-rest-site", .captureRest restRule 0 .left [0] [] "tail" .hashBag [.apply "a" []]⟩]

def incorrectResults : List (Fixture × Term) :=
  [(⟨"refuse-same-body-wrong-result", .capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 1)⟩, .symbol "None"),
   (⟨"refuse-unselected-dependence-success-result", .capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 0)⟩,
     ScopedCapture.scopedAssignmentOptionTerm (some [("body", capturedBody)])),
   (⟨"refuse-duplicate-dependencies-singleton-result", .dependencies duplicateDependencies "body"⟩,
     dependencyOptionTerm (some [nameSort])),
   (⟨"refuse-incorrect-address-depth", .depthAtSite (binderRule []) .left [0]⟩,
     ScopedCapture.naturalOptionTerm (some 1))]

theorem incorrect_results_differ : ∀ entry ∈ incorrectResults, entry.1.expectedTerm ≠ entry.2 := by decide +kernel

theorem different_spines_same_body :
    (Input.capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 1)).expectedTerm =
      (Input.capture (binderRule [.bvar 0]) 0 .left [0] [] "body" (.bvar 0)).expectedTerm ∧
    (Input.capture (binderRule [.bvar 1]) 0 .left [0] [] "body" (.bvar 1)).expectedTerm =
      ScopedCapture.scopedAssignmentOptionTerm (some [("body", capturedBody)]) := by decide +kernel

end Controls


#print axioms dependency_rows_returns
#print axioms dependency_rows_captured_returns
#print axioms dependencies_returns
#print axioms dependencies_captured_returns
#print axioms occurrence_rows_returns
#print axioms occurrence_rows_captured_returns
#print axioms quantified_body_returns
#print axioms quantified_body_captured_returns
#print axioms site_premise_returns
#print axioms site_premise_captured_returns
#print axioms premise_pattern_returns
#print axioms premise_pattern_captured_returns
#print axioms premise_depth_returns
#print axioms premise_depth_captured_returns
#print axioms site_pattern_returns
#print axioms site_pattern_captured_returns
#print axioms site_depth_returns
#print axioms site_depth_captured_returns
#print axioms occurrence_name_returns
#print axioms occurrence_name_captured_returns
#print axioms occurrence_depth_returns
#print axioms occurrence_depth_captured_returns
#print axioms depth_at_site_returns
#print axioms depth_at_site_captured_returns
#print axioms occurrence_declared_returns
#print axioms occurrence_declared_captured_returns
#print axioms arguments_returns
#print axioms arguments_captured_returns
#print axioms capture_returns
#print axioms capture_captured_returns
#print axioms capture_rest_returns
#print axioms capture_rest_captured_returns
#print axioms capture_term_returns
#print axioms capture_completed_iff
#print axioms capture_derivation_iff
#print axioms capture_success_iff
#print axioms TypedOccurrence.compiled_capture_returns
#print axioms TypedOccurrence.compiled_capture_canonical_iff
#print axioms Controls.Input.returns
#print axioms Controls.Fixture.returns
#print axioms Controls.incorrect_results_differ
#print axioms Controls.different_spines_same_body


end ScopedMetadata

end MetadataExecution

namespace ScopedMatching

open Mettapedia.OSLF.MeTTaIL.RuleBinding (DepthCoherent ArgumentsDepthCoherent depthCoherent_of_site depthCoherent_left depthCoherent_right)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (OrderedPattern)

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000


open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval
open scoped ProgramQuotation

private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)

attribute [local simp] encoded a v number patternValue patternsValue

private inductive Helper where
  | match | arguments | argumentResults | vector | vectorResults | rule

private def Helper.head : Helper → String
  | .match => "gslt:rule:scope-match"
  | .arguments => "gslt:rule:scope-match-arguments"
  | .argumentResults => "gslt:rule:scope-match-arguments-results"
  | .vector => "gslt:rule:scope-match-vector"
  | .vectorResults => "gslt:rule:scope-match-vector-results"
  | .rule => "gslt:rule:scope-match-rule"

private def Helper.names : Helper → List String
  | .match => ["rule", "ambient", "site", "path", "assignment", "schema", "target"]
  | .arguments => ["rule", "ambient", "site", "path", "assignment", "index", "patterns", "targets"]
  | .argumentResults => ["rule", "ambient", "site", "path", "results", "index", "patterns", "targets"]
  | .vector => ["rule", "ambient", "site", "path", "assignment", "index", "patterns", "rest", "targets"]
  | .vectorResults => ["rule", "ambient", "site", "path", "results", "index", "patterns", "rest", "targets"]
  | .rule => ["rule", "ambient", "target"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (RuleExecutionProgram.equations helper.head)[0]'(by cases helper <;> decide +kernel)

private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] := by
  apply PureData.named_equation_clause program helper.head (equation helper) helper.names values
  · cases helper <;> rfl
  · cases helper <;> rfl
  · cases helper <;> decide +kernel
  · exact length

private theorem helper_raw (helper : Helper) (index : Nat) (within : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  have checked : (List.range helper.names.length).all (fun index => argumentIsRaw program helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr within)

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index within
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem lookup_cons (caller : Subst) (name query : String) (value : Atom) :
    Subst.lookup ((name, value) :: caller) query =
      if name == query then some value else Subst.lookup caller query := by
  simp only [Subst.lookup, List.find?_cons]
  cases same : (name == query) <;> simp

private theorem variable_cons (caller : Subst) (name query : String) (value : Atom) :
    applySubst ((name, value) :: caller) (v query) =
      if name == query then value else applySubst caller (v query) := by
  simp only [applySubst, lookup_cons]
  cases same : (name == query) <;> simp

attribute [local simp] lookup_cons variable_cons

private theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  induction values with
  | nil => rfl
  | cons first rest ih => rw [List.map_cons, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, ih]

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private abbrev ruleValue (rule : RewriteRule) : Atom :=
  encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)
private abbrev siteValue (site : RulePatternSite) : Atom :=
  encoded (InferenceCettaWire.AuthoredRule.siteTerm site)
private abbrev pathValue (path : List Nat) : Atom := encoded (encodeList Term.natural path)
private abbrev assignmentValue (assignment : ScopedRuleMatching.Assignment) : Atom :=
  encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)

/-- The existing contextual assignments in their original ordered list wire. -/
def assignmentsTerm (assignments : List ScopedRuleMatching.Assignment) : Term :=
  encodeList RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignments

private abbrev resultsValue (assignments : List ScopedRuleMatching.Assignment) : Atom :=
  encoded (assignmentsTerm assignments)

private theorem append_results_returns (caller : Subst) (state : State)
    (left right : List ScopedRuleMatching.Assignment) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [resultsValue left, resultsValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v one, v two]) state
      (resultsValue (left ++ right)) := by
  have lifted := RuleExecutionProgram.automata_captured_returns (by
      simp [codeWithin, expressionHeadWithin, atomsWithin, RuleExecutionProgram.matcherHead])
    (MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm)
      (right.map RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm) (v one) (v two) (by
        simpa only [resultsValue, assignmentsTerm, MatchAutomataSourceExecution.listValue, encodeList_map, Function.comp_def, id] using captured))
  have kept := lifted
  rw [← List.map_append] at kept
  simpa only [resultsValue, assignmentsTerm, MatchAutomataSourceExecution.listValue, encodeList_map, Function.comp_def, id] using kept

private inductive ResultKind where | arguments | vector

private def ResultKind.helper : ResultKind → Helper
  | .arguments => .argumentResults
  | .vector => .vectorResults
private def ResultKind.called : ResultKind → Helper
  | .arguments => .arguments
  | .vector => .vector
private def ResultKind.tailName : ResultKind → String
  | .arguments => "rest"
  | .vector => "remaining"
private def ResultKind.extraNames : ResultKind → List String
  | .arguments => ["index", "patterns", "targets"]
  | .vector => ["index", "patterns", "rest", "targets"]
private def ResultKind.extraValues (kind : ResultKind) (index : Nat) (patterns : List Pattern)
    (rest : Option String) (targets : List Pattern) : List Atom :=
  [number index, patternsValue patterns] ++
    (match kind with | .arguments => [] | .vector => [encoded (InferenceCettaWire.encodeRest rest)]) ++
    [patternsValue targets]
private def ResultKind.values (kind : ResultKind) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (results : List ScopedRuleMatching.Assignment)
    (index : Nat) (patterns : List Pattern) (rest : Option String) (targets : List Pattern) : List Atom :=
  [ruleValue rule, number ambient, siteValue site, pathValue path, resultsValue results] ++
    kind.extraValues index patterns rest targets
private def ResultKind.callValues (kind : ResultKind) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (index : Nat) (patterns : List Pattern) (rest : Option String) (targets : List Pattern) : List Atom :=
  [ruleValue rule, number ambient, siteValue site, pathValue path, assignmentValue assignment] ++
    kind.extraValues index patterns rest targets
private def ResultKind.callArguments (kind : ResultKind) (assignment : String) : List Atom :=
  [v "rule", v "ambient", v "site", v "path", v assignment] ++ kind.extraNames.map v
private def resultConsBody (kind : ResultKind) : Atom :=
  a "let" [v "head", a kind.called.head (kind.callArguments "assignment"),
    a "let" [v "tail", a kind.helper.head (kind.callArguments kind.tailName),
      a "gslt:automata:append" [v "head", v "tail"]]]
private def resultCases (kind : ResultKind) : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [v "assignment", v kind.tailName], resultConsBody kind)]
private theorem results_shape (kind : ResultKind) : (equation kind.helper).body =
    a "case" [v "results", .expression ((resultCases kind).map fun row => .expression [row.1, row.2])] := by
  cases kind <;> decide +kernel

/-- An actual source continuation combines the supplied child computations
in their physical list order. This private composition law is discharged by
structural matcher induction below. -/
private theorem results_returns (kind : ResultKind) (state : State)
    (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (results : List ScopedRuleMatching.Assignment) (index : Nat) (patterns : List Pattern)
    (rest : Option String) (targets : List Pattern)
    (outputs : ScopedRuleMatching.Assignment → List ScopedRuleMatching.Assignment)
    (computed : ∀ assignment ∈ results,
      PureReturns program [] state (a kind.called.head
        (kind.callValues rule ambient site path assignment index patterns rest targets)) state
        (resultsValue (outputs assignment))) :
    PureReturns program [] state (a kind.helper.head
      (kind.values rule ambient site path results index patterns rest targets)) state
      (resultsValue (results.flatMap outputs)) := by
  induction results with
  | nil =>
      let values := kind.values rule ambient site path [] index patterns rest targets
      let caller := environment kind.helper values
      apply helper_call kind.helper [] state _ values _ (by cases kind <;> rfl) (captured_closed _)
      rw [results_shape]
      apply case_returns program caller caller state state state (v "results") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ (resultCases kind) (read_cases_encoded _) _ _ _
      · cases kind <;> simpa [caller, values, environment, Helper.names, ResultKind.values, ResultKind.extraValues,
          ResultKind.helper, resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "results"
      · simp [resultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons first results ih =>
      let values := kind.values rule ambient site path (first :: results) index patterns rest targets
      let caller := environment kind.helper values
      let selected := (kind.tailName, resultsValue results) :: ("assignment", assignmentValue first) :: caller
      let headBound := ("head", resultsValue (outputs first)) :: selected
      let tailBound := ("tail", resultsValue (results.flatMap outputs)) :: headBound
      apply helper_call kind.helper [] state _ values _ (by cases kind <;> rfl) (captured_closed _)
      rw [results_shape]
      apply case_returns program caller selected state state state (v "results")
        (resultsValue (first :: results)) (resultConsBody kind) _ _ (resultCases kind) (read_cases_encoded _) _ _ _
      · cases kind <;> simpa [caller, values, environment, Helper.names, ResultKind.values, ResultKind.extraValues,
          ResultKind.helper, resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "results"
      · cases kind <;> simp [resultCases, caller, values, environment, Helper.names, ResultKind.values,
          ResultKind.extraValues, ResultKind.helper, ResultKind.tailName, selected, resultsValue,
          assignmentsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · have headReturned := helper_capture kind.called selected state (kind.callArguments "assignment")
            (kind.callValues rule ambient site path first index patterns rest targets) _
            (by cases kind <;> rfl) (by
              cases kind <;> simp [ResultKind.callArguments, ResultKind.callValues, ResultKind.values, ResultKind.extraValues,
                ResultKind.extraNames, selected, caller, values, environment, Helper.names,
                ResultKind.helper, ResultKind.tailName, applySubst, Subst.lookup])
            (computed first List.mem_cons_self)
        apply named_let_returns selected state "head" _ _ _ _
          (by cases kind <;> simp [selected, caller, values, environment, Helper.names,
            ResultKind.helper, ResultKind.tailName, ResultKind.values, ResultKind.extraValues, Subst.lookup]) headReturned
        have tailReturned := helper_capture kind.helper headBound state (kind.callArguments kind.tailName)
            (kind.values rule ambient site path results index patterns rest targets) _
            (by cases kind <;> rfl) (by
              cases kind <;> simp [ResultKind.callArguments, ResultKind.values, ResultKind.extraValues,
                ResultKind.extraNames, headBound, selected, caller, values, environment, Helper.names,
                ResultKind.helper, ResultKind.tailName, applySubst, Subst.lookup])
            (ih (fun assignment member => computed assignment (List.mem_cons_of_mem _ member)))
        apply named_let_returns headBound state "tail" _ _ _ _
          (by cases kind <;> simp [headBound, selected, caller, values, environment, Helper.names,
            ResultKind.helper, ResultKind.tailName, ResultKind.values, ResultKind.extraValues, Subst.lookup]) tailReturned
        simpa only [List.flatMap_cons] using append_results_returns tailBound state
          (outputs first) (results.flatMap outputs) "head" "tail" (by simp [tailBound, headBound])

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v name) (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

private theorem append_path_returns (caller : Subst) (state : State) (path : List Nat) (index : Nat)
    (one two : Atom)
    (matcherOne : codeWithin RuleExecutionProgram.matcherHead one = true)
    (matcherTwo : codeWithin RuleExecutionProgram.matcherHead two = true)
    (captured : [one, two].map (applySubst caller) = [pathValue path, pathValue [index]]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state (pathValue (path ++ [index])) := by
  have lifted := RuleExecutionProgram.automata_captured_returns (by
      simp [codeWithin, expressionHeadWithin, atomsWithin, RuleExecutionProgram.matcherHead, matcherOne, matcherTwo])
    (MatchAutomataSourceExecution.append_captured_returns caller state (path.map Term.natural) [Term.natural index]
      one two (by simpa [pathValue, MatchAutomataSourceExecution.listValue] using captured))
  have kept := lifted
  have mapped : path.map Term.natural ++ [Term.natural index] = (path ++ [index]).map Term.natural := by simp
  change PureReturns program caller state (a "gslt:automata:append" [one, two]) state
    (encoded (encodeList id (path.map Term.natural ++ [Term.natural index]))) at kept
  rw [mapped, encodeList_map] at kept
  exact kept

private theorem option_list_returns (caller : Subst) (state : State) (code : Atom)
    (value : Option ScopedRuleMatching.Assignment) (fresh : Subst.lookup caller "found" = none)
    (computed : PureReturns program caller state code state
      (encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentOptionTerm value))) :
    PureReturns program caller state (a "case" [code, .expression
      [.expression [.symbol "None", .symbol "LNil"],
       .expression [a "Some" [v "found"], a "LCons" [v "found", .symbol "LNil"]]]]) state
      (resultsValue value.toList) := by
  cases value with
  | none =>
      apply case_returns program caller caller state state state code (.symbol "None")
        (.symbol "LNil") (.symbol "LNil") _
        [(.symbol "None", .symbol "LNil"), (a "Some" [v "found"], a "LCons" [v "found", .symbol "LNil"])]
        (read_cases_encoded _) computed _ (symbol_returns program caller state "LNil")
      simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  | some found =>
      let selected := ("found", assignmentValue found) :: caller
      apply case_returns program caller selected state state state code (a "Some" [assignmentValue found])
        (a "LCons" [v "found", .symbol "LNil"]) _ _
        [(.symbol "None", .symbol "LNil"), (a "Some" [v "found"], a "LCons" [v "found", .symbol "LNil"])]
        (read_cases_encoded _) computed _ _
      · simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, fresh, selected]
      · simpa [resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          selected, applySubst, applySubst.applySubstList] using
          PureData.template_return program selected state (a "LCons" [v "found", .symbol "LNil"])
            (.constructor "LCons" _ (by decide +kernel) (by decide) (by
              intro child member
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
              rcases member with rfl | rfl
              · exact .captured "found"
              · exact .symbol "LNil"))

private inductive MatchForm where
  | fvar | bvar | application | lambda | multiLambda | substitution | vector | other

private def metadataCaptureBody : Atom := a "case"
  [a "gslt:rule:scope-metadata-capture" [v "rule", v "ambient", v "site", v "path",
      v "assignment", v "name", v "target"],
   .expression [.expression [.symbol "None", .symbol "LNil"],
     .expression [a "Some" [v "found"], a "LCons" [v "found", .symbol "LNil"]]]]
private def applicationBody : Atom := a "if"
  [a "==" [v "label", v "actual"], a Helper.arguments.head
    [v "rule", v "ambient", v "site", v "path", v "assignment", number 0, v "patterns", v "targets"],
   .symbol "LNil"]
private def lambdaBody : Atom := a "let"
  [v "nested", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]],
   a Helper.match.head [v "rule", v "ambient", v "site", v "nested", v "assignment", v "body", v "actual-body"]]
private def multiLambdaBody : Atom := a "if"
  [a "==" [v "arity", v "actual-arity"], lambdaBody, .symbol "LNil"]
private def substitutionBody : Atom := a "let"
  [v "nested", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]],
   a "let" [v "heads", a Helper.match.head
     [v "rule", v "ambient", v "site", v "nested", v "assignment", v "body", v "actual-body"],
     a Helper.argumentResults.head [v "rule", v "ambient", v "site", v "path", v "heads", number 1,
       a "LCons" [v "replacement", .symbol "LNil"],
       a "LCons" [v "actual-replacement", .symbol "LNil"]]]]
private def vectorBody : Atom := a Helper.vector.head
  [v "rule", v "ambient", v "site", v "path", v "assignment", number 0, v "patterns", v "rest", v "targets"]
private def targetCases : MatchForm → SpaceSemantics.Cases
  | .application => [(a "PApp" [v "actual", v "targets"], applicationBody), (v "other", .symbol "LNil")]
  | .lambda => [(a "PLam" [v "actual-display", v "actual-body"], lambdaBody), (v "other", .symbol "LNil")]
  | .multiLambda => [(a "PMultiLam" [v "actual-arity", v "actual-display", v "actual-body"], multiLambdaBody),
      (v "other", .symbol "LNil")]
  | .substitution => [(a "PSubst" [v "actual-body", v "actual-replacement"], substitutionBody), (v "other", .symbol "LNil")]
  | .vector => [(a "PCollection" [encoded (InferenceCettaWire.encodeCollectionType .vec), v "targets", .symbol "RNone"], vectorBody), (v "other", .symbol "LNil")]
  | _ => []
private def matchBody : MatchForm → Atom
  | .fvar => metadataCaptureBody
  | .bvar => a "if" [a "==" [v "schema", v "target"], a "LCons" [v "assignment", .symbol "LNil"], .symbol "LNil"]
  | .other => .symbol "LNil"
  | form => a "case" [v "target", .expression ((targetCases form).map fun row => .expression [row.1, row.2])]
private def matchCases : SpaceSemantics.Cases :=
  [(a "FVar" [v "name"], matchBody .fvar), (a "Var" [v "index"], matchBody .bvar),
   (a "PApp" [v "label", v "patterns"], matchBody .application),
   (a "PLam" [v "display", v "body"], matchBody .lambda),
   (a "PMultiLam" [v "arity", v "display", v "body"], matchBody .multiLambda),
   (a "PSubst" [v "body", v "replacement"], matchBody .substitution),
   (a "PCollection" [encoded (InferenceCettaWire.encodeCollectionType .vec), v "patterns", v "rest"], matchBody .vector),
   (v "other", matchBody .other)]
private theorem matching_shape : (equation .match).body =
    a "case" [v "schema", .expression (matchCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private def matchValues (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern) : List Atom :=
  [ruleValue rule, number ambient, siteValue site, pathValue path, assignmentValue assignment,
    patternValue schema, patternValue target]
private def matchEnvironment (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern) : Subst :=
  environment .match (matchValues rule ambient site path assignment schema target)
private def schemaForm : Pattern → MatchForm
  | .fvar _ => .fvar
  | .bvar _ => .bvar
  | .apply _ _ => .application
  | .lambda _ _ => .lambda
  | .multiLambda _ _ _ => .multiLambda
  | .subst _ _ => .substitution
  | .collection .vec _ _ => .vector
  | _ => .other
private def schemaSelected (caller : Subst) : Pattern → Subst
  | .fvar name => ("name", encoded (.string name)) :: caller
  | .bvar index => ("index", number index) :: caller
  | .apply label patterns => ("patterns", patternsValue patterns) :: ("label", encoded (.string label)) :: caller
  | .lambda display body => ("body", patternValue body) :: ("display", encoded (InferenceCettaWire.encodeBinder display)) :: caller
  | .multiLambda arity display body => ("body", patternValue body) ::
      ("display", encoded (encodeList Term.string display)) :: ("arity", number arity) :: caller
  | .subst body replacement => ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
  | .collection .vec patterns rest => ("rest", encoded (InferenceCettaWire.encodeRest rest)) :: ("patterns", patternsValue patterns) :: caller
  | schema => ("other", patternValue schema) :: caller

private theorem schema_case_returns (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (schema target : Pattern) (answer : Atom)
    (continued : PureReturns program
      (schemaSelected (matchEnvironment rule ambient site path assignment schema target) schema)
      state (matchBody (schemaForm schema)) state answer) :
    PureReturns program (matchEnvironment rule ambient site path assignment schema target)
      state (equation .match).body state answer := by
  let caller := matchEnvironment rule ambient site path assignment schema target
  rw [matching_shape]
  apply case_returns program caller (schemaSelected caller schema) state state state (v "schema")
    (patternValue schema) (matchBody (schemaForm schema)) answer _ matchCases (read_cases_encoded _) _ _ continued
  · simpa [caller, matchEnvironment, matchValues, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "schema"
  · cases schema with
    | collection kind patterns rest =>
        cases kind <;> simp [schemaSelected, schemaForm, caller, matchEnvironment, matchValues, environment,
          Helper.names, matchCases, InferenceCettaWire.encodePattern,
          InferenceCettaWire.encodeCollectionType, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
    | _ =>
        simp [schemaSelected, schemaForm, caller, matchEnvironment, matchValues, environment,
          Helper.names, matchCases, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeBinder, InferenceCettaWire.encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]

private def targetNames : MatchForm → List String
  | .application => ["actual", "targets", "other"]
  | .lambda => ["actual-display", "actual-body", "other"]
  | .multiLambda => ["actual-arity", "actual-display", "actual-body", "other"]
  | .substitution => ["actual-body", "actual-replacement", "other"]
  | .vector => ["targets", "other"]
  | _ => []
private def targetSelected (caller : Subst) : MatchForm → Pattern → Subst
  | .application, .apply actual targets => ("targets", patternsValue targets) :: ("actual", encoded (.string actual)) :: caller
  | .lambda, .lambda display body => ("actual-body", patternValue body) ::
      ("actual-display", encoded (InferenceCettaWire.encodeBinder display)) :: caller
  | .multiLambda, .multiLambda arity display body => ("actual-body", patternValue body) ::
      ("actual-display", encoded (encodeList Term.string display)) :: ("actual-arity", number arity) :: caller
  | .substitution, .subst body replacement => ("actual-replacement", patternValue replacement) :: ("actual-body", patternValue body) :: caller
  | .vector, .collection .vec targets none => ("targets", patternsValue targets) :: caller
  | _, target => ("other", patternValue target) :: caller
private def targetCode : MatchForm → Pattern → Atom
  | .application, .apply _ _ => applicationBody
  | .lambda, .lambda _ _ => lambdaBody
  | .multiLambda, .multiLambda _ _ _ => multiLambdaBody
  | .substitution, .subst _ _ => substitutionBody
  | .vector, .collection .vec _ none => vectorBody
  | _, _ => .symbol "LNil"


private theorem matchValue_variable (caller : Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue caller (v name) value = matchAtom caller (v name) value := by
  cases value <;> simp only [SpaceSemantics.matchValue]
private theorem matchValue_symbol (caller : Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue caller (.symbol name) value =
      if .symbol name = value then some caller else none :=
  SpaceSemantics.matchValue_literal (.symbol name) caller value
private theorem matchValue_grounded (caller : Subst) (ground : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue)
    (value : Atom) :
    SpaceSemantics.matchValue caller (.grounded ground) value =
      if .grounded ground = value then some caller else none :=
  SpaceSemantics.matchValue_literal (.grounded ground) caller value
private theorem matchValue_application (caller : Subst) (head : String) (patterns values : List Atom)
    (notCons : head ≠ "cons") :
    SpaceSemantics.matchValue caller (a head patterns) (.expression values) =
      SpaceSemantics.matchValue.matchValues caller (.symbol head :: patterns) values := by
  apply SpaceSemantics.matchValue_expression_of_not_cons
  intro first rest same
  have eq := List.cons.inj same
  apply notCons
  exact Atom.symbol.inj eq.1
private theorem target_case_returns (caller : Subst) (state : State) (form : MatchForm)
    (target : Pattern) (answer : Atom)
    (supported : form = .application ∨ form = .lambda ∨ form = .multiLambda ∨ form = .substitution ∨ form = .vector)
    (fresh : ∀ name ∈ targetNames form, Subst.lookup caller name = none)
    (captured : applySubst caller (v "target") = patternValue target)
    (continued : PureReturns program (targetSelected caller form target) state (targetCode form target) state answer) :
    PureReturns program caller state (matchBody form) state answer := by
  have evaluated : PureReturns program caller state (v "target") state (patternValue target) := by
    simpa only [captured] using variable_returns program caller state "target"
  have actualFresh : form = .application → Subst.lookup caller "actual" = none := by
    intro same; subst form; exact fresh _ (by simp [targetNames])
  have targetsFresh : form = .application ∨ form = .vector → Subst.lookup caller "targets" = none := by
    intro same; rcases same with rfl | rfl <;> exact fresh _ (by simp [targetNames])
  have displayFresh : form = .lambda ∨ form = .multiLambda → Subst.lookup caller "actual-display" = none := by
    intro same; rcases same with rfl | rfl <;> exact fresh _ (by simp [targetNames])
  have bodyFresh : form = .lambda ∨ form = .multiLambda ∨ form = .substitution →
      Subst.lookup caller "actual-body" = none := by
    intro same; rcases same with rfl | rfl | rfl <;> exact fresh _ (by simp [targetNames])
  have arityFresh : form = .multiLambda → Subst.lookup caller "actual-arity" = none := by
    intro same; subst form; exact fresh _ (by simp [targetNames])
  have replacementFresh : form = .substitution → Subst.lookup caller "actual-replacement" = none := by
    intro same; subst form; exact fresh _ (by simp [targetNames])
  have otherFresh : Subst.lookup caller "other" = none := by
    rcases supported with rfl | rfl | rfl | rfl | rfl <;> exact fresh _ (by simp [targetNames])
  rcases supported with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply case_returns program caller (targetSelected caller _ target) state state state (v "target")
      (patternValue target) (targetCode _ target) answer _ (targetCases _) (read_cases_encoded _) evaluated _ continued
  all_goals
    cases target with
    | collection kind targets rest =>
        cases kind <;> cases rest <;> simp [targetSelected, targetCode, targetCases, InferenceCettaWire.encodePattern,
          InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, matchValue_variable, matchValue_symbol, matchValue_grounded, matchValue_application,
          SpaceSemantics.matchValue.matchValues, matchAtom, targetsFresh, otherFresh]
    | _ =>
        simp [targetSelected, targetCode, targetCases, InferenceCettaWire.encodePattern,
          InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, matchValue_variable, matchValue_symbol, matchValue_application, SpaceSemantics.matchValue.matchValues,
          matchAtom, actualFresh, targetsFresh, displayFresh, bodyFresh, arityFresh, replacementFresh, otherFresh]

private def argumentsConsBody : Atom := a "let"
  [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]],
   a "let" [v "heads", a Helper.match.head
     [v "rule", v "ambient", v "site", v "nested", v "assignment", v "pattern", v "target"],
     a "let" [v "next", a "+" [v "index", number 1],
       a Helper.argumentResults.head [v "rule", v "ambient", v "site", v "path", v "heads", v "next", v "tail", v "rest"]]]]
private def argumentsCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", .symbol "LNil"], a "LCons" [v "assignment", .symbol "LNil"]),
   (.expression [a "LCons" [v "pattern", v "tail"], a "LCons" [v "target", v "rest"]], argumentsConsBody),
   (v "other", .symbol "LNil")]
private theorem arguments_shape : (equation .arguments).body =
    a "case" [.expression [v "patterns", v "targets"],
      .expression (argumentsCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private def argumentValues (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (patterns targets : List Pattern) : List Atom :=
  [ruleValue rule, number ambient, siteValue site, pathValue path, assignmentValue assignment,
    number index, patternsValue patterns, patternsValue targets]
private def argumentEnvironment (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (patterns targets : List Pattern) : Subst :=
  environment .arguments (argumentValues rule ambient site path assignment index patterns targets)
private def argumentsSelected (caller : Subst) : List Pattern → List Pattern → Subst
  | [], [] => caller
  | pattern :: patterns, target :: targets =>
      ("rest", patternsValue targets) :: ("target", patternValue target) ::
        ("tail", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
  | patterns, targets => ("other", .expression [patternsValue patterns, patternsValue targets]) :: caller
private def argumentsCode : List Pattern → List Pattern → Atom
  | [], [] => a "LCons" [v "assignment", .symbol "LNil"]
  | _ :: _, _ :: _ => argumentsConsBody
  | _, _ => .symbol "LNil"

private theorem arguments_case_returns (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (index : Nat) (patterns targets : List Pattern) (answer : Atom)
    (continued : PureReturns program
      (argumentsSelected (argumentEnvironment rule ambient site path assignment index patterns targets) patterns targets)
      state (argumentsCode patterns targets) state answer) :
    PureReturns program (argumentEnvironment rule ambient site path assignment index patterns targets)
      state (equation .arguments).body state answer := by
  let caller := argumentEnvironment rule ambient site path assignment index patterns targets
  rw [arguments_shape]
  apply case_returns program caller (argumentsSelected caller patterns targets) state state state
    (.expression [v "patterns", v "targets"]) (.expression [patternsValue patterns, patternsValue targets])
    (argumentsCode patterns targets) answer _ argumentsCases (read_cases_encoded _) _ _ continued
  · simpa [caller, argumentEnvironment, argumentValues, environment, Helper.names, applySubst, Subst.lookup] using
      PureData.variables_return program caller state ["patterns", "targets"]
  · cases patterns <;> cases targets <;>
      simp [argumentsSelected, argumentsCode, argumentsCases, caller, argumentEnvironment, argumentValues,
        environment, Helper.names, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def vectorRestBody : Atom := a "let"
  [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]],
   a "case" [a "gslt:rule:scope-metadata-capture-rest" [v "rule", v "ambient", v "site", v "nested", v "assignment",
     v "name", encoded (InferenceCettaWire.encodeCollectionType .vec), v "targets"],
     .expression [.expression [.symbol "None", .symbol "LNil"],
       .expression [a "Some" [v "found"], a "LCons" [v "found", .symbol "LNil"]]]]]
private def vectorNilBody : Atom := a "case" [v "rest", .expression
  [.expression [.symbol "RNone", a "case" [v "targets", .expression
    [.expression [.symbol "LNil", a "LCons" [v "assignment", .symbol "LNil"]],
     .expression [v "other", .symbol "LNil"]]]],
   .expression [a "RSome" [v "name"], vectorRestBody]]]
private def vectorConsBody : Atom := a "let"
  [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "index", .symbol "LNil"]],
   a "let" [v "heads", a Helper.match.head
     [v "rule", v "ambient", v "site", v "nested", v "assignment", v "pattern", v "target"],
     a "let" [v "next", a "+" [v "index", number 1],
       a Helper.vectorResults.head [v "rule", v "ambient", v "site", v "path", v "heads", v "next", v "tail", v "rest", v "remaining"]]]]
private def vectorTargetsBody : Atom := a "case" [v "targets", .expression
  [.expression [a "LCons" [v "target", v "remaining"], vectorConsBody],
   .expression [v "other", .symbol "LNil"]]]
private def vectorCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", vectorNilBody), (a "LCons" [v "pattern", v "tail"], vectorTargetsBody)]
private theorem vector_shape : (equation .vector).body =
    a "case" [v "patterns", .expression (vectorCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private def vectorValues (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (patterns : List Pattern) (rest : Option String)
    (targets : List Pattern) : List Atom :=
  [ruleValue rule, number ambient, siteValue site, pathValue path, assignmentValue assignment,
    number index, patternsValue patterns, encoded (InferenceCettaWire.encodeRest rest), patternsValue targets]
private def vectorEnvironment (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (patterns : List Pattern) (rest : Option String)
    (targets : List Pattern) : Subst :=
  environment .vector (vectorValues rule ambient site path assignment index patterns rest targets)
private def vectorSelected (caller : Subst) : List Pattern → Subst
  | [] => caller
  | pattern :: patterns => ("tail", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
private def vectorCode : List Pattern → Atom
  | [] => vectorNilBody
  | _ :: _ => vectorTargetsBody
private theorem vector_case_returns (state : State) (rule : RewriteRule) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : ScopedRuleMatching.Assignment)
    (index : Nat) (patterns : List Pattern) (rest : Option String) (targets : List Pattern) (answer : Atom)
    (continued : PureReturns program
      (vectorSelected (vectorEnvironment rule ambient site path assignment index patterns rest targets) patterns)
      state (vectorCode patterns) state answer) :
    PureReturns program (vectorEnvironment rule ambient site path assignment index patterns rest targets)
      state (equation .vector).body state answer := by
  let caller := vectorEnvironment rule ambient site path assignment index patterns rest targets
  rw [vector_shape]
  apply case_returns program caller (vectorSelected caller patterns) state state state (v "patterns")
    (patternsValue patterns) (vectorCode patterns) answer _ vectorCases (read_cases_encoded _) _ _ continued
  · simpa [caller, vectorEnvironment, vectorValues, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "patterns"
  · cases patterns <;> simp [vectorSelected, vectorCode, vectorCases, caller, vectorEnvironment, vectorValues,
        environment, Helper.names, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]


private abbrev vectorExpected (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat)
    (patterns : List Pattern) (rest : Option String) (targets : List Pattern) :
    List ScopedRuleMatching.Assignment :=
  match rest with
  | none => ScopedRuleMatching.matchArgsAt rule spec ambient site path depth assignment index patterns targets
  | some name =>
      (ScopedRuleMatching.matchArgsAt rule spec ambient site path depth assignment index
        patterns (targets.take patterns.length)).filterMap fun found =>
          ScopedRuleMatching.captureRest? rule spec ambient depth site
            (path ++ [index + patterns.length]) found name .vec (targets.drop patterns.length)

private theorem vectorExpected_nil_none (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (targets : List Pattern) :
    vectorExpected rule spec ambient site path depth assignment index [] none targets =
      if targets.isEmpty then [assignment] else [] := by
  cases targets <;> simp only [vectorExpected, ScopedRuleMatching.matchArgsAt,
    ScopedRuleMatching.matchArgsAtWith, List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]

private theorem vectorExpected_nil_some (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (name : String) (targets : List Pattern) :
    vectorExpected rule spec ambient site path depth assignment index [] (some name) targets =
      (ScopedRuleMatching.captureRest? rule spec ambient depth site (path ++ [index])
        assignment name .vec targets).toList := by
  simp only [vectorExpected, List.length_nil, List.take_zero, List.drop_zero, Nat.add_zero,
    ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith, List.filterMap_cons, List.filterMap_nil]
  cases captured : ScopedRuleMatching.captureRest? rule spec ambient depth site
      (path ++ [index]) assignment name .vec targets <;> rfl

private theorem vectorExpected_cons (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat)
    (pattern target : Pattern) (patterns targets : List Pattern) (rest : Option String) :
    vectorExpected rule spec ambient site path depth assignment index (pattern :: patterns) rest (target :: targets) =
      (ScopedRuleMatching.matchAt rule spec ambient site (path ++ [index]) depth assignment pattern target).flatMap
        (fun found => vectorExpected rule spec ambient site path depth found (index + 1) patterns rest targets) := by
  cases rest with
  | none => simp only [vectorExpected, ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith, ScopedRuleMatching.matchAt]
  | some name =>
      simp only [vectorExpected, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
        ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith,
        List.filterMap_flatMap, ScopedRuleMatching.matchAt, Nat.add_assoc, Nat.add_comm 1 patterns.length]

private theorem vectorExpected_short (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat)
    (pattern : Pattern) (patterns : List Pattern) (rest : Option String) :
    vectorExpected rule spec ambient site path depth assignment index (pattern :: patterns) rest [] = [] := by
  cases rest <;> simp only [vectorExpected, List.take_nil, ScopedRuleMatching.matchArgsAt,
    ScopedRuleMatching.matchArgsAtWith, List.filterMap_nil]

private theorem singleton_returns (caller : Subst) (state : State) (assignment : ScopedRuleMatching.Assignment)
    (captured : applySubst caller (v "assignment") = assignmentValue assignment) :
    PureReturns program caller state (a "LCons" [v "assignment", .symbol "LNil"]) state
      (resultsValue [assignment]) := by
  have literal : PureData.Template program (a "LCons" [v "assignment", .symbol "LNil"]) :=
    .constructor "LCons" _ (by decide +kernel) (by decide) (by
      intro child member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · exact .captured "assignment"
      · exact .symbol "LNil")
  simpa only [resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    applySubst, applySubst.applySubstList, ← captured] using
    PureData.template_return program caller state _ literal

theorem fvar_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (name : String) (target : Pattern)
    (attached : rule.bindings = some spec)
    (coherent : DepthCoherent rule site path depth (.fvar name)) :
    PureReturns program [] state (a Helper.match.head
      (matchValues rule ambient site path assignment (.fvar name) target)) state
      (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth assignment (.fvar name) target)) := by
  let values := matchValues rule ambient site path assignment (.fvar name) target
  let caller := matchEnvironment rule ambient site path assignment (.fvar name) target
  let selected := ("name", encoded (.string name)) :: caller
  apply helper_call .match [] state _ values _ rfl (captured_closed _)
  apply schema_case_returns state rule ambient site path assignment (.fvar name) target
  change PureReturns program selected state metadataCaptureBody state _
  rw [ScopedRuleMatching.matchAt_fvar]
  apply option_list_returns selected state _ _
    (by simp [selected, caller, matchEnvironment, matchValues, environment, Helper.names, Subst.lookup])
  have actual := RuleInstantiationExecution.ScopedMetadata.capture_captured_returns selected state rule ambient
    site path assignment name target (v "rule") (v "ambient") (v "site") (v "path")
    (v "assignment") (v "name") (v "target") (by
      simp [selected, caller, matchEnvironment, matchValues, environment, Helper.names, applySubst, Subst.lookup])
  have kept := actual
  simpa only [attached, coherent.fvar, Option.bind_some] using kept

private theorem bvar_canonical (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (target : Pattern) :
    ScopedRuleMatching.matchAt rule spec ambient site path depth assignment (.bvar index) target =
      if (.bvar index : Pattern) = target then [assignment] else [] := by
  cases target <;> simp [ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith]

theorem bvar_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (target : Pattern) :
    PureReturns program [] state (a Helper.match.head
      (matchValues rule ambient site path assignment (.bvar index) target)) state
      (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth assignment (.bvar index) target)) := by
  let values := matchValues rule ambient site path assignment (.bvar index) target
  let caller := matchEnvironment rule ambient site path assignment (.bvar index) target
  let selected := ("index", number index) :: caller
  apply helper_call .match [] state _ values _ rfl (captured_closed _)
  apply schema_case_returns state rule ambient site path assignment (.bvar index) target
  change PureReturns program selected state (matchBody .bvar) state _
  rw [bvar_canonical]
  have equal := CettaWireAtom.equality_captured_returns program selected state
    (InferenceCettaWire.encodePattern (.bvar index)) (InferenceCettaWire.encodePattern target)
    "schema" "target"
    (by simp [selected, caller, matchEnvironment, matchValues, environment, Helper.names, applySubst, Subst.lookup])
    (by simp [selected, caller, matchEnvironment, matchValues, environment, Helper.names, applySubst, Subst.lookup])
  have wireEqual : InferenceCettaWire.encodePattern (.bvar index) = InferenceCettaWire.encodePattern target ↔
      (.bvar index : Pattern) = target := InferenceCettaWire.encodePattern_injective.eq_iff
  have tested : PureReturns program selected state (a "==" [v "schema", v "target"]) state
      (Effects.boolean (decide ((.bvar index : Pattern) = target))) := by
    simpa only [wireEqual] using equal
  apply bool_if_returns selected state _ _ _ _ _ tested
  by_cases same : (.bvar index : Pattern) = target
  · simp only [same, decide_true, ↓reduceIte]
    exact singleton_returns selected state assignment (by
      simp [selected, caller, matchEnvironment, matchValues, environment, Helper.names, applySubst, Subst.lookup])
  · simp only [same, decide_false, ↓reduceIte]
    exact symbol_returns program selected state "LNil"

private theorem arguments_returns_from_elements (state : State)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (patterns : List Pattern)
    (computed : ∀ pattern ∈ patterns, ∀ childPath childDepth assignment target,
      DepthCoherent rule site childPath childDepth pattern →
      PureReturns program [] state (a Helper.match.head
        (matchValues rule ambient site childPath assignment pattern target)) state
        (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site childPath childDepth
          assignment pattern target)))
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (targets : List Pattern)
    (coherent : ArgumentsDepthCoherent rule site path depth index patterns) :
    PureReturns program [] state (a Helper.arguments.head
      (argumentValues rule ambient site path assignment index patterns targets)) state
      (resultsValue (ScopedRuleMatching.matchArgsAt rule spec ambient site path depth
        assignment index patterns targets)) := by
  induction patterns generalizing assignment index targets with
  | nil =>
      cases targets with
      | nil =>
          let caller := argumentEnvironment rule ambient site path assignment index [] []
          apply helper_call .arguments [] state _ _ _ rfl (captured_closed _)
          apply arguments_case_returns state rule ambient site path assignment index [] []
          rw [ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith]
          change PureReturns program caller state (a "LCons" [v "assignment", .symbol "LNil"]) state
            (resultsValue [assignment])
          exact singleton_returns caller state assignment (by
            simp [caller, argumentEnvironment, argumentValues, environment, Helper.names, applySubst, Subst.lookup])
      | cons first targets =>
          apply helper_call .arguments [] state _ _ _ rfl (captured_closed _)
          apply arguments_case_returns state rule ambient site path assignment index [] (first :: targets)
          simpa [argumentsCode, ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"
  | cons first patterns ih =>
      cases targets with
      | nil =>
          apply helper_call .arguments [] state _ _ _ rfl (captured_closed _)
          apply arguments_case_returns state rule ambient site path assignment index (first :: patterns) []
          simpa [argumentsCode, ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"
      | cons target targets =>
          let caller := argumentEnvironment rule ambient site path assignment index (first :: patterns) (target :: targets)
          let selected := argumentsSelected caller (first :: patterns) (target :: targets)
          let nested := ("nested", pathValue (path ++ [index])) :: selected
          let heads := ScopedRuleMatching.matchAt rule spec ambient site (path ++ [index]) depth assignment first target
          let headBound := ("heads", resultsValue heads) :: nested
          let nextBound := ("next", number (index + 1)) :: headBound
          let outputs := fun found => ScopedRuleMatching.matchArgsAt rule spec ambient site path depth found
            (index + 1) patterns targets
          have pathReturned := append_path_returns selected state path index (v "path")
              (a "LCons" [v "index", .symbol "LNil"])
              (by decide) (by decide) (by
                simp [selected, caller, argumentsSelected, argumentEnvironment, argumentValues,
                  environment, Helper.names, pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  applySubst, applySubst.applySubstList, Subst.lookup])
          have headReturned := helper_capture .match nested state
              [v "rule", v "ambient", v "site", v "nested", v "assignment", v "pattern", v "target"]
              (matchValues rule ambient site (path ++ [index]) assignment first target) _ rfl (by
                simp [nested, selected, caller, argumentsSelected, argumentEnvironment, argumentValues,
                  environment, Helper.names, matchValues, applySubst, Subst.lookup])
              (computed first List.mem_cons_self _ _ assignment target coherent.head)
          have nextReturned := add_one_returns headBound state index "index" (by
            simp [headBound, nested, selected, caller, argumentsSelected, argumentEnvironment,
              argumentValues, environment, Helper.names, applySubst, Subst.lookup])
          have continued := results_returns .arguments state rule ambient site path heads (index + 1)
              patterns none targets outputs (fun found _ =>
                ih (fun child member => computed child (List.mem_cons_of_mem first member))
                  found (index + 1) targets coherent.tail)
          have tailReturned := helper_capture .argumentResults nextBound state
              [v "rule", v "ambient", v "site", v "path", v "heads", v "next", v "tail", v "rest"]
              (ResultKind.values .arguments rule ambient site path heads (index + 1) patterns none targets)
              _ rfl (by
                simp [nextBound, headBound, nested, selected, caller, argumentsSelected, argumentEnvironment,
                  argumentValues, environment, Helper.names, ResultKind.values, ResultKind.extraValues,
                  applySubst, Subst.lookup]) continued
          apply helper_call .arguments [] state _ _ _ rfl (captured_closed _)
          apply arguments_case_returns state rule ambient site path assignment index (first :: patterns) (target :: targets)
          rw [ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith]
          change PureReturns program selected state argumentsConsBody state (resultsValue (heads.flatMap outputs))
          apply named_let_returns selected state "nested" _ _ _ _
              (by simp [selected, caller, argumentsSelected, argumentEnvironment, argumentValues,
                environment, Helper.names, Subst.lookup]) pathReturned
          apply named_let_returns nested state "heads" _ _ _ _
              (by simp [nested, selected, caller, argumentsSelected, argumentEnvironment, argumentValues,
                environment, Helper.names, Subst.lookup]) headReturned
          exact named_let_returns headBound state "next" _ _ _ _
            (by simp [headBound, nested, selected, caller, argumentsSelected, argumentEnvironment, argumentValues,
              environment, Helper.names, Subst.lookup]) nextReturned tailReturned

private def vectorNoneBody : Atom := a "case" [v "targets", .expression
  [.expression [.symbol "LNil", a "LCons" [v "assignment", .symbol "LNil"]],
   .expression [v "other", .symbol "LNil"]]]

private theorem vector_rest_case_returns (caller : Subst) (state : State) (rest : Option String)
    (answer : Atom) (captured : applySubst caller (v "rest") = encoded (InferenceCettaWire.encodeRest rest))
    (fresh : Subst.lookup caller "name" = none)
    (continued : PureReturns program (match rest with
        | none => caller | some name => ("name", encoded (.string name)) :: caller)
      state (match rest with | none => vectorNoneBody | some _ => vectorRestBody) state answer) :
    PureReturns program caller state vectorNilBody state answer := by
  have evaluated : PureReturns program caller state (v "rest") state (encoded (InferenceCettaWire.encodeRest rest)) := by
    simpa only [captured] using variable_returns program caller state "rest"
  let cases := [(.symbol "RNone", vectorNoneBody), (a "RSome" [v "name"], vectorRestBody)]
  cases rest with
  | none =>
      apply case_returns program caller caller state state state (v "rest") (.symbol "RNone")
        vectorNoneBody answer _ cases (read_cases_encoded _) evaluated _ continued
      simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  | some name =>
      apply case_returns program caller (("name", encoded (.string name)) :: caller) state state state
        (v "rest") (a "RSome" [encoded (.string name)]) vectorRestBody answer _ cases
        (read_cases_encoded _) evaluated _ continued
      simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, fresh]

private theorem vector_none_target_returns (caller : Subst) (state : State)
    (assignment : ScopedRuleMatching.Assignment) (targets : List Pattern)
    (capturedTargets : applySubst caller (v "targets") = patternsValue targets)
    (capturedAssignment : applySubst caller (v "assignment") = assignmentValue assignment)
    (fresh : Subst.lookup caller "other" = none) :
    PureReturns program caller state vectorNoneBody state
      (resultsValue (if targets.isEmpty then [assignment] else [])) := by
  have evaluated : PureReturns program caller state (v "targets") state (patternsValue targets) := by
    simpa only [capturedTargets] using variable_returns program caller state "targets"
  let cases := [(.symbol "LNil", a "LCons" [v "assignment", .symbol "LNil"]), (v "other", .symbol "LNil")]
  cases targets with
  | nil =>
      simp only [patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] at evaluated
      apply case_returns program caller caller state state state (v "targets") (.symbol "LNil")
        (a "LCons" [v "assignment", .symbol "LNil"]) _ _ cases (read_cases_encoded _) evaluated _
        (singleton_returns caller state assignment capturedAssignment)
      simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  | cons first targets =>
      apply case_returns program caller (("other", patternsValue (first :: targets)) :: caller) state state state
        (v "targets") (patternsValue (first :: targets)) (.symbol "LNil") _ _ cases (read_cases_encoded _)
        evaluated _ (symbol_returns program _ state "LNil")
      simp [cases, SpaceSemantics.selectCase, matchValue_symbol, matchValue_variable,
        InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany, matchAtom, fresh]

private theorem vector_targets_case_returns (caller : Subst) (state : State) (targets : List Pattern)
    (answer : Atom) (captured : applySubst caller (v "targets") = patternsValue targets)
    (targetFresh : Subst.lookup caller "target" = none)
    (remainingFresh : Subst.lookup caller "remaining" = none)
    (otherFresh : Subst.lookup caller "other" = none)
    (continued : PureReturns program (match targets with
      | [] => ("other", .symbol "LNil") :: caller
      | target :: remaining => ("remaining", patternsValue remaining) :: ("target", patternValue target) :: caller)
      state (match targets with | [] => .symbol "LNil" | _ :: _ => vectorConsBody) state answer) :
    PureReturns program caller state vectorTargetsBody state answer := by
  have evaluated : PureReturns program caller state (v "targets") state (patternsValue targets) := by
    simpa only [captured] using variable_returns program caller state "targets"
  let cases := [(a "LCons" [v "target", v "remaining"], vectorConsBody), (v "other", .symbol "LNil")]
  cases targets with
  | nil =>
      simp only [patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] at evaluated
      apply case_returns program caller (("other", .symbol "LNil") :: caller) state state state
        (v "targets") (.symbol "LNil") (.symbol "LNil") answer _ cases (read_cases_encoded _) evaluated _ continued
      simp [cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        matchAtom, otherFresh]
  | cons target remaining =>
      apply case_returns program caller
        (("remaining", patternsValue remaining) :: ("target", patternValue target) :: caller) state state state
        (v "targets") (patternsValue (target :: remaining)) vectorConsBody answer _ cases
        (read_cases_encoded _) evaluated _ continued
      simp [cases, SpaceSemantics.selectCase, matchValue_application, matchValue_variable, matchValue_symbol,
        SpaceSemantics.matchValue.matchValues, InferenceCettaWire.encodePatterns,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, matchAtom, targetFresh, remainingFresh]

private theorem vector_returns_from_elements (state : State)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (patterns : List Pattern)
    (computed : ∀ pattern ∈ patterns, ∀ childPath childDepth assignment target,
      DepthCoherent rule site childPath childDepth pattern →
      PureReturns program [] state (a Helper.match.head
        (matchValues rule ambient site childPath assignment pattern target)) state
        (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site childPath childDepth
          assignment pattern target)))
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (rest : Option String) (targets : List Pattern)
    (attached : rule.bindings = some spec)
    (coherent : ArgumentsDepthCoherent rule site path depth index patterns)
    (restDepth : ∀ name, rest = some name →
      RuleBinding.occurrenceDepthAtSite? rule site (path ++ [index + patterns.length]) = some depth) :
    PureReturns program [] state (a Helper.vector.head
      (vectorValues rule ambient site path assignment index patterns rest targets)) state
      (resultsValue (vectorExpected rule spec ambient site path depth assignment index patterns rest targets)) := by
  induction patterns generalizing assignment index targets with
  | nil =>
      let caller := vectorEnvironment rule ambient site path assignment index [] rest targets
      apply helper_call .vector [] state _ _ _ rfl (captured_closed _)
      apply vector_case_returns state rule ambient site path assignment index [] rest targets
      apply vector_rest_case_returns caller state rest _
        (by simp [caller, vectorEnvironment, vectorValues, environment, Helper.names, applySubst, Subst.lookup])
        (by simp [caller, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup])
      cases rest with
      | none =>
          rw [vectorExpected_nil_none]
          apply vector_none_target_returns caller state assignment targets
          · simp [caller, vectorEnvironment, vectorValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [caller, vectorEnvironment, vectorValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [caller, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
      | some name =>
          let selected := ("name", encoded (.string name)) :: caller
          let nested := ("nested", pathValue (path ++ [index])) :: selected
          rw [vectorExpected_nil_some]
          apply named_let_returns selected state "nested" _ _ _ _
              (by simp [selected, caller, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup])
          · apply append_path_returns selected state path index (v "path") (a "LCons" [v "index", .symbol "LNil"])
              (by decide) (by decide)
            simp [selected, caller, vectorEnvironment, vectorValues, environment, Helper.names,
              pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
              Subst.lookup]
          · apply option_list_returns nested state _ _
              (by simp [nested, selected, caller, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup])
            have actual := RuleInstantiationExecution.ScopedMetadata.capture_rest_captured_returns nested state
              rule ambient site (path ++ [index]) assignment name .vec targets
              (v "rule") (v "ambient") (v "site") (v "nested") (v "assignment") (v "name")
              (encoded (InferenceCettaWire.encodeCollectionType .vec)) (v "targets") (by
                simp [nested, selected, caller, vectorEnvironment, vectorValues, environment, Helper.names,
                  applySubst, Subst.lookup])
            have kept := actual
            have addressed : RuleBinding.occurrenceDepthAtSite? rule site (path ++ [index]) = some depth := by
              simpa only [List.length_nil, Nat.add_zero] using restDepth name rfl
            simpa only [attached, addressed, Option.bind_some] using kept
  | cons first patterns ih =>
      cases targets with
      | nil =>
          let caller := vectorSelected
            (vectorEnvironment rule ambient site path assignment index (first :: patterns) rest []) (first :: patterns)
          apply helper_call .vector [] state _ _ _ rfl (captured_closed _)
          apply vector_case_returns state rule ambient site path assignment index (first :: patterns) rest []
          rw [vectorExpected_short]
          refine vector_targets_case_returns caller state [] _ ?_ ?_ ?_ ?_ ?_
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
          · exact symbol_returns program _ state "LNil"
      | cons target targets =>
          let caller := vectorSelected
            (vectorEnvironment rule ambient site path assignment index (first :: patterns) rest (target :: targets))
            (first :: patterns)
          let selected := ("remaining", patternsValue targets) :: ("target", patternValue target) :: caller
          let nested := ("nested", pathValue (path ++ [index])) :: selected
          let heads := ScopedRuleMatching.matchAt rule spec ambient site (path ++ [index]) depth assignment first target
          let headBound := ("heads", resultsValue heads) :: nested
          let nextBound := ("next", number (index + 1)) :: headBound
          let outputs := fun found => vectorExpected rule spec ambient site path depth found
            (index + 1) patterns rest targets
          have pathReturned := append_path_returns selected state path index (v "path")
              (a "LCons" [v "index", .symbol "LNil"])
              (by decide) (by decide) (by
                simp [selected, caller, vectorSelected, vectorEnvironment, vectorValues,
                  environment, Helper.names, pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  applySubst, applySubst.applySubstList, Subst.lookup])
          have headReturned := helper_capture .match nested state
              [v "rule", v "ambient", v "site", v "nested", v "assignment", v "pattern", v "target"]
              (matchValues rule ambient site (path ++ [index]) assignment first target) _ rfl (by
                simp [nested, selected, caller, vectorSelected, vectorEnvironment, vectorValues,
                  environment, Helper.names, matchValues, applySubst, Subst.lookup])
              (computed first List.mem_cons_self _ _ assignment target coherent.head)
          have nextReturned := add_one_returns headBound state index "index" (by
            simp [headBound, nested, selected, caller, vectorSelected, vectorEnvironment,
              vectorValues, environment, Helper.names, applySubst, Subst.lookup])
          have continued := results_returns .vector state rule ambient site path heads (index + 1)
              patterns rest targets outputs (fun found _ =>
                ih (fun child member => computed child (List.mem_cons_of_mem first member))
                  found (index + 1) targets coherent.tail (by
                    intro name same
                    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 patterns.length] using restDepth name same))
          have tailReturned := helper_capture .vectorResults nextBound state
              [v "rule", v "ambient", v "site", v "path", v "heads", v "next", v "tail", v "rest", v "remaining"]
              (ResultKind.values .vector rule ambient site path heads (index + 1) patterns rest targets)
              _ rfl (by
                simp [nextBound, headBound, nested, selected, caller, vectorSelected, vectorEnvironment,
                  vectorValues, environment, Helper.names, ResultKind.values, ResultKind.extraValues,
                  applySubst, Subst.lookup]) continued
          apply helper_call .vector [] state _ _ _ rfl (captured_closed _)
          apply vector_case_returns state rule ambient site path assignment index (first :: patterns) rest (target :: targets)
          rw [vectorExpected_cons]
          refine vector_targets_case_returns caller state (target :: targets) _ ?_ ?_ ?_ ?_ ?_
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, applySubst, Subst.lookup]
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
          · simp [caller, vectorSelected, vectorEnvironment, vectorValues, environment, Helper.names, Subst.lookup]
          · change PureReturns program selected state vectorConsBody state (resultsValue (heads.flatMap outputs))
            apply named_let_returns selected state "nested" _ _ _ _
                (by simp [selected, caller, vectorSelected, vectorEnvironment, vectorValues,
                  environment, Helper.names, Subst.lookup]) pathReturned
            apply named_let_returns nested state "heads" _ _ _ _
                (by simp [nested, selected, caller, vectorSelected, vectorEnvironment, vectorValues,
                  environment, Helper.names, Subst.lookup]) headReturned
            exact named_let_returns headBound state "next" _ _ _ _
              (by simp [headBound, nested, selected, caller, vectorSelected, vectorEnvironment, vectorValues,
                environment, Helper.names, Subst.lookup]) nextReturned tailReturned

private theorem selected_target_fresh (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern) :
    ∀ name ∈ targetNames (schemaForm schema),
      Subst.lookup (schemaSelected (matchEnvironment rule ambient site path assignment schema target) schema) name = none := by
  cases schema with
  | collection kind patterns rest =>
      cases kind <;> simp [targetNames, schemaForm, schemaSelected, matchEnvironment, matchValues,
        environment, Helper.names, Subst.lookup]
  | _ =>
      simp [targetNames, schemaForm, schemaSelected, matchEnvironment, matchValues,
        environment, Helper.names, Subst.lookup]

private theorem selected_target_captured (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern) :
    applySubst (schemaSelected (matchEnvironment rule ambient site path assignment schema target) schema)
      (v "target") = patternValue target := by
  cases schema with
  | collection kind patterns rest =>
      cases kind <;> simp [schemaSelected, matchEnvironment, matchValues,
        environment, Helper.names, applySubst, Subst.lookup]
  | _ =>
      simp [schemaSelected, matchEnvironment, matchValues, environment, Helper.names, applySubst, Subst.lookup]

private theorem lambda_body_returns (caller : Subst) (state : State) (rule : RewriteRule)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (body target : Pattern) (results : List ScopedRuleMatching.Assignment)
    (capturedRule : applySubst caller (v "rule") = ruleValue rule)
    (capturedAmbient : applySubst caller (v "ambient") = number ambient)
    (capturedSite : applySubst caller (v "site") = siteValue site)
    (capturedPath : applySubst caller (v "path") = pathValue path)
    (capturedAssignment : applySubst caller (v "assignment") = assignmentValue assignment)
    (capturedBody : applySubst caller (v "body") = patternValue body)
    (capturedTarget : applySubst caller (v "actual-body") = patternValue target)
    (fresh : Subst.lookup caller "nested" = none)
    (computed : PureReturns program [] state (a Helper.match.head
      (matchValues rule ambient site (path ++ [0]) assignment body target)) state (resultsValue results)) :
    PureReturns program caller state lambdaBody state (resultsValue results) := by
  let nested := ("nested", pathValue (path ++ [0])) :: caller
  apply named_let_returns caller state "nested" _ _ _ _ fresh
  · apply append_path_returns caller state path 0 (v "path") (a "LCons" [number 0, .symbol "LNil"])
      (by decide) (by decide)
    have singletonCaptured : applySubst caller (a "LCons" [number 0, .symbol "LNil"]) = pathValue [0] := by
      simp [pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        applySubst, applySubst.applySubstList]
    simp only [List.map_cons, List.map_nil, capturedPath, singletonCaptured]
  · apply helper_capture .match nested state
      [v "rule", v "ambient", v "site", v "nested", v "assignment", v "body", v "actual-body"]
      (matchValues rule ambient site (path ++ [0]) assignment body target) _ rfl _ computed
    simp [nested, matchValues, capturedRule, capturedAmbient, capturedSite, capturedAssignment,
      capturedBody, capturedTarget]

/-- The actual ordered scoped source implements the original matcher. The
structural address hypothesis is earned at an authored site; no typing or
context permission is inferred from a successful capture. -/
theorem match_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (attached : rule.bindings = some spec) (supported : OrderedPattern schema)
    (coherent : DepthCoherent rule site path depth schema) :
    PureReturns program [] state (a Helper.match.head
      (matchValues rule ambient site path assignment schema target)) state
      (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth assignment schema target)) := by
  induction supported generalizing path depth assignment target with
  | fvar name => exact fvar_returns state rule spec ambient site path depth assignment name target attached coherent
  | bvar index => exact bvar_returns state rule spec ambient site path depth assignment index target
  | apply label patterns children ih =>
      let selected := schemaSelected (matchEnvironment rule ambient site path assignment (.apply label patterns) target)
        (.apply label patterns)
      apply helper_call .match [] state _ _ _ rfl (captured_closed _)
      apply schema_case_returns state rule ambient site path assignment (.apply label patterns) target
      apply target_case_returns selected state .application target _ (by simp)
        (selected_target_fresh rule ambient site path assignment (.apply label patterns) target)
        (selected_target_captured rule ambient site path assignment (.apply label patterns) target)
      cases target with
      | apply actual targets =>
          let caller := targetSelected selected .application (.apply actual targets)
          have tested := CettaWireAtom.equality_captured_returns program caller state (.string label) (.string actual)
            "label" "actual"
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, targetSelected, applySubst, Subst.lookup])
          simp only [Term.string.injEq] at tested
          apply bool_if_returns caller state _ _ _ _ _ tested
          by_cases same : label = actual
          · subst actual
            simp only [decide_true, ↓reduceIte]
            have computed := arguments_returns_from_elements state rule spec ambient site path depth patterns
              (fun child member childPath childDepth found childTarget addressed =>
                ih child member childPath childDepth found childTarget addressed)
              assignment 0 targets coherent.constructorArguments
            have captured := helper_capture .arguments caller state
              [v "rule", v "ambient", v "site", v "path", v "assignment", number 0, v "patterns", v "targets"]
              (argumentValues rule ambient site path assignment 0 patterns targets) _ rfl (by
                simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                  argumentValues, environment, Helper.names, applySubst, Subst.lookup]) computed
            simpa only [ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
              ScopedRuleMatching.matchArgsAt, beq_self_eq_true, ↓reduceIte] using captured
          · have unequal : (label == actual) = false := by simpa using same
            simpa only [same, decide_false, ↓reduceIte, targetCode, ScopedRuleMatching.matchAt,
              ScopedRuleMatching.matchAtWith, unequal, Bool.false_eq_true, resultsValue, assignmentsTerm, encodeList,
              CettaWireAtom.encode] using symbol_returns program caller state "LNil"
      | _ =>
          simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"
  | lambda display body child ih =>
      let selected := schemaSelected (matchEnvironment rule ambient site path assignment (.lambda display body) target)
        (.lambda display body)
      apply helper_call .match [] state _ _ _ rfl (captured_closed _)
      apply schema_case_returns state rule ambient site path assignment (.lambda display body) target
      apply target_case_returns selected state .lambda target _ (by simp)
        (selected_target_fresh rule ambient site path assignment (.lambda display body) target)
        (selected_target_captured rule ambient site path assignment (.lambda display body) target)
      cases target with
      | lambda actual actualBody =>
          let caller := targetSelected selected .lambda (.lambda actual actualBody)
          have computed := ih (path ++ [0]) (depth + 1) assignment actualBody coherent.lambda
          have captured := lambda_body_returns caller state rule ambient site path assignment body actualBody _
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, targetSelected, applySubst, Subst.lookup])
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, Subst.lookup]) computed
          simpa only [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith] using captured
      | _ =>
          simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"
  | multiLambda arity display body child ih =>
      let selected := schemaSelected
        (matchEnvironment rule ambient site path assignment (.multiLambda arity display body) target)
        (.multiLambda arity display body)
      apply helper_call .match [] state _ _ _ rfl (captured_closed _)
      apply schema_case_returns state rule ambient site path assignment (.multiLambda arity display body) target
      apply target_case_returns selected state .multiLambda target _ (by simp)
        (selected_target_fresh rule ambient site path assignment (.multiLambda arity display body) target)
        (selected_target_captured rule ambient site path assignment (.multiLambda arity display body) target)
      cases target with
      | multiLambda actual actualDisplay actualBody =>
          let caller := targetSelected selected .multiLambda (.multiLambda actual actualDisplay actualBody)
          have tested := CettaWireAtom.equality_captured_returns program caller state (.natural arity) (.natural actual)
            "arity" "actual-arity"
            (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, applySubst, Subst.lookup])
            (by simp [caller, targetSelected, applySubst, Subst.lookup])
          simp only [Term.natural.injEq] at tested
          apply bool_if_returns caller state _ _ _ _ _ tested
          by_cases same : arity = actual
          · subst actual
            simp only [decide_true, ↓reduceIte]
            have computed := ih (path ++ [0]) (depth + arity) assignment actualBody coherent.multiLambda
            have captured := lambda_body_returns caller state rule ambient site path assignment body actualBody _
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, applySubst, Subst.lookup])
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, applySubst, Subst.lookup])
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, applySubst, Subst.lookup])
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, applySubst, Subst.lookup])
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, applySubst, Subst.lookup])
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, applySubst, Subst.lookup])
              (by simp [caller, targetSelected, applySubst, Subst.lookup])
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, Subst.lookup]) computed
            simpa only [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
              beq_self_eq_true, ↓reduceIte] using captured
          · have unequal : (arity == actual) = false := by simpa using same
            simpa only [same, decide_false, ↓reduceIte, targetCode, ScopedRuleMatching.matchAt,
              ScopedRuleMatching.matchAtWith, unequal, Bool.false_eq_true, resultsValue, assignmentsTerm, encodeList,
              CettaWireAtom.encode] using symbol_returns program caller state "LNil"
      | _ =>
          simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"
  | subst body replacement bodySupported replacementSupported bodyIH replacementIH =>
      let selected := schemaSelected
        (matchEnvironment rule ambient site path assignment (.subst body replacement) target) (.subst body replacement)
      apply helper_call .match [] state _ _ _ rfl (captured_closed _)
      apply schema_case_returns state rule ambient site path assignment (.subst body replacement) target
      apply target_case_returns selected state .substitution target _ (by simp)
        (selected_target_fresh rule ambient site path assignment (.subst body replacement) target)
        (selected_target_captured rule ambient site path assignment (.subst body replacement) target)
      cases target with
      | subst actualBody actualReplacement =>
          let caller := targetSelected selected .substitution (.subst actualBody actualReplacement)
          let nested := ("nested", pathValue (path ++ [0])) :: caller
          let heads := ScopedRuleMatching.matchAt rule spec ambient site (path ++ [0]) (depth + 1)
            assignment body actualBody
          let headBound := ("heads", resultsValue heads) :: nested
          let outputs := fun found => ScopedRuleMatching.matchArgsAt rule spec ambient site path depth
            found 1 [replacement] [actualReplacement]
          have pathReturned := append_path_returns caller state path 0 (v "path")
              (a "LCons" [number 0, .symbol "LNil"])
              (by decide) (by decide) (by
                simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                  environment, Helper.names, pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  applySubst, applySubst.applySubstList, Subst.lookup])
          have headReturned := helper_capture .match nested state
              [v "rule", v "ambient", v "site", v "nested", v "assignment", v "body", v "actual-body"]
              (matchValues rule ambient site (path ++ [0]) assignment body actualBody) _ rfl (by
                simp [nested, caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                  environment, Helper.names, applySubst, Subst.lookup])
              (bodyIH (path ++ [0]) (depth + 1) assignment actualBody coherent.substitutionBody)
          have addressed : ArgumentsDepthCoherent rule site path depth 1 [replacement] := by
            intro offset pattern found
            cases offset with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst pattern
                simpa only [Nat.add_zero] using coherent.substitutionReplacement
            | succ offset => simp at found
          have continued := results_returns .arguments state rule ambient site path heads 1
              [replacement] none [actualReplacement] outputs (fun found _ =>
                arguments_returns_from_elements state rule spec ambient site path depth [replacement]
                  (by
                    intro child member childPath childDepth inner target addressed
                    simp only [List.mem_singleton] at member
                    subst child
                    exact replacementIH childPath childDepth inner target addressed)
                  found 1 [actualReplacement] addressed)
          have tailReturned := helper_capture .argumentResults headBound state
              [v "rule", v "ambient", v "site", v "path", v "heads", number 1,
                a "LCons" [v "replacement", .symbol "LNil"], a "LCons" [v "actual-replacement", .symbol "LNil"]]
              (ResultKind.values .arguments rule ambient site path heads 1 [replacement] none [actualReplacement])
              _ rfl (by
                simp [headBound, nested, caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                  environment, Helper.names, ResultKind.values, ResultKind.extraValues,
                  InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  applySubst, applySubst.applySubstList, Subst.lookup]) continued
          have canonical : ScopedRuleMatching.matchAt rule spec ambient site path depth assignment
              (.subst body replacement) (.subst actualBody actualReplacement) = heads.flatMap outputs := by
            simp [ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith, heads, outputs,
              ScopedRuleMatching.matchArgsAt, ScopedRuleMatching.matchArgsAtWith]
          rw [canonical]
          change PureReturns program caller state substitutionBody state (resultsValue (heads.flatMap outputs))
          apply named_let_returns caller state "nested" _ _ _ _
              (by simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                environment, Helper.names, Subst.lookup]) pathReturned
          exact named_let_returns nested state "heads" _ _ _ _
            (by simp [nested, caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
              environment, Helper.names, Subst.lookup]) headReturned tailReturned
      | _ =>
          simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"
  | vector patterns rest children ih =>
      let selected := schemaSelected
        (matchEnvironment rule ambient site path assignment (.collection .vec patterns rest) target)
        (.collection .vec patterns rest)
      apply helper_call .match [] state _ _ _ rfl (captured_closed _)
      apply schema_case_returns state rule ambient site path assignment (.collection .vec patterns rest) target
      apply target_case_returns selected state .vector target _ (by simp)
        (selected_target_fresh rule ambient site path assignment (.collection .vec patterns rest) target)
        (selected_target_captured rule ambient site path assignment (.collection .vec patterns rest) target)
      cases target with
      | collection kind targets actualRest =>
          cases kind with
          | vec =>
              cases actualRest with
              | none =>
                  let caller := targetSelected selected .vector (.collection .vec targets none)
                  have computed := vector_returns_from_elements state rule spec ambient site path depth patterns
                    (fun child member childPath childDepth found childTarget addressed =>
                      ih child member childPath childDepth found childTarget addressed)
                    assignment 0 rest targets attached coherent.collectionArguments (by
                      intro name same
                      subst rest
                      simpa only [Nat.zero_add] using coherent.collectionRest)
                  have captured := helper_capture .vector caller state
                    [v "rule", v "ambient", v "site", v "path", v "assignment", number 0, v "patterns", v "rest", v "targets"]
                    (vectorValues rule ambient site path assignment 0 patterns rest targets) _ rfl (by
                      simp [caller, selected, targetSelected, schemaSelected, matchEnvironment, matchValues,
                        vectorValues, environment, Helper.names, applySubst, Subst.lookup]) computed
                  cases rest <;> simpa [targetCode, vectorBody, caller, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
                    vectorExpected, ScopedRuleMatching.matchArgsAt] using captured
              | some name =>
                  cases rest <;> simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
                    resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
                    symbol_returns program _ state "LNil"
          | _ =>
              cases rest <;> cases actualRest <;> simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
                resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
                symbol_returns program _ state "LNil"
      | _ =>
          simpa [targetCode, ScopedRuleMatching.matchAt, ScopedRuleMatching.matchAtWith,
            resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program _ state "LNil"

def matchArguments (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern) : List Term :=
  [InferenceCettaWire.AuthoredRule.rewriteTerm rule, .natural ambient,
    InferenceCettaWire.AuthoredRule.siteTerm site, encodeList Term.natural path,
    RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment,
    InferenceCettaWire.encodePattern schema, InferenceCettaWire.encodePattern target]

def matchTerm (rule : RewriteRule) (ambient : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern) : Term :=
  .application "gslt:rule:scope-match" (matchArguments rule ambient site path assignment schema target)

theorem match_term_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (attached : rule.bindings = some spec) (supported : OrderedPattern schema)
    (coherent : DepthCoherent rule site path depth schema) :
    PureReturns program [] state (encoded (matchTerm rule ambient site path assignment schema target)) state
      (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth assignment schema target)) := by
  simpa only [matchTerm, matchArguments, matchValues, Helper.head, a, number, ruleValue, siteValue, pathValue, assignmentValue,
    patternValue, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    match_returns state rule spec ambient site path depth assignment schema target attached supported coherent

/-- Both the endpoint and its initial local binder depth are read from the
original authored rule site before executing the same native matcher. -/
theorem site_match_returns (state : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (attached : rule.bindings = some spec) (supported : OrderedPattern schema)
    (patternFound : RuleBinding.sitePattern? rule site = some schema)
    (depthFound : RuleBinding.siteBinderDepth? rule site = some depth) :
    PureReturns program [] state (encoded (matchTerm rule ambient site [] assignment schema target)) state
      (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site [] depth assignment schema target)) :=
  match_term_returns state rule spec ambient site [] depth assignment schema target attached supported
    (depthCoherent_of_site rule site schema depth patternFound depthFound)

theorem match_completed_iff (state after : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (attached : rule.bindings = some spec) (supported : OrderedPattern schema)
    (coherent : DepthCoherent rule site path depth schema) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (matchTerm rule ambient site path assignment schema target)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth
        assignment schema target)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (match_term_returns state rule spec ambient site path depth assignment schema target attached supported coherent)
    after answers input output

theorem match_derivation_iff (state after : State) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (attached : rule.bindings = some spec) (supported : OrderedPattern schema)
    (coherent : DepthCoherent rule site path depth schema) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (matchTerm rule ambient site path assignment schema target)) }
        (.complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth
        assignment schema target)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (match_term_returns state rule spec ambient site path depth assignment schema target attached supported coherent)
    after answers input output

theorem assignmentsTerm_injective : Function.Injective assignmentsTerm :=
  CettaWire.encodeList_injective RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
    RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective

private theorem matchValue_expression_symbol (caller : Subst) (patterns : List Atom) (name : String) :
    SpaceSemantics.matchValue caller (.expression patterns) (.symbol name) = none := by
  unfold SpaceSemantics.matchValue
  split <;> simp_all

private def ruleCases : SpaceSemantics.Cases :=
  [(a "ScopedRewriteRuleV1" [v "name", v "types", v "premises", v "left", v "right", a "RuleBindingSome" [v "spec"]],
    a Helper.match.head [v "rule", v "ambient", .symbol "RuleLeft", .symbol "LNil", .symbol "LNil", v "left", v "target"]),
   (v "other", .symbol "LNil")]

private theorem rule_shape : (equation .rule).body =
    a "case" [v "rule", .expression (ruleCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

def ruleTerm (rule : RewriteRule) (ambient : Nat) (target : Pattern) : Term :=
  .application "gslt:rule:scope-match-rule"
    [InferenceCettaWire.AuthoredRule.rewriteTerm rule, .natural ambient, InferenceCettaWire.encodePattern target]

/-- Matching is an operation over an attached specification. This primitive
does not replace the whole authored rule's admission and source typing checks. -/
def ruleResults (rule : RewriteRule) (ambient : Nat) (target : Pattern) : List ScopedRuleMatching.Assignment :=
  match rule.bindings with
  | none => []
  | some spec => ScopedRuleMatching.matchRuleAt rule spec ambient target

theorem rule_returns (state : State) (rule : RewriteRule) (ambient : Nat) (target : Pattern)
    (supported : OrderedPattern rule.left) :
    PureReturns program [] state (encoded (ruleTerm rule ambient target)) state (resultsValue (ruleResults rule ambient target)) := by
  let values := [ruleValue rule, number ambient, patternValue target]
  let caller := environment .rule values
  change PureReturns program [] state (a Helper.rule.head values) state _
  apply helper_call .rule [] state _ values _ rfl (captured_closed _)
  rw [rule_shape]
  have computed : PureReturns program caller state (v "rule") state (ruleValue rule) := by
    simpa [caller, values, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "rule"
  cases attached : rule.bindings with
  | none =>
      let selected := ("other", ruleValue rule) :: caller
      apply case_returns program caller selected state state state (v "rule") (ruleValue rule) (.symbol "LNil")
        _ _ ruleCases (read_cases_encoded _) computed _ _
      · simp [ruleCases, ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
          InferenceCettaWire.AuthoredRule.optionalBindingTerm, attached,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, matchValue_application, matchValue_expression_symbol, matchValue_variable, matchValue_symbol,
          SpaceSemantics.matchValue.matchValues, matchAtom, caller, values, environment, Helper.names,
          selected, Subst.lookup]
      · simpa only [ruleResults, attached, resultsValue, assignmentsTerm, encodeList, CettaWireAtom.encode] using
          symbol_returns program selected state "LNil"
  | some spec =>
      let selected := ("spec", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)) ::
        ("right", patternValue rule.right) :: ("left", patternValue rule.left) ::
        ("premises", encoded (encodeList InferenceCettaWire.AuthoredRule.premiseTerm rule.premises)) ::
        ("types", encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm rule.typeContext)) ::
        ("name", encoded (.string rule.name)) :: caller
      apply case_returns program caller selected state state state (v "rule") (ruleValue rule)
        (a Helper.match.head [v "rule", v "ambient", .symbol "RuleLeft", .symbol "LNil", .symbol "LNil", v "left", v "target"])
        _ _ ruleCases (read_cases_encoded _) computed _ _
      · simp [ruleCases, ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
          InferenceCettaWire.AuthoredRule.optionalBindingTerm, attached, InferenceCettaWire.encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, matchValue_application, matchValue_variable, matchValue_symbol,
          SpaceSemantics.matchValue.matchValues, matchAtom, caller, values, environment, Helper.names,
          selected, Subst.lookup]
      · have returned := helper_capture .match selected state
          [v "rule", v "ambient", .symbol "RuleLeft", .symbol "LNil", .symbol "LNil", v "left", v "target"]
          (matchValues rule ambient .left [] [] rule.left target) _ rfl (by
            simp [selected, caller, values, environment, Helper.names, matchValues,
              siteValue, assignmentValue, InferenceCettaWire.AuthoredRule.siteTerm, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
              pathValue, MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup])
          (match_returns state rule spec ambient .left [] 0 [] rule.left target attached supported (depthCoherent_left rule))
        simpa only [ruleResults, attached, ScopedRuleMatching.matchRuleAt, ScopedRuleMatching.matchRuleWithAt,
          ScopedRuleMatching.matchAt] using returned

theorem rule_completed_iff (state after : State) (rule : RewriteRule) (ambient : Nat) (target : Pattern)
    (supported : OrderedPattern rule.left) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (ruleTerm rule ambient target)) } =
      .complete after answers input output) ↔
    after = state ∧ answers = [resultsValue (ruleResults rule ambient target)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (rule_returns state rule ambient target supported)
    after answers input output

theorem rule_derivation_iff (state after : State) (rule : RewriteRule) (ambient : Nat) (target : Pattern)
    (supported : OrderedPattern rule.left) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (ruleTerm rule ambient target)) }
      (.complete after answers input output) ↔
    after = state ∧ answers = [resultsValue (ruleResults rule ambient target)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (rule_returns state rule ambient target supported)
    after answers input output

theorem match_captured_returns (caller : Subst) (state : State) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (attached : rule.bindings = some spec) (supported : OrderedPattern schema)
    (coherent : DepthCoherent rule site path depth schema) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      (matchArguments rule ambient site path assignment schema target).map CettaWireAtom.encode) :
    PureReturns program caller state (.expression (.symbol "gslt:rule:scope-match" :: arguments)) state
      (resultsValue (ScopedRuleMatching.matchAt rule spec ambient site path depth assignment schema target)) := by
  exact helper_capture .match caller state arguments (matchValues rule ambient site path assignment schema target) _ rfl
    (by simpa only [matchArguments, matchValues, List.map_cons, List.map_nil] using captured)
    (match_returns state rule spec ambient site path depth assignment schema target attached supported coherent)

theorem rule_captured_returns (caller : Subst) (state : State) (rule : RewriteRule) (ambient : Nat)
    (target : Pattern) (supported : OrderedPattern rule.left) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [ruleValue rule, number ambient, patternValue target]) :
    PureReturns program caller state (a Helper.rule.head arguments) state (resultsValue (ruleResults rule ambient target)) := by
  apply helper_capture .rule caller state arguments [ruleValue rule, number ambient, patternValue target] _ rfl captured
  simpa only [ruleTerm, Helper.head, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    rule_returns state rule ambient target supported

namespace CompiledProfile

open Mettapedia.GSLT.LanguageDef.BindingSyntax
open ScopedElaboration SchemaElaboration
open Mettapedia.GSLT.LanguageDef.WellSorted


theorem authored_left_returns (state : State) (language : LanguageDef)
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (found : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (ambient : Nat) (target : Pattern) :
    PureReturns program [] state
      (encoded (ruleTerm (language.rewrites.get ruleIndex) ambient target)) state
      (resultsValue (ScopedRuleMatching.matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient target)) := by
  have supported := elaborateAuthoredSchema?_ordered language left found
  have source : left.source = (language.rewrites.get ruleIndex).left := (Option.some.inj left.atSite).symm
  rw [source] at supported
  simpa only [ruleResults, left.attached] using rule_returns state _ ambient target supported

theorem authored_left_completed_iff (state after : State) (language : LanguageDef)
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (found : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (ambient : Nat) (target : Pattern) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (ruleTerm (language.rewrites.get ruleIndex) ambient target)) } = .complete after answers input output) ↔
    after = state ∧ answers = [resultsValue (ScopedRuleMatching.matchRuleAt
      (language.rewrites.get ruleIndex) left.spec ambient target)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (authored_left_returns state language left found ambient target) after answers input output

open AmbientCorrespondence TargetReification

/-- Actual native completion reflects to the already proved canonical typed
instance theorem. The same physical rule and original contextual captures are
retained; matching does not establish context permission or premise discharge. -/
theorem authored_left_canonical_iff (state : State) (language : LanguageDef)
    {ruleIndex : Fin language.rewrites.length} {sort : TypeExpr} {ambient : List TypeExpr}
    (left : AuthoredSchema language ruleIndex .left sort)
    (found : elaborateAuthoredSchema? language ruleIndex .left sort = some left)
    (bodies : AmbientBodies language (language.rewrites.get ruleIndex) left.spec ambient)
    (target : Mettapedia.OSLF.Binding.Term (signatureOf language) ambient sort)
    (instanceCanonical : CanonicalObject (scopedInstantiation bodies left.compiled.term))
    (targetCanonical : CanonicalObject target) :
    (∃ fuel results, run program fuel { state := state, control := .evaluate [] (encoded (ruleTerm (language.rewrites.get ruleIndex) ambient.length (erase target))) } =
      .complete state [encoded (assignmentsTerm results)] [] [] ∧
      ∃ raw ∈ results, ContextualCapturesInputs left.compiled.inputOccurrences raw bodies) ↔
    scopedInstantiation bodies left.compiled.term = target := by
  rw [← AmbientMatching.authored_left_match_canonical_iff left found bodies target instanceCanonical targetCanonical]
  constructor
  · rintro ⟨fuel, results, completed, raw, member, captured⟩
    have observed := (authored_left_completed_iff state state language left found ambient.length (erase target) _ [] []).mp ⟨fuel, completed⟩
    have encodedSame : encoded (assignmentsTerm results) = resultsValue
        (ScopedRuleMatching.matchRuleAt (language.rewrites.get ruleIndex) left.spec ambient.length (erase target)) :=
      (List.cons.inj observed.2.1).1
    have same := assignmentsTerm_injective (CettaWireAtom.encode_injective _ _ encodedSame)
    exact ⟨raw, same ▸ member, captured⟩
  · rintro ⟨raw, member, captured⟩
    obtain ⟨fuel, completed⟩ := (authored_left_completed_iff state state language left found ambient.length
      (erase target) _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨fuel, _, completed, raw, member, captured⟩

end CompiledProfile

namespace Controls

structure Fixture where
  name : String
  rule : RewriteRule
  ambient : Nat
  target : Pattern
  supported : OrderedPattern rule.left

def Fixture.queryTerm (fixture : Fixture) : Term := ruleTerm fixture.rule fixture.ambient fixture.target
def Fixture.expectedTerm (fixture : Fixture) : Term := assignmentsTerm (ruleResults fixture.rule fixture.ambient fixture.target)

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (encoded fixture.queryTerm) state (encoded fixture.expectedTerm) :=
  rule_returns state fixture.rule fixture.ambient fixture.target fixture.supported

private def atom (name : String) : Pattern := .apply name []
private theorem atom_ordered (name : String) : OrderedPattern (atom name) :=
  .apply name [] (by intro pattern member; cases member)
private def nameSort : TypeExpr := .base "Name"
private def emptySpec : RuleBindingSpec := ⟨[], []⟩

private def fixture (name : String) (left : Pattern) (supported : OrderedPattern left) (target : Pattern)
    (spec : Option RuleBindingSpec := some emptySpec) (ambient : Nat := 0) : Fixture :=
  ⟨name, {
      name := "scoped-match-control"
      typeContext := []
      premises := []
      left := left
      right := atom "done"
      bindings := spec }, ambient, target, supported⟩

private def captureSpec (arguments : List Pattern) (dependencies : List TypeExpr := [nameSort]) : RuleBindingSpec :=
  ⟨[("body", dependencies)], [⟨"body", .left, [0], arguments⟩]⟩
private def lambdaSource : Pattern := .lambda none (.fvar "body")
private theorem lambda_ordered : OrderedPattern lambdaSource := .lambda none (.fvar "body") (.fvar "body")
private def multiSource : Pattern := .multiLambda 2 ["x", "y"] (.fvar "body")
private theorem multi_ordered : OrderedPattern multiSource := .multiLambda 2 ["x", "y"] (.fvar "body") (.fvar "body")
private def repeatedSource : Pattern := .apply "pair" [multiSource, multiSource]
private theorem repeated_ordered : OrderedPattern repeatedSource := .apply "pair" _ (by
  intro pattern member
  have same : pattern = multiSource := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  rw [same]
  exact multi_ordered)
private def repeatedSpec : RuleBindingSpec :=
  ⟨[("body", [nameSort])], [⟨"body", .left, [0, 0], [.bvar 0]⟩, ⟨"body", .left, [1, 0], [.bvar 1]⟩]⟩
private def box (index : Nat) : Pattern := .apply "box" [.bvar index]
private def repeatedTarget (first second : Pattern) : Pattern :=
  .apply "pair" [.multiLambda 2 [] first, .multiLambda 2 [] second]
private def vectorSource (rest : Option String) : Pattern := .collection .vec [atom "fixed"] rest
private theorem vector_ordered (rest : Option String) : OrderedPattern (vectorSource rest) :=
  .vector [atom "fixed"] rest (by
    intro pattern member
    have same : pattern = atom "fixed" := by simpa only [List.mem_singleton] using member
    rw [same]
    exact atom_ordered "fixed")
private def restSpec : RuleBindingSpec := ⟨[("tail", [])], []⟩
private def substitutionSource : Pattern := .subst (.fvar "body") (.fvar "replacement")
private theorem substitution_ordered : OrderedPattern substitutionSource :=
  .subst (.fvar "body") (.fvar "replacement") (.fvar "body") (.fvar "replacement")
private def substitutionSpec : RuleBindingSpec :=
  ⟨[("body", [nameSort]), ("replacement", [])], [⟨"body", .left, [0], [.bvar 0]⟩]⟩

def fixtures : List Fixture :=
  [fixture "constructor-identity" (atom "a") (atom_ordered "a") (atom "a"),
   fixture "refuse-wrong-constructor" (atom "a") (atom_ordered "a") (atom "b"),
   fixture "refuse-extra-constructor-argument" (atom "a") (atom_ordered "a") (.apply "a" [atom "b"]),
   fixture "bound-index-identity" (.bvar 3) (.bvar 3) (.bvar 3),
   fixture "refuse-wrong-bound-index" (.bvar 3) (.bvar 3) (.bvar 2),
   fixture "refuse-unattached-rule" (atom "a") (atom_ordered "a") (atom "a") none,
   fixture "zero-dependency-capture-literal" (.fvar "value") (.fvar "value") (atom "a") (some ⟨[("value", [])], []⟩),
   fixture "zero-dependency-capture-opaque-free-variable" (.fvar "value") (.fvar "value") (.fvar "inner") (some ⟨[("value", [])], []⟩),
   fixture "refuse-undeclared-free-variable" (.fvar "value") (.fvar "value") (atom "a"),
   fixture "lambda-capture-local" lambdaSource lambda_ordered (.lambda none (box 0)) (some (captureSpec [.bvar 0])),
   fixture "lambda-display-does-not-change-capture" lambdaSource lambda_ordered (.lambda (some "other") (box 0)) (some (captureSpec [.bvar 0])),
   fixture "refuse-lambda-target-shape" lambdaSource lambda_ordered (box 0) (some (captureSpec [.bvar 0])),
   fixture "refuse-unselected-lambda-local" lambdaSource lambda_ordered (.lambda none (box 0)) (some (captureSpec [] [])),
   fixture "lambda-retains-admitted-ambient" lambdaSource lambda_ordered (.lambda none (.bvar 1)) (some (captureSpec [.bvar 0])) 1,
   fixture "refuse-lambda-outside-ambient" lambdaSource lambda_ordered (.lambda none (.bvar 2)) (some (captureSpec [.bvar 0])) 1,
   fixture "multi-lambda-spine-one" multiSource multi_ordered (.multiLambda 2 [] (box 1)) (some (captureSpec [.bvar 1])),
   fixture "multi-lambda-spine-zero" multiSource multi_ordered (.multiLambda 2 [] (box 0)) (some (captureSpec [.bvar 0])),
   fixture "refuse-multi-lambda-arity" multiSource multi_ordered (.multiLambda 1 [] (box 0)) (some (captureSpec [.bvar 0])),
   fixture "refuse-unselected-multi-lambda-local" multiSource multi_ordered (.multiLambda 2 [] (box 0)) (some (captureSpec [.bvar 1])),
   fixture "refuse-duplicate-local-spine" multiSource multi_ordered (.multiLambda 2 [] (box 0)) (some (captureSpec [.bvar 0, .bvar 0] [nameSort, nameSort])),
   fixture "refuse-non-variable-spine" multiSource multi_ordered (.multiLambda 2 [] (box 0)) (some (captureSpec [atom "bad"])),
   fixture "refuse-outside-local-spine" multiSource multi_ordered (.multiLambda 2 [] (box 0)) (some (captureSpec [.bvar 2])),
   fixture "refuse-wrong-metadata-site" multiSource multi_ordered (.multiLambda 2 [] (box 0))
     (some ⟨[("body", [nameSort])], [⟨"body", .right, [0], [.bvar 0]⟩]⟩),
   fixture "refuse-wrong-metadata-name" multiSource multi_ordered (.multiLambda 2 [] (box 0))
     (some ⟨[("body", [nameSort])], [⟨"other", .left, [0], [.bvar 0]⟩]⟩),
   fixture "refuse-duplicate-dependency-declaration" multiSource multi_ordered (.multiLambda 2 [] (box 0))
     (some ⟨[("body", [nameSort]), ("body", [nameSort])], (captureSpec [.bvar 0]).occurrences⟩),
   fixture "refuse-duplicate-occurrence-declaration" multiSource multi_ordered (.multiLambda 2 [] (box 0))
     (some ⟨[("body", [nameSort])], [⟨"body", .left, [0], [.bvar 0]⟩, ⟨"body", .left, [0], [.bvar 0]⟩]⟩),
   fixture "different-spines-recover-the-same-body" repeatedSource repeated_ordered (repeatedTarget (box 0) (box 1)) (some repeatedSpec),
   fixture "refuse-repeated-recovered-body-conflict" repeatedSource repeated_ordered (repeatedTarget (box 0) (.apply "other" [.bvar 1])) (some repeatedSpec),
   fixture "vector-exact-prefix" (vectorSource none) (vector_ordered none) (.collection .vec [atom "fixed"] none),
   fixture "refuse-vector-extra-element-without-rest" (vectorSource none) (vector_ordered none) (.collection .vec [atom "fixed", atom "extra"] none),
   fixture "vector-rest-retains-order-and-duplicates" (vectorSource (some "tail")) (vector_ordered (some "tail"))
     (.collection .vec [atom "fixed", atom "a", atom "a", atom "b"] none) (some restSpec),
   fixture "vector-empty-rest" (vectorSource (some "tail")) (vector_ordered (some "tail")) (.collection .vec [atom "fixed"] none) (some restSpec),
   fixture "refuse-vector-short-prefix" (vectorSource (some "tail")) (vector_ordered (some "tail")) (.collection .vec [] none) (some restSpec),
   fixture "refuse-vector-wrong-tag" (vectorSource (some "tail")) (vector_ordered (some "tail")) (.collection .hashBag [atom "fixed"] none) (some restSpec),
   fixture "refuse-vector-target-rest" (vectorSource (some "tail")) (vector_ordered (some "tail")) (.collection .vec [atom "fixed"] (some "unknown")) (some restSpec),
   fixture "substitution-captures-separate-depths" substitutionSource substitution_ordered (.subst (box 0) (atom "value")) (some substitutionSpec),
   fixture "refuse-substitution-unselected-local" substitutionSource substitution_ordered (.subst (.bvar 1) (atom "value")) (some substitutionSpec),
   fixture "refuse-substitution-target-shape" substitutionSource substitution_ordered (.lambda none (box 0)) (some substitutionSpec)]

namespace AuthoredControls

open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.Controls.RawInstantiationControls
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.Controls.AmbientControls
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.Controls.RecursiveControls
open SchemaElaboration

private theorem compiled_left_found : elaborateAuthoredSchema? outputLanguage outputIndex .left (.base "T") = some outputLeft := by
  exact Option.eq_some_of_isSome second_physical_position_both_sides_admitted.1

private theorem source_supported : OrderedPattern outputRule.left := by
  have supported := Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.elaborateAuthoredSchema?_ordered outputLanguage outputLeft compiled_left_found
  have same : outputLeft.source = outputRule.left := (Option.some.inj outputLeft.atSite).symm
  exact same ▸ supported

def closedFixture : Fixture := ⟨"typed-authored-second-row-closed-capture", outputRule, 0, sourceTarget, source_supported⟩
def openFixture : Fixture := ⟨"typed-authored-open-ambient-capture", outputRule, 1, openSourceTarget, source_supported⟩

private def malformedSpec : RuleBindingSpec := { outputSpec with
  dependencies := outputSpec.dependencies ++ [("unused", []), ("unused", [])] }
private def malformedRule : RewriteRule := { outputRule with bindings := some malformedSpec }
private def malformedLanguage : LanguageDef := { outputLanguage with rewrites := [malformedRule] }

theorem unused_malformed_metadata_refused : RuleBinding.admittedFor malformedRule malformedSpec = false := by decide +kernel

theorem authored_unused_malformed_metadata_refused :
    elaborateAuthoredSchema? malformedLanguage ⟨0, by decide⟩ .left (.base "T") = none := by decide +kernel

/-- Raw ordered-rest matching is available, but the current authored typed
compiler's admitted profile still refuses a schema rest. -/
theorem typed_rest_not_admitted :
    (compileSchemaWithFuel? outputLanguage outputRule outputSpec .left 4 [] []
      (.collection .vec [] (some "P")) (.collection .vec (.base "T"))) = none := by decide +kernel

end AuthoredControls

def authoredFixtures : List Fixture := [AuthoredControls.closedFixture, AuthoredControls.openFixture]

/-- Wrong observations are checked against the same independently computed
canonical assignment list used by the positive and refusal corpus. -/
def incorrectResults : List (Fixture × Term) :=
  [(fixture "refuse-lambda-success-as-empty" lambdaSource lambda_ordered (.lambda none (box 0)) (some (captureSpec [.bvar 0])), .symbol "LNil"),
   (fixture "refuse-repeated-success-as-empty" repeatedSource repeated_ordered (repeatedTarget (box 0) (box 1)) (some repeatedSpec), .symbol "LNil"),
   (fixture "refuse-vector-success-as-empty" (vectorSource (some "tail")) (vector_ordered (some "tail")) (.collection .vec [atom "fixed", atom "a", atom "a"] none) (some restSpec), .symbol "LNil"),
   (fixture "refuse-wrong-spine-as-success" multiSource multi_ordered (.multiLambda 2 [] (box 0)) (some (captureSpec [.bvar 1])),
     assignmentsTerm [[("body", ⟨[nameSort], 0, .bvar 0⟩)]]),
   (fixture "refuse-wrong-arity-as-success" multiSource multi_ordered (.multiLambda 1 [] (box 0)) (some (captureSpec [.bvar 0])),
     assignmentsTerm [[]])]

theorem incorrect_results_differ : ∀ entry ∈ incorrectResults, entry.1.expectedTerm ≠ entry.2 := by decide +kernel

theorem incorrect_results_refused (state : State) (entry : Fixture × Term) (member : entry ∈ incorrectResults) :
    ¬ ∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded entry.1.queryTerm) } =
      .complete state [encoded entry.2] [] [] := by
  intro completed
  have observed := (rule_completed_iff state state entry.1.rule entry.1.ambient entry.1.target entry.1.supported
    [encoded entry.2] [] []).mp completed
  have same := (List.cons.inj observed.2.1).1
  exact incorrect_results_differ entry member (CettaWireAtom.encode_injective _ _ same.symm)

end Controls

#print axioms Controls.AuthoredControls.unused_malformed_metadata_refused
#print axioms Controls.AuthoredControls.authored_unused_malformed_metadata_refused
#print axioms Controls.AuthoredControls.typed_rest_not_admitted
#print axioms Controls.Fixture.returns
#print axioms Controls.incorrect_results_refused
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.depthCoherent_of_site
#print axioms site_match_returns
#print axioms match_captured_returns
#print axioms rule_captured_returns

#print axioms Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.elaborateAuthoredSchema?_ordered
#print axioms CompiledProfile.authored_left_returns
#print axioms CompiledProfile.authored_left_completed_iff
#print axioms CompiledProfile.authored_left_canonical_iff
#print axioms Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration.compileSchemaWithFuel?_ordered

#print axioms match_returns
#print axioms match_completed_iff
#print axioms match_derivation_iff
#print axioms rule_returns
#print axioms rule_completed_iff
#print axioms rule_derivation_iff
#print axioms arguments_returns_from_elements
#print axioms vector_returns_from_elements
#print axioms results_returns
#print axioms fvar_returns
#print axioms bvar_returns

#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.depthCoherent_left
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.depthCoherent_right
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.fvar
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.lambda
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.multiLambda
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.substitutionBody
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.substitutionReplacement
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.constructorChild
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.collectionChild
#print axioms Mettapedia.OSLF.MeTTaIL.RuleBinding.DepthCoherent.collectionRest

end ScopedMatching

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ContextObservation

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire.ContextObservation
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Eval RuleExecutionProgram

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : CettaTerm) : Atom := CettaWireAtom.encode value
private abbrev patternValue (value : Pattern) : Atom := encoded (encodePattern value)
private abbrev patternsValue (values : List Pattern) : Atom := encoded (encodePatterns values)
private abbrev listValue (values : List CettaTerm) : Atom :=
  encoded (Mettapedia.GSLT.LanguageDef.CettaWire.encodeList id values)
private abbrev contextValue (context : OneHoleContext) : Atom := encoded (contextTerm context)
private abbrev permissionValue (permissions : OperationalPermissions) : Atom := encoded (permissionsTerm permissions)

private inductive Helper where | permitted | fill
private def Helper.head : Helper → String
  | .permitted => "gslt:rule:scope-permitted"
  | .fill => "gslt:rule:scope-fill"
private def Helper.names : Helper → List String
  | .permitted => ["permissions", "context"]
  | .fill => ["context", "pattern"]
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (program.equations.filter fun row => row.head == helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst := (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause program helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel) (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals interval_cases index <;> decide +kernel

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body : Atom) {answer : Atom}
    (computed : PureReturns program caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns program selected state body state answer) :
    PureReturns program caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns program caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private inductive Constructor where | slot | cons | app | lam | multi | subst | collection
private def Constructor.head : Constructor → String
  | .slot => "TermSlot" | .cons => "LCons" | .app => "PApp" | .lam => "PLam"
  | .multi => "PMultiLam" | .subst => "PSubst" | .collection => "PCollection"

private theorem constructor_template (constructor : Constructor) (names : List String) :
    PureData.Template program (a constructor.head (names.map v)) := by
  apply PureData.Template.constructor constructor.head _
    (by cases constructor <;> decide +kernel) (by cases constructor <;> decide)
  intro argument member
  obtain ⟨name, _, same⟩ := List.mem_map.mp member
  subst argument
  exact .captured name

private theorem member_returns (caller : Subst) (state : State) (value : CettaTerm)
    (values : List CettaTerm) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded value, listValue values]) :
    PureReturns program caller state (a "gslt:automata:member" [one, two]) state
      (Effects.boolean (decide (value ∈ values))) := by
  let callee : Subst := [("second", listValue values), ("first", encoded value)]
  have returned : PureReturns program callee state
      (a "gslt:automata:member" [v "first", v "second"]) state (Effects.boolean (decide (value ∈ values))) := by
    apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] callee state state "gslt:automata:member"
      [encoded value, listValue values] [v "first", v "second"] _ (by decide +kernel) _ (by decide)
      (by simp [callee, applySubst, Subst.lookup]) (MatchAutomataSourceExecution.member_returns state value values)
    intro index bounded
    simp only [List.length_cons, List.length_nil] at bounded
    interval_cases index <;> decide +kernel
  apply PureData.raw_capture_returns program callee caller state state "gslt:automata:member"
    [v "first", v "second"] [one, two] _ (by decide +kernel) _ (by decide) _ returned
  · intro index bounded
    simp only [List.length_cons, List.length_nil] at bounded
    interval_cases index <;> decide +kernel
  · simpa [callee, applySubst, Subst.lookup] using captured.symm

private theorem length_returns (caller : Subst) (state : State) (values : List CettaTerm)
    (argument : Atom) (captured : applySubst caller argument = listValue values) :
    PureReturns program caller state (a "gslt:automata:length" [argument]) state
      (encoded (.natural values.length)) := by
  let callee : Subst := [("first", listValue values)]
  have returned : PureReturns program callee state (a "gslt:automata:length" [v "first"]) state
      (encoded (.natural values.length)) :=
    RuleExecutionProgram.automata_captured_returns (by decide +kernel) (MatchAutomataSourceExecution.length_captured_returns callee state values
      (v "first") (by simp [callee, applySubst, Subst.lookup]))
  apply PureData.raw_capture_returns program callee caller state state "gslt:automata:length"
    [v "first"] [argument] _ (by decide +kernel) _ (by decide) _ returned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    subst index
    decide +kernel
  · simp [callee, applySubst, Subst.lookup, captured]

private theorem append_returns (caller : Subst) (state : State) (left right : List CettaTerm)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [listValue left, listValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state (listValue (left ++ right)) := by
  let callee : Subst := [("second", listValue right), ("first", listValue left)]
  have returned : PureReturns program callee state (a "gslt:automata:append" [v "first", v "second"]) state
      (listValue (left ++ right)) :=
    RuleExecutionProgram.automata_captured_returns (by decide +kernel) (MatchAutomataSourceExecution.append_captured_returns callee state left right
      (v "first") (v "second") (by simp [callee, applySubst, Subst.lookup]))
  apply PureData.raw_capture_returns program callee caller state state "gslt:automata:append"
    [v "first", v "second"] [one, two] _ (by decide +kernel) _ (by decide) _ returned
  · intro index bounded
    simp only [List.length_cons, List.length_nil] at bounded
    interval_cases index <;> decide +kernel
  · simpa [callee, applySubst, Subst.lookup] using captured.symm

private def fillSimpleBody (constructor : Constructor) (names : List String) : Atom :=
  a "let" [v "filled", a Helper.fill.head [v "inner", v "pattern"], a constructor.head (names.map v)]

private def fillOrderedBody (constructor : Constructor) (names : List String) : Atom :=
  a "let" [v "filled", a Helper.fill.head [v "inner", v "pattern"],
    a "let" [v "tail", a "LCons" [v "filled", v "after"],
      a "let" [v "arguments", a "gslt:automata:append" [v "before", v "tail"],
        a constructor.head (names.map v)]]]

private def fillCases : SpaceSemantics.Cases :=
  [(.symbol "ContextHole", v "pattern"),
   (a "ContextApp" [v "head", v "before", v "inner", v "after"], fillOrderedBody .app ["head", "arguments"]),
   (a "ContextLam" [v "binder", v "inner"], fillSimpleBody .lam ["binder", "filled"]),
   (a "ContextMultiLam" [v "arity", v "binders", v "inner"], fillSimpleBody .multi ["arity", "binders", "filled"]),
   (a "ContextSubstBody" [v "inner", v "replacement"], fillSimpleBody .subst ["filled", "replacement"]),
   (a "ContextSubstReplacement" [v "body", v "inner"], fillSimpleBody .subst ["body", "filled"]),
   (a "ContextCollection" [v "kind", v "before", v "inner", v "after", v "rest"],
     fillOrderedBody .collection ["kind", "arguments", "rest"])]

private theorem fill_shape : (equation .fill).body =
    a "case" [v "context", .expression (fillCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def frameBindings : OneHoleContext → Subst
  | .hole => []
  | .apply head before inner after =>
      [("after", patternsValue after), ("inner", contextValue inner),
        ("before", patternsValue before), ("head", encoded (.string head))]
  | .lambda binder inner => [("inner", contextValue inner), ("binder", encoded (encodeBinder binder))]
  | .multiLambda arity binders inner =>
      [("inner", contextValue inner), ("binders", encoded (encodeList CettaTerm.string binders)),
        ("arity", encoded (.natural arity))]
  | .substBody inner replacement => [("replacement", patternValue replacement), ("inner", contextValue inner)]
  | .substReplacement body inner => [("inner", contextValue inner), ("body", patternValue body)]
  | .collection kind before inner after rest =>
      [("rest", encoded (encodeRest rest)), ("after", patternsValue after),
        ("inner", contextValue inner), ("before", patternsValue before), ("kind", encoded (encodeCollectionType kind))]

private def frameFillBody : OneHoleContext → Atom
  | .hole => v "pattern"
  | .apply .. => fillOrderedBody .app ["head", "arguments"]
  | .lambda .. => fillSimpleBody .lam ["binder", "filled"]
  | .multiLambda .. => fillSimpleBody .multi ["arity", "binders", "filled"]
  | .substBody .. => fillSimpleBody .subst ["filled", "replacement"]
  | .substReplacement .. => fillSimpleBody .subst ["body", "filled"]
  | .collection .. => fillOrderedBody .collection ["kind", "arguments", "rest"]

private theorem fill_frame_returns (state : State) (context : OneHoleContext) (pattern : Pattern)
    (continued : PureReturns program
      (frameBindings context ++ environment .fill [contextValue context, patternValue pattern]) state
      (frameFillBody context) state (patternValue (context.fill pattern))) :
    PureReturns program [] state (a Helper.fill.head [contextValue context, patternValue pattern]) state
      (patternValue (context.fill pattern)) := by
  let caller := environment .fill [contextValue context, patternValue pattern]
  apply helper_call .fill [] state _ [contextValue context, patternValue pattern] _ rfl (by simp)
  rw [fill_shape]
  apply branch_returns caller (frameBindings context ++ caller) state (v "context") (contextValue context)
    fillCases (frameFillBody context)
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "context"
  · cases context <;> simp [caller, frameBindings, frameFillBody, fillCases, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      contextValue, contextTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      environment, Helper.names]
  · exact continued

private theorem fill_simple_returns (caller : Subst) (state : State) (inner : OneHoleContext)
    (pattern target : Pattern) (constructor : Constructor) (names : List String)
    (fresh : Subst.lookup caller "filled" = none)
    (captured : [v "inner", v "pattern"].map (applySubst caller) = [contextValue inner, patternValue pattern])
    (output : applySubst (("filled", patternValue (inner.fill pattern)) :: caller)
      (a constructor.head (names.map v)) = patternValue target)
    (recursive : PureReturns program [] state (a Helper.fill.head [contextValue inner, patternValue pattern]) state
      (patternValue (inner.fill pattern))) :
    PureReturns program caller state (fillSimpleBody constructor names) state (patternValue target) := by
  apply named_let_returns caller state "filled" _ (patternValue (inner.fill pattern)) _ _ fresh
  · exact helper_capture .fill caller state _ _ _ rfl captured recursive
  · rw [← output]
    exact PureData.template_return program _ state _ (constructor_template constructor names)

private theorem lookup_cons_ne (key name : String) (value : Atom) (caller : Subst) (different : key ≠ name) :
    Subst.lookup ((key, value) :: caller) name = Subst.lookup caller name := by
  simp [Subst.lookup, different]

private theorem fill_ordered_returns (caller : Subst) (state : State) (inner : OneHoleContext)
    (pattern target : Pattern) (before after : List Pattern) (constructor : Constructor) (names : List String)
    (freshFilled : Subst.lookup caller "filled" = none)
    (freshTail : Subst.lookup caller "tail" = none)
    (freshArguments : Subst.lookup caller "arguments" = none)
    (captured : [v "inner", v "pattern"].map (applySubst caller) = [contextValue inner, patternValue pattern])
    (readBefore : applySubst caller (v "before") = patternsValue before)
    (readAfter : applySubst caller (v "after") = patternsValue after)
    (output : applySubst
      (("arguments", patternsValue (before ++ inner.fill pattern :: after)) ::
       ("tail", patternsValue (inner.fill pattern :: after)) ::
       ("filled", patternValue (inner.fill pattern)) :: caller)
      (a constructor.head (names.map v)) = patternValue target)
    (recursive : PureReturns program [] state (a Helper.fill.head [contextValue inner, patternValue pattern]) state
      (patternValue (inner.fill pattern))) :
    PureReturns program caller state (fillOrderedBody constructor names) state (patternValue target) := by
  let filled := ("filled", patternValue (inner.fill pattern)) :: caller
  let tail := ("tail", patternsValue (inner.fill pattern :: after)) :: filled
  apply named_let_returns caller state "filled" _ (patternValue (inner.fill pattern)) _ _ freshFilled
  · exact helper_capture .fill caller state _ _ _ rfl captured recursive
  · apply named_let_returns filled state "tail" _ (patternsValue (inner.fill pattern :: after)) _ _
      (by simpa only [filled, lookup_cons_ne "filled" "tail" _ _ (by decide)] using freshTail)
    · have afterRead := readAfter
      simp only [applySubst, Subst.lookup] at afterRead
      simpa [filled, applySubst, applySubst.applySubstList, Subst.lookup, afterRead,
        patternsValue, patternValue, encoded, encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return program filled state (a "LCons" [v "filled", v "after"])
          (constructor_template .cons ["filled", "after"])
    · apply named_let_returns tail state "arguments" _ (patternsValue (before ++ inner.fill pattern :: after)) _ _
        (by simpa only [tail, filled, lookup_cons_ne "tail" "arguments" _ _ (by decide),
          lookup_cons_ne "filled" "arguments" _ _ (by decide)] using freshArguments)
      · have computed := append_returns tail state (before.map encodePattern)
          ((inner.fill pattern :: after).map encodePattern) (v "before") (v "tail")
          (by
            have beforeRead := readBefore
            simp only [applySubst, Subst.lookup] at beforeRead
            simp [tail, filled, applySubst, Subst.lookup, beforeRead,
              patternsValue, listValue, encodePatterns_eq_encodeList,
              Mettapedia.GSLT.LanguageDef.CettaWire.encodeList_map,
              Mettapedia.GSLT.LanguageDef.CettaWire.encodeList])
        simpa only [← List.map_cons, ← List.map_append, listValue, patternsValue, encodePatterns_eq_encodeList,
          Mettapedia.GSLT.LanguageDef.CettaWire.encodeList_map, Function.id_comp] using computed
      · rw [← output]
        exact PureData.template_return program _ state _ (constructor_template constructor names)

/-- Actual source filling commutes with every original zipper constructor.
Payloads, siblings, names and binder arities remain opaque captured data. -/
theorem fill_returns (state : State) (context : OneHoleContext) (pattern : Pattern) :
    PureReturns program [] state (a "gslt:rule:scope-fill" [contextValue context, patternValue pattern]) state
      (patternValue (context.fill pattern)) := by
  induction context with
  | hole =>
      apply fill_frame_returns
      simpa [frameBindings, frameFillBody, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns program (environment .fill [contextValue .hole, patternValue pattern]) state "pattern"
  | apply head before inner after ih =>
      apply fill_frame_returns
      apply fill_ordered_returns _ state inner pattern _ before after .app ["head", "arguments"]
      all_goals first
        | exact ih
        | simp [frameBindings, environment, Helper.names, applySubst, applySubst.applySubstList,
            Subst.lookup, Constructor.head, encoded, patternValue, patternsValue, encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, OneHoleContext.fill]
  | lambda binder inner ih =>
      apply fill_frame_returns
      apply fill_simple_returns _ state inner pattern _ .lam ["binder", "filled"]
      all_goals first
        | exact ih
        | simp [frameBindings, environment, Helper.names, applySubst, applySubst.applySubstList,
            Subst.lookup, Constructor.head, encoded, patternValue, encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, OneHoleContext.fill]
  | multiLambda arity binders inner ih =>
      apply fill_frame_returns
      apply fill_simple_returns _ state inner pattern _ .multi ["arity", "binders", "filled"]
      all_goals first
        | exact ih
        | simp [frameBindings, environment, Helper.names, applySubst, applySubst.applySubstList,
            Subst.lookup, Constructor.head, encoded, patternValue, encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, OneHoleContext.fill]
  | substBody inner replacement ih =>
      apply fill_frame_returns
      apply fill_simple_returns _ state inner pattern _ .subst ["filled", "replacement"]
      all_goals first
        | exact ih
        | simp [frameBindings, environment, Helper.names, applySubst, applySubst.applySubstList,
            Subst.lookup, Constructor.head, encoded, patternValue, encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, OneHoleContext.fill]
  | substReplacement body inner ih =>
      apply fill_frame_returns
      apply fill_simple_returns _ state inner pattern _ .subst ["body", "filled"]
      all_goals first
        | exact ih
        | simp [frameBindings, environment, Helper.names, applySubst, applySubst.applySubstList,
            Subst.lookup, Constructor.head, encoded, patternValue, encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, OneHoleContext.fill]
  | collection kind before inner after rest ih =>
      apply fill_frame_returns
      apply fill_ordered_returns _ state inner pattern _ before after .collection ["kind", "arguments", "rest"]
      all_goals first
        | exact ih
        | simp [frameBindings, environment, Helper.names, applySubst, applySubst.applySubstList,
            Subst.lookup, Constructor.head, encoded, patternValue, patternsValue, encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, OneHoleContext.fill]

theorem fill_captured_returns (caller : Subst) (state : State) (context : OneHoleContext)
    (pattern : Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [contextValue context, patternValue pattern]) :
    PureReturns program caller state (a "gslt:rule:scope-fill" [one, two]) state
      (patternValue (context.fill pattern)) :=
  helper_capture .fill caller state _ _ _ rfl captured (fill_returns state context pattern)

private def permittedAppBody : Atom :=
  a "let" [v "index", a "gslt:automata:length" [v "before"],
    a "let" [v "slot", a "TermSlot" [v "head", v "index"],
      a "if" [a "==" [v "all", .symbol "PermissionYes"], a Helper.permitted.head [v "permissions", v "inner"],
        a "if" [a "gslt:automata:member" [v "slot", v "slots"],
          a Helper.permitted.head [v "permissions", v "inner"], Effects.boolean false]]]]

private def permittedBinderBody (flag : String) : Atom :=
  a "if" [a "==" [v flag, .symbol "PermissionYes"], a Helper.permitted.head [v "permissions", v "inner"],
    Effects.boolean false]

private def permittedCollectionBody : Atom :=
  a "if" [a "gslt:automata:member" [v "kind", v "kinds"],
    a "if" [a "==" [v "rest", .symbol "RNone"], a Helper.permitted.head [v "permissions", v "inner"],
      Effects.boolean false], Effects.boolean false]

private def permittedCases : SpaceSemantics.Cases :=
  [(.symbol "ContextHole", a "==" [v "enabled", .symbol "PermissionYes"]),
   (a "ContextApp" [v "head", v "before", v "inner", v "after"], permittedAppBody),
   (a "ContextLam" [v "binder", v "inner"], permittedBinderBody "lambda"),
   (a "ContextMultiLam" [v "arity", v "binders", v "inner"], permittedBinderBody "multi"),
   (a "ContextSubstBody" [v "inner", v "replacement"], Effects.boolean false),
   (a "ContextSubstReplacement" [v "body", v "inner"], Effects.boolean false),
   (a "ContextCollection" [v "kind", v "before", v "inner", v "after", v "rest"], permittedCollectionBody)]

private def permissionsCases : SpaceSemantics.Cases :=
  [(a "OperationalPermissions" [v "enabled", v "all", v "slots", v "lambda", v "multi", v "kinds"],
    a "case" [v "context", .expression (permittedCases.map fun row => .expression [row.1, row.2])])]

private theorem permitted_shape : (equation .permitted).body =
    a "case" [v "permissions", .expression (permissionsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def permissionFields (permissions : OperationalPermissions) : Subst :=
  [("kinds", encoded (encodeList encodeCollectionType permissions.collectionKinds)),
   ("multi", encoded (booleanTerm permissions.underMultiLambda)),
   ("lambda", encoded (booleanTerm permissions.underLambda)),
   ("slots", encoded (encodeList slotTerm permissions.constructorArguments)),
   ("all", encoded (booleanTerm permissions.allConstructorArguments)),
   ("enabled", encoded (booleanTerm permissions.enabled))]

private def framePermittedBody : OneHoleContext → Atom
  | .hole => a "==" [v "enabled", .symbol "PermissionYes"]
  | .apply .. => permittedAppBody
  | .lambda .. => permittedBinderBody "lambda"
  | .multiLambda .. => permittedBinderBody "multi"
  | .substBody .. | .substReplacement .. => Effects.boolean false
  | .collection .. => permittedCollectionBody

private def permittedCaller (permissions : OperationalPermissions) (context : OneHoleContext) : Subst :=
  frameBindings context ++ permissionFields permissions ++
    environment .permitted [permissionValue permissions, contextValue context]

private theorem permitted_frame_returns (state : State) (permissions : OperationalPermissions)
    (context : OneHoleContext)
    (continued : PureReturns program (permittedCaller permissions context) state
      (framePermittedBody context) state (Effects.boolean (permissions.permitsContext context))) :
    PureReturns program [] state (a Helper.permitted.head [permissionValue permissions, contextValue context]) state
      (Effects.boolean (permissions.permitsContext context)) := by
  let caller := environment .permitted [permissionValue permissions, contextValue context]
  let unpacked := permissionFields permissions ++ caller
  apply helper_call .permitted [] state _ [permissionValue permissions, contextValue context] _ rfl (by simp)
  rw [permitted_shape]
  apply branch_returns caller unpacked state (v "permissions") (permissionValue permissions) permissionsCases
    (a "case" [v "context", .expression (permittedCases.map fun row => .expression [row.1, row.2])])
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "permissions"
  · simp [unpacked, caller, permissionFields, permissionsCases, permissionValue, permissionsTerm,
      encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      environment, Helper.names]
  · apply branch_returns unpacked (permittedCaller permissions context) state (v "context") (contextValue context)
      permittedCases (framePermittedBody context)
    · simpa [unpacked, caller, permissionFields, environment, Helper.names, applySubst, Subst.lookup] using
        variable_returns program unpacked state "context"
    · cases context <;> simp [permittedCaller, unpacked, caller, permissionFields, frameBindings,
        framePermittedBody, permittedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, contextValue, contextTerm,
        encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, environment, Helper.names]
    · exact continued

private theorem flag_returns (caller : Subst) (state : State) (name : String) (flag : Bool)
    (captured : applySubst caller (v name) = encoded (booleanTerm flag)) :
    PureReturns program caller state (a "==" [v name, .symbol "PermissionYes"]) state (Effects.boolean flag) := by
  have returned := CettaWireAtom.equality_evaluated_returns program caller state
    (booleanTerm flag) (.symbol "PermissionYes") (v name) (.symbol "PermissionYes")
    (by decide +kernel) (by decide +kernel)
    (by simpa only [captured] using variable_returns program caller state name)
    (symbol_returns program caller state "PermissionYes")
  cases flag <;> simpa [booleanTerm] using returned

private theorem slot_member_iff (slot : String × Nat) (slots : List (String × Nat)) :
    slotTerm slot ∈ slots.map slotTerm ↔ slot ∈ slots := by
  constructor
  · intro present
    obtain ⟨found, present, same⟩ := List.mem_map.mp present
    have recovered := congrArg decodeSlot? same
    have equal : found = slot := by simpa using recovered
    simpa only [equal] using present
  · intro present
    exact List.mem_map.mpr ⟨slot, present, rfl⟩

private theorem kind_member_iff (kind : CollType) (kinds : List CollType) :
    encodeCollectionType kind ∈ kinds.map encodeCollectionType ↔ kind ∈ kinds := by
  constructor
  · intro present
    obtain ⟨found, present, same⟩ := List.mem_map.mp present
    have recovered := congrArg decodeCollectionType same
    have equal : found = kind := by simpa using recovered
    simpa only [equal] using present
  · intro present
    exact List.mem_map.mpr ⟨kind, present, rfl⟩

/-- The retained source checks exactly the original explicit capability on
the original context, including refusal beneath substitutions and unresolved
collection rests. No typing or matching outcome supplies permission. -/
theorem permitted_returns (state : State) (permissions : OperationalPermissions) (context : OneHoleContext) :
    PureReturns program [] state (a "gslt:rule:scope-permitted" [permissionValue permissions, contextValue context]) state
      (Effects.boolean (permissions.permitsContext context)) := by
  induction context with
  | hole =>
      apply permitted_frame_returns
      exact flag_returns _ state "enabled" permissions.enabled (by
        simp [permittedCaller, frameBindings, permissionFields, environment, Helper.names, applySubst, Subst.lookup])
  | apply head before inner after ih =>
      apply permitted_frame_returns
      let caller := permittedCaller permissions (.apply head before inner after)
      let indexed := ("index", encoded (.natural before.length)) :: caller
      let slotted := ("slot", encoded (slotTerm (head, before.length))) :: indexed
      apply named_let_returns caller state "index" _ (encoded (.natural before.length)) _ _
      · simp [caller, permittedCaller, frameBindings, permissionFields, environment, Helper.names, Subst.lookup]
      · have returned := length_returns caller state (before.map encodePattern) (v "before") (by
          simp [caller, permittedCaller, frameBindings, permissionFields, environment, Helper.names,
            applySubst, Subst.lookup, listValue, patternsValue, encodePatterns_eq_encodeList,
            Mettapedia.GSLT.LanguageDef.CettaWire.encodeList_map])
        simpa only [List.length_map] using returned
      · apply named_let_returns indexed state "slot" _ (encoded (slotTerm (head, before.length))) _ _
        · simp [indexed, caller, permittedCaller, frameBindings, permissionFields, environment, Helper.names, Subst.lookup]
        · simpa [indexed, caller, permittedCaller, frameBindings, permissionFields, environment, Helper.names,
            applySubst, applySubst.applySubstList, Subst.lookup, Constructor.head, slotTerm, encoded,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program indexed state (a "TermSlot" [v "head", v "index"])
              (constructor_template .slot ["head", "index"])
        · apply bool_if_returns slotted state _ permissions.allConstructorArguments
          · exact flag_returns _ state "all" _ (by simp [slotted, indexed, caller, permittedCaller,
              frameBindings, permissionFields, environment, Helper.names, applySubst, Subst.lookup])
          · cases all : permissions.allConstructorArguments with
            | true =>
                simp only [all, ite_true, OperationalPermissions.permitsContext,
                  OperationalPermissions.permitsArgument, Bool.true_or, Bool.true_and]
                exact helper_capture .permitted slotted state _ _ _ rfl
                  (by simp [slotted, indexed, caller, permittedCaller, frameBindings, permissionFields,
                    environment, Helper.names, applySubst, Subst.lookup]) ih
            | false =>
                simp only [all, Bool.false_eq_true, ite_false, OperationalPermissions.permitsContext,
                  OperationalPermissions.permitsArgument, Bool.false_or]
                apply bool_if_returns slotted state _ (decide ((head, before.length) ∈ permissions.constructorArguments))
                · have returned := member_returns slotted state (slotTerm (head, before.length))
                    (permissions.constructorArguments.map slotTerm) (v "slot") (v "slots") (by
                    simp [slotted, indexed, caller, permittedCaller, frameBindings, permissionFields,
                      environment, Helper.names, applySubst, Subst.lookup, listValue,
                      Mettapedia.GSLT.LanguageDef.InferenceCettaWire.encodeList,
                      Mettapedia.GSLT.LanguageDef.CettaWire.encodeList_map])
                  simpa only [slot_member_iff] using returned
                · by_cases present : (head, before.length) ∈ permissions.constructorArguments
                  · simp only [present, decide_true, ite_true, Bool.true_and]
                    exact helper_capture .permitted slotted state _ _ _ rfl
                      (by simp [slotted, indexed, caller, permittedCaller, frameBindings, permissionFields,
                        environment, Helper.names, applySubst, Subst.lookup]) ih
                  · simp only [present, decide_false, Bool.false_eq_true, ite_false, Bool.false_and]
                    exact grounded_returns program slotted state (.bool false)
  | lambda binder inner ih =>
      apply permitted_frame_returns
      let caller := permittedCaller permissions (.lambda binder inner)
      apply bool_if_returns caller state _ permissions.underLambda
      · exact flag_returns _ state "lambda" _ (by simp [caller, permittedCaller, frameBindings,
          permissionFields, environment, Helper.names, applySubst, Subst.lookup])
      · cases allowed : permissions.underLambda with
        | false =>
            simp only [allowed, Bool.false_eq_true, ite_false, OperationalPermissions.permitsContext, Bool.false_and]
            exact grounded_returns program caller state (.bool false)
        | true =>
            simp only [allowed, ite_true, OperationalPermissions.permitsContext, Bool.true_and]
            exact helper_capture .permitted caller state _ _ _ rfl
              (by simp [caller, permittedCaller, frameBindings, permissionFields, environment,
                Helper.names, applySubst, Subst.lookup]) ih
  | multiLambda arity binders inner ih =>
      apply permitted_frame_returns
      let caller := permittedCaller permissions (.multiLambda arity binders inner)
      apply bool_if_returns caller state _ permissions.underMultiLambda
      · exact flag_returns _ state "multi" _ (by simp [caller, permittedCaller, frameBindings,
          permissionFields, environment, Helper.names, applySubst, Subst.lookup])
      · cases allowed : permissions.underMultiLambda with
        | false =>
            simp only [allowed, Bool.false_eq_true, ite_false, OperationalPermissions.permitsContext, Bool.false_and]
            exact grounded_returns program caller state (.bool false)
        | true =>
            simp only [allowed, ite_true, OperationalPermissions.permitsContext, Bool.true_and]
            exact helper_capture .permitted caller state _ _ _ rfl
              (by simp [caller, permittedCaller, frameBindings, permissionFields, environment,
                Helper.names, applySubst, Subst.lookup]) ih
  | substBody inner replacement _ =>
      apply permitted_frame_returns
      exact grounded_returns program _ state (.bool false)
  | substReplacement body inner _ =>
      apply permitted_frame_returns
      exact grounded_returns program _ state (.bool false)
  | collection kind before inner after rest ih =>
      apply permitted_frame_returns
      let caller := permittedCaller permissions (.collection kind before inner after rest)
      apply bool_if_returns caller state _ (decide (kind ∈ permissions.collectionKinds))
      · have returned := member_returns caller state (encodeCollectionType kind)
          (permissions.collectionKinds.map encodeCollectionType) (v "kind") (v "kinds") (by
          simp [caller, permittedCaller, frameBindings, permissionFields, environment, Helper.names,
            applySubst, Subst.lookup, listValue, Mettapedia.GSLT.LanguageDef.InferenceCettaWire.encodeList,
            Mettapedia.GSLT.LanguageDef.CettaWire.encodeList_map])
        simpa only [kind_member_iff] using returned
      · by_cases present : kind ∈ permissions.collectionKinds
        · simp only [present, decide_true, ite_true, OperationalPermissions.permitsContext, Bool.true_and]
          apply bool_if_returns caller state _ rest.isNone
          · have returned := CettaWireAtom.equality_evaluated_returns program caller state (encodeRest rest)
              (.symbol "RNone") (v "rest") (.symbol "RNone") (by decide +kernel) (by decide +kernel)
              (by simpa [caller, permittedCaller, frameBindings, permissionFields, environment, Helper.names,
                  applySubst, Subst.lookup] using variable_returns program caller state "rest")
              (symbol_returns program caller state "RNone")
            cases rest <;> simpa [encodeRest] using returned
          · cases rest with
            | none =>
                simp only [Option.isNone_none, ite_true, Bool.true_and]
                exact helper_capture .permitted caller state _ _ _ rfl
                  (by simp [caller, permittedCaller, frameBindings, permissionFields, environment,
                    Helper.names, applySubst, Subst.lookup]) ih
            | some name =>
                simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Bool.false_and]
                exact grounded_returns program caller state (.bool false)
        · simp only [present, decide_false, Bool.false_eq_true, ite_false,
            OperationalPermissions.permitsContext, Bool.false_and]
          exact grounded_returns program caller state (.bool false)

theorem permitted_captured_returns (caller : Subst) (state : State) (permissions : OperationalPermissions)
    (context : OneHoleContext) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [permissionValue permissions, contextValue context]) :
    PureReturns program caller state (a "gslt:rule:scope-permitted" [one, two]) state
      (Effects.boolean (permissions.permitsContext context)) :=
  helper_capture .permitted caller state _ _ _ rfl captured (permitted_returns state permissions context)

namespace Controls

def binderPermissions : OperationalPermissions :=
  {enabled := true, allConstructorArguments := false, constructorArguments := [("Binder", 0)],
    underLambda := false, underMultiLambda := true, collectionKinds := []}

def binderContext : OneHoleContext :=
  .apply "Binder" [] (.multiLambda 3 ["x", "y", "z"] .hole) []

theorem actual_source_permits_open_multiLambda (state : State) :
    PureReturns program [] state
      (CettaWireAtom.encode (.application "gslt:rule:scope-permitted"
        [permissionsTerm binderPermissions, contextTerm binderContext])) state
      (Effects.boolean true) := by
  exact permitted_returns state binderPermissions binderContext

theorem actual_source_refuses_blocked_multiLambda (state : State) :
    PureReturns program [] state
      (CettaWireAtom.encode (.application "gslt:rule:scope-permitted"
        [permissionsTerm {binderPermissions with underMultiLambda := false}, contextTerm binderContext])) state
      (Effects.boolean false) := by
  exact permitted_returns state {binderPermissions with underMultiLambda := false} binderContext

theorem actual_source_fill_retains_ambient_index_and_binder_frame (state : State) :
    PureReturns program [] state
      (CettaWireAtom.encode (.application "gslt:rule:scope-fill"
        [contextTerm binderContext, encodePattern (.bvar 3)])) state
      (CettaWireAtom.encode (encodePattern
        (.apply "Binder" [.multiLambda 3 ["x", "y", "z"] (.bvar 3)]))) := by
  exact fill_returns state binderContext (.bvar 3)

theorem actual_source_refuses_substitution_permission (state : State) :
    PureReturns program [] state
      (CettaWireAtom.encode (.application "gslt:rule:scope-permitted"
        [permissionsTerm .all, contextTerm (.substBody .hole (.bvar 0))])) state
      (Effects.boolean false) := by
  exact permitted_returns state .all (.substBody .hole (.bvar 0))

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.ContextObservation
