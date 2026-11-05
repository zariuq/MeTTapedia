import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataCompilationExecution
import Mettapedia.GSLT.LanguageDef.MeTTaILSubtermMatchAutomata
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Lowering and interning the retained matching inventory

The retained PeTTa equations collect structural subpatterns and remove repeated
inventory entries in first-occurrence order. This inventory is separate from
the authored rule list: interning instructions does not erase derivations.
The source/wire adapters reuse the canonical first-order syntax and views.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataInventoryExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire OrderedPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval MatchAutomataProgram
open MatchAutomataSourceExecution (listValue)
open MatchAutomataCompilationExecution (shapeTerm subjectTerm)
open MeTTaILFirstOrderRuleCompilation (PatternPlan erasePatterns)

/-- An injective wire representation of the canonical constructor observations.
The first-order source helpers use `HFree`, `HBound`, and `HApp`; the remaining
tags keep this representation distinct across the full observation vocabulary. -/
def headTerm : MeTTaILPatternMatrixCompilation.Matrix.Head → Term
  | .freeVariable name => .application "HFree" [.string name]
  | .boundVariable index => .application "HBound" [.natural index]
  | .application head arity => .application "HApp" [.string head, .natural arity]
  | .lambda => .symbol "HLambda"
  | .multiLambda arity => .application "HMultiLambda" [.natural arity]
  | .substitution => .symbol "HSubstitution"
  | .collection kind => .application "HCollection" [InferenceCettaWire.encodeCollectionType kind]

theorem headTerm_injective : Function.Injective headTerm := by
  intro first second same
  cases first <;> cases second <;> simp_all [headTerm]
  rename_i firstKind secondKind
  cases firstKind <;> cases secondKind <;>
    simp_all [InferenceCettaWire.encodeCollectionType]

/-- The canonical pattern view, with its constructor heads encoded for MeTTa. -/
def patternView (plan : PatternPlan) : Pattern Term :=
  Pattern.mapHeads headTerm (MeTTaILPatternMatrixCompilation.Matrix.lowerPattern plan.erase)

/-- The canonical subject view, with the same injective constructor encoding. -/
def subjectView (plan : PatternPlan) : Subject Term :=
  Subject.mapHeads headTerm (MeTTaILPatternMatrixCompilation.Matrix.lowerSubject plan.erase)

private theorem erasePatterns_eq_map (plans : List PatternPlan) :
    erasePatterns plans = plans.map PatternPlan.erase := by
  induction plans with
  | nil => rfl
  | cons first rest ih => simp [erasePatterns, ih]

@[simp] theorem patternView_metavariable (name : String) :
    patternView (.metavariable name) = .wildcard := by
  simp [patternView, PatternPlan.erase, MeTTaILPatternMatrixCompilation.Matrix.lowerPattern, Pattern.mapHeads]

@[simp] theorem patternView_bound (index : Nat) :
    patternView (.bound index) = .node (.application "HBound" [.natural index]) [] := by
  simp [patternView, PatternPlan.erase, MeTTaILPatternMatrixCompilation.Matrix.lowerPattern, Pattern.mapHeads, headTerm]

@[simp] theorem patternView_application (head : String) (children : List PatternPlan) :
    patternView (.application head children) =
      .node (.application "HApp" [.string head, .natural children.length]) (children.map patternView) := by
  simp [patternView, PatternPlan.erase, MeTTaILPatternMatrixCompilation.Matrix.lowerPattern,
    Pattern.mapHeads, headTerm, erasePatterns_eq_map, List.map_map, Function.comp_def]

@[simp] theorem subjectView_metavariable (name : String) :
    subjectView (.metavariable name) = .node (.application "HFree" [.string name]) [] := by
  simp [subjectView, PatternPlan.erase, MeTTaILPatternMatrixCompilation.Matrix.lowerSubject, Subject.mapHeads, headTerm]

@[simp] theorem subjectView_bound (index : Nat) :
    subjectView (.bound index) = .node (.application "HBound" [.natural index]) [] := by
  simp [subjectView, PatternPlan.erase, MeTTaILPatternMatrixCompilation.Matrix.lowerSubject, Subject.mapHeads, headTerm]

@[simp] theorem subjectView_application (head : String) (children : List PatternPlan) :
    subjectView (.application head children) =
      .node (.application "HApp" [.string head, .natural children.length]) (children.map subjectView) := by
  simp [subjectView, PatternPlan.erase, MeTTaILPatternMatrixCompilation.Matrix.lowerSubject,
    Subject.mapHeads, headTerm, erasePatterns_eq_map, List.map_map, Function.comp_def]

/-- Canonical GSLT candidate identities survive the concrete source encoding. -/
theorem reference_views (patterns : List PatternPlan) (subject : PatternPlan) :
    SubtermMatching.reference (patterns.map patternView) (subjectView subject) =
      SubtermMatching.reference
        ((erasePatterns patterns).map MeTTaILPatternMatrixCompilation.Matrix.lowerPattern)
        (MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject.erase) := by
  have mapped : patterns.map patternView =
      ((erasePatterns patterns).map MeTTaILPatternMatrixCompilation.Matrix.lowerPattern).map
        (Pattern.mapHeads headTerm) := by
    rw [erasePatterns_eq_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro plan _
    rfl
  rw [mapped]
  exact SubtermMatching.reference_mapHeads headTerm headTerm_injective
    ((erasePatterns patterns).map MeTTaILPatternMatrixCompilation.Matrix.lowerPattern)
    (MeTTaILPatternMatrixCompilation.Matrix.lowerSubject subject.erase)

private def patternValue (plan : PatternPlan) : Atom :=
  CettaWireAtom.encode (InferenceCettaWire.encodePattern plan.erase)

private theorem pattern_values (plans : List PatternPlan) :
    CettaWireAtom.encode (InferenceCettaWire.encodePatterns (erasePatterns plans)) =
      listValue (plans.map (fun plan => InferenceCettaWire.encodePattern plan.erase)) := by
  rw [InferenceCettaWire.encodePatterns_eq_encodeList, erasePatterns_eq_map]
  simp only [listValue, encodeList_map]
  rfl

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

private inductive Helper where
  | unique | subpatterns | subpatternsList | shape | shapes | subject | subjects
private def Helper.head : Helper → String
  | .unique => "gslt:automata:unique"
  | .subpatterns => "gslt:automata:subpatterns"
  | .subpatternsList => "gslt:automata:subpatterns-list"
  | .shape => "gslt:automata:shape"
  | .shapes => "gslt:automata:shapes"
  | .subject => "gslt:automata:subject"
  | .subjects => "gslt:automata:subjects"
private def Helper.argument : Helper → String
  | .unique => "xs"
  | .subpatterns | .shape | .subject => "p"
  | .subpatternsList | .shapes | .subjects => "ps"
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (value : Atom) : Subst := [(helper.argument, value)]
private theorem helper_clause (helper : Helper) (value : Atom) :
    clauses program helper.head [value] = [.evaluate (environment helper value) (equation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [equation helper] from by cases helper <;> rfl]
  have formals : (equation helper).arguments = [v helper.argument] := by cases helper <;> decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]
private theorem helper_call (helper : Helper) (bindings : Subst) (state : State)
    (argument value answer : Atom) (captured : applySubst bindings argument = value)
    (returned : PureReturns program (environment helper value) state (equation helper).body state answer) :
    PureReturns program bindings state (a helper.head [argument]) state answer := by
  apply PureData.raw_authored_call_return program bindings (environment helper value) state state
    helper.head [argument] (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    cases helper <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil, captured] using helper_clause helper value

private theorem append_captured (bindings : Subst) (state : State) (left right : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst bindings) = [listValue left, listValue right]) :
    PureReturns program bindings state (a "gslt:automata:append" [one, two]) state
      (listValue (left ++ right)) := by
  apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:append"
    [listValue left, listValue right] [one, two] _ (by decide +kernel) _ (by decide) _
    (MatchAutomataSourceExecution.append_returns state left right)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simpa using captured.symm

private theorem member_captured (bindings : Subst) (state : State) (value : Term) (values : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst bindings) = [CettaWireAtom.encode value, listValue values]) :
    PureReturns program bindings state (a "gslt:automata:member" [one, two]) state
      (Effects.boolean (decide (value ∈ values))) := by
  apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:member"
    [CettaWireAtom.encode value, listValue values] [one, two] _ (by decide +kernel) _ (by decide) _
    (MatchAutomataSourceExecution.member_returns state value values)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · simpa using captured.symm

private theorem pair_template (first second : String) : PureData.Template program (a "LCons" [v first, v second]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private def subpatternsCases : SpaceSemantics.Cases :=
  [(.symbol "MAny", a "LCons" [.symbol "MAny", .symbol "LNil"]),
    (a "MNode" [v "head", v "children"],
      a "let" [v "rest", a "gslt:automata:subpatterns-list" [v "children"], a "LCons" [v "p", v "rest"]])]
private def subpatternsListCons : Atom :=
  a "let*" [.expression [.expression [v "head", a "gslt:automata:subpatterns" [v "p"]],
    .expression [v "tail", a "gslt:automata:subpatterns-list" [v "rest"]]],
    a "gslt:automata:append" [v "head", v "tail"]]
private def subpatternsListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "p", v "rest"], subpatternsListCons)]
private theorem subpatterns_shape : (equation .subpatterns).body =
    a "case" [v "p", .expression (subpatternsCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem subpatterns_list_shape : (equation .subpatternsList).body =
    a "case" [v "ps", .expression (subpatternsListCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

mutual
  theorem subpatterns_body_returns (state : State) (pattern : Pattern Term) :
      PureReturns program (environment .subpatterns (CettaWireAtom.encode (shapeTerm pattern))) state
        (equation .subpatterns).body state
        (listValue ((BottomUpMatchAutomaton.subpatterns pattern).map shapeTerm)) := by
    cases pattern with
    | wildcard =>
        let bindings := environment .subpatterns (.symbol "MAny")
        rw [subpatterns_shape]
        apply case_returns program bindings bindings state state state (v "p") (.symbol "MAny")
          (a "LCons" [.symbol "MAny", .symbol "LNil"]) _ _ subpatternsCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, Helper.argument, applySubst, Subst.lookup] using variable_returns program bindings state "p"
        · simp [subpatternsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · apply PureData.constructor_return program bindings state "LCons" _ _ (by decide +kernel) (by decide)
          exact .cons (symbol_returns program bindings state "MAny")
            (.cons (symbol_returns program bindings state "LNil") (.nil))
    | node head children =>
        let bindings := environment .subpatterns (CettaWireAtom.encode (shapeTerm (.node head children)))
        let selected := ("children", listValue (children.map shapeTerm)) :: ("head", CettaWireAtom.encode head) :: bindings
        let rest := listValue ((BottomUpMatchAutomaton.subpatternsList children).map shapeTerm)
        let bound := ("rest", rest) :: selected
        rw [subpatterns_shape]
        apply case_returns program bindings selected state state state (v "p")
          (CettaWireAtom.encode (shapeTerm (.node head children)))
          (a "let" [v "rest", a "gslt:automata:subpatterns-list" [v "children"], a "LCons" [v "p", v "rest"]])
          _ _ subpatternsCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, Helper.argument, applySubst, Subst.lookup] using variable_returns program bindings state "p"
        · simp [subpatternsCases, MatchAutomataCompilationExecution.shapeTerm_node, listValue,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, bindings, environment, Helper.argument]
        · apply let_returns program selected bound state state state (v "rest") _ _ rest _
          · exact helper_call .subpatternsList selected state (v "children") (listValue (children.map shapeTerm)) rest
              (by simp [selected, applySubst, Subst.lookup]) (subpatterns_list_body_returns state children)
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, bindings, environment, Helper.argument]
          · simpa [BottomUpMatchAutomaton.subpatterns, listValue, encodeList, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
              bound, selected, bindings, environment, Helper.argument, rest] using
              PureData.template_return program bound state _ (pair_template "p" "rest")

  theorem subpatterns_list_body_returns (state : State) (patterns : List (Pattern Term)) :
      PureReturns program (environment .subpatternsList (listValue (patterns.map shapeTerm))) state
        (equation .subpatternsList).body state
        (listValue ((BottomUpMatchAutomaton.subpatternsList patterns).map shapeTerm)) := by
    cases patterns with
    | nil =>
        let bindings := environment .subpatternsList (.symbol "LNil")
        rw [subpatterns_list_shape]
        apply case_returns program bindings bindings state state state (v "ps") (.symbol "LNil")
          (.symbol "LNil") (.symbol "LNil") _ subpatternsListCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, Helper.argument, applySubst, Subst.lookup] using variable_returns program bindings state "ps"
        · simp [subpatternsListCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program bindings state "LNil"
    | cons first rest =>
        let bindings := environment .subpatternsList (listValue ((first :: rest).map shapeTerm))
        let selected := ("rest", listValue (rest.map shapeTerm)) :: ("p", CettaWireAtom.encode (shapeTerm first)) :: bindings
        let headValue := listValue ((BottomUpMatchAutomaton.subpatterns first).map shapeTerm)
        let headBound := ("head", headValue) :: selected
        let tailValue := listValue ((BottomUpMatchAutomaton.subpatternsList rest).map shapeTerm)
        let tailBound := ("tail", tailValue) :: headBound
        rw [subpatterns_list_shape]
        apply case_returns program bindings selected state state state (v "ps") (listValue ((first :: rest).map shapeTerm))
          subpatternsListCons _ _ subpatternsListCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, Helper.argument, applySubst, Subst.lookup] using variable_returns program bindings state "ps"
        · simp [subpatternsListCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selected, bindings, environment, Helper.argument]
        · have headReturned := helper_call .subpatterns selected state (v "p")
              (CettaWireAtom.encode (shapeTerm first)) headValue
              (by simp [selected, applySubst, Subst.lookup]) (subpatterns_body_returns state first)
          have headMatched : SpaceSemantics.matchBinding selected (v "head") headValue = some headBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, selected, bindings, environment, Helper.argument]
          have tailReturned := helper_call .subpatternsList headBound state (v "rest")
              (listValue (rest.map shapeTerm)) tailValue
              (by simp [headBound, selected, applySubst, Subst.lookup]) (subpatterns_list_body_returns state rest)
          have tailMatched : SpaceSemantics.matchBinding headBound (v "tail") tailValue = some tailBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, headBound, selected, bindings, environment, Helper.argument]
          have appended := append_captured tailBound state
            ((BottomUpMatchAutomaton.subpatterns first).map shapeTerm)
            ((BottomUpMatchAutomaton.subpatternsList rest).map shapeTerm) (v "head") (v "tail")
            (by simp [tailBound, headBound, headValue, tailValue, applySubst, Subst.lookup])
          have computed := PureData.let_bindings_return
            (PureData.BindingsReturn.cons headReturned headMatched
              (PureData.BindingsReturn.cons tailReturned tailMatched (.nil tailBound state))) state
            (a "gslt:automata:append" [v "head", v "tail"]) _ appended
          simpa only [BottomUpMatchAutomaton.subpatternsList, List.map_append,
            List.map_cons, List.map_nil, Helper.head, subpatternsListCons] using computed
end

theorem subpatterns_captured_returns (bindings : Subst) (state : State) (pattern : Pattern Term)
    (argument : Atom) (captured : applySubst bindings argument = CettaWireAtom.encode (shapeTerm pattern)) :
    PureReturns program bindings state (a "gslt:automata:subpatterns" [argument]) state
      (listValue ((BottomUpMatchAutomaton.subpatterns pattern).map shapeTerm)) :=
  helper_call .subpatterns bindings state argument _ _ captured (subpatterns_body_returns state pattern)

theorem subpatterns_returns (state : State) (pattern : Pattern Term) :
    PureReturns program [] state (a "gslt:automata:subpatterns" [CettaWireAtom.encode (shapeTerm pattern)]) state
      (listValue ((BottomUpMatchAutomaton.subpatterns pattern).map shapeTerm)) :=
  subpatterns_captured_returns [] state pattern _ (by simp)

theorem subpatterns_list_captured_returns (bindings : Subst) (state : State) (patterns : List (Pattern Term))
    (argument : Atom) (captured : applySubst bindings argument = listValue (patterns.map shapeTerm)) :
    PureReturns program bindings state (a "gslt:automata:subpatterns-list" [argument]) state
      (listValue ((BottomUpMatchAutomaton.subpatternsList patterns).map shapeTerm)) :=
  helper_call .subpatternsList bindings state argument _ _ captured (subpatterns_list_body_returns state patterns)

theorem subpatterns_list_returns (state : State) (patterns : List (Pattern Term)) :
    PureReturns program [] state (a "gslt:automata:subpatterns-list" [listValue (patterns.map shapeTerm)]) state
      (listValue ((BottomUpMatchAutomaton.subpatternsList patterns).map shapeTerm)) :=
  subpatterns_list_captured_returns [] state patterns _ (by simp)

private theorem unique_cons (first : Term) (rest seen : List Term) :
    ((first :: rest).removeAll seen).eraseDups =
      if first ∈ seen then (rest.removeAll seen).eraseDups
      else first :: (rest.removeAll (first :: seen)).eraseDups := by
  by_cases present : first ∈ seen
  · simp [List.cons_removeAll, present]
  · simp only [present, if_false, List.cons_removeAll,
      show seen.contains first = false from by simp [present], if_true, List.eraseDups_cons]
    rw [List.removeAll_cons]
    simp [List.removeAll, List.filter_filter, Bool.and_comm]

private def uniqueAccEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:unique-acc")[0]'(by decide +kernel)
private def uniqueAccEnv (values seen : List Term) : Subst := [("seen", listValue seen), ("xs", listValue values)]
private def uniqueSeen : Atom := a "gslt:automata:unique-acc" [v "rest", v "seen"]
private def uniqueNew : Atom :=
  a "let*" [.expression [.expression [v "seen-next", a "LCons" [v "x", v "seen"]],
    .expression [v "tail", a "gslt:automata:unique-acc" [v "rest", v "seen-next"]]],
    a "LCons" [v "x", v "tail"]]
private def uniqueAccCons : Atom := a "if" [a "gslt:automata:member" [v "x", v "seen"], uniqueSeen, uniqueNew]
private def uniqueAccCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "x", v "rest"], uniqueAccCons)]
private theorem unique_acc_shape : uniqueAccEquation.body =
    a "case" [v "xs", .expression (uniqueAccCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem unique_acc_clause (values seen : List Term) :
    clauses program "gslt:automata:unique-acc" [listValue values, listValue seen] =
      [.evaluate (uniqueAccEnv values seen) uniqueAccEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:unique-acc").filterMap _ = _
  rw [show equations "gslt:automata:unique-acc" = [uniqueAccEquation] from rfl]
  have formals : uniqueAccEquation.arguments = [v "xs", v "seen"] := by decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, uniqueAccEnv]
private theorem unique_acc_call (bindings : Subst) (state : State) (values seen : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst bindings) = [listValue values, listValue seen])
    (returned : PureReturns program (uniqueAccEnv values seen) state uniqueAccEquation.body state
      (listValue ((values.removeAll seen).eraseDups))) :
    PureReturns program bindings state (a "gslt:automata:unique-acc" [one, two]) state
      (listValue ((values.removeAll seen).eraseDups)) := by
  apply PureData.raw_authored_call_return program bindings (uniqueAccEnv values seen) state state
    "gslt:automata:unique-acc" [one, two] uniqueAccEquation.body _ (by decide) (by decide)
    (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact unique_acc_clause values seen

theorem unique_acc_body_returns (state : State) (values seen : List Term) :
    PureReturns program (uniqueAccEnv values seen) state uniqueAccEquation.body state
      (listValue ((values.removeAll seen).eraseDups)) := by
  induction values generalizing seen with
  | nil =>
      rw [unique_acc_shape]
      apply case_returns program (uniqueAccEnv [] seen) (uniqueAccEnv [] seen) state state state
        (v "xs") (.symbol "LNil") (.symbol "LNil") (.symbol "LNil") _ uniqueAccCases (read_cases_encoded _) _ _ _
      · simpa [uniqueAccEnv, listValue, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup]
          using variable_returns program (uniqueAccEnv [] seen) state "xs"
      · simp [uniqueAccCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons first rest ih =>
      let bindings := uniqueAccEnv (first :: rest) seen
      let selected := ("rest", listValue rest) :: ("x", CettaWireAtom.encode first) :: bindings
      rw [unique_acc_shape]
      apply case_returns program bindings selected state state state (v "xs") (listValue (first :: rest))
        uniqueAccCons _ _ uniqueAccCases (read_cases_encoded _) _ _ _
      · simpa [bindings, uniqueAccEnv, applySubst, Subst.lookup] using variable_returns program bindings state "xs"
      · simp [uniqueAccCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, bindings, uniqueAccEnv]
      · have tested := member_captured selected state first seen (v "x") (v "seen")
            (by simp [selected, bindings, uniqueAccEnv, applySubst, Subst.lookup])
        apply if_returns program selected state state state _ _ _ _ _ tested
        rw [unique_cons]
        by_cases present : first ∈ seen
        · simp only [present, decide_true]
          rw [show (Effects.boolean true == Effects.boolean true) = true from by decide]
          simp only [if_true]
          exact unique_acc_call selected state rest seen (v "rest") (v "seen")
            (by simp [selected, bindings, uniqueAccEnv, applySubst, Subst.lookup]) (ih seen)
        · simp only [present, decide_false]
          rw [show (Effects.boolean false == Effects.boolean true) = false from by decide]
          simp only [if_false]
          let seenValue := listValue (first :: seen)
          let seenBound := ("seen-next", seenValue) :: selected
          let tailValue := listValue ((rest.removeAll (first :: seen)).eraseDups)
          let tailBound := ("tail", tailValue) :: seenBound
          have seenReturned : PureReturns program selected state (a "LCons" [v "x", v "seen"]) state seenValue := by
            simpa [seenValue, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup, selected, bindings, uniqueAccEnv] using
                PureData.template_return program selected state _ (pair_template "x" "seen")
          have seenMatched : SpaceSemantics.matchBinding selected (v "seen-next") seenValue = some seenBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, seenBound, selected, bindings, uniqueAccEnv]
          have tailReturned := unique_acc_call seenBound state rest (first :: seen) (v "rest") (v "seen-next")
            (by simp [seenBound, selected, seenValue, applySubst, Subst.lookup]) (ih (first :: seen))
          have tailMatched : SpaceSemantics.matchBinding seenBound (v "tail") tailValue = some tailBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, seenBound, selected, bindings, uniqueAccEnv]
          have resultReturned : PureReturns program tailBound state (a "LCons" [v "x", v "tail"]) state
              (listValue (first :: (rest.removeAll (first :: seen)).eraseDups)) := by
            simpa [listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup, tailBound, seenBound, selected,
                tailValue] using PureData.template_return program tailBound state _ (pair_template "x" "tail")
          have computed := PureData.let_bindings_return
            (PureData.BindingsReturn.cons seenReturned seenMatched
              (PureData.BindingsReturn.cons tailReturned tailMatched (.nil tailBound state))) state
            (a "LCons" [v "x", v "tail"]) _ resultReturned
          simpa [uniqueNew] using computed

theorem unique_acc_captured_returns (bindings : Subst) (state : State) (values seen : List Term)
    (one two : Atom) (captured : [one, two].map (applySubst bindings) = [listValue values, listValue seen]) :
    PureReturns program bindings state (a "gslt:automata:unique-acc" [one, two]) state
      (listValue ((values.removeAll seen).eraseDups)) :=
  unique_acc_call bindings state values seen one two captured (unique_acc_body_returns state values seen)

theorem unique_acc_returns (state : State) (values seen : List Term) :
    PureReturns program [] state (a "gslt:automata:unique-acc" [listValue values, listValue seen]) state
      (listValue ((values.removeAll seen).eraseDups)) :=
  unique_acc_captured_returns [] state values seen _ _ (by simp)

private theorem unique_shape : (equation .unique).body =
    a "gslt:automata:unique-acc" [v "xs", .symbol "LNil"] := by decide +kernel

theorem unique_captured_returns (bindings : Subst) (state : State) (values : List Term)
    (argument : Atom) (captured : applySubst bindings argument = listValue values) :
    PureReturns program bindings state (a "gslt:automata:unique" [argument]) state (listValue values.eraseDups) := by
  apply helper_call .unique bindings state argument (listValue values) _ captured
  rw [unique_shape]
  simpa using unique_acc_captured_returns (environment .unique (listValue values)) state values []
    (v "xs") (.symbol "LNil")
    (by simp [environment, Helper.argument, applySubst, Subst.lookup, listValue, encodeList, CettaWireAtom.encode])

theorem unique_returns (state : State) (values : List Term) :
    PureReturns program [] state (a "gslt:automata:unique" [listValue values]) state (listValue values.eraseDups) :=
  unique_captured_returns [] state values _ (by simp)

private theorem eraseDups_shape_loop (patterns seen : List (Pattern Term)) :
    List.eraseDupsBy.loop (· == ·) (patterns.map shapeTerm) (seen.map shapeTerm) =
      (List.eraseDupsBy.loop (· == ·) patterns seen).map shapeTerm := by
  induction patterns generalizing seen with
  | nil => simp [List.eraseDupsBy.loop]
  | cons first rest ih =>
      have sameContains : (seen.map shapeTerm).contains (shapeTerm first) = seen.contains first := by
        apply Bool.eq_iff_iff.mpr
        simp [MatchAutomataCompilationExecution.shapeTerm_injective.eq_iff]
      simp only [List.map_cons, List.eraseDupsBy.loop, List.any_beq, sameContains]
      cases present : seen.contains first
      · simpa [present, List.map_cons] using ih (first :: seen)
      · simpa [present] using ih seen

theorem eraseDups_shape_map (patterns : List (Pattern Term)) :
    (patterns.map shapeTerm).eraseDups = patterns.eraseDups.map shapeTerm := by
  exact eraseDups_shape_loop patterns []

/-- Interning source instructions agrees with the existing inventory;
authored rows remain outside this deduplication. -/
theorem inventory_returns (state : State) (patterns : List (Pattern Term)) :
    PureReturns program [] state
      (a "gslt:automata:unique" [listValue ((BottomUpMatchAutomaton.subpatternsList patterns).map shapeTerm)]) state
      (listValue ((BottomUpMatchAutomaton.inventory patterns).map shapeTerm)) := by
  simpa only [eraseDups_shape_map, BottomUpMatchAutomaton.inventory] using
    unique_returns state ((BottomUpMatchAutomaton.subpatternsList patterns).map shapeTerm)

private inductive Lowering where
  | pattern | subject

private def Lowering.scalar : Lowering → Helper
  | .pattern => .shape
  | .subject => .subject

private def Lowering.vector : Lowering → Helper
  | .pattern => .shapes
  | .subject => .subjects

private def Lowering.childrenName : Lowering → String
  | .pattern => "shapes"
  | .subject => "subjects"

private def Lowering.term (mode : Lowering) (plan : PatternPlan) : Term :=
  match mode with
  | .pattern => shapeTerm (patternView plan)
  | .subject => subjectTerm (subjectView plan)

@[simp] private theorem pattern_term : Lowering.pattern.term = fun plan => shapeTerm (patternView plan) := by
  funext plan
  rfl

@[simp] private theorem subject_term : Lowering.subject.term = fun plan => subjectTerm (subjectView plan) := by
  funext plan
  rfl

@[simp] private theorem Lowering.scalar_argument (mode : Lowering) : mode.scalar.argument = "p" := by
  cases mode <;> rfl

@[simp] private theorem Lowering.vector_argument (mode : Lowering) : mode.vector.argument = "ps" := by
  cases mode <;> rfl

private def Lowering.freeBody : Lowering → Atom
  | .pattern => .symbol "MAny"
  | .subject => a "MNode" [a "HFree" [v "name"], .symbol "LNil"]

private def Lowering.applicationBody (mode : Lowering) : Atom :=
  a "let*" [.expression [.expression [v "arity", a "gslt:automata:length" [v "children"]],
    .expression [v mode.childrenName, a mode.vector.head [v "children"]]],
    a "MNode" [a "HApp" [v "head", v "arity"], v mode.childrenName]]

private def Lowering.cases (mode : Lowering) : SpaceSemantics.Cases :=
  [(a "FVar" [v "name"], mode.freeBody),
    (a "Var" [v "index"], a "MNode" [a "HBound" [v "index"], .symbol "LNil"]),
    (a "PApp" [v "head", v "children"], mode.applicationBody)]

private def Lowering.vectorBody (mode : Lowering) : Atom :=
  a "let*" [.expression [.expression [v "head", a mode.scalar.head [v "p"]],
    .expression [v "tail", a mode.vector.head [v "rest"]]], a "LCons" [v "head", v "tail"]]

private def Lowering.vectorCases (mode : Lowering) : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "p", v "rest"], mode.vectorBody)]

private theorem lowering_shape (mode : Lowering) : (equation mode.scalar).body =
    a "case" [v "p", .expression (mode.cases.map fun row => .expression [row.1, row.2])] := by
  cases mode <;> decide +kernel

private theorem lowering_vector_shape (mode : Lowering) : (equation mode.vector).body =
    a "case" [v "ps", .expression (mode.vectorCases.map fun row => .expression [row.1, row.2])] := by
  cases mode <;> decide +kernel

private theorem mnode_template (head children : Atom) (headTemplate : PureData.Template program head)
    (childrenTemplate : PureData.Template program children) :
    PureData.Template program (a "MNode" [head, children]) := by
  apply PureData.Template.constructor "MNode" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> assumption

private theorem unary_template (head name : String)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]) :
    PureData.Template program (a head [v name]) := by
  apply PureData.Template.constructor head _ inert ordinary
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  exact .captured name

private theorem free_template (mode : Lowering) : PureData.Template program mode.freeBody := by
  cases mode with
  | pattern => exact .symbol "MAny"
  | subject =>
      exact mnode_template _ _ (unary_template "HFree" "name" (by decide +kernel) (by decide)) (.symbol "LNil")

private theorem bound_template : PureData.Template program
    (a "MNode" [a "HBound" [v "index"], .symbol "LNil"]) :=
  mnode_template _ _ (unary_template "HBound" "index" (by decide +kernel) (by decide)) (.symbol "LNil")

private theorem application_template (mode : Lowering) : PureData.Template program
    (a "MNode" [a "HApp" [v "head", v "arity"], v mode.childrenName]) := by
  apply mnode_template _ _ _ (.captured _)
  apply PureData.Template.constructor "HApp" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem term_application (mode : Lowering) (head : String) (children : List PatternPlan) :
    mode.term (.application head children) = .application "MNode"
      [.application "HApp" [.string head, .natural children.length], encodeList (mode.term) children] := by
  cases mode <;> simp [MatchAutomataCompilationExecution.shapeTerm_node,
    MatchAutomataCompilationExecution.subjectTerm_node, Function.comp_def]

mutual
  private theorem lowering_body_returns (mode : Lowering) (state : State) (plan : PatternPlan) :
      PureReturns program (environment mode.scalar (patternValue plan)) state
        (equation mode.scalar).body state (CettaWireAtom.encode (mode.term plan)) := by
    cases plan with
    | metavariable name =>
        let bindings := environment mode.scalar (patternValue (.metavariable name))
        let selected := ("name", CettaWireAtom.encode (.string name)) :: bindings
        rw [lowering_shape]
        apply case_returns program bindings selected state state state (v "p")
          (patternValue (.metavariable name)) mode.freeBody _ _ mode.cases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "p"
        · simp [Lowering.cases, patternValue, PatternPlan.erase, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            Subst.lookup, selected, bindings, environment]
        · have returned := PureData.template_return program selected state _ (free_template mode)
          cases mode <;> simpa [Lowering.term, Lowering.freeBody,
            MatchAutomataCompilationExecution.shapeTerm, MatchAutomataCompilationExecution.subjectTerm,
            MatchAutomataCompilationExecution.subjectTerms, listValue, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            selected, bindings, environment] using returned
    | bound index =>
        let bindings := environment mode.scalar (patternValue (.bound index))
        let selected := ("index", CettaWireAtom.encode (.natural index)) :: bindings
        rw [lowering_shape]
        apply case_returns program bindings selected state state state (v "p") (patternValue (.bound index))
          (a "MNode" [a "HBound" [v "index"], .symbol "LNil"]) _ _ mode.cases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "p"
        · simp [Lowering.cases, patternValue, PatternPlan.erase, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            Subst.lookup, selected, bindings, environment]
        · have returned := PureData.template_return program selected state _ bound_template
          cases mode <;> simpa [Lowering.term, MatchAutomataCompilationExecution.shapeTerm,
            MatchAutomataCompilationExecution.shapeTerms, MatchAutomataCompilationExecution.subjectTerm,
            MatchAutomataCompilationExecution.subjectTerms, encodeList, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
            selected, bindings, environment] using returned
    | application head children =>
        let values := children.map (fun plan => InferenceCettaWire.encodePattern plan.erase)
        let bindings := environment mode.scalar (patternValue (.application head children))
        let selected := ("children", listValue values) :: ("head", CettaWireAtom.encode (.string head)) :: bindings
        let arityValue := CettaWireAtom.encode (.natural children.length)
        let arityBound := ("arity", arityValue) :: selected
        let loweredValue := listValue (children.map mode.term)
        let loweredBound := (mode.childrenName, loweredValue) :: arityBound
        rw [lowering_shape]
        apply case_returns program bindings selected state state state (v "p")
          (patternValue (.application head children)) mode.applicationBody _ _ mode.cases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "p"
        · simp [Lowering.cases, patternValue, PatternPlan.erase, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, pattern_values,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
            selected, bindings, environment, values]
        · have lengthReturned : PureReturns program selected state
              (a "gslt:automata:length" [v "children"]) state arityValue := by
            simpa [values, arityValue] using MatchAutomataSourceExecution.length_captured_returns selected state values
              (v "children") (by simp [selected, applySubst, Subst.lookup])
          have lengthMatched : SpaceSemantics.matchBinding selected (v "arity") arityValue = some arityBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, arityBound, selected, bindings, environment]
          have loweredReturned := helper_call mode.vector arityBound state (v "children") (listValue values)
            loweredValue (by simp [arityBound, selected, applySubst, Subst.lookup])
            (by simpa only [values] using lowering_vector_body_returns mode state children)
          have loweredMatched : SpaceSemantics.matchBinding arityBound (v mode.childrenName) loweredValue = some loweredBound := by
            cases mode <;> simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, loweredBound,
              arityBound, selected, bindings, environment, Lowering.childrenName]
          have resultReturned : PureReturns program loweredBound state
              (a "MNode" [a "HApp" [v "head", v "arity"], v mode.childrenName]) state
              (CettaWireAtom.encode (mode.term (.application head children))) := by
            have returned := PureData.template_return program loweredBound state _ (application_template mode)
            cases mode <;> simpa [term_application, Lowering.childrenName, loweredBound, loweredValue,
              arityBound, arityValue, selected, bindings, environment, listValue,
              encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
              applySubst.applySubstList, Subst.lookup] using returned
          have computed := PureData.let_bindings_return
            (PureData.BindingsReturn.cons lengthReturned lengthMatched
              (PureData.BindingsReturn.cons loweredReturned loweredMatched (.nil loweredBound state))) state
            (a "MNode" [a "HApp" [v "head", v "arity"], v mode.childrenName]) _ resultReturned
          simpa only [Lowering.applicationBody, List.map_cons, List.map_nil] using computed

  private theorem lowering_vector_body_returns (mode : Lowering) (state : State) (plans : List PatternPlan) :
      PureReturns program
        (environment mode.vector (listValue (plans.map (fun plan => InferenceCettaWire.encodePattern plan.erase)))) state
        (equation mode.vector).body state (listValue (plans.map mode.term)) := by
    cases plans with
    | nil =>
        let bindings := environment mode.vector (.symbol "LNil")
        rw [lowering_vector_shape]
        apply case_returns program bindings bindings state state state (v "ps") (.symbol "LNil")
          (.symbol "LNil") (.symbol "LNil") _ mode.vectorCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "ps"
        · simp [Lowering.vectorCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · exact symbol_returns program bindings state "LNil"
    | cons first rest =>
        let values := (first :: rest).map (fun plan => InferenceCettaWire.encodePattern plan.erase)
        let bindings := environment mode.vector (listValue values)
        let selected := ("rest", listValue (rest.map (fun plan => InferenceCettaWire.encodePattern plan.erase))) ::
          ("p", patternValue first) :: bindings
        let headValue := CettaWireAtom.encode (mode.term first)
        let headBound := ("head", headValue) :: selected
        let tailValue := listValue (rest.map mode.term)
        let tailBound := ("tail", tailValue) :: headBound
        rw [lowering_vector_shape]
        apply case_returns program bindings selected state state state (v "ps") (listValue values)
          mode.vectorBody _ _ mode.vectorCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup] using variable_returns program bindings state "ps"
        · simp [Lowering.vectorCases, listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selected, bindings, environment, values, patternValue]
        · have headReturned := helper_call mode.scalar selected state (v "p") (patternValue first) headValue
            (by simp [selected, applySubst, Subst.lookup]) (lowering_body_returns mode state first)
          have headMatched : SpaceSemantics.matchBinding selected (v "head") headValue = some headBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, selected, bindings, environment]
          have tailReturned := helper_call mode.vector headBound state (v "rest")
            (listValue (rest.map (fun plan => InferenceCettaWire.encodePattern plan.erase))) tailValue
            (by simp [headBound, selected, applySubst, Subst.lookup])
            (lowering_vector_body_returns mode state rest)
          have tailMatched : SpaceSemantics.matchBinding headBound (v "tail") tailValue = some tailBound := by
            simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, headBound, selected, bindings, environment]
          have resultReturned : PureReturns program tailBound state (a "LCons" [v "head", v "tail"]) state
              (listValue ((first :: rest).map mode.term)) := by
            simpa [listValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup, tailBound, tailValue,
                headBound, headValue, selected] using
              PureData.template_return program tailBound state _ (pair_template "head" "tail")
          have computed := PureData.let_bindings_return
            (PureData.BindingsReturn.cons headReturned headMatched
              (PureData.BindingsReturn.cons tailReturned tailMatched (.nil tailBound state))) state
            (a "LCons" [v "head", v "tail"]) _ resultReturned
          simpa only [Lowering.vectorBody, List.map_cons, List.map_nil] using computed
end

theorem shape_captured_returns (bindings : Subst) (state : State) (plan : PatternPlan)
    (argument : Atom) (captured : applySubst bindings argument =
      CettaWireAtom.encode (InferenceCettaWire.encodePattern plan.erase)) :
    PureReturns program bindings state (a "gslt:automata:shape" [argument]) state
      (CettaWireAtom.encode (shapeTerm (patternView plan))) :=
  helper_call .shape bindings state argument _ _ captured (lowering_body_returns .pattern state plan)

theorem shape_returns (state : State) (plan : PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:shape" [CettaWireAtom.encode (InferenceCettaWire.encodePattern plan.erase)]) state
      (CettaWireAtom.encode (shapeTerm (patternView plan))) :=
  shape_captured_returns [] state plan _ (by simp)

theorem shapes_captured_returns (bindings : Subst) (state : State) (plans : List PatternPlan)
    (argument : Atom) (captured : applySubst bindings argument =
      CettaWireAtom.encode (InferenceCettaWire.encodePatterns (erasePatterns plans))) :
    PureReturns program bindings state (a "gslt:automata:shapes" [argument]) state
      (listValue (plans.map (fun plan => shapeTerm (patternView plan)))) := by
  apply helper_call .shapes bindings state argument _ _ captured
  simpa only [pattern_values, Lowering.vector, pattern_term] using lowering_vector_body_returns .pattern state plans

theorem shapes_returns (state : State) (plans : List PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:shapes" [CettaWireAtom.encode (InferenceCettaWire.encodePatterns (erasePatterns plans))]) state
      (listValue (plans.map (fun plan => shapeTerm (patternView plan)))) :=
  shapes_captured_returns [] state plans _ (by simp)

theorem subject_captured_returns (bindings : Subst) (state : State) (plan : PatternPlan)
    (argument : Atom) (captured : applySubst bindings argument =
      CettaWireAtom.encode (InferenceCettaWire.encodePattern plan.erase)) :
    PureReturns program bindings state (a "gslt:automata:subject" [argument]) state
      (CettaWireAtom.encode (subjectTerm (subjectView plan))) :=
  helper_call .subject bindings state argument _ _ captured (lowering_body_returns .subject state plan)

theorem subject_returns (state : State) (plan : PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:subject" [CettaWireAtom.encode (InferenceCettaWire.encodePattern plan.erase)]) state
      (CettaWireAtom.encode (subjectTerm (subjectView plan))) :=
  subject_captured_returns [] state plan _ (by simp)

theorem subjects_captured_returns (bindings : Subst) (state : State) (plans : List PatternPlan)
    (argument : Atom) (captured : applySubst bindings argument =
      CettaWireAtom.encode (InferenceCettaWire.encodePatterns (erasePatterns plans))) :
    PureReturns program bindings state (a "gslt:automata:subjects" [argument]) state
      (listValue (plans.map (fun plan => subjectTerm (subjectView plan)))) := by
  apply helper_call .subjects bindings state argument _ _ captured
  simpa only [pattern_values, Lowering.vector, subject_term] using lowering_vector_body_returns .subject state plans

theorem subjects_returns (state : State) (plans : List PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:subjects" [CettaWireAtom.encode (InferenceCettaWire.encodePatterns (erasePatterns plans))]) state
      (listValue (plans.map (fun plan => subjectTerm (subjectView plan)))) :=
  subjects_captured_returns [] state plans _ (by simp)

example (state : State) :
    PureReturns program [] state
      (a "gslt:automata:shape" [CettaWireAtom.encode (.application "FVar" [.string "x"])]) state
      (.symbol "MAny") := by
  simpa [PatternPlan.erase, InferenceCettaWire.encodePattern, InferenceCettaWire.CettaTerm.application,
    MatchAutomataCompilationExecution.shapeTerm, CettaWireAtom.encode] using
    shape_returns state (.metavariable "x")

example : structuralMatch
    (patternView (.application "pair" [.metavariable "x", .bound 0]))
    (subjectView (.application "pair" [.bound 7, .bound 1])) = false := by
  simp [structuralMatch, structuralMatchList]

#print axioms headTerm_injective
#print axioms reference_views
#print axioms subpatterns_returns
#print axioms subpatterns_list_returns
#print axioms unique_acc_returns
#print axioms unique_returns
#print axioms inventory_returns
#print axioms shape_returns
#print axioms shapes_returns
#print axioms subject_returns
#print axioms subjects_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataInventoryExecution
