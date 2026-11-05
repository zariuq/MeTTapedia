import Mettapedia.Languages.MeTTa.PeTTa.Resumption
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderContextualExecution
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Retained first-order contextual rule execution

The retained source performs relative matching and original-seed merging for
recursive premise results. Its recursive depth belongs to the existing
canonical contextual executor. Source profiles and premise projection are
explicit: the current wire admits freshness, congruence and variable-only
relation queries, while scoped-step and quantified premises are refused.
Pattern, binding, rule, and language carriers are reused throughout.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution

open Mettapedia.GSLT.LanguageDef CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (ProviderRow)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst applySubst_nil matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval RuleExecutionProgram
open MatchAutomataBindingExecution (bindingsTerm bindingsOptionTerm matchesTerm boundMatchTerm)
open RelationPremiseExecution (providerEnv providerRowsTerm bindingResultsTerm)
open MeTTaILMatchAutomataExecution (Strategy)
open MeTTaILSubtermMatchAutomata (BoundMatch)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : Term) : Atom := CettaWireAtom.encode value
private abbrev patternValue (value : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern value)
private abbrev patternsValue (values : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns values)
private abbrev bindingsValue (bindings : Bindings) : Atom := encoded (bindingsTerm bindings)
private abbrev resultsValue (results : List Bindings) : Atom := encoded (bindingResultsTerm results)
private abbrev number (value : Nat) : Atom := encoded (.natural value)

def strategyTerm : Strategy → Term
  | .bottomUp => .symbol "MatchBottomUp"
  | .topDown => .symbol "MatchTopDown"

/-- Current source premise profile, refining the canonical structural wire
and the independently proved first-order contextual syntax admission. -/
def variableRelationSourceShape (premise : Premise) : Bool :=
  match premise with
  | .relationQuery _ arguments => (compileArgumentNames? arguments).isSome
  | _ => true

def premiseAdmitted (premise : Premise) : Bool :=
  MeTTaILFirstOrderContextualExecution.premiseAdmitted premise &&
    (CanonicalWire.premiseSupported premise && variableRelationSourceShape premise)

/-- Projection is partial: unsupported authored data has no successful wire. -/
def premiseTerm? (premise : Premise) : Option Term :=
  if premiseAdmitted premise then some (InferenceCettaWire.AuthoredRule.premiseTerm premise) else none

def premisesTerm? : List Premise → Option Term
  | [] => some (.symbol "LNil")
  | premise :: premises => do
      let first ← premiseTerm? premise
      let rest ← premisesTerm? premises
      pure (.application "LCons" [first, rest])

theorem premise_projection_admitted (premise : Premise) (wire : Term)
    (projected : premiseTerm? premise = some wire) : premiseAdmitted premise = true := by
  unfold premiseTerm? at projected
  split at projected
  · assumption
  · simp at projected

theorem premises_projection_admitted (premises : List Premise) (wire : Term)
    (projected : premisesTerm? premises = some wire) : premises.all premiseAdmitted = true := by
  induction premises generalizing wire with
  | nil => rfl
  | cons premise premises ih =>
      cases first : premiseTerm? premise with
      | none => simp [premisesTerm?, first] at projected
      | some firstWire =>
          cases rest : premisesTerm? premises with
          | none => simp [premisesTerm?, first, rest] at projected
          | some restWire =>
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨premise_projection_admitted premise firstWire first,
                ih restWire rest⟩

/-- Admitted premise syntax constructively has an exact physical projection.
The unsupported constructors cannot acquire a successful wire. -/
theorem premise_projection_exists (premise : Premise) (admitted : premiseAdmitted premise = true) :
    ∃ wire, premiseTerm? premise = some wire := by
  exact ⟨InferenceCettaWire.AuthoredRule.premiseTerm premise,
    by simp only [premiseTerm?, admitted, ↓reduceIte]⟩

theorem premises_projection_exists (premises : List Premise)
    (admitted : premises.all premiseAdmitted = true) :
    ∃ wire, premisesTerm? premises = some wire := by
  induction premises with
  | nil => exact ⟨.symbol "LNil", rfl⟩
  | cons premise premises ih =>
      simp only [List.all_cons, Bool.and_eq_true] at admitted
      obtain ⟨head, first⟩ := premise_projection_exists premise admitted.1
      obtain ⟨tail, rest⟩ := ih admitted.2
      exact ⟨.application "LCons" [head, tail], by simp [premisesTerm?, first, rest, Option.bind_eq_bind]⟩

/-- Operational source admission. Equations and binding annotations are not
projected away; this profile requires their existing empty/absent checks.
Successful premise projection below additionally identifies the retained
physical fields of every authored row. -/
def languageAdmitted (language : LanguageDef) : Bool :=
  language.isEquationFree &&
    (MeTTaILFirstOrderContextualExecution.languageAdmitted language &&
      language.rewrites.all fun rule => rule.premises.all premiseAdmitted)

theorem language_admitted_iff (language : LanguageDef) : languageAdmitted language = true ↔
    language.isEquationFree = true ∧
    MeTTaILFirstOrderContextualExecution.languageAdmitted language = true ∧
    language.rewrites.all (fun rule => rule.premises.all premiseAdmitted) = true := by
  simp only [languageAdmitted, Bool.and_eq_true]

private def recursiveEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:recursive-results")[0]'(by decide +kernel)
private def recursiveEnvironment (target : PatternPlan) (candidates : List Pattern)
    (seed : Bindings) : Subst :=
  [("seed", bindingsValue seed), ("candidates", patternsValue candidates),
   ("target", patternValue target.erase)]

private def recursiveMergeCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"),
   (a "Some" [v "extended"], a "LCons" [v "extended", v "tail"])]
private def recursiveMergeBody : Atom :=
  a "case" [a "gslt:automata:merge" [v "seed", v "relative"],
    .expression (recursiveMergeCases.map fun row => .expression [row.1, row.2])]
private def recursiveMatchCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"), (a "Some" [v "relative"], recursiveMergeBody)]
private def recursiveCons : Atom :=
  a "let" [v "tail", a "gslt:rule:recursive-results" [v "target", v "rest", v "seed"],
    a "case" [a "gslt:automata:bind" [v "target", v "candidate"],
      .expression (recursiveMatchCases.map fun row => .expression [row.1, row.2])]]

private def recursiveCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "candidate", v "rest"], recursiveCons)]

private theorem recursive_shape : recursiveEquation.body = a "case"
    [v "candidates", .expression (recursiveCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem recursive_clause (target : PatternPlan) (candidates : List Pattern) (seed : Bindings) :
    clauses program "gslt:rule:recursive-results"
      [patternValue target.erase, patternsValue candidates, bindingsValue seed] =
      [.evaluate (recursiveEnvironment target candidates seed) recursiveEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:recursive-results").filterMap _ = _
  rw [show equations "gslt:rule:recursive-results" = [recursiveEquation] from rfl]
  have formals : recursiveEquation.arguments = [v "target", v "candidates", v "seed"] := by
    decide +kernel
  simp [formals, recursiveEnvironment, v, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem recursive_call (caller : Subst) (state : State) (target : PatternPlan)
    (candidates : List Pattern) (seed : Bindings) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst caller) =
      [patternValue target.erase, patternsValue candidates, bindingsValue seed])
    (returned : PureReturns program (recursiveEnvironment target candidates seed) state
      recursiveEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:recursive-results" arguments) state answer := by
  have length : arguments.length = 3 := by
    have := congrArg List.length captured
    simpa using this
  apply PureData.raw_authored_call_return program caller
    (recursiveEnvironment target candidates seed) state state "gslt:rule:recursive-results"
    arguments recursiveEquation.body answer (by decide) (by decide) (by decide)
    (by decide +kernel) _ _ returned
  · intro index bounded
    rw [length] at bounded
    interval_cases index <;> decide +kernel
  · rw [captured]
    exact recursive_clause target candidates seed

private abbrev recursiveBindings (target : Pattern) (candidates : List Pattern) (seed : Bindings) : List Bindings :=
  candidates.flatMap fun candidate =>
    (matchPattern target candidate).filterMap (mergeBindings seed)

attribute [local simp] a v encoded patternValue patternsValue bindingsValue resultsValue number

private theorem recursive_body_returns (state : State) (target : PatternPlan)
    (candidates : List Pattern) (seed : Bindings)
    (firstOrder : isMatchCorrectListAux candidates = true) :
    PureReturns program (recursiveEnvironment target candidates seed) state
      recursiveEquation.body state (resultsValue (recursiveBindings target.erase candidates seed)) := by
  induction candidates with
  | nil =>
      rw [recursive_shape]
      apply case_returns program (recursiveEnvironment target [] seed)
        (recursiveEnvironment target [] seed) state state state (v "candidates") (.symbol "LNil")
        (.symbol "LNil") _ _ recursiveCases (read_cases_encoded _) _ _ _
      · simpa [recursiveEnvironment, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          applySubst, Subst.lookup] using
          variable_returns program (recursiveEnvironment target [] seed) state "candidates"
      · simp [recursiveCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons candidate candidates ih =>
      simp only [isMatchCorrectListAux, Bool.and_eq_true] at firstOrder
      cases compiled : compilePattern? candidate with
      | none =>
          have same := compilePattern?_isSome_eq_isMatchCorrectAux candidate
          simp only [compiled, Option.isSome_none, firstOrder.1] at same
          cases same
      | some candidatePlan =>
          have erased := erase_of_compilePattern? candidate candidatePlan compiled
          subst candidate
          let caller := recursiveEnvironment target (candidatePlan.erase :: candidates) seed
          let selected := ("rest", patternsValue candidates) ::
            ("candidate", patternValue candidatePlan.erase) :: caller
          let tail := recursiveBindings target.erase candidates seed
          let bound := ("tail", resultsValue tail) :: selected
          have tailReturned := recursive_call selected state target candidates seed
            [v "target", v "rest", v "seed"] _
            (by simp [selected, caller, recursiveEnvironment, applySubst, Subst.lookup]) (ih firstOrder.2)
          have matched := automata_captured_returns
            (show codeWithin RuleExecutionProgram.matcherHead
              (a "gslt:automata:bind" [v "target", v "candidate"]) = true from by decide +kernel)
            (MatchAutomataBindingExecution.bind_captured_returns bound state target candidatePlan
              [v "target", v "candidate"]
              (by simp [bound, selected, caller, recursiveEnvironment, applySubst, Subst.lookup]))
          have singleton := MatchAutomataBindingExecution.bind_matches_singleton target candidatePlan
          rw [recursive_shape]
          apply case_returns program caller selected state state state (v "candidates")
            (patternsValue (candidatePlan.erase :: candidates)) recursiveCons _ _ recursiveCases
            (read_cases_encoded _) _ _ _
          · simpa [caller, recursiveEnvironment, applySubst, Subst.lookup] using
              variable_returns program caller state "candidates"
          · simp [recursiveCases, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, caller, recursiveEnvironment]
          · unfold recursiveCons
            apply let_returns program selected bound state state state (v "tail") _ _ _ _ tailReturned _ _
            · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, tail,
                selected, caller, recursiveEnvironment]
            · cases chosen : (matchPattern target.erase candidatePlan.erase).head? with
              | none =>
                  have empty : matchPattern target.erase candidatePlan.erase = [] := by
                    rw [← singleton, chosen]
                    rfl
                  have emptyReturned : PureReturns program bound state
                      (a "gslt:automata:bind" [v "target", v "candidate"]) state (.symbol "None") := by
                    simpa only [chosen, bindingsOptionTerm, CettaWireAtom.encode] using matched
                  apply case_returns program bound bound state state state _ (.symbol "None") (v "tail") _ _
                    recursiveMatchCases
                    (read_cases_encoded _) emptyReturned _ _
                  · simp [recursiveMatchCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · simpa [recursiveBindings, empty, tail, bound, applySubst, Subst.lookup] using
                      variable_returns program bound state "tail"
              | some relative =>
                  have single : matchPattern target.erase candidatePlan.erase = [relative] := by
                    rw [← singleton, chosen]
                    rfl
                  let relativeBound := ("relative", bindingsValue relative) :: bound
                  have relativeReturned : PureReturns program bound state
                      (a "gslt:automata:bind" [v "target", v "candidate"]) state
                      (a "Some" [bindingsValue relative]) := by
                    simpa only [chosen, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using matched
                  have merged := automata_captured_returns
                    (show codeWithin RuleExecutionProgram.matcherHead
                      (a "gslt:automata:merge" [v "seed", v "relative"]) = true from by decide +kernel)
                    (MatchAutomataBindingExecution.merge_captured_returns relativeBound state seed relative
                      [v "seed", v "relative"]
                      (by simp [relativeBound, bound, selected, caller, recursiveEnvironment,
                        applySubst, Subst.lookup]))
                  apply case_returns program bound relativeBound state state state _
                    (a "Some" [bindingsValue relative]) recursiveMergeBody _ _
                    recursiveMatchCases
                    (read_cases_encoded _) relativeReturned _ _
                  · simp [recursiveMatchCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, relativeBound,
                      bound, selected, caller, recursiveEnvironment]
                  · unfold recursiveMergeBody
                    cases combined : mergeBindings seed relative with
                    | none =>
                        have refused : PureReturns program relativeBound state
                            (a "gslt:automata:merge" [v "seed", v "relative"]) state (.symbol "None") := by
                          simpa only [combined, bindingsOptionTerm, CettaWireAtom.encode] using merged
                        apply case_returns program relativeBound relativeBound state state state _
                          (.symbol "None") (v "tail") _ _
                          recursiveMergeCases
                          (read_cases_encoded _) refused _ _
                        · simp [recursiveMergeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                        · simpa [recursiveBindings, single, combined, tail, relativeBound, bound,
                            applySubst, Subst.lookup] using variable_returns program relativeBound state "tail"
                    | some extended =>
                        let extendedBound := ("extended", bindingsValue extended) :: relativeBound
                        have accepted : PureReturns program relativeBound state
                            (a "gslt:automata:merge" [v "seed", v "relative"]) state
                            (a "Some" [bindingsValue extended]) := by
                          simpa only [combined, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using merged
                        apply case_returns program relativeBound extendedBound state state state _
                          (a "Some" [bindingsValue extended]) (a "LCons" [v "extended", v "tail"]) _ _
                          recursiveMergeCases
                          (read_cases_encoded _) accepted _ _
                        · simp [recursiveMergeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, extendedBound,
                            relativeBound, bound, selected, caller, recursiveEnvironment]
                        · simpa [recursiveBindings, single, combined, tail, bindingResultsTerm, encodeList,
                            CettaWireAtom.encode, CettaWireAtom.encodeMany,
                            extendedBound, relativeBound, bound, applySubst, Subst.lookup] using
                            constructor_variables_return program extendedBound state "LCons" ["extended", "tail"]
                              (by decide +kernel) (by decide)

/-- Actual recursive-candidate matching retains the canonical relative match
and original-seed merge, including successful duplicate candidates. -/
theorem recursive_results_captured_returns (caller : Subst) (state : State)
    (target : PatternPlan) (candidates : List Pattern) (seed : Bindings)
    (firstOrder : isMatchCorrectListAux candidates = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [patternValue target.erase, patternsValue candidates, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:recursive-results" arguments) state
      (resultsValue (candidates.flatMap fun candidate =>
        (matchPattern target.erase candidate).filterMap (mergeBindings seed))) :=
  recursive_call caller state target candidates seed arguments _ captured
    (recursive_body_returns state target candidates seed firstOrder)

theorem recursive_results_returns (state : State) (target : PatternPlan)
    (candidates : List Pattern) (seed : Bindings)
    (firstOrder : isMatchCorrectListAux candidates = true) :
    PureReturns program [] state (a "gslt:rule:recursive-results"
      [patternValue target.erase, patternsValue candidates, bindingsValue seed]) state
      (resultsValue (candidates.flatMap fun candidate =>
        (matchPattern target.erase candidate).filterMap (mergeBindings seed))) :=
  recursive_results_captured_returns [] state target candidates seed firstOrder _ (by simp)

/-! ## Source dispatch metadata for six raw arguments -/

private inductive ContextHelper where | premises | results | applyMatch | matches

private def ContextHelper.head : ContextHelper → String
  | .premises => "gslt:rule:premises-at"
  | .results => "gslt:rule:premise-results-at"
  | .applyMatch => "gslt:rule:apply-root-match-at"
  | .matches => "gslt:rule:matched-root-reducts-at"

private def ContextHelper.names : ContextHelper → List String
  | .premises => ["strategy", "language", "rows", "depth", "premises", "seed"]
  | .results => ["strategy", "language", "rows", "depth", "premises", "results"]
  | .applyMatch => ["strategy", "language", "rewrites", "rows", "depth", "matched"]
  | .matches => ["strategy", "language", "rewrites", "rows", "depth", "matches"]

private def contextEquation (helper : ContextHelper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)

private def contextEnvironment (helper : ContextHelper) (one two three four five six : Atom) : Subst :=
  (helper.names.zip [one, two, three, four, five, six]).reverse

private theorem context_clause (helper : ContextHelper) (one two three four five six : Atom) :
    clauses program helper.head [one, two, three, four, five, six] =
      [.evaluate (contextEnvironment helper one two three four five six) (contextEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [contextEquation helper] from by cases helper <;> rfl]
  have formals : (contextEquation helper).arguments = helper.names.map Atom.var := by
    cases helper <;> decide +kernel
  cases helper <;> simp [formals, ContextHelper.names, contextEnvironment,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem context_call (helper : ContextHelper) (caller : Subst) (state : State)
    (one two three four five six : Atom) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst caller) = [one, two, three, four, five, six])
    (returned : PureReturns program (contextEnvironment helper one two three four five six) state
      (contextEquation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  have length : arguments.length = 6 := by
    have := congrArg List.length captured
    simpa using this
  apply PureData.raw_authored_call_return program caller
    (contextEnvironment helper one two three four five six) state state helper.head
    arguments (contextEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    rw [length] at bounded
    interval_cases index <;> cases helper <;> decide +kernel
  · rw [captured]
    exact context_clause helper one two three four five six

private theorem source_capture {before after : State} {head : String} {one two : List Atom}
    {caller : Subst} {answer : Atom}
    (dispatch : program.equations.any (·.head == head) = true)
    (raw : ∀ index < one.length, argumentIsRaw program head index = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (captured : one = two.map (applySubst caller))
    (returned : PureReturns program [] before (a head one) after answer) :
    PureReturns program caller before (a head two) after answer := by
  apply PureData.raw_capture_returns program [] caller before after head one two answer
    (by simp [dispatch]) raw ordinary _ returned
  have empty : applySubst [] = id := funext applySubst_nil
  simpa only [empty, List.map_id] using captured

private theorem append_patterns_return (caller : Subst) (state : State)
    (left right : List Pattern)
    (captured : [v "head", v "tail"].map (applySubst caller) = [patternsValue left, patternsValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v "head", v "tail"]) state
      (patternsValue (left ++ right)) := by
  have canonical (patterns : List Pattern) : InferenceCettaWire.encodePatterns patterns =
      encodeList id (patterns.map InferenceCettaWire.encodePattern) := by
    rw [InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map]
    rfl
  apply automata_captured_returns (by decide +kernel)
  simpa only [patternsValue, encoded, canonical, List.map_append, MatchAutomataSourceExecution.listValue] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map InferenceCettaWire.encodePattern) (right.map InferenceCettaWire.encodePattern)
      (v "head") (v "tail") (by simpa only [patternsValue, encoded, canonical,
        MatchAutomataSourceExecution.listValue] using captured)

private theorem append_bindings_return (caller : Subst) (state : State)
    (left right : List Bindings)
    (captured : [v "head", v "tail"].map (applySubst caller) = [resultsValue left, resultsValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v "head", v "tail"]) state
      (resultsValue (left ++ right)) := by
  have canonical (results : List Bindings) : bindingResultsTerm results =
      encodeList id (results.map bindingsTerm) := by
    simp only [bindingResultsTerm, encodeList_map]
    rfl
  apply automata_captured_returns (by decide +kernel)
  simpa only [resultsValue, encoded, canonical, List.map_append, MatchAutomataSourceExecution.listValue] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map bindingsTerm) (right.map bindingsTerm) (v "head") (v "tail")
      (by simpa only [resultsValue, encoded, canonical, MatchAutomataSourceExecution.listValue] using captured)

private abbrev languageWire (language : LanguageDef) (types terms : Term)
    (contexts premises : RewriteRule → Term) : Term :=
  MatchAutomataExecution.matchingProjectionTerm language types terms (.symbol "LNil") contexts premises

private abbrev recursiveStep (rows : List ProviderRow) (language : LanguageDef) (depth : Nat) : Pattern → List Pattern :=
  Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
    RuleInterpretation.syntactic (engineBasePremises (providerEnv rows)) language depth

private abbrev executePremises (rows : List ProviderRow) (language : LanguageDef) (depth : Nat)
    (premises : List Premise) (seed : Bindings) : List Bindings :=
  premisesUsing (engineBasePremises (providerEnv rows)) language (recursiveStep rows language depth) premises seed

private abbrev premiseEnvironment (helper : ContextHelper) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (depth : Nat) (premises : Term) (last : Atom) : Subst :=
  contextEnvironment helper (encoded (strategyTerm strategy))
    (encoded (languageWire language types terms contexts fields))
    (encoded (providerRowsTerm rows)) (number depth) (encoded premises) last

private def resultsAtPairs : List (Atom × Atom) :=
  [(v "head", a "gslt:rule:premises-at" [v "strategy", v "language", v "rows", v "depth", v "premises", v "seed"]),
   (v "tail", a "gslt:rule:premise-results-at" [v "strategy", v "language", v "rows", v "depth", v "premises", v "rest"])]
private def resultsAtResult : Atom := a "gslt:automata:append" [v "head", v "tail"]
private def resultsAtCons : Atom :=
  a "let*" [.expression (resultsAtPairs.map fun pair => .expression [pair.1, pair.2]), resultsAtResult]
private def resultsAtCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "seed", v "rest"], resultsAtCons)]

private theorem resultsAt_shape : (contextEquation .results).body =
    a "case" [v "results", .expression (resultsAtCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem resultsAt_body_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat)
    (premises : List Premise) (wire : Term)
    (allSeeds : ∀ seed, FirstOrderBindings seed →
      PureReturns program (premiseEnvironment .premises strategy language types terms contexts fields
        rows depth wire (bindingsValue seed)) state (contextEquation .premises).body state
        (resultsValue (executePremises rows language depth premises seed)))
    (results : List Bindings) (resultsFirstOrder : ∀ seed ∈ results, FirstOrderBindings seed) :
    PureReturns program (premiseEnvironment .results strategy language types terms contexts fields
      rows depth wire (resultsValue results)) state (contextEquation .results).body state
      (resultsValue (results.flatMap (executePremises rows language depth premises))) := by
  induction results with
  | nil =>
      let caller := premiseEnvironment .results strategy language types terms contexts fields rows depth wire (resultsValue [])
      rw [resultsAt_shape]
      apply case_returns program caller caller state state state (v "results") (.symbol "LNil")
        (.symbol "LNil") _ _ resultsAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, premiseEnvironment, contextEnvironment, ContextHelper.names,
          bindingResultsTerm, encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "results"
      · simp [resultsAtCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons seed results ih =>
      let caller := premiseEnvironment .results strategy language types terms contexts fields rows depth wire
        (resultsValue (seed :: results))
      let selected := ("rest", resultsValue results) :: ("seed", bindingsValue seed) :: caller
      let headResults := executePremises rows language depth premises seed
      let tailResults := results.flatMap (executePremises rows language depth premises)
      let headBound := ("head", resultsValue headResults) :: selected
      let tailBound := ("tail", resultsValue tailResults) :: headBound
      have headReturned := context_call .premises selected state
        (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
        (encoded (providerRowsTerm rows)) (number depth) (encoded wire) (bindingsValue seed)
        [v "strategy", v "language", v "rows", v "depth", v "premises", v "seed"] _
        (by simp [selected, caller, contextEnvironment, ContextHelper.names,
          applySubst, Subst.lookup]) (allSeeds seed (resultsFirstOrder seed (by simp)))
      have tailReturned := context_call .results headBound state
        (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
        (encoded (providerRowsTerm rows)) (number depth) (encoded wire) (resultsValue results)
        [v "strategy", v "language", v "rows", v "depth", v "premises", v "rest"] _
        (by simp [headBound, selected, caller, contextEnvironment, ContextHelper.names,
          applySubst, Subst.lookup]) (ih (fun next member => resultsFirstOrder next (by simp [member])))
      rw [resultsAt_shape]
      apply case_returns program caller selected state state state (v "results")
        (resultsValue (seed :: results)) resultsAtCons _ _ resultsAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, premiseEnvironment, contextEnvironment, ContextHelper.names,
          applySubst, Subst.lookup] using variable_returns program caller state "results"
      · simp [resultsAtCases, bindingResultsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, contextEnvironment, ContextHelper.names]
      · have computed : PureData.BindingsReturn program selected state resultsAtPairs tailBound state := by
          apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, selected,
              caller, contextEnvironment, ContextHelper.names, headResults]
          apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, headBound, selected,
              caller, contextEnvironment, ContextHelper.names, tailResults]
          exact .nil _ _
        have appended := append_bindings_return tailBound state headResults tailResults
          (by simp [tailBound, headBound, applySubst, Subst.lookup])
        simpa only [resultsAtCons, resultsAtResult, List.flatMap_cons] using
          PureData.let_bindings_return computed state resultsAtResult _ appended

private theorem lcons_template {head tail : Atom}
    (headTemplate : PureData.Template program head) (tailTemplate : PureData.Template program tail) :
    PureData.Template program (a "LCons" [head, tail]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact headTemplate
  · exact tailTemplate

private def premisesAtRelationPairs : List (Atom × Atom) :=
  [(v "names", a "gslt:rule:argument-names" [v "arguments"]),
   (v "choices", a "gslt:rule:relation-query" [v "relation", v "names", v "rows", v "seed"])]
private def premisesAtRecursivePairs : List (Atom × Atom) :=
  [(v "instance", a "gslt:rule:instantiate" [v "source", v "seed"]),
   (v "candidates", a "gslt:rule:language-contextual-reducts"
     [v "strategy", v "language", v "rows", v "depth", v "instance"]),
   (v "choices", a "gslt:rule:recursive-results" [v "target", v "candidates", v "seed"])]
private def premisesAtContinue : Atom :=
  a "gslt:rule:premise-results-at"
    [v "strategy", v "language", v "rows", v "depth", v "rest", v "choices"]
private def premisesAtFreshness : Atom :=
  a "let" [v "choices", a "gslt:premise:freshness" [v "name", v "term", v "seed"],
    premisesAtContinue]
private def premisesAtRelation : Atom :=
  a "let*" [.expression (premisesAtRelationPairs.map fun pair => .expression [pair.1, pair.2]), premisesAtContinue]
private def premisesAtRecursive : Atom :=
  a "let*" [.expression (premisesAtRecursivePairs.map fun pair => .expression [pair.1, pair.2]), premisesAtContinue]
private def premisesAtCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "LCons" [v "seed", .symbol "LNil"]),
   (a "LCons" [a "Freshness" [v "name", v "term"], v "rest"], premisesAtFreshness),
   (a "LCons" [a "RelationQuery" [v "relation", v "arguments"], v "rest"], premisesAtRelation),
   (a "LCons" [a "Congruence" [v "source", v "target"], v "rest"], premisesAtRecursive)]
private theorem premisesAt_shape : (contextEquation .premises).body =
    a "case" [v "premises", .expression (premisesAtCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private abbrev reentryReturns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat) : Prop :=
  ∀ subject : PatternPlan, PureReturns program [] state
    (a "gslt:rule:language-contextual-reducts" [encoded (strategyTerm strategy),
      encoded (languageWire language types terms contexts fields), encoded (providerRowsTerm rows),
      number depth, patternValue subject.erase]) state
    (patternsValue (recursiveStep rows language depth subject.erase))

private theorem recursive_step_firstOrder (rows : List ProviderRow) (language : LanguageDef)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (languageAdmitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true)
    (depth : Nat) : ∀ source, isMatchCorrectAux source = true →
      ∀ target ∈ recursiveStep rows language depth source, isMatchCorrectAux target = true :=
  MeTTaILFirstOrderContextualExecution.rewriteAt_firstOrder (providerEnv rows)
    (RuleTraceExecution.providerEnv_firstOrder rows providerAdmitted) language languageAdmitted depth

private theorem premise_choices_firstOrder (rows : List ProviderRow) (language : LanguageDef)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (languageAdmitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true)
    (depth : Nat) (premise : Premise) (admitted : premiseAdmitted premise = true)
    (seed : Bindings) (seedFirstOrder : FirstOrderBindings seed) :
    ∀ result ∈ premiseStepUsing (engineBasePremises (providerEnv rows)) language
      (recursiveStep rows language depth) seed premise, FirstOrderBindings result :=
  MeTTaILFirstOrderContextualExecution.premiseStepUsing_bindings_firstOrder (providerEnv rows)
    (RuleTraceExecution.providerEnv_firstOrder rows providerAdmitted) language _
    (recursive_step_firstOrder rows language providerAdmitted languageAdmitted depth)
    seed seedFirstOrder premise (by
      have parts : MeTTaILFirstOrderContextualExecution.premiseAdmitted premise = true ∧
          CanonicalWire.premiseSupported premise = true := by
        have checked := admitted
        simp only [premiseAdmitted, Bool.and_eq_true] at checked
        exact ⟨checked.1, checked.2.1⟩
      exact parts.1)

private theorem premisesAt_body_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (languageAdmitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true)
    (reentry : reentryReturns state strategy language types terms contexts fields rows depth)
    (premises : List Premise) : ∀ wire, premisesTerm? premises = some wire →
    ∀ seed, FirstOrderBindings seed →
      PureReturns program (premiseEnvironment .premises strategy language types terms contexts fields
        rows depth wire (bindingsValue seed)) state (contextEquation .premises).body state
        (resultsValue (executePremises rows language depth premises seed)) := by
  induction premises with
  | nil =>
      intro wire projected seed seedFirstOrder
      simp only [premisesTerm?, Option.some.injEq] at projected
      subst wire
      let caller := premiseEnvironment .premises strategy language types terms contexts fields
        rows depth (.symbol "LNil") (bindingsValue seed)
      rw [premisesAt_shape]
      apply case_returns program caller caller state state state (v "premises") (.symbol "LNil")
        (a "LCons" [v "seed", .symbol "LNil"]) _ _ premisesAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, contextEnvironment, ContextHelper.names, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "premises"
      · simp [premisesAtCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [caller, contextEnvironment, ContextHelper.names, executePremises, premisesUsing,
          bindingResultsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using PureData.template_return program caller state
          (a "LCons" [v "seed", .symbol "LNil"]) (lcons_template (.captured _) (.symbol _))
  | cons premise premises ih =>
      intro wire projected seed seedFirstOrder
      cases first : premiseTerm? premise with
      | none => simp [premisesTerm?, first] at projected
      | some firstWire =>
        cases rest : premisesTerm? premises with
        | none => simp [premisesTerm?, first, rest] at projected
        | some restWire =>
          simp [premisesTerm?, first, rest, Option.bind_eq_bind] at projected
          subst wire
          have admitted := premise_projection_admitted premise firstWire first
          have allSeeds := ih restWire rest
          have choicesFirstOrder := premise_choices_firstOrder rows language providerAdmitted
            languageAdmitted depth premise admitted seed seedFirstOrder
          cases premise with
          | freshness condition =>
            have termAdmitted : isMatchCorrectAux condition.term = true := by
              have parts : MeTTaILFirstOrderContextualExecution.premiseAdmitted (.freshness condition) = true ∧
                  CanonicalWire.premiseSupported (.freshness condition) = true := by
                have checked := admitted
                simp only [premiseAdmitted, Bool.and_eq_true] at checked
                exact ⟨checked.1, checked.2.1⟩
              exact parts.1
            cases compiled : compilePattern? condition.term with
            | none =>
                have supported := compilePattern?_isSome_eq_isMatchCorrectAux condition.term
                simp [compiled, termAdmitted] at supported
            | some plan =>
              have erased := erase_of_compilePattern? condition.term plan compiled
              have firstShape : firstWire = .application "Freshness"
                  [.string condition.varName, InferenceCettaWire.encodePattern condition.term] := by
                simpa only [premiseTerm?, admitted, ↓reduceIte,
                  InferenceCettaWire.AuthoredRule.premiseTerm, Option.some.injEq] using first.symm
              subst firstWire
              let wire : Term := .application "LCons" [.application "Freshness"
                [.string condition.varName, InferenceCettaWire.encodePattern condition.term], restWire]
              let caller := premiseEnvironment .premises strategy language types terms contexts fields
                rows depth wire (bindingsValue seed)
              let selected := ("rest", encoded restWire) :: ("term", patternValue condition.term) ::
                ("name", encoded (.string condition.varName)) :: caller
              let choices := Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv
                (providerEnv rows) language seed (.freshness condition)
              let choicesBound := ("choices", resultsValue choices) :: selected
              have sameChoices : choices = premiseStepUsing (engineBasePremises (providerEnv rows))
                  language (recursiveStep rows language depth) seed (.freshness condition) := by
                rfl
              have choicesReturned := PremiseOperationsExecution.freshness_captured_returns selected state
                (providerEnv rows) language condition.varName plan seed (v "name") (v "term") (v "seed")
                (by simp [selected, caller, contextEnvironment, ContextHelper.names, erased,
                  applySubst, Subst.lookup])
              have continued := context_call .results choicesBound state
                (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
                (encoded (providerRowsTerm rows)) (number depth) (encoded restWire) (resultsValue choices)
                [v "strategy", v "language", v "rows", v "depth", v "rest", v "choices"] _
                (by simp [choicesBound, selected, caller, contextEnvironment,
                  ContextHelper.names, applySubst, Subst.lookup])
                (resultsAt_body_returns state strategy language types terms contexts fields rows depth
                  premises restWire allSeeds choices (by rw [sameChoices]; exact choicesFirstOrder))
              rw [premisesAt_shape]
              apply case_returns program caller selected state state state (v "premises") (encoded wire)
                premisesAtFreshness _ _ premisesAtCases (read_cases_encoded _) _ _ _
              · simpa [caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup] using
                  variable_returns program caller state "premises"
              · simp [premisesAtCases, wire, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, selected, caller, contextEnvironment, ContextHelper.names]
              · unfold premisesAtFreshness
                apply let_returns program selected choicesBound state state state (v "choices") _ _
                  (resultsValue choices) _
                · simpa only [erased, choices] using choicesReturned
                · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, selected,
                    caller, contextEnvironment, ContextHelper.names]
                · simpa only [premisesAtContinue, ContextHelper.head, executePremises, premisesUsing, sameChoices] using continued
          | forAll collection variableName nested =>
              simp [premiseAdmitted, CanonicalWire.premiseSupported] at admitted
          | scopedStep step =>
              simp [premiseAdmitted, CanonicalWire.premiseSupported] at admitted
          | relationQuery relation arguments =>
            have argumentAdmitted : (compileArgumentNames? arguments).isSome = true := by
              have checked := admitted
              simp only [premiseAdmitted, Bool.and_eq_true] at checked
              exact checked.2.2
            cases accepted : compileArgumentNames? arguments with
            | none => simp [accepted] at argumentAdmitted
            | some names =>
              have erased := compileArgumentNames?_erase arguments names accepted
              rw [← erased] at first
              have admittedNames : premiseAdmitted (.relationQuery relation (names.map Pattern.fvar)) = true := by
                simpa only [erased] using admitted
              have firstShape : firstWire = .application "RelationQuery"
                  [.string relation, InferenceCettaWire.encodePatterns (names.map Pattern.fvar)] := by
                simpa only [premiseTerm?, admittedNames, ↓reduceIte, InferenceCettaWire.AuthoredRule.premiseTerm, Option.some.injEq] using first.symm
              subst firstWire
              let plan : VariablePremisePlan := ⟨relation, names⟩
              let wire : Term := .application "LCons" [.application "RelationQuery"
                [.string relation, InferenceCettaWire.encodePatterns (names.map Pattern.fvar)], restWire]
              let caller := premiseEnvironment .premises strategy language types terms contexts fields
                rows depth wire (bindingsValue seed)
              let selected := ("rest", encoded restWire) ::
                ("arguments", patternsValue (names.map Pattern.fvar)) ::
                ("relation", encoded (.string relation)) :: caller
              let namesBound := ("names", encoded (RelationPremiseExecution.namesTerm names)) :: selected
              let choices := plan.run (providerEnv rows) language seed
              let choicesBound := ("choices", resultsValue choices) :: namesBound
              have sameChoices : choices = premiseStepUsing (engineBasePremises (providerEnv rows))
                  language (recursiveStep rows language depth) seed (.relationQuery relation arguments) := by
                simpa only [choices, VariablePremisePlan.toPlan_run,
                  VariablePremisePlan.toPlan_erase, plan, VariablePremisePlan.erase, erased] using
                  PremisePlan.run_eq_premiseStepUsing (providerEnv rows) language
                    (recursiveStep rows language depth) seed plan.toPlan
              have namesReturned := RelationPremiseExecution.argument_names_captured_returns selected state names
                (v "arguments") (by simp [selected, caller, contextEnvironment, ContextHelper.names,
                  applySubst, Subst.lookup])
              have choicesReturned := RelationPremiseExecution.relation_query_captured_returns namesBound state
                language rows plan seed (v "relation") (v "names") (v "rows") (v "seed")
                (by simp [namesBound, selected, caller, contextEnvironment, ContextHelper.names,
                  plan, applySubst, Subst.lookup])
              have continued := context_call .results choicesBound state
                (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
                (encoded (providerRowsTerm rows)) (number depth) (encoded restWire) (resultsValue choices)
                [v "strategy", v "language", v "rows", v "depth", v "rest", v "choices"] _
                (by simp [choicesBound, namesBound, selected, caller, contextEnvironment,
                  ContextHelper.names, applySubst, Subst.lookup])
                (resultsAt_body_returns state strategy language types terms contexts fields rows depth
                  premises restWire allSeeds choices (by rw [sameChoices]; exact choicesFirstOrder))
              rw [premisesAt_shape]
              apply case_returns program caller selected state state state (v "premises") (encoded wire)
                premisesAtRelation _ _ premisesAtCases (read_cases_encoded _) _ _ _
              · simpa [caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup] using
                  variable_returns program caller state "premises"
              · simp [premisesAtCases, wire, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, selected, caller, contextEnvironment, ContextHelper.names]
              · have computed : PureData.BindingsReturn program selected state premisesAtRelationPairs
                    choicesBound state := by
                  apply PureData.BindingsReturn.cons (bound := namesBound) namesReturned
                  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, namesBound, selected,
                      caller, contextEnvironment, ContextHelper.names]
                  apply PureData.BindingsReturn.cons (bound := choicesBound) choicesReturned
                  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, namesBound,
                      selected, caller, contextEnvironment, ContextHelper.names, choices]
                  exact .nil _ _
                simpa only [premisesAtRelation, executePremises, premisesUsing, sameChoices] using
                  PureData.let_bindings_return computed state premisesAtContinue _ continued
          | congruence source target =>
            have syntaxAdmitted : isMatchCorrectAux source = true ∧ isMatchCorrectAux target = true := by
              have parts : MeTTaILFirstOrderContextualExecution.premiseAdmitted (.congruence source target) = true ∧
                  CanonicalWire.premiseSupported (.congruence source target) = true := by
                have checked := admitted
                simp only [premiseAdmitted, Bool.and_eq_true] at checked
                exact ⟨checked.1, checked.2.1⟩
              simpa only [MeTTaILFirstOrderContextualExecution.premiseAdmitted, Bool.and_eq_true] using parts.1
            cases sourceAccepted : compilePattern? source with
            | none =>
                have supported := compilePattern?_isSome_eq_isMatchCorrectAux source
                simp [sourceAccepted, syntaxAdmitted.1] at supported
            | some sourcePlan =>
              cases targetAccepted : compilePattern? target with
              | none =>
                  have supported := compilePattern?_isSome_eq_isMatchCorrectAux target
                  simp [targetAccepted, syntaxAdmitted.2] at supported
              | some targetPlan =>
                have sourceErased := erase_of_compilePattern? source sourcePlan sourceAccepted
                have targetErased := erase_of_compilePattern? target targetPlan targetAccepted
                have firstShape : firstWire = .application "Congruence"
                    [InferenceCettaWire.encodePattern source, InferenceCettaWire.encodePattern target] := by
                  simpa only [premiseTerm?, admitted, ↓reduceIte, InferenceCettaWire.AuthoredRule.premiseTerm, Option.some.injEq] using first.symm
                subst firstWire
                let wire : Term := .application "LCons" [.application "Congruence"
                  [InferenceCettaWire.encodePattern source, InferenceCettaWire.encodePattern target], restWire]
                let caller := premiseEnvironment .premises strategy language types terms contexts fields
                  rows depth wire (bindingsValue seed)
                let selected := ("rest", encoded restWire) :: ("target", patternValue target) ::
                  ("source", patternValue source) :: caller
                let instantiated := sourcePlan.instantiate seed
                let instanceBound := ("instance", patternValue instantiated) :: selected
                let candidates := recursiveStep rows language depth instantiated
                let candidatesBound := ("candidates", patternsValue candidates) :: instanceBound
                let choices := recursiveBindings target candidates seed
                let choicesBound := ("choices", resultsValue choices) :: candidatesBound
                have instanceFirstOrder := sourcePlan.instantiate_firstOrder seed seedFirstOrder
                change isMatchCorrectAux instantiated = true at instanceFirstOrder
                cases instanceAccepted : compilePattern? instantiated with
                | none =>
                    have supported := compilePattern?_isSome_eq_isMatchCorrectAux instantiated
                    simp [instanceAccepted, instanceFirstOrder] at supported
                | some instancePlan =>
                  have instanceErased := erase_of_compilePattern? instantiated instancePlan instanceAccepted
                  have candidatesFirstOrder : isMatchCorrectListAux candidates = true := by
                    apply (Mettapedia.OSLF.MeTTaIL.MatchSpec.isMatchCorrectListAux_iff_forall candidates).mpr
                    exact recursive_step_firstOrder rows language providerAdmitted languageAdmitted
                      depth instantiated instanceFirstOrder
                  have sameChoices : choices = premiseStepUsing (engineBasePremises (providerEnv rows))
                      language (recursiveStep rows language depth) seed (.congruence source target) := by
                    simp only [choices, recursiveBindings, premiseStepUsing, candidates, instantiated,
                      instantiate_eq_applyBindings, sourceErased]
                  have instanceReturned := RuleInstantiationExecution.instantiate_captured_returns selected state
                    seed sourcePlan (v "source") (v "seed")
                    (by simp [selected, caller, contextEnvironment, ContextHelper.names, sourceErased,
                      applySubst, Subst.lookup])
                  have candidatesReturned : PureReturns program instanceBound state
                      (a "gslt:rule:language-contextual-reducts"
                        [v "strategy", v "language", v "rows", v "depth", v "instance"])
                      state (patternsValue candidates) := by
                    apply source_capture (by decide +kernel) _ (by decide) _
                      (by simpa only [instanceErased] using reentry instancePlan)
                    · intro index bounded
                      have small : index < 5 := by simpa using bounded
                      interval_cases index <;> decide +kernel
                    · simp [instanceBound, selected, caller, contextEnvironment, ContextHelper.names,
                        applySubst, Subst.lookup]
                  have choicesReturned := recursive_results_captured_returns candidatesBound state targetPlan
                    candidates seed candidatesFirstOrder [v "target", v "candidates", v "seed"]
                    (by simp [candidatesBound, instanceBound, selected, caller, contextEnvironment,
                      ContextHelper.names, targetErased, applySubst, Subst.lookup])
                  have continued := context_call .results choicesBound state
                    (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
                    (encoded (providerRowsTerm rows)) (number depth) (encoded restWire) (resultsValue choices)
                    [v "strategy", v "language", v "rows", v "depth", v "rest", v "choices"] _
                    (by simp [choicesBound, candidatesBound, instanceBound, selected, caller,
                      contextEnvironment, ContextHelper.names, applySubst, Subst.lookup])
                    (resultsAt_body_returns state strategy language types terms contexts fields rows depth
                      premises restWire allSeeds choices (by rw [sameChoices]; exact choicesFirstOrder))
                  rw [premisesAt_shape]
                  apply case_returns program caller selected state state state (v "premises") (encoded wire)
                    premisesAtRecursive _ _ premisesAtCases (read_cases_encoded _) _ _ _
                  · simpa [caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup] using
                      variable_returns program caller state "premises"
                  · simp [premisesAtCases, wire, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                      matchAtom, Subst.lookup, selected, caller, contextEnvironment, ContextHelper.names]
                  · have computed : PureData.BindingsReturn program selected state premisesAtRecursivePairs
                        choicesBound state := by
                      apply PureData.BindingsReturn.cons (bound := instanceBound) instanceReturned
                      · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, instanceBound, selected,
                          caller, contextEnvironment, ContextHelper.names, instantiated]
                      apply PureData.BindingsReturn.cons (bound := candidatesBound) candidatesReturned
                      · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, candidatesBound,
                          instanceBound, selected, caller, contextEnvironment, ContextHelper.names, candidates]
                      apply PureData.BindingsReturn.cons (bound := choicesBound)
                        (by simpa only [targetErased] using choicesReturned)
                      · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound,
                          candidatesBound, instanceBound, selected, caller, contextEnvironment,
                          ContextHelper.names, choices]
                      exact .nil _ _
                    simpa only [premisesAtRecursive, executePremises, premisesUsing, sameChoices] using
                      PureData.let_bindings_return computed state premisesAtContinue _ continued

private abbrev ruleEnvironment (helper : ContextHelper) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (depth : Nat) (last : Atom) : Subst :=
  contextEnvironment helper (encoded (strategyTerm strategy))
    (encoded (languageWire language types terms contexts fields))
    (encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites))
    (encoded (providerRowsTerm rows)) (number depth) last

private abbrev executeRoot (rows : List ProviderRow) (language : LanguageDef) (depth : Nat)
    (observations : List BoundMatch) : List Pattern :=
  MeTTaILMatchAutomataExecution.dispatchRoot (engineBasePremises (providerEnv rows))
    language (recursiveStep rows language depth) observations

private theorem execute_root_cons (rows : List ProviderRow) (language : LanguageDef) (depth : Nat)
    (matched : BoundMatch) (observations : List BoundMatch) :
    executeRoot rows language depth (matched :: observations) =
      executeRoot rows language depth [matched] ++ executeRoot rows language depth observations := by
  unfold executeRoot MeTTaILMatchAutomataExecution.dispatchRoot MeTTaILMatchAutomataExecution.atRoot
  cases root : matched.location.position.isEmpty <;> simp [root]

private abbrev optionValue (value : Option Term) : Atom := encoded
  (match value with | none => .symbol "None" | some value => .application "Some" [value])

private theorem rewrite_rows_as_list (contexts fields : RewriteRule → Term) (rules : List RewriteRule) :
    MatchAutomataExecution.rewriteRowsTerm contexts fields rules =
      encodeList id (rules.map (MatchAutomataExecution.rewriteRowTerm contexts fields)) := by
  simp only [MatchAutomataExecution.rewriteRowsTerm, encodeList_map]
  rfl

private def applyAtSome : Atom :=
  a "let" [v "choices", a "gslt:rule:premises-at"
    [v "strategy", v "language", v "rows", v "depth", v "premises", v "seed"],
    a "gslt:rule:instantiate-results" [v "right", v "choices"]]
private def applyAtRowCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"),
   (a "Some" [a "RewriteRule" [v "name", v "context", v "premises", v "left", v "right"]], applyAtSome)]
private def applyAtRoot : Atom :=
  a "let" [v "selected", a "gslt:rule:row-at" [v "index", v "rewrites"],
    a "case" [v "selected", .expression (applyAtRowCases.map fun row => .expression [row.1, row.2])]]
private def applyAtCases : SpaceSemantics.Cases :=
  [(a "Found" [.symbol "LNil", v "index", v "seed"], applyAtRoot),
   (a "Found" [a "LCons" [v "child", v "path"], v "index", v "seed"], .symbol "LNil")]
private theorem applyAt_shape : (contextEquation .applyMatch).body =
    a "case" [v "matched", .expression (applyAtCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem applyAt_body_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (languageAdmitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (reentry : reentryReturns state strategy language types terms contexts fields rows depth)
    (matched : BoundMatch) (seedFirstOrder : FirstOrderBindings matched.bindings) :
    PureReturns program (ruleEnvironment .applyMatch strategy language types terms contexts fields
      rows depth (encoded (boundMatchTerm matched))) state (contextEquation .applyMatch).body state
      (patternsValue (executeRoot rows language depth [matched])) := by
  rcases matched with ⟨⟨position, index⟩, seed⟩
  rw [applyAt_shape]
  cases position with
  | nil =>
      let caller := ruleEnvironment .applyMatch strategy language types terms contexts fields rows depth
        (encoded (boundMatchTerm ⟨⟨[], index⟩, seed⟩))
      let selected := ("seed", bindingsValue seed) :: ("index", number index) :: caller
      let rowTerms := language.rewrites.map (MatchAutomataExecution.rewriteRowTerm contexts fields)
      let looked := ("selected", optionValue rowTerms[index]?) :: selected
      have lookup : PureReturns program selected state
          (a "gslt:rule:row-at" [v "index", v "rewrites"]) state (optionValue rowTerms[index]?) :=
        RootRuleExecution.Matched.row_at_captured_returns selected state index rowTerms
          (v "index") (v "rewrites")
          (by simp [selected, caller, contextEnvironment, ContextHelper.names,
            rewrite_rows_as_list, rowTerms, applySubst, Subst.lookup, number, CettaWireAtom.encode])
      simp only [executeRoot, MeTTaILMatchAutomataExecution.dispatchRoot,
        MeTTaILMatchAutomataExecution.atRoot, List.filter_cons, List.isEmpty_nil, ↓reduceIte, List.filter_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      apply case_returns program caller selected state state state (v "matched")
        (encoded (boundMatchTerm ⟨⟨[], index⟩, seed⟩)) applyAtRoot _ _
        applyAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "matched"
      · simp [applyAtCases, boundMatchTerm, MatchAutomataDerivativeExecution.positionTerm,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, contextEnvironment, ContextHelper.names, number]
      · unfold applyAtRoot
        apply let_returns program selected looked state state state (v "selected") _ _ _ _ lookup _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, looked, selected,
            caller, contextEnvironment, ContextHelper.names]
        · cases found : language.rewrites[index]? with
          | none =>
              have emptyRow : rowTerms[index]? = none := by simp [rowTerms, List.getElem?_map, found]
              simp only [MeTTaILMatchAutomataExecution.dispatchMatch, found, patternsValue,
                InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
              apply case_returns program looked looked state state state (v "selected") (.symbol "None")
                (.symbol "LNil") (.symbol "LNil") _ applyAtRowCases (read_cases_encoded _) _ _ _
              · simpa [looked, emptyRow, optionValue, CettaWireAtom.encode, applySubst, Subst.lookup] using
                  variable_returns program looked state "selected"
              · simp [applyAtRowCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · exact symbol_returns program looked state "LNil"
          | some rule =>
              have chosenRow : rowTerms[index]? = some (MatchAutomataExecution.rewriteRowTerm contexts fields rule) := by
                simp [rowTerms, List.getElem?_map, found]
              have member := List.mem_of_getElem? found
              have admitted := (MeTTaILFirstOrderContextualExecution.rule_admitted_iff rule).mp
                (MeTTaILFirstOrderContextualExecution.language_admitted_rule language languageAdmitted rule member)
              cases rightAccepted : compilePattern? rule.right with
              | none =>
                  have supported := compilePattern?_isSome_eq_isMatchCorrectAux rule.right
                  simp [rightAccepted, admitted.2.2.1] at supported
              | some rightPlan =>
                have rightErased := erase_of_compilePattern? rule.right rightPlan rightAccepted
                let rowBound := ("right", patternValue rule.right) :: ("left", patternValue rule.left) ::
                  ("premises", encoded (fields rule)) :: ("context", encoded (contexts rule)) ::
                  ("name", encoded (.string rule.name)) :: looked
                let choices := executePremises rows language depth rule.premises seed
                let choicesBound := ("choices", resultsValue choices) :: rowBound
                have sameInstantiations : choices.map (rightPlan.instantiate) =
                    MeTTaILMatchAutomataExecution.dispatchMatch (engineBasePremises (providerEnv rows))
                      language (recursiveStep rows language depth) ⟨⟨[], index⟩, seed⟩ := by
                  simp only [MeTTaILMatchAutomataExecution.dispatchMatch, found]
                  apply List.map_congr_left
                  intro bindings bindingsMember
                  simp only [instantiate_eq_applyBindings, rightErased, RuleInterpretation.syntactic,
                    applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _
                      (binderFree_of_firstOrder rule.right admitted.2.2.1)]
                simp only [MeTTaILMatchAutomataExecution.dispatchMatch, found]
                apply case_returns program looked rowBound state state state (v "selected")
                  (encoded (.application "Some" [MatchAutomataExecution.rewriteRowTerm contexts fields rule]))
                  applyAtSome _ _ applyAtRowCases (read_cases_encoded _) _ _ _
                · simpa [looked, chosenRow, optionValue, applySubst, Subst.lookup] using
                    variable_returns program looked state "selected"
                · simp [applyAtRowCases, MatchAutomataExecution.rewriteRowTerm, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, rowBound, looked,
                    selected, caller, contextEnvironment, ContextHelper.names]
                · have guarded := context_call .premises rowBound state
                      (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
                      (encoded (providerRowsTerm rows)) (number depth) (encoded (fields rule)) (bindingsValue seed)
                      [v "strategy", v "language", v "rows", v "depth", v "premises", v "seed"] _
                      (by simp [rowBound, looked, selected, caller, contextEnvironment,
                        ContextHelper.names, applySubst, Subst.lookup])
                      (premisesAt_body_returns state strategy language types terms contexts fields rows depth
                        providerAdmitted languageAdmitted reentry rule.premises (fields rule)
                        (projected rule member) seed seedFirstOrder)
                  unfold applyAtSome
                  apply let_returns program rowBound choicesBound state state state (v "choices")
                    _ _ _ _ guarded _ _
                  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, choices, bindingResultsTerm,
                      rowBound, looked, selected, caller, contextEnvironment, ContextHelper.names]
                  · have instantiated := RuleInstantiationExecution.instantiate_results_captured_returns
                      choicesBound state rightPlan choices (v "right") (v "choices")
                      (by simp [choicesBound, bindingResultsTerm, rowBound, looked, selected, caller,
                        contextEnvironment, ContextHelper.names, rightErased, applySubst, Subst.lookup])
                    simpa only [sameInstantiations, MeTTaILMatchAutomataExecution.dispatchMatch, found] using instantiated
  | cons child path =>
      let caller := ruleEnvironment .applyMatch strategy language types terms contexts fields rows depth
        (encoded (boundMatchTerm ⟨⟨child :: path, index⟩, seed⟩))
      let selected := ("seed", bindingsValue seed) :: ("index", number index) ::
        ("path", encoded (MatchAutomataDerivativeExecution.positionTerm path)) :: ("child", number child) :: caller
      simp only [executeRoot, MeTTaILMatchAutomataExecution.dispatchRoot,
        MeTTaILMatchAutomataExecution.atRoot, List.filter_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
        List.flatMap_nil, patternsValue, InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller selected state state state (v "matched")
        (encoded (boundMatchTerm ⟨⟨child :: path, index⟩, seed⟩)) (.symbol "LNil") (.symbol "LNil") _
        applyAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "matched"
      · simp [applyAtCases, boundMatchTerm, MatchAutomataDerivativeExecution.positionTerm,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, caller, contextEnvironment, ContextHelper.names, number]
      · exact symbol_returns program selected state "LNil"

private def matchesAtPairs : List (Atom × Atom) :=
  [(v "head", a "gslt:rule:apply-root-match-at"
    [v "strategy", v "language", v "rewrites", v "rows", v "depth", v "matched"]),
   (v "tail", a "gslt:rule:matched-root-reducts-at"
    [v "strategy", v "language", v "rewrites", v "rows", v "depth", v "rest"])]
private def matchesAtResult : Atom := a "gslt:automata:append" [v "head", v "tail"]
private def matchesAtCons : Atom :=
  a "let*" [.expression (matchesAtPairs.map fun pair => .expression [pair.1, pair.2]), matchesAtResult]
private def matchesAtCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "matched", v "rest"], matchesAtCons)]
private theorem matchesAt_shape : (contextEquation .matches).body =
    a "case" [v "matches", .expression (matchesAtCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem matchesAt_body_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (languageAdmitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (reentry : reentryReturns state strategy language types terms contexts fields rows depth)
    (observations : List BoundMatch)
    (seedsFirstOrder : ∀ matched ∈ observations, FirstOrderBindings matched.bindings) :
    PureReturns program (ruleEnvironment .matches strategy language types terms contexts fields
      rows depth (encoded (matchesTerm observations))) state (contextEquation .matches).body state
      (patternsValue (executeRoot rows language depth observations)) := by
  induction observations with
  | nil =>
      let caller := ruleEnvironment .matches strategy language types terms contexts fields rows depth
        (encoded (matchesTerm []))
      rw [matchesAt_shape]
      apply case_returns program caller caller state state state (v "matches") (.symbol "LNil")
        (.symbol "LNil") _ _ matchesAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, contextEnvironment, ContextHelper.names, matchesTerm,
          encodeList, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "matches"
      · simp [matchesAtCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [executeRoot, MeTTaILMatchAutomataExecution.dispatchRoot,
          MeTTaILMatchAutomataExecution.atRoot, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns program caller state "LNil"
  | cons matched observations ih =>
      let caller := ruleEnvironment .matches strategy language types terms contexts fields rows depth
        (encoded (matchesTerm (matched :: observations)))
      let selected := ("rest", encoded (matchesTerm observations)) :: ("matched", encoded (boundMatchTerm matched)) :: caller
      let headResults := executeRoot rows language depth [matched]
      let tailResults := executeRoot rows language depth observations
      let headBound := ("head", patternsValue headResults) :: selected
      let tailBound := ("tail", patternsValue tailResults) :: headBound
      have headReturned := context_call .applyMatch selected state
        (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
        (encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites))
        (encoded (providerRowsTerm rows)) (number depth) (encoded (boundMatchTerm matched))
        [v "strategy", v "language", v "rewrites", v "rows", v "depth", v "matched"] _
        (by simp [selected, caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup])
        (applyAt_body_returns state strategy language types terms contexts fields rows depth
          providerAdmitted languageAdmitted projected reentry matched (seedsFirstOrder matched (by simp)))
      have tailReturned := context_call .matches headBound state
        (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
        (encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites))
        (encoded (providerRowsTerm rows)) (number depth) (encoded (matchesTerm observations))
        [v "strategy", v "language", v "rewrites", v "rows", v "depth", v "rest"] _
        (by simp [headBound, selected, caller, contextEnvironment, ContextHelper.names,
          applySubst, Subst.lookup]) (ih (fun next member => seedsFirstOrder next (by simp [member])))
      rw [matchesAt_shape]
      apply case_returns program caller selected state state state (v "matches")
        (encoded (matchesTerm (matched :: observations))) matchesAtCons _ _ matchesAtCases (read_cases_encoded _) _ _ _
      · simpa [caller, contextEnvironment, ContextHelper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "matches"
      · simp [matchesAtCases, matchesTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, contextEnvironment, ContextHelper.names]
      · have computed : PureData.BindingsReturn program selected state matchesAtPairs tailBound state := by
          apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, headResults, selected,
              caller, contextEnvironment, ContextHelper.names]
          apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, tailResults, headBound,
              selected, caller, contextEnvironment, ContextHelper.names]
          exact .nil _ _
        have appended := append_patterns_return tailBound state headResults tailResults
          (by simp [tailBound, headBound, applySubst, Subst.lookup])
        rw [execute_root_cons]
        simpa only [matchesAtCons, matchesAtResult, headResults, tailResults] using
          PureData.let_bindings_return computed state matchesAtResult _ appended

private def matcherHead : Strategy → String
  | .bottomUp => "gslt:automata:language-bottom"
  | .topDown => "gslt:automata:language-top"
private def matcherResult (strategy : Strategy) (patterns : List PatternPlan) (subject : PatternPlan) : Term :=
  match strategy with
  | .bottomUp => MatchAutomataExecution.bottomRunTerm patterns subject
  | .topDown => MatchAutomataExecution.topRunTerm patterns subject
private theorem matcher_result_shape (strategy : Strategy) (patterns : List PatternPlan) (subject : PatternPlan) :
    ∃ reads tests, matcherResult strategy patterns subject =
      MatchAutomataExecution.matchRunTerm
        (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject) reads tests := by
  cases strategy <;> exact ⟨_, _, rfl⟩

private def languageMatchesEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:language-matches")[0]'(by decide +kernel)
private def languageMatchesEnvironment (strategy : Strategy) (wire : Term) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("language", encoded wire), ("strategy", encoded (strategyTerm strategy))]
private def languageMatchesCases : SpaceSemantics.Cases :=
  [(.symbol "MatchBottomUp", a "gslt:automata:language-bottom" [v "language", v "subject"]),
   (.symbol "MatchTopDown", a "gslt:automata:language-top" [v "language", v "subject"])]
private theorem languageMatches_shape : languageMatchesEquation.body =
    a "case" [v "strategy", .expression (languageMatchesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem languageMatches_body_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language) :
    PureReturns program (languageMatchesEnvironment strategy
      (languageWire language types terms contexts fields) subject) state languageMatchesEquation.body state
      (encoded (matcherResult strategy patterns subject)) := by
  let caller := languageMatchesEnvironment strategy (languageWire language types terms contexts fields) subject
  have closed : PureReturns MatchAutomataProgram.program [] state
      (a (matcherHead strategy) [encoded (languageWire language types terms contexts fields), patternValue subject.erase])
      state (encoded (matcherResult strategy patterns subject)) := by
    cases strategy with
    | bottomUp =>
        exact MatchAutomataExecution.language_bottom_returns state language types terms (.symbol "LNil")
          contexts fields patterns subject admitted
    | topDown =>
        exact MatchAutomataExecution.language_top_returns state language types terms (.symbol "LNil")
          contexts fields patterns subject admitted
  have captured : PureReturns MatchAutomataProgram.program caller state
      (a (matcherHead strategy) [v "language", v "subject"]) state
      (encoded (matcherResult strategy patterns subject)) := by
    apply PureData.raw_capture_returns MatchAutomataProgram.program [] caller state state
      (matcherHead strategy)
      [encoded (languageWire language types terms contexts fields), patternValue subject.erase]
      [v "language", v "subject"] _ _ _ _ _ closed
    · cases strategy <;> decide +kernel
    · intro index bounded
      have small : index < 2 := by simpa using bounded
      interval_cases index <;> cases strategy <;> decide +kernel
    · cases strategy <;> decide
    · simp [caller, languageMatchesEnvironment, applySubst, Subst.lookup]
  have matched := automata_captured_returns
    (show codeWithin RuleExecutionProgram.matcherHead
      (a (matcherHead strategy) [v "language", v "subject"]) = true from by cases strategy <;> decide +kernel)
    captured
  rw [languageMatches_shape]
  cases strategy with
  | bottomUp =>
      apply case_returns program caller caller state state state (v "strategy")
        (.symbol "MatchBottomUp") (a "gslt:automata:language-bottom" [v "language", v "subject"]) _ _
        languageMatchesCases (read_cases_encoded _) _ _ _
      · simpa [caller, languageMatchesEnvironment, strategyTerm, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "strategy"
      · simp [languageMatchesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact matched
  | topDown =>
      apply case_returns program caller caller state state state (v "strategy")
        (.symbol "MatchTopDown") (a "gslt:automata:language-top" [v "language", v "subject"]) _ _
        languageMatchesCases (read_cases_encoded _) _ _ _
      · simpa [caller, languageMatchesEnvironment, strategyTerm, CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "strategy"
      · simp [languageMatchesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact matched

/-- The retained selector executes one of the two shared matchers. It does
not grant any rewrite permission, and retains the matcher's full counters. -/
theorem language_matches_captured_returns (caller : Subst) (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (arguments : List Atom) (captured : arguments.map (applySubst caller) =
      [encoded (strategyTerm strategy), encoded (languageWire language types terms contexts fields), patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:language-matches" arguments) state
      (encoded (matcherResult strategy patterns subject)) := by
  apply PureData.raw_authored_call_return program caller
    (languageMatchesEnvironment strategy (languageWire language types terms contexts fields) subject)
    state state "gslt:rule:language-matches" arguments languageMatchesEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (languageMatches_body_returns state strategy language types terms contexts fields patterns subject admitted)
  · have length : arguments.length = 3 := by
      have := congrArg List.length captured
      simpa using this
    intro index bounded
    rw [length] at bounded
    interval_cases index <;> decide +kernel
  · rw [captured, clauses_use_only_the_named_equations]
    change (equations "gslt:rule:language-matches").filterMap _ = _
    rw [show equations "gslt:rule:language-matches" = [languageMatchesEquation] from rfl]
    have formals : languageMatchesEquation.arguments = [v "strategy", v "language", v "subject"] := by
      decide +kernel
    simp [formals, languageMatchesEnvironment, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem language_patterns_compiled (language : LanguageDef)
    (admitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true) :
    ∃ patterns, erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language := by
  have supported : isMatchCorrectListAux (MeTTaILSubtermMatchAutomata.languagePatterns language) = true := by
    apply (Mettapedia.OSLF.MeTTaIL.MatchSpec.isMatchCorrectListAux_iff_forall _).mpr
    intro pattern member
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
    exact ((MeTTaILFirstOrderContextualExecution.rule_admitted_iff rule).mp
      (MeTTaILFirstOrderContextualExecution.language_admitted_rule language admitted rule ruleMember)).2.1
  cases compiled : compilePatterns? (MeTTaILSubtermMatchAutomata.languagePatterns language) with
  | none =>
      have exactness := compilePatterns?_isSome_eq_isMatchCorrectListAux
        (MeTTaILSubtermMatchAutomata.languagePatterns language)
      simp [compiled, supported] at exactness
  | some patterns => exact ⟨patterns, erasePatterns_of_compilePatterns? _ _ compiled⟩

private def contextualEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:language-contextual-reducts")[0]'(by decide +kernel)
private def contextualEnvironment (strategy : Strategy) (language : LanguageDef) (types terms : Term)
    (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("depth", number depth), ("rows", encoded (providerRowsTerm rows)),
   ("language", encoded (languageWire language types terms contexts fields)), ("strategy", encoded (strategyTerm strategy))]
private def contextualResult : Atom :=
  a "gslt:rule:matched-root-reducts-at"
    [v "strategy", v "language", v "rewrites", v "rows", v "previous", v "matches"]
private def contextualResultCases : SpaceSemantics.Cases :=
  [(a "MatchRun" [v "matches", v "reads", v "tests"], contextualResult)]
private def contextualPairs : List (Atom × Atom) :=
  [(v "previous", a "-" [v "depth", number 1]),
   (v "matched", a "gslt:rule:language-matches" [v "strategy", v "language", v "subject"])]
private def contextualSelected : Atom :=
  a "let*" [.expression (contextualPairs.map fun pair => .expression [pair.1, pair.2]),
    a "case" [v "matched", .expression (contextualResultCases.map fun row => .expression [row.1, row.2])]]
private def contextualLanguageCases : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", .symbol "LNil", v "rewrites"], contextualSelected)]
private def contextualNonzero : Atom :=
  a "case" [v "language", .expression (contextualLanguageCases.map fun row => .expression [row.1, row.2])]
private theorem contextual_shape : contextualEquation.body =
    a "if" [a "==" [v "depth", number 0], .symbol "LNil", contextualNonzero] := by
  decide +kernel

private theorem contextual_call (caller : Subst) (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (strategyTerm strategy), encoded (languageWire language types terms contexts fields),
       encoded (providerRowsTerm rows), number depth, patternValue subject.erase])
    (returned : PureReturns program
      (contextualEnvironment strategy language types terms contexts fields rows depth subject)
      state contextualEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:language-contextual-reducts" arguments) state answer := by
  apply PureData.raw_authored_call_return program caller
    (contextualEnvironment strategy language types terms contexts fields rows depth subject) state state
    "gslt:rule:language-contextual-reducts" arguments contextualEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · have length : arguments.length = 5 := by
      have := congrArg List.length captured
      simpa using this
    intro index bounded
    rw [length] at bounded
    interval_cases index <;> decide +kernel
  · rw [captured, clauses_use_only_the_named_equations]
    change (equations "gslt:rule:language-contextual-reducts").filterMap _ = _
    rw [show equations "gslt:rule:language-contextual-reducts" = [contextualEquation] from rfl]
    have formals : contextualEquation.arguments = [v "strategy", v "language", v "rows", v "depth", v "subject"] := by
      decide +kernel
    simp [formals, contextualEnvironment, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem contextual_body_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (types terms : Term) (contexts fields : RewriteRule → Term) (rows : List ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : MeTTaILFirstOrderContextualExecution.languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (patterns : List PatternPlan)
    (patternsAdmitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (depth : Nat) (subject : PatternPlan) :
    PureReturns program (contextualEnvironment strategy language types terms contexts fields rows depth subject)
      state contextualEquation.body state (patternsValue (recursiveStep rows language depth subject.erase)) := by
  induction depth generalizing subject with
  | zero =>
      let caller := contextualEnvironment strategy language types terms contexts fields rows 0 subject
      have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural 0) (.natural 0)
        (v "depth") (number 0) (by decide +kernel) (by decide +kernel)
        (by simpa [caller, contextualEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "depth") (grounded_returns program caller state (.int 0))
      rw [contextual_shape]
      apply if_returns program caller state state state _ _ _ _ _ tested
      simp only [decide_true]
      rw [show (Effects.boolean true == Effects.boolean true) = true from by decide +kernel]
      simp only [↓reduceIte]
      simpa only [patternsValue, encoded, recursiveStep, Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt,
        InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using symbol_returns program caller state "LNil"
  | succ depth ih =>
      let caller := contextualEnvironment strategy language types terms contexts fields rows (depth + 1) subject
      have reentry : reentryReturns state strategy language types terms contexts fields rows depth := by
        intro next
        exact contextual_call [] state strategy language types terms contexts fields rows depth next _ _
          (by simp) (ih next)
      have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural (depth + 1)) (.natural 0)
        (v "depth") (number 0) (by decide +kernel) (by decide +kernel)
        (by simpa [caller, contextualEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "depth") (grounded_returns program caller state (.int 0))
      rw [contextual_shape]
      apply if_returns program caller state state state _ _ _ _ _ tested
      simp only [Term.natural.injEq, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false]
      rw [show (Effects.boolean false == Effects.boolean true) = false from by decide +kernel]
      let selected := ("rewrites", encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites)) ::
        ("terms", encoded terms) :: ("types", encoded types) :: ("name", encoded (.string language.name)) :: caller
      let previousBound := ("previous", number depth) :: selected
      let observations := MeTTaILSubtermMatchAutomata.reference
        (MeTTaILSubtermMatchAutomata.languagePatterns language) subject
      have matched := language_matches_captured_returns previousBound state strategy language types terms contexts fields
        patterns subject patternsAdmitted [v "strategy", v "language", v "subject"]
        (by simp [previousBound, selected, caller, contextualEnvironment, applySubst, Subst.lookup])
      obtain ⟨reads, tests, shape⟩ := matcher_result_shape strategy patterns subject
      rw [shape, patternsAdmitted] at matched
      let matchValue := encoded (MatchAutomataExecution.matchRunTerm observations reads tests)
      let matchedBound := ("matched", matchValue) :: previousBound
      let resultBound := ("tests", number tests) :: ("reads", number reads) ::
        ("matches", encoded (matchesTerm observations)) :: matchedBound
      have previous : PureReturns program selected state (a "-" [v "depth", number 1]) state (number depth) := by
        apply native_binary_call_returns program selected state state state state "-"
          (v "depth") (number 1) (number (depth + 1)) (number 1) (number depth)
          (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
        · simpa [selected, caller, contextualEnvironment, applySubst, Subst.lookup] using
            variable_returns program selected state "depth"
        · exact grounded_returns program selected state (.int 1)
        · change (Except.ok (state, [Atom.grounded (.int (((depth + 1 : Nat) : Int) - 1))]) : Effects.Result) =
            Except.ok (state, [.grounded (.int (depth : Int))])
          simp
      unfold contextualNonzero
      apply case_returns program caller selected state state state (v "language")
        (encoded (languageWire language types terms contexts fields)) contextualSelected _ _
        contextualLanguageCases (read_cases_encoded _) _ _ _
      · simpa [caller, contextualEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "language"
      · simp [contextualLanguageCases, MatchAutomataExecution.matchingProjectionTerm, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, contextualEnvironment]
      · have computed : PureData.BindingsReturn program selected state contextualPairs matchedBound state := by
          apply PureData.BindingsReturn.cons (bound := previousBound) previous
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, previousBound, selected,
              caller, contextualEnvironment]
          apply PureData.BindingsReturn.cons (bound := matchedBound) matched
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, matchedBound, matchValue, observations,
              previousBound, selected, caller, contextualEnvironment]
          exact .nil _ _
        unfold contextualSelected
        apply PureData.let_bindings_return (pairs := contextualPairs) computed state _ _
        apply case_returns program matchedBound resultBound state state state (v "matched") matchValue
          contextualResult _ _ contextualResultCases (read_cases_encoded _) _ _ _
        · simpa [matchedBound, matchValue, applySubst, Subst.lookup] using
            variable_returns program matchedBound state "matched"
        · simp [contextualResultCases, matchValue, MatchAutomataExecution.matchRunTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
            resultBound, matchedBound, previousBound, selected, caller, contextualEnvironment, number]
        · have frontier : executeRoot rows language depth observations =
              recursiveStep rows language (depth + 1) subject.erase :=
            MeTTaILMatchAutomataExecution.dispatch_reference (engineBasePremises (providerEnv rows))
              language (recursiveStep rows language depth) subject
          rw [← frontier]
          exact context_call .matches resultBound state
            (encoded (strategyTerm strategy)) (encoded (languageWire language types terms contexts fields))
            (encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites))
            (encoded (providerRowsTerm rows)) (number depth) (encoded (matchesTerm observations))
            [v "strategy", v "language", v "rewrites", v "rows", v "previous", v "matches"] _
            (by simp [resultBound, matchedBound, previousBound, selected, caller, contextualEnvironment,
              applySubst, Subst.lookup])
            (matchesAt_body_returns state strategy language types terms contexts fields rows depth
              providerAdmitted admitted projected reentry observations
              (MeTTaILFirstOrderContextualExecution.reference_bindings_firstOrder language admitted subject))

/-- The retained contextual entry is an actual PeTTa computation. Every
recursive re-entry is earned from source/provider syntax closure; no
intermediate representation or execution callback is assumed. -/
theorem language_contextual_captured_returns (caller : Subst) (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (strategyTerm strategy), encoded (languageWire language types terms contexts fields),
       encoded (providerRowsTerm rows), number depth, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:rule:language-contextual-reducts" arguments) state
      (patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
        (engineBasePremises (providerEnv rows)) language depth subject)) := by
  have admissionFields := (language_admitted_iff language).mp admitted
  obtain ⟨patterns, patternsAdmitted⟩ := language_patterns_compiled language admissionFields.2.1
  rw [MeTTaILMatchAutomataExecution.runAt_exact]
  exact contextual_call caller state strategy language types terms contexts fields rows depth subject arguments _ captured
    (contextual_body_returns state strategy language types terms contexts fields rows providerAdmitted
      admissionFields.2.1 projected patterns patternsAdmitted depth subject)

def languageQueryTerm (strategy : Strategy) (language : LanguageDef) (types terms : Term)
    (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan) : Term :=
  .application "gslt:rule:language-contextual-reducts"
    [strategyTerm strategy, languageWire language types terms contexts fields, providerRowsTerm rows,
     .natural depth, InferenceCettaWire.encodePattern subject.erase]

theorem language_contextual_returns (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) :
    PureReturns program [] state (encoded (languageQueryTerm strategy language types terms contexts fields rows depth subject))
      state (patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
        (engineBasePremises (providerEnv rows)) language depth subject)) := by
  simpa only [languageQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    language_contextual_captured_returns [] state strategy language types terms contexts fields rows
      providerAdmitted admitted projected depth subject _ (by simp [applySubst, CettaWireAtom.encode])

private def strategyEntryHead : Strategy → String
  | .bottomUp => "gslt:rule:language-contextual-bottom-reducts"
  | .topDown => "gslt:rule:language-contextual-top-reducts"
private def strategyEntryEquation (strategy : Strategy) : SpaceSemantics.Equation :=
  (equations (strategyEntryHead strategy))[0]'(by cases strategy <;> decide +kernel)
private def strategyEntryEnvironment (language : LanguageDef) (types terms : Term)
    (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject.erase), ("depth", number depth), ("rows", encoded (providerRowsTerm rows)),
   ("language", encoded (languageWire language types terms contexts fields))]

def languageStrategyQueryTerm (strategy : Strategy) (language : LanguageDef) (types terms : Term)
    (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan) : Term :=
  .application (strategyEntryHead strategy)
    [languageWire language types terms contexts fields, providerRowsTerm rows,
     .natural depth, InferenceCettaWire.encodePattern subject.erase]

/-- The two retained convenience entries call the same contextual executor;
their strategy choice changes shared matching, not rewrite authority. -/
theorem language_strategy_captured_returns (caller : Subst) (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (languageWire language types terms contexts fields), encoded (providerRowsTerm rows),
       number depth, patternValue subject.erase]) :
    PureReturns program caller state (a (strategyEntryHead strategy) arguments) state
      (patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
        (engineBasePremises (providerEnv rows)) language depth subject)) := by
  let callee := strategyEntryEnvironment language types terms contexts fields rows depth subject
  have inner := language_contextual_captured_returns callee state strategy language types terms contexts fields rows
    providerAdmitted admitted projected depth subject
    [encoded (strategyTerm strategy), v "language", v "rows", v "depth", v "subject"]
    (by simp [callee, strategyEntryEnvironment, applySubst, Subst.lookup])
  apply PureData.raw_authored_call_return program caller callee state state (strategyEntryHead strategy)
    arguments (strategyEntryEquation strategy).body _
    (by cases strategy <;> decide) (by cases strategy <;> decide) (by cases strategy <;> decide)
    (by cases strategy <;> decide +kernel) _ _ _
  · have length : arguments.length = 4 := by
      have := congrArg List.length captured
      simpa using this
    intro index bounded
    rw [length] at bounded
    interval_cases index <;> cases strategy <;> decide +kernel
  · rw [captured, clauses_use_only_the_named_equations]
    change (equations (strategyEntryHead strategy)).filterMap _ = _
    rw [show equations (strategyEntryHead strategy) = [strategyEntryEquation strategy] from by cases strategy <;> rfl]
    have formals : (strategyEntryEquation strategy).arguments = [v "language", v "rows", v "depth", v "subject"] := by
      cases strategy <;> decide +kernel
    simp [formals, callee, strategyEntryEnvironment, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · have shape : (strategyEntryEquation strategy).body =
        a "gslt:rule:language-contextual-reducts"
          [encoded (strategyTerm strategy), v "language", v "rows", v "depth", v "subject"] := by
      cases strategy <;> decide +kernel
    rw [shape]
    exact inner

theorem language_strategy_returns (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) :
    PureReturns program [] state (encoded (languageStrategyQueryTerm strategy language types terms contexts fields rows depth subject))
      state (patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
        (engineBasePremises (providerEnv rows)) language depth subject)) := by
  simpa only [languageStrategyQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    language_strategy_captured_returns [] state strategy language types terms contexts fields rows
      providerAdmitted admitted projected depth subject _ (by simp [applySubst, CettaWireAtom.encode])

/-- Exact complete observations of the actual finite-depth entry: ordered
frontier, preserved store, and empty I/O. Target machine fuel is independent
of the authored contextual evidence depth. -/
theorem language_contextual_completed_iff (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (encoded (languageQueryTerm strategy language types terms contexts fields rows depth subject)) } =
      .complete after answers input output) ↔
    after = state ∧ answers = [patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
      (engineBasePremises (providerEnv rows)) language depth subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_contextual_returns state strategy language types terms contexts fields rows
      providerAdmitted admitted projected depth subject) after answers input output

theorem language_contextual_derivation_iff (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (languageQueryTerm strategy language types terms contexts fields rows depth subject)) }
      (.complete after answers input output) ↔
    after = state ∧ answers = [patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
      (engineBasePremises (providerEnv rows)) language depth subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_contextual_returns state strategy language types terms contexts fields rows
      providerAdmitted admitted projected depth subject) after answers input output

/-- A reduct occurs in an actually completed contextual entry. This is an
observation property over the existing PeTTa judgment, not another evaluator. -/
def ObservesContextualReduct (state : State) (strategy : Strategy) (language : LanguageDef) (types terms : Term)
    (contexts fields : RewriteRule → Term) (rows : List ProviderRow) (subject : PatternPlan) (target : Pattern) : Prop :=
  ∃ depth, ∃ reducts : List Pattern,
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (languageQueryTerm strategy language types terms contexts fields rows depth subject)) }
      (.complete state [patternsValue reducts] [] []) ∧ target ∈ reducts

/-- Preservation and reflection to the canonical GSLT's actual root step.
Authored recursive premises authorize contextual progress; matcher subterm
positions alone never authorize a child replacement. -/
theorem observes_contextual_iff_gslt_step (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (subject : PatternPlan) (target : Pattern) :
    ObservesContextualReduct state strategy language types terms contexts fields rows subject target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step subject.erase target := by
  rw [← MeTTaILMatchAutomataExecution.runAt_iff_gslt_step strategy (providerEnv rows)
    language ((language_admitted_iff language).mp admitted).1 subject target]
  constructor
  · rintro ⟨depth, reducts, executed, member⟩
    have observation := (language_contextual_derivation_iff state strategy language types terms contexts fields rows
      providerAdmitted admitted projected depth subject state [patternsValue reducts] [] []).mp executed
    have sameAtom := List.cons.inj observation.2.1 |>.1
    have sameWire := CettaWireAtom.encode_injective _ _ sameAtom
    have same := InferenceCettaWire.encodePatterns_injective sameWire
    exact ⟨depth, by simpa only [same] using member⟩
  · rintro ⟨depth, member⟩
    exact ⟨depth, _, (language_contextual_derivation_iff state strategy language types terms contexts fields rows
      providerAdmitted admitted projected depth subject state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩, member⟩

/-- The actual common-machine run observes exactly the licensed contextual
GSLT steps. The terminal frontier retains its occurrence list and complete
effect store; evaluator budget remains distinct from premise depth. -/
theorem common_machine_observes_contextual_iff_gslt_step (state : State) (strategy : Strategy)
    (language : LanguageDef) (types terms : Term) (contexts fields : RewriteRule → Term)
    (rows : List ProviderRow) (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (admitted : languageAdmitted language = true)
    (projected : ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (fields rule))
    (subject : PatternPlan) (target : Pattern) :
    (∃ depth, ∃ reducts : List Pattern, ∃ fuel events,
      (CommonMachine.machine program).run fuel
        { state, control := .evaluate [] (encoded
            (languageQueryTerm strategy language types terms contexts fields rows depth subject)) } =
        (events, .finished (.complete state [patternsValue reducts] [] [])) ∧ target ∈ reducts) ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step
        subject.erase target := by
  rw [← observes_contextual_iff_gslt_step state strategy language types terms contexts fields rows
    providerAdmitted admitted projected subject target]
  constructor
  · rintro ⟨depth, reducts, fuel, events, finished, member⟩
    exact ⟨depth, reducts,
      (CommonMachine.finished_iff_source program _ _).mp ⟨fuel, events, finished⟩, member⟩
  · rintro ⟨depth, reducts, executed, member⟩
    obtain ⟨fuel, events, finished⟩ := (CommonMachine.finished_iff_source program _ _).mpr executed
    exact ⟨depth, reducts, fuel, events, finished, member⟩

namespace Controls

theorem variable_query_source_admitted :
    premiseAdmitted (.relationQuery "r" [.fvar "x"]) = true := by decide +kernel

theorem constructed_query_core_admitted :
    MeTTaILFirstOrderContextualExecution.premiseAdmitted
      (.relationQuery "r" [.apply "wrap" [.fvar "x"]]) = true := by decide +kernel

theorem constructed_query_source_refused :
    premiseTerm? (.relationQuery "r" [.apply "wrap" [.fvar "x"]]) = none := by decide +kernel


open MeTTaILFirstOrderContextualExecution.Controls

/-- The controls use the sole partial premise adapter. Its unsuccessful case
has an explicit marker; the admitted-row theorem below proves that marker is
unreachable in each executable fixture. -/
private def premiseFields (rule : RewriteRule) : Term :=
  (premisesTerm? rule.premises).getD (.symbol "UnprojectedPremises")

private theorem projected_fields (language : LanguageDef) (admitted : languageAdmitted language = true) :
    ∀ rule ∈ language.rewrites, premisesTerm? rule.premises = some (premiseFields rule) := by
  intro rule member
  obtain ⟨wire, projected⟩ := premises_projection_exists rule.premises
    (List.all_eq_true.mp ((language_admitted_iff language).mp admitted).2.2 rule member)
  simp only [premiseFields, projected, Option.getD_some]

def queryTerm (strategy : Strategy) (language : LanguageDef) (rows : List ProviderRow)
    (depth : Nat) (subject : PatternPlan) : Term :=
  languageStrategyQueryTerm strategy language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") premiseFields rows depth subject

private theorem fixture_returns (state : State) (strategy : Strategy) (language : LanguageDef)
    (admitted : languageAdmitted language = true) (rows : List ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true) (depth : Nat) (subject : PatternPlan) :
    PureReturns program [] state (encoded (queryTerm strategy language rows depth subject)) state
      (patternsValue (MeTTaILMatchAutomataExecution.runAt strategy
        (engineBasePremises (providerEnv rows)) language depth subject)) :=
  language_strategy_returns state strategy language (.symbol "LNil") (.symbol "LNil")
    (fun _ => .symbol "LNil") premiseFields rows providerAdmitted admitted
    (projected_fields language admitted) depth subject

private theorem empty_provider : providerEnv [] = RelationEnv.empty := rfl

theorem recursive_witnesses_preserved (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy language [] 2 subject)) state
      (patternsValue [box middle, box final, box middle]) := by
  simpa only [empty_provider, recursive_witnesses_ordered] using
    fixture_returns state strategy language (by decide +kernel) [] (by decide +kernel) 2 subject

/-- The common runner preserves the repeated recursive witness in its actual
ordered answer frontier. -/
theorem common_machine_recursive_witnesses_preserved (state : State) (strategy : Strategy) :
    ∃ fuel events, (CommonMachine.machine program).run fuel
      { state, control := .evaluate [] (encoded (queryTerm strategy language [] 2 subject)) } =
      (events, .finished (.complete state
        [patternsValue [box middle, box final, box middle]] [] [])) := by
  apply (CommonMachine.finished_iff_source program _ _).mpr
  exact (pure_returns_derivation_iff program [] state state _ _
    (recursive_witnesses_preserved state strategy) state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

theorem zero_depth_preserved (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy language [] 0 subject)) state (.symbol "LNil") := by
  simpa only [MeTTaILMatchAutomataExecution.runAt, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy language (by decide +kernel) [] (by decide +kernel) 0 subject

theorem exhausted_depth_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy language [] 1 subject)) state (.symbol "LNil") := by
  simpa only [empty_provider, exhausted_context_depth, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy language (by decide +kernel) [] (by decide +kernel) 1 subject

theorem unauthorized_child_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy childOnlyLanguage [] 4 subject)) state (.symbol "LNil") := by
  simpa only [empty_provider, unauthorized_child, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy childOnlyLanguage (by decide +kernel) [] (by decide +kernel) 4 subject

theorem conflicting_relative_match_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy conflictingLanguage [] 2 subject)) state (.symbol "LNil") := by
  simpa only [empty_provider, conflicting_relative_match, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy conflictingLanguage (by decide +kernel) [] (by decide +kernel) 2 subject

theorem missing_guard_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy guardedLanguage [] 2 subject)) state (.symbol "LNil") := by
  simpa only [empty_provider, missing_guard, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy guardedLanguage (by decide +kernel) [] (by decide +kernel) 2 subject

def guardedRows : List ProviderRow := [⟨"allow", [start]⟩, ⟨"allow", [start]⟩]

private theorem guarded_provider : providerEnv guardedRows = guardedRelations := by
  apply congrArg RelationEnv.mk
  funext relation arguments
  by_cases selected : relation = "allow"
  · simp [RelationPremiseExecution.providerTuples, guardedRows, selected]
  · simp [RelationPremiseExecution.providerTuples, guardedRows, selected, Ne.symm selected]

theorem duplicate_guard_witnesses_preserved (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy guardedLanguage guardedRows 2 subject)) state
      (patternsValue [box middle, box final, box middle, box middle, box final, box middle]) := by
  simpa only [guarded_provider, guarded_recursive_witnesses_ordered] using
    fixture_returns state strategy guardedLanguage (by decide +kernel) guardedRows (by decide +kernel) 2 subject

theorem freshness_occurrences_preserved (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy freshnessLanguage [] 1
      (.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "other"]]))) state
      (patternsValue [.apply "Accepted" [], .apply "Accepted" []]) := by
  simpa only [empty_provider, freshness_witnesses_ordered] using
    fixture_returns state strategy freshnessLanguage (by decide +kernel) [] (by decide +kernel) 1
      (.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "other"]])

theorem nonfresh_capture_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy freshnessLanguage [] 1
      (.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "atom"]]))) state
      (.symbol "LNil") := by
  simpa only [empty_provider, nonfresh_subject_refused, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy freshnessLanguage (by decide +kernel) [] (by decide +kernel) 1
      (.application "Fresh" [.application "Pair" [.metavariable "other", .metavariable "atom"]])

theorem captured_name_preserved (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy resolvedFreshnessLanguage [] 1
      (.application "FreshName" [.metavariable "actual", .metavariable "other"]))) state
      (patternsValue [.apply "Accepted" []]) := by
  simpa only [empty_provider, resolved_freshness_name] using
    fixture_returns state strategy resolvedFreshnessLanguage (by decide +kernel) [] (by decide +kernel) 1
      (.application "FreshName" [.metavariable "actual", .metavariable "other"])

theorem captured_nonfresh_name_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy resolvedFreshnessLanguage [] 1
      (.application "FreshName" [.metavariable "actual", .metavariable "actual"]))) state
      (.symbol "LNil") := by
  simpa only [empty_provider, resolved_nonfresh_name_refused, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy resolvedFreshnessLanguage (by decide +kernel) [] (by decide +kernel) 1
      (.application "FreshName" [.metavariable "actual", .metavariable "actual"])

theorem captured_nonname_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy resolvedFreshnessLanguage [] 1
      (.application "FreshName" [.application "NotAName" [], .metavariable "other"]))) state
      (.symbol "LNil") := by
  simpa only [empty_provider, nonname_freshness_binding_refused, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy resolvedFreshnessLanguage (by decide +kernel) [] (by decide +kernel) 1
      (.application "FreshName" [.application "NotAName" [], .metavariable "other"])

def nameGuardRows : List ProviderRow := [⟨"name", [.fvar "actual"]⟩, ⟨"name", [.fvar "actual"]⟩]

private theorem nameGuard_provider : providerEnv nameGuardRows = nameGuardRelations := by
  apply congrArg RelationEnv.mk
  funext relation arguments
  by_cases selected : relation = "name"
  · simp [RelationPremiseExecution.providerTuples, nameGuardRows, selected]
  · simp [RelationPremiseExecution.providerTuples, nameGuardRows,
      selected, Ne.symm selected]

theorem query_before_freshness_refused (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy (nameGuardLanguage true) nameGuardRows 1
      (.application "Fresh" [.metavariable "actual"]))) state (.symbol "LNil") := by
  simpa only [nameGuard_provider, resolved_guard_order_refused, patternsValue, encoded,
    InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
    fixture_returns state strategy (nameGuardLanguage true) (by decide +kernel)
      nameGuardRows (by decide +kernel) 1 (.application "Fresh" [.metavariable "actual"])

theorem freshness_before_query_preserved (state : State) (strategy : Strategy) :
    PureReturns program [] state (encoded (queryTerm strategy (nameGuardLanguage false) nameGuardRows 1
      (.application "Fresh" [.metavariable "actual"]))) state
      (patternsValue [.apply "Accepted" [], .apply "Accepted" []]) := by
  simpa only [nameGuard_provider, literal_guard_order_preserved] using
    fixture_returns state strategy (nameGuardLanguage false) (by decide +kernel)
      nameGuardRows (by decide +kernel) 1 (.application "Fresh" [.metavariable "actual"])

theorem annotated_language_refused : languageAdmitted
    { language with rewrites := [{ contextualRule with bindings := some { dependencies := [] } }] } = false := by
  decide +kernel

theorem equation_language_refused : languageAdmitted
    { language with equations :=
      [{ name := "extra"
         typeContext := []
         premises := []
         left := .fvar "x"
         right := .fvar "y" }] } = false := by
  decide +kernel

theorem scoped_wire_refused : premiseTerm? (.scopedStep
    (ScopedStepPremise.root (.base "Term") (.fvar "x") (.fvar "y"))) = none := rfl

theorem scoped_language_refused : languageAdmitted scopedLanguage = false := by decide +kernel

theorem binder_endpoint_wire_refused : premiseTerm?
    (.congruence (.lambda (some "x") (.bvar 0)) (.fvar "y")) = none := rfl

/-- Determinism excludes an incorrect completed frontier, rather than merely
checking one selected expected execution. -/
theorem incorrect_observation_refused (state : State) (strategy : Strategy)
    (language : LanguageDef) (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan)
    (admitted : languageAdmitted language = true)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (incorrect : List Pattern)
    (different : incorrect ≠ MeTTaILMatchAutomataExecution.runAt strategy
      (engineBasePremises (providerEnv rows)) language depth subject) :
    ¬ DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (queryTerm strategy language rows depth subject)) }
      (.complete state [patternsValue incorrect] [] []) := by
  intro executed
  have observed := (pure_returns_derivation_iff program [] state state _ _
    (fixture_returns state strategy language admitted rows providerAdmitted depth subject)
    state [patternsValue incorrect] [] []).mp executed
  have sameAtom := List.cons.inj observed.2.1 |>.1
  exact different (InferenceCettaWire.encodePatterns_injective (CettaWireAtom.encode_injective _ _ sameAtom))

/-- A common-machine completion cannot publish a different frontier from the
independently justified contextual execution. -/
theorem common_machine_incorrect_observation_refused (state : State) (strategy : Strategy)
    (language : LanguageDef) (rows : List ProviderRow) (depth : Nat) (subject : PatternPlan)
    (admitted : languageAdmitted language = true)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (incorrect : List Pattern)
    (different : incorrect ≠ MeTTaILMatchAutomataExecution.runAt strategy
      (engineBasePremises (providerEnv rows)) language depth subject) :
    ¬ ∃ fuel events, (CommonMachine.machine program).run fuel
      { state, control := .evaluate [] (encoded (queryTerm strategy language rows depth subject)) } =
      (events, .finished (.complete state [patternsValue incorrect] [] [])) := by
  intro finished
  exact incorrect_observation_refused state strategy language rows depth subject admitted
    providerAdmitted incorrect different
    ((CommonMachine.finished_iff_source program _ _).mp finished)

#print axioms variable_query_source_admitted
#print axioms constructed_query_core_admitted
#print axioms constructed_query_source_refused

end Controls

#print axioms common_machine_observes_contextual_iff_gslt_step

#print axioms recursive_results_captured_returns
#print axioms recursive_results_returns
#print axioms language_matches_captured_returns
#print axioms language_contextual_captured_returns
#print axioms language_contextual_returns
#print axioms language_strategy_returns
#print axioms language_contextual_completed_iff
#print axioms language_contextual_derivation_iff
#print axioms observes_contextual_iff_gslt_step
#print axioms premise_projection_exists
#print axioms premises_projection_exists
#print axioms Controls.recursive_witnesses_preserved
#print axioms Controls.common_machine_recursive_witnesses_preserved
#print axioms Controls.unauthorized_child_refused
#print axioms Controls.duplicate_guard_witnesses_preserved
#print axioms Controls.freshness_occurrences_preserved
#print axioms Controls.nonfresh_capture_refused
#print axioms Controls.captured_name_preserved
#print axioms Controls.captured_nonfresh_name_refused
#print axioms Controls.captured_nonname_refused
#print axioms Controls.query_before_freshness_refused
#print axioms Controls.freshness_before_query_preserved
#print axioms Controls.incorrect_observation_refused
#print axioms Controls.common_machine_incorrect_observation_refused

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution
