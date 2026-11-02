import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationContextExecutionProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleTraceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ContextualRuleExecution

/-!
# Source execution of contextual equation certificates

Physical positions resolve through the existing first-order subject plans and
one-hole contexts. The retained source keeps atomic provenance and checks the
reconstructed whole target. Reversed receipts first check the original
conditional witness at its supplied predecessor. Canonical equation equivalence remains the source
judgment; a refused certificate is not an inequivalence verdict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationContextExecution

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open MeTTaILFirstOrderRuleCompilation MeTTaILFirstOrderEquationCompilation
open Eval _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects EquationContextExecutionProgram
open RelationPremiseExecution (providerEnv providerRowsTerm)

/-- The checked local shape of equations executable by the retained names-only
premise helpers. General equation plans remain available as data. -/
abbrev VariableEquationPlans :=
  {plans : List RulePlan // ∀ plan ∈ plans, plan.variablePremises?.isSome = true}

abbrev variableEquationPlans (plans : List RulePlan)
    (admitted : plans.all (fun plan => plan.variablePremises?.isSome) = true) : VariableEquationPlans :=
  ⟨plans, List.all_eq_true.mp admitted⟩

@[simp] theorem variableEquationPlans_val (plans : List RulePlan)
    (admitted : plans.all (fun plan => plan.variablePremises?.isSome) = true) :
    (variableEquationPlans plans admitted).val = plans := rfl

def variableEquationPlans? (plans : List RulePlan) : Option VariableEquationPlans :=
  if admitted : plans.all (fun plan => plan.variablePremises?.isSome) = true then
    some ⟨plans, List.all_eq_true.mp admitted⟩
  else none

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (index : Nat) : Atom := encoded (.natural index)
private abbrev listValue (terms : List Term) : Atom := encoded (encodeList id terms)

def positionedReceiptTerm (receipt : PositionedReceipt) : Term :=
  .application "EqAt" [EquationExecution.pathTerm receipt.position,
    EquationExecution.receiptTerm receipt.atomic, InferenceCettaWire.encodePattern receipt.target]

def splitWireTerm (index : Nat) (children : List Term) : Term :=
  match children[index]? with
  | none => .symbol "None"
  | some child => .application "Some"
      [.application "EqSite" [encodeList id (children.take index), child, encodeList id (children.drop (index + 1))]]

private inductive Helper where
  | split | focus | replace | validate | replay | directedView | afterResults | witnessed
  | lift | frontierMatches | frontier | findTarget | findSigned | acquirePath
  | acquiredReplay | acquiredAfter | acquiredWitnessed
private def Helper.head : Helper → String
  | .split => "gslt:equation-context:split"
  | .focus => "gslt:equation-context:focus"
  | .replace => "gslt:equation-context:replace"
  | .validate => "gslt:equation-context:validate"
  | .replay => "gslt:equation-context:replay"
  | .directedView => "gslt:equation-context:directed-view"
  | .afterResults => "gslt:equation-context:after-results"
  | .witnessed => "gslt:equation-context:witnessed-reducts"
  | .lift => "gslt:equation-context:lift"
  | .frontierMatches => "gslt:equation-context:frontier-matches"
  | .frontier => "gslt:equation-context:frontier"
  | .findTarget => "gslt:equation-context:find-target"
  | .findSigned => "gslt:equation-context:find-signed"
  | .acquirePath => "gslt:equation-context:acquire-path"
  | .acquiredReplay => "gslt:equation-context:acquired-replay"
  | .acquiredAfter => "gslt:equation-context:acquired-after-results"
  | .acquiredWitnessed => "gslt:equation-context:acquired-witnessed-reducts"
private def Helper.names : Helper → List String
  | .split => ["index", "children"]
  | .focus => ["position", "subject"]
  | .replace => ["position", "subject", "target"]
  | .validate => ["equations", "rows", "subject", "receipt"]
  | .replay => ["equations", "rows", "subject", "receipts"]
  | .directedView => ["language"]
  | .afterResults => ["equations", "rows", "receipts", "results"]
  | .witnessed => ["strategy", "language", "rows", "depth", "subject", "before", "after"]
  | .lift => ["position", "subject", "receipts"]
  | .frontierMatches => ["equations", "rows", "subject", "matches"]
  | .frontier => ["equations", "rows", "subject"]
  | .findTarget => ["receipts", "target"]
  | .findSigned => ["equations", "rows", "subject", "target"]
  | .acquirePath => ["equations", "rows", "subject", "endpoints"]
  | .acquiredReplay => ["equations", "rows", "subject", "endpoints"]
  | .acquiredAfter => ["equations", "rows", "receipts", "results"]
  | .acquiredWitnessed => ["strategy", "language", "rows", "depth", "subject", "before", "after"]
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [equation helper] from by cases helper <;> rfl]
  have formals : (equation helper).arguments = helper.names.map Atom.var := by cases helper <;> decide +kernel
  have selected := PureData.match_variable_values helper.names values [] (by cases helper <;> decide) length
    (by intro name _; rfl)
  simp only [List.append_nil] at selected
  -- `clauses` matches the argument list element by element, which is `selected`.
  simp [formals, selected, environment]

set_option maxHeartbeats 1000000 in
private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (values arguments : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have capturedLength : arguments.length = helper.names.length := by
      simpa [length] using congrArg List.length captured
    rw [capturedLength] at bounded
    have declared : .expression [.symbol ":", .symbol helper.head,
        .expression (.symbol "->" :: (List.replicate helper.names.length (.symbol "Atom") ++ [.symbol "%Undefined%"]))]
          ∈ program.declarations := by cases helper <;> decide +kernel
    apply (argumentIsRaw_iff_declaredAtom program helper.head index (by cases helper <;> decide)).mpr
    refine ⟨_, declared, ?_⟩
    rw [List.getElem?_append_left (by simpa using bounded)]
    simp [bounded]
  · rw [captured]
    exact helper_clause helper values length

private theorem previous_returns (caller : Subst) (state : State) (index : Nat)
    (captured : applySubst caller (v "index") = number (index + 1)) :
    PureReturns program caller state (a "-" [v "index", number 1]) state (number index) := by
  apply native_binary_call_returns program caller state state state state "-" (v "index") (number 1)
    (number (index + 1)) (number 1) (number index)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state "index"
  · exact grounded_returns program caller state (.int 1)
  · change (Except.ok (state, [.grounded (.int (((index + 1 : Nat) : Int) - 1))]) : Effects.Result) =
      Except.ok (state, [.grounded (.int (index : Int))])
    simp

private theorem index_zero_returns (caller : Subst) (state : State) (index : Nat)
    (captured : applySubst caller (v "index") = number index) :
    PureReturns program caller state (a "==" [v "index", number 0]) state
      (Effects.boolean (decide (index = 0))) := by
  simpa only [Term.natural.injEq] using
    CettaWireAtom.equality_evaluated_returns program caller state (.natural index) (.natural 0)
      (v "index") (number 0) (by decide +kernel) (by decide +kernel)
      (by simpa only [captured] using variable_returns program caller state "index")
      (grounded_returns program caller state (.int 0))

private theorem data_template (head : String) (arguments : List Atom)
    (supported : head ∈ ["Some", "EqSite", "LCons", "PApp", "GSLTLanguageDefWireV1", "EqAt", "EqPrevious"])
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor _ _ _ _ children
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
    rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
    rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem lcons_template (head tail : String) :
    PureData.Template program (a "LCons" [v head, v tail]) := by
  apply data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem site_template (before : Atom) (checked : PureData.Template program before)
    (focus after : String) :
    PureData.Template program (a "Some" [a "EqSite" [before, v focus, v after]]) := by
  apply data_template _ _ (by simp)
  intro argument member
  have same := List.mem_singleton.mp member
  subst argument
  apply data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact checked
  · exact .captured _
  · exact .captured _

private def splitResult : Atom := a "Some" [a "EqSite" [a "LCons" [v "head", v "before"], v "focus", v "after"]]
private def splitRecurCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"),
   (a "Some" [a "EqSite" [v "before", v "focus", v "after"]], splitResult)]
private def splitRecur : Atom := a "case" [a "gslt:equation-context:split" [v "previous", v "rest"],
  .expression (splitRecurCases.map fun row => .expression [row.1, row.2])]
private def splitLater : Atom := a "let" [v "previous", a "-" [v "index", number 1], splitRecur]
private def splitFirst : Atom := a "Some" [a "EqSite" [.symbol "LNil", v "head", v "rest"]]
private def splitCons : Atom := a "if" [a "==" [v "index", number 0], splitFirst, splitLater]
private def splitCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"), (a "LCons" [v "head", v "rest"], splitCons)]
private theorem split_shape : (equation .split).body = a "case" [v "children",
    .expression (splitCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem split_body_returns (state : State) (index : Nat) (children : List Term) :
    PureReturns program (environment .split [number index, listValue children]) state (equation .split).body state
      (encoded (splitWireTerm index children)) := by
  induction children generalizing index with
  | nil =>
      rw [split_shape]
      let caller := environment .split [number index, listValue []]
      apply case_returns program caller caller state state state (v "children") (.symbol "LNil")
        (.symbol "None") _ _ splitCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "children"
      · simp [splitCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "None"
  | cons head children ih =>
      rw [split_shape]
      let caller := environment .split [number index, listValue (head :: children)]
      let selected := ("rest", listValue children) :: ("head", encoded head) :: caller
      apply case_returns program caller selected state state state (v "children") (listValue (head :: children))
        splitCons _ _ splitCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "children"
      · simp [splitCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, caller, environment, Helper.names,
          CettaWireAtom.encode, selected]
      · unfold splitCons
        apply if_returns program selected state state state _ (Effects.boolean (decide (index = 0))) _ _ _
          (index_zero_returns selected state index (by simp [selected, caller, environment, Helper.names,
            applySubst, Subst.lookup]))
        cases index with
        | zero =>
            simp only [decide_true, beq_self_eq_true, ite_true]
            simpa [splitFirst, splitWireTerm, applySubst, applySubst.applySubstList, Subst.lookup, selected, caller, environment, Helper.names,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList] using
              PureData.template_return program selected state splitFirst
                (site_template (.symbol "LNil") (.symbol _) "head" "rest")
        | succ index =>
            simp only [Nat.succ_ne_zero, decide_false, Effects.boolean]
            let previousBound := ("previous", number index) :: selected
            unfold splitLater
            apply let_returns program selected previousBound state state state (v "previous") _ splitRecur
              (number index) _ _ _ _
            · exact previous_returns selected state index (by simp [selected, caller, environment, Helper.names,
                applySubst, Subst.lookup])
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                selected, caller, environment, Helper.names, previousBound]
            · have continued := helper_call .split previousBound state [number index, listValue children]
                [v "previous", v "rest"] (encoded (splitWireTerm index children)) rfl
                (by simp [previousBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih index)
              cases childRead : children[index]? with
              | none =>
                  have tail : splitWireTerm index children = .symbol "None" := by simp [splitWireTerm, childRead]
                  have whole : splitWireTerm (index + 1) (head :: children) = .symbol "None" := by
                    simp [splitWireTerm, childRead]
                  rw [whole]
                  unfold splitRecur
                  apply case_returns program previousBound previousBound state state state _ (.symbol "None")
                    (.symbol "None") (.symbol "None") _ splitRecurCases (read_cases_encoded _) _ _ _
                  · simpa only [tail, Helper.head, encoded, CettaWireAtom.encode] using continued
                  · simp [splitRecurCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · exact symbol_returns program previousBound state "None"
              | some focus =>
                  let before := children.take index
                  let after := children.drop (index + 1)
                  let siteBound := ("after", listValue after) :: ("focus", encoded focus) ::
                    ("before", listValue before) :: previousBound
                  have tail : splitWireTerm index children =
                      .application "Some" [.application "EqSite" [encodeList id before, focus, encodeList id after]] := by
                    simp [splitWireTerm, childRead, before, after]
                  have whole : splitWireTerm (index + 1) (head :: children) =
                      .application "Some" [.application "EqSite" [encodeList id (head :: before), focus, encodeList id after]] := by
                    simp [splitWireTerm, childRead, before, after]
                  rw [whole]
                  unfold splitRecur
                  apply case_returns program previousBound siteBound state state state _
                    (encoded (.application "Some" [.application "EqSite" [encodeList id before, focus, encodeList id after]]))
                    splitResult _ _ splitRecurCases (read_cases_encoded _) _ _ _
                  · simpa only [tail, Helper.head, encoded, CettaWireAtom.encode] using continued
                  · simp [splitRecurCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, previousBound,
                      selected, caller, environment, Helper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany, siteBound]
                  · simpa [splitResult, applySubst, applySubst.applySubstList, Subst.lookup, siteBound, previousBound, selected, caller,
                      environment, Helper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany, encodeList] using
                      PureData.template_return program siteBound state splitResult
                        (site_template (a "LCons" [v "head", v "before"]) (lcons_template _ _) "focus" "after")

/-- The retained splitter finds the physical child and preserves its ordered
prefix/suffix. Missing indices return `None` without changing state or I/O. -/
theorem split_captured_returns (caller : Subst) (state : State) (index : Nat) (children : List Term)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, listValue children]) :
    PureReturns program caller state (a "gslt:equation-context:split" [one, two]) state
      (encoded (splitWireTerm index children)) :=
  helper_call .split caller state _ _ _ rfl captured (split_body_returns state index children)

def focusWireTerm (position : SubtermMatching.Position) (subject : PatternPlan) : Term :=
  MatchAutomataBindingExecution.patternOptionTerm
    ((MeTTaILSubtermMatchAutomata.selectSite? subject position).map fun site => site.2.erase)

private theorem children_as_list (children : List PatternPlan) :
    InferenceCettaWire.encodePatterns (erasePatterns children) =
      encodeList id (children.map fun child => InferenceCettaWire.encodePattern child.erase) := by
  rw [InferenceCettaWire.encodePatterns_eq_encodeList, erasePatterns_eq_map]
  simp only [encodeList_map, Function.comp_def, id_eq]

private theorem patterns_as_list (patterns : List Pattern) :
    InferenceCettaWire.encodePatterns patterns = encodeList id (patterns.map InferenceCettaWire.encodePattern) := by
  rw [InferenceCettaWire.encodePatterns_eq_encodeList]
  simp only [encodeList_map, Function.comp_def, id_eq]

private theorem row_at_returns (caller : Subst) (state : State) (index : Nat) (children : List PatternPlan)
    (captured : [v "index", v "children"].map (applySubst caller) =
      [number index, listValue (children.map fun child => InferenceCettaWire.encodePattern child.erase)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [v "index", v "children"]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm (children[index]?.map PatternPlan.erase))) := by
  apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
  apply EquationExecutionProgram.retained_captured_returns (by decide +kernel)
  have returned := RootRuleExecution.Matched.row_at_captured_returns caller state index
    (children.map fun child => InferenceCettaWire.encodePattern child.erase) (v "index") (v "children") captured
  cases childRead : children[index]? with
  | none =>
      simp only [List.getElem?_map, childRead, Option.map_none] at returned
      exact returned
  | some child =>
      simp only [List.getElem?_map, childRead, Option.map_some] at returned
      exact returned

private def focusChildCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"),
    (a "Some" [v "child"], a "gslt:equation-context:focus" [v "path", v "child"])]
private def focusChild : Atom := a "case" [a "gslt:rule:row-at" [v "index", v "children"],
  .expression (focusChildCases.map fun row => .expression [row.1, row.2])]
private def focusCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", v "value"], a "Some" [v "value"]),
   (.expression [a "LCons" [v "index", v "path"], a "PApp" [v "head", v "children"]], focusChild),
   (v "bad", .symbol "None")]
private theorem focus_shape : (equation .focus).body = a "case" [.expression [v "position", v "subject"],
    .expression (focusCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem some_template (name : String) : PureData.Template program (a "Some" [v name]) := by
  apply data_template _ _ (by simp)
  intro argument member
  rw [List.mem_singleton] at member
  subst argument
  exact .captured _

private theorem focus_body_returns (state : State) (position : SubtermMatching.Position) (subject : PatternPlan) :
    PureReturns program (environment .focus [encoded (EquationExecution.pathTerm position),
        encoded (InferenceCettaWire.encodePattern subject.erase)]) state (equation .focus).body state
      (encoded (focusWireTerm position subject)) := by
  induction position generalizing subject with
  | nil =>
      let caller := environment .focus [encoded (EquationExecution.pathTerm []),
        encoded (InferenceCettaWire.encodePattern subject.erase)]
      let selected := ("value", encoded (InferenceCettaWire.encodePattern subject.erase)) :: caller
      rw [focus_shape]
      apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
        (.expression [.symbol "LNil", encoded (InferenceCettaWire.encodePattern subject.erase)])
        (a "Some" [v "value"]) _ _ focusCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, EquationExecution.pathTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using PureData.variables_return program caller state ["position", "subject"]
      · simp [focusCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · simpa [focusWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
          selected, caller, environment, Helper.names] using
            PureData.template_return program selected state (a "Some" [v "value"]) (some_template "value")
  | cons index position ih =>
      let caller := environment .focus [encoded (EquationExecution.pathTerm (index :: position)),
        encoded (InferenceCettaWire.encodePattern subject.erase)]
      rw [focus_shape]
      cases subject with
      | metavariable name =>
          let pair : Atom := .expression [encoded (EquationExecution.pathTerm (index :: position)),
            encoded (InferenceCettaWire.encodePattern (.fvar name))]
          let selected := ("bad", pair) :: caller
          apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
            pair (.symbol "None") _ _ focusCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, PatternPlan.erase, pair, applySubst, Subst.lookup] using
              PureData.variables_return program caller state ["position", "subject"]
          · simp [focusCases, pair, EquationExecution.pathTerm, encodeList, InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names,
              PatternPlan.erase]
          · simpa [focusWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, MatchAutomataBindingExecution.patternOptionTerm,
              CettaWireAtom.encode] using symbol_returns program selected state "None"
      | bound boundIndex =>
          let pair : Atom := .expression [encoded (EquationExecution.pathTerm (index :: position)),
            encoded (InferenceCettaWire.encodePattern (.bvar boundIndex))]
          let selected := ("bad", pair) :: caller
          apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
            pair (.symbol "None") _ _ focusCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, PatternPlan.erase, pair, applySubst, Subst.lookup] using
              PureData.variables_return program caller state ["position", "subject"]
          · simp [focusCases, pair, EquationExecution.pathTerm, encodeList, InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names,
              PatternPlan.erase]
          · simpa [focusWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, MatchAutomataBindingExecution.patternOptionTerm,
              CettaWireAtom.encode] using symbol_returns program selected state "None"
      | application head children =>
          let childrenValue := listValue (children.map fun child => InferenceCettaWire.encodePattern child.erase)
          let selected := ("children", childrenValue) :: ("head", encoded (.string head)) ::
            ("path", encoded (EquationExecution.pathTerm position)) :: ("index", number index) :: caller
          apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
            (.expression [encoded (EquationExecution.pathTerm (index :: position)),
              encoded (InferenceCettaWire.encodePattern (.apply head (erasePatterns children)))])
            focusChild _ _ focusCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, PatternPlan.erase, applySubst, Subst.lookup] using
              PureData.variables_return program caller state ["position", "subject"]
          · simp [focusCases, EquationExecution.pathTerm, encodeList, InferenceCettaWire.encodePattern,
              children_as_list, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
              selected, caller, environment, Helper.names, PatternPlan.erase, childrenValue]
          · have lookedUp := row_at_returns selected state index children
                (by simp [selected, caller, environment, Helper.names, childrenValue, applySubst, Subst.lookup])
            unfold focusChild
            cases childRead : children[index]? with
            | none =>
                apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
                  focusChildCases (read_cases_encoded _) _ _ _
                · simpa [childRead, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using lookedUp
                · simp [focusChildCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · simpa [focusWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, childRead,
                    MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                      symbol_returns program selected state "None"
            | some child =>
                let bound := ("child", encoded (InferenceCettaWire.encodePattern child.erase)) :: selected
                apply case_returns program selected bound state state state _
                  (a "Some" [encoded (InferenceCettaWire.encodePattern child.erase)])
                  (a "gslt:equation-context:focus" [v "path", v "child"]) _ _ focusChildCases (read_cases_encoded _) _ _ _
                · simpa [childRead, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode,
                    CettaWireAtom.encodeMany] using lookedUp
                · simp [focusChildCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, selected, caller,
                    environment, Helper.names]
                · have same : focusWireTerm (index :: position) (.application head children) = focusWireTerm position child := by
                    cases inner : MeTTaILSubtermMatchAutomata.selectSite? child position <;>
                      simp [focusWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, childRead, inner]
                  rw [same]
                  exact helper_call .focus bound state
                    [encoded (EquationExecution.pathTerm position), encoded (InferenceCettaWire.encodePattern child.erase)]
                    [v "path", v "child"] _ rfl
                    (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih child)

/-- Focus follows the actual physical position; equal siblings remain distinct
sites and missing paths are explicitly refused. -/
theorem focus_captured_returns (caller : Subst) (state : State) (position : SubtermMatching.Position)
    (subject : PatternPlan) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (EquationExecution.pathTerm position), encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:equation-context:focus" [one, two]) state
      (encoded (focusWireTerm position subject)) :=
  helper_call .focus caller state _ _ _ rfl captured (focus_body_returns state position subject)

def replaceWireTerm (position : SubtermMatching.Position) (subject : PatternPlan) (target : Pattern) : Term :=
  MatchAutomataBindingExecution.patternOptionTerm
    ((MeTTaILSubtermMatchAutomata.selectSite? subject position).map fun site => site.1.fill target)

private def replaceResult : Atom := a "Some" [a "PApp" [v "head", v "filled"]]
private def replaceFill : Atom := a "let" [v "filled",
  a "gslt:automata:append" [v "before", a "LCons" [v "replacement", v "after"]], replaceResult]
private def replaceInnerCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "replacement"], replaceFill)]
private def replaceInner : Atom := a "case" [a "gslt:equation-context:replace" [v "path", v "focus", v "target"],
  .expression (replaceInnerCases.map fun row => .expression [row.1, row.2])]
private def replaceSiteCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [a "EqSite" [v "before", v "focus", v "after"]], replaceInner)]
private def replaceSite : Atom := a "case" [a "gslt:equation-context:split" [v "index", v "children"],
  .expression (replaceSiteCases.map fun row => .expression [row.1, row.2])]
private def replaceCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", v "value"], a "Some" [v "target"]),
   (.expression [a "LCons" [v "index", v "path"], a "PApp" [v "head", v "children"]], replaceSite),
   (v "bad", .symbol "None")]
private theorem replace_shape : (equation .replace).body = a "case" [.expression [v "position", v "subject"],
    .expression (replaceCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem replace_result_template : PureData.Template program replaceResult := by
  apply data_template _ _ (by simp)
  intro argument member
  rw [List.mem_singleton] at member
  subst argument
  apply data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem append_fill_returns (caller : Subst) (state : State) (before after : List Term) (replacement : Term)
    (captured : [v "before", a "LCons" [v "replacement", v "after"]].map (applySubst caller) =
      [listValue before, listValue (replacement :: after)]) :
    PureReturns program caller state
      (a "gslt:automata:append" [v "before", a "LCons" [v "replacement", v "after"]]) state
      (listValue (before ++ replacement :: after)) := by
  apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
  apply EquationExecutionProgram.retained_captured_returns (by decide +kernel)
  apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
  exact MatchAutomataSourceExecution.append_captured_returns caller state before (replacement :: after)
    _ _ captured

private theorem replace_body_returns (state : State) (position : SubtermMatching.Position) (subject : PatternPlan)
    (target : Pattern) :
    PureReturns program (environment .replace [encoded (EquationExecution.pathTerm position),
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePattern target)])
      state (equation .replace).body state (encoded (replaceWireTerm position subject target)) := by
  induction position generalizing subject with
  | nil =>
      let caller := environment .replace [encoded (EquationExecution.pathTerm []),
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePattern target)]
      let selected := ("value", encoded (InferenceCettaWire.encodePattern subject.erase)) :: caller
      rw [replace_shape]
      apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
        (.expression [.symbol "LNil", encoded (InferenceCettaWire.encodePattern subject.erase)])
        (a "Some" [v "target"]) _ _ replaceCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, EquationExecution.pathTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using PureData.variables_return program caller state ["position", "subject"]
      · simp [replaceCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · simpa [replaceWireTerm, MeTTaILSubtermMatchAutomata.selectSite?,
          Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
          selected, caller, environment, Helper.names] using
            PureData.template_return program selected state (a "Some" [v "target"]) (some_template "target")
  | cons index position ih =>
      let caller := environment .replace [encoded (EquationExecution.pathTerm (index :: position)),
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePattern target)]
      rw [replace_shape]
      cases subject with
      | metavariable name =>
          let pair : Atom := .expression [encoded (EquationExecution.pathTerm (index :: position)),
            encoded (InferenceCettaWire.encodePattern (.fvar name))]
          let selected := ("bad", pair) :: caller
          apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
            pair (.symbol "None") _ _ replaceCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, PatternPlan.erase, pair, applySubst, Subst.lookup] using
              PureData.variables_return program caller state ["position", "subject"]
          · simp [replaceCases, pair, EquationExecution.pathTerm, encodeList, InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names,
              PatternPlan.erase]
          · simpa [replaceWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, MatchAutomataBindingExecution.patternOptionTerm,
              CettaWireAtom.encode] using symbol_returns program selected state "None"
      | bound boundIndex =>
          let pair : Atom := .expression [encoded (EquationExecution.pathTerm (index :: position)),
            encoded (InferenceCettaWire.encodePattern (.bvar boundIndex))]
          let selected := ("bad", pair) :: caller
          apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
            pair (.symbol "None") _ _ replaceCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, PatternPlan.erase, pair, applySubst, Subst.lookup] using
              PureData.variables_return program caller state ["position", "subject"]
          · simp [replaceCases, pair, EquationExecution.pathTerm, encodeList, InferenceCettaWire.encodePattern,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names,
              PatternPlan.erase]
          · simpa [replaceWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, MatchAutomataBindingExecution.patternOptionTerm,
              CettaWireAtom.encode] using symbol_returns program selected state "None"
      | application head children =>
          let before := children.take index
          let after := children.drop (index + 1)
          let childTerms := children.map fun child => InferenceCettaWire.encodePattern child.erase
          let selected := ("children", listValue childTerms) :: ("head", encoded (.string head)) ::
            ("path", encoded (EquationExecution.pathTerm position)) :: ("index", number index) :: caller
          apply case_returns program caller selected state state state (.expression [v "position", v "subject"])
            (.expression [encoded (EquationExecution.pathTerm (index :: position)),
              encoded (InferenceCettaWire.encodePattern (.apply head (erasePatterns children)))])
            replaceSite _ _ replaceCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, PatternPlan.erase, applySubst, Subst.lookup] using
              PureData.variables_return program caller state ["position", "subject"]
          · simp [replaceCases, EquationExecution.pathTerm, encodeList, InferenceCettaWire.encodePattern,
              children_as_list, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
              selected, caller, environment, Helper.names, PatternPlan.erase, childTerms]
          · have split := split_captured_returns selected state index childTerms (v "index") (v "children")
                (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            unfold replaceSite
            cases childRead : children[index]? with
            | none =>
                apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
                  replaceSiteCases (read_cases_encoded _) _ _ _
                · simpa [splitWireTerm, childTerms, List.getElem?_map, childRead, CettaWireAtom.encode] using split
                · simp [replaceSiteCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · simpa [replaceWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, childRead,
                    MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                      symbol_returns program selected state "None"
            | some child =>
                let siteBound := ("after", listValue (after.map fun child => InferenceCettaWire.encodePattern child.erase)) ::
                  ("focus", encoded (InferenceCettaWire.encodePattern child.erase)) ::
                  ("before", listValue (before.map fun child => InferenceCettaWire.encodePattern child.erase)) :: selected
                apply case_returns program selected siteBound state state state _
                  (a "Some" [a "EqSite" [listValue (before.map fun child => InferenceCettaWire.encodePattern child.erase),
                    encoded (InferenceCettaWire.encodePattern child.erase),
                    listValue (after.map fun child => InferenceCettaWire.encodePattern child.erase)]])
                  replaceInner _ _ replaceSiteCases (read_cases_encoded _) _ _ _
                · simpa [splitWireTerm, childTerms, List.getElem?_map, childRead, List.map_take, List.map_drop,
                    before, after, CettaWireAtom.encode, CettaWireAtom.encodeMany] using split
                · simp [replaceSiteCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, siteBound, selected, caller,
                    environment, Helper.names]
                · have continued := helper_call .replace siteBound state
                    [encoded (EquationExecution.pathTerm position), encoded (InferenceCettaWire.encodePattern child.erase),
                      encoded (InferenceCettaWire.encodePattern target)]
                    [v "path", v "focus", v "target"] _ rfl
                    (by simp [siteBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih child)
                  unfold replaceInner
                  cases innerRead : MeTTaILSubtermMatchAutomata.selectSite? child position with
                  | none =>
                      apply case_returns program siteBound siteBound state state state _ (.symbol "None") (.symbol "None") _ _
                        replaceInnerCases (read_cases_encoded _) _ _ _
                      · simpa [Helper.head, replaceWireTerm, innerRead, MatchAutomataBindingExecution.patternOptionTerm,
                          CettaWireAtom.encode] using continued
                      · simp [replaceInnerCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                      · simpa [replaceWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, childRead, innerRead,
                          MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                            symbol_returns program siteBound state "None"
                  | some inner =>
                      let actual := inner.1.fill target
                      let resultBound := ("replacement", encoded (InferenceCettaWire.encodePattern actual)) :: siteBound
                      let filledTerms := (before.map fun child => InferenceCettaWire.encodePattern child.erase) ++
                        InferenceCettaWire.encodePattern actual :: (after.map fun child => InferenceCettaWire.encodePattern child.erase)
                      let filledBound := ("filled", listValue filledTerms) :: resultBound
                      apply case_returns program siteBound resultBound state state state _
                        (a "Some" [encoded (InferenceCettaWire.encodePattern actual)]) replaceFill _ _
                        replaceInnerCases (read_cases_encoded _) _ _ _
                      · simpa [Helper.head, replaceWireTerm, innerRead, actual, MatchAutomataBindingExecution.patternOptionTerm,
                          CettaWireAtom.encode, CettaWireAtom.encodeMany] using continued
                      · simp [replaceInnerCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, resultBound, siteBound,
                          selected, caller, environment, Helper.names]
                      · unfold replaceFill
                        apply let_returns program resultBound filledBound state state state (v "filled") _ replaceResult
                          (listValue filledTerms) _ _ _ _
                        · exact append_fill_returns resultBound state _ _ _
                            (by simp [resultBound, siteBound, selected, caller, environment, Helper.names,
                              applySubst, applySubst.applySubstList, Subst.lookup,
                              CettaWireAtom.encode])
                        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                            filledBound, resultBound, siteBound, selected, caller, environment, Helper.names]
                        · simpa [replaceResult, replaceWireTerm, MeTTaILSubtermMatchAutomata.selectSite?, childRead, innerRead,
                            Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, MatchAutomataBindingExecution.patternOptionTerm,
                            InferenceCettaWire.encodePattern, patterns_as_list, erasePatterns_eq_map,
                            List.map_append, List.map_cons, List.map_map, List.map_take, List.map_drop, Function.comp_def,
                            actual, before, after, filledTerms, applySubst, applySubst.applySubstList, Subst.lookup,
                            filledBound, resultBound, siteBound, selected, caller, environment, Helper.names,
                            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                              PureData.template_return program filledBound state replaceResult replace_result_template

/-- The source replacement reconstructs exactly the existing one-hole context;
it preserves every sibling and refuses a missing physical position. -/
theorem replace_captured_returns (caller : Subst) (state : State) (position : SubtermMatching.Position)
    (subject : PatternPlan) (target : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (EquationExecution.pathTerm position), encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (InferenceCettaWire.encodePattern target)]) :
    PureReturns program caller state (a "gslt:equation-context:replace" [one, two, three]) state
      (encoded (replaceWireTerm position subject target)) :=
  helper_call .replace caller state _ _ _ rfl captured (replace_body_returns state position subject target)

private abbrev rowsValue (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Atom :=
  encoded (providerRowsTerm rows)

private def validateAccept : Atom := a "if" [a "==" [v "actual", v "whole"], a "Some" [v "actual"], .symbol "None"]
private def validateReplaceCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "actual"], validateAccept)]
private def validateReplace : Atom := a "case" [a "gslt:equation-context:replace" [v "position", v "subject", v "target"],
  .expression (validateReplaceCases.map fun row => .expression [row.1, row.2])]
private def validateAtomicCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "target"], validateReplace)]
private def validateAtomic : Atom := a "case" [a "gslt:equation:validate" [v "equations", v "rows", v "focus", v "atomic"],
  .expression (validateAtomicCases.map fun row => .expression [row.1, row.2])]
private def validateFocusCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "focus"], validateAtomic)]
private def validateFocus : Atom := a "case" [a "gslt:equation-context:focus" [v "position", v "subject"],
  .expression (validateFocusCases.map fun row => .expression [row.1, row.2])]
private def validatePreviousAccept : Atom :=
  a "if" [a "==" [v "actual", v "subject"], a "Some" [v "predecessor"], .symbol "None"]
private def validatePreviousCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "actual"], validatePreviousAccept)]
private def validatePrevious : Atom := a "case" [a "gslt:equation-context:validate"
    [v "equations", v "rows", v "predecessor", a "EqAt" [v "position", v "atomic", v "whole"]],
  .expression (validatePreviousCases.map fun row => .expression [row.1, row.2])]
private def validateCases : SpaceSemantics.Cases :=
  [(a "EqAt" [v "position", v "atomic", v "whole"], validateFocus),
    (a "EqPrevious" [v "predecessor", a "EqAt" [v "position", v "atomic", v "whole"]], validatePrevious),
    (v "bad", .symbol "None")]
private theorem validate_shape : (equation .validate).body = a "case" [v "receipt",
    .expression (validateCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem pattern_equal_returns (caller : Subst) (state : State) (actual claimed : Pattern)
    (one two : String)
    (left : applySubst caller (v one) = encoded (InferenceCettaWire.encodePattern actual))
    (right : applySubst caller (v two) = encoded (InferenceCettaWire.encodePattern claimed)) :
    PureReturns program caller state (a "==" [v one, v two]) state
      (Effects.boolean (decide (actual = claimed))) := by
  simpa only [InferenceCettaWire.encodePattern_injective.eq_iff] using
    CettaWireAtom.equality_evaluated_returns program caller state
      (InferenceCettaWire.encodePattern actual) (InferenceCettaWire.encodePattern claimed) (v one) (v two)
      (by decide +kernel) (by decide +kernel)
      (by simpa only [left] using variable_returns program caller state one)
      (by simpa only [right] using variable_returns program caller state two)

private theorem validate_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) :
    PureReturns program (environment .validate [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (positionedReceiptTerm receipt)]) state
      (equation .validate).body state (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validatePositionedReceipt? (providerEnv rows) language plans subject receipt))) := by
  let caller := environment .validate [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase), encoded (positionedReceiptTerm receipt)]
  let selected := ("whole", encoded (InferenceCettaWire.encodePattern receipt.target)) ::
    ("atomic", encoded (EquationExecution.receiptTerm receipt.atomic)) ::
    ("position", encoded (EquationExecution.pathTerm receipt.position)) :: caller
  rw [validate_shape]
  apply case_returns program caller selected state state state (v "receipt") (encoded (positionedReceiptTerm receipt))
    validateFocus _ _ validateCases (read_cases_encoded _) _ _ _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "receipt"
  · simp [validateCases, positionedReceiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
  · have focused := focus_captured_returns selected state receipt.position subject (v "position") (v "subject")
        (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
    unfold validateFocus
    cases selectedSite : MeTTaILSubtermMatchAutomata.selectSite? subject receipt.position with
    | none =>
        apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
          validateFocusCases (read_cases_encoded _) _ _ _
        · simpa [focusWireTerm, selectedSite, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using focused
        · simp [validateFocusCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [validatePositionedReceipt?, selectedSite, MatchAutomataBindingExecution.patternOptionTerm,
            CettaWireAtom.encode] using symbol_returns program selected state "None"
    | some site =>
        let focusBound := ("focus", encoded (InferenceCettaWire.encodePattern site.2.erase)) :: selected
        apply case_returns program selected focusBound state state state _
          (a "Some" [encoded (InferenceCettaWire.encodePattern site.2.erase)]) validateAtomic _ _
          validateFocusCases (read_cases_encoded _) _ _ _
        · simpa [focusWireTerm, selectedSite, MatchAutomataBindingExecution.patternOptionTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using focused
        · simp [validateFocusCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, focusBound, selected, caller,
            environment, Helper.names]
        · have validated : PureReturns program focusBound state
              (a "gslt:equation:validate" [v "equations", v "rows", v "focus", v "atomic"]) state
              (encoded (MatchAutomataBindingExecution.patternOptionTerm
                (validateReceipt? (providerEnv rows) language plans site.2.erase receipt.atomic))) := by
            apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
            exact EquationExecution.validate_captured_returns focusBound state language rows contexts plans.val plans.property site.2 receipt.atomic
              _ _ _ _ (by simp [focusBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          unfold validateAtomic
          cases localRead : validateReceipt? (providerEnv rows) language plans site.2.erase receipt.atomic with
          | none =>
              apply case_returns program focusBound focusBound state state state _ (.symbol "None") (.symbol "None") _ _
                validateAtomicCases (read_cases_encoded _) _ _ _
              · simpa [localRead, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using validated
              · simp [validateAtomicCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [validatePositionedReceipt?, selectedSite, localRead, MatchAutomataBindingExecution.patternOptionTerm,
                  CettaWireAtom.encode] using symbol_returns program focusBound state "None"
          | some localTarget =>
              let targetBound := ("target", encoded (InferenceCettaWire.encodePattern localTarget)) :: focusBound
              let actual := site.1.fill localTarget
              let actualBound := ("actual", encoded (InferenceCettaWire.encodePattern actual)) :: targetBound
              apply case_returns program focusBound targetBound state state state _
                (a "Some" [encoded (InferenceCettaWire.encodePattern localTarget)]) validateReplace _ _
                validateAtomicCases (read_cases_encoded _) _ _ _
              · simpa [localRead, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany] using validated
              · simp [validateAtomicCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, targetBound, focusBound,
                  selected, caller, environment, Helper.names]
              · have replaced := replace_captured_returns targetBound state receipt.position subject localTarget
                  (v "position") (v "subject") (v "target")
                  (by simp [targetBound, focusBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                unfold validateReplace
                apply case_returns program targetBound actualBound state state state _
                  (a "Some" [encoded (InferenceCettaWire.encodePattern actual)]) validateAccept _ _
                  validateReplaceCases (read_cases_encoded _) _ _ _
                · simpa [replaceWireTerm, selectedSite, actual, MatchAutomataBindingExecution.patternOptionTerm,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany] using replaced
                · simp [validateReplaceCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, actualBound, targetBound,
                    focusBound, selected, caller, environment, Helper.names]
                · have compared := pattern_equal_returns actualBound state actual receipt.target "actual" "whole"
                    (by simp [actualBound, targetBound, focusBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                    (by simp [actualBound, targetBound, focusBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                  unfold validateAccept
                  apply if_returns program actualBound state state state _ (Effects.boolean (decide (actual = receipt.target)))
                    _ _ _ compared
                  by_cases same : actual = receipt.target
                  · simp only [same, decide_true, Effects.boolean]
                    simpa [validatePositionedReceipt?, selectedSite, localRead, guard, actual, same,
                      MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                      applySubst, applySubst.applySubstList, Subst.lookup, actualBound, targetBound, focusBound,
                      selected, caller, environment, Helper.names] using
                        PureData.template_return program actualBound state (a "Some" [v "actual"]) (some_template "actual")
                  · simp only [same, decide_false, Effects.boolean]
                    simpa [validatePositionedReceipt?, selectedSite, localRead, guard, actual, same,
                      MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                        symbol_returns program actualBound state "None"

/-- Actual source validation resolves the site, validates the complete atomic
receipt, reconstructs the whole term and checks the claimed whole target. -/
theorem validate_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (positionedReceiptTerm receipt)]) :
    PureReturns program caller state (a "gslt:equation-context:validate" [one, two, three, four]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validatePositionedReceipt? (providerEnv rows) language plans subject receipt))) :=
  helper_call .validate caller state _ _ _ rfl captured (validate_body_returns state language rows contexts plans subject receipt)

/-- Signed receipt encoding reuses the complete positioned receipt wire.
Previous receipts retain that original witness and its supplied predecessor. -/
def signedReceiptTerm : SignedReceipt → Term
  | .inl receipt => positionedReceiptTerm receipt
  | .inr (predecessor, receipt) =>
      .application "EqPrevious" [InferenceCettaWire.encodePattern predecessor.erase, positionedReceiptTerm receipt]

def signedReceiptsTerm (receipts : List SignedReceipt) : Term := encodeList signedReceiptTerm receipts

def positionedReceiptsTerm (receipts : List PositionedReceipt) : Term := encodeList positionedReceiptTerm receipts
def replayResultTerm (result : Option PatternPlan) : Term :=
  MatchAutomataBindingExecution.patternOptionTerm (result.map PatternPlan.erase)

private def replayNext : Atom := a "gslt:equation-context:replay" [v "equations", v "rows", v "next", v "rest"]
private def replayValidateCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "next"], replayNext)]
private def replayValidate : Atom := a "case" [a "gslt:equation-context:validate"
  [v "equations", v "rows", v "subject", v "receipt"],
  .expression (replayValidateCases.map fun row => .expression [row.1, row.2])]
private def replayCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [v "subject"]), (a "LCons" [v "receipt", v "rest"], replayValidate),
    (v "bad", .symbol "None")]
private theorem replay_shape : (equation .replay).body = a "case" [v "receipts",
    .expression (replayCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

/-- Check the original oriented receipt before accepting its reversed edge. -/
private theorem validate_previous_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject predecessor : PatternPlan) (receipt : PositionedReceipt) :
    PureReturns program (environment .validate [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (signedReceiptTerm (.inr (predecessor, receipt)))]) state
      (equation .validate).body state
      (encoded (replayResultTerm (validateSignedReceipt? (providerEnv rows) language plans subject (.inr (predecessor, receipt))))) := by
  let caller := environment .validate [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase), encoded (signedReceiptTerm (.inr (predecessor, receipt)))]
  let selected := ("whole", encoded (InferenceCettaWire.encodePattern receipt.target)) ::
    ("atomic", encoded (EquationExecution.receiptTerm receipt.atomic)) ::
    ("position", encoded (EquationExecution.pathTerm receipt.position)) ::
    ("predecessor", encoded (InferenceCettaWire.encodePattern predecessor.erase)) :: caller
  rw [validate_shape]
  apply case_returns program caller selected state state state (v "receipt")
    (encoded (signedReceiptTerm (.inr (predecessor, receipt)))) validatePrevious _ _
    validateCases (read_cases_encoded _) _ _ _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "receipt"
  · simp [validateCases, signedReceiptTerm, positionedReceiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
  · have validated := validate_captured_returns selected state language rows contexts plans predecessor receipt
      (v "equations") (v "rows") (v "predecessor") (a "EqAt" [v "position", v "atomic", v "whole"])
      (by simp [selected, caller, environment, Helper.names, applySubst, applySubst.applySubstList,
        Subst.lookup, positionedReceiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany])
    unfold validatePrevious
    cases localRead : validatePositionedReceipt? (providerEnv rows) language plans predecessor receipt with
    | none =>
        apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
          validatePreviousCases (read_cases_encoded _) _ _ _
        · simpa [localRead, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using validated
        · simp [validatePreviousCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [validateSignedReceipt?, localRead, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
            CettaWireAtom.encode] using symbol_returns program selected state "None"
    | some actual =>
        let actualBound := ("actual", encoded (InferenceCettaWire.encodePattern actual)) :: selected
        apply case_returns program selected actualBound state state state _
          (a "Some" [encoded (InferenceCettaWire.encodePattern actual)]) validatePreviousAccept _ _
          validatePreviousCases (read_cases_encoded _) _ _ _
        · simpa [localRead, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using validated
        · simp [validatePreviousCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, actualBound, selected,
            caller, environment, Helper.names]
        · have compared := pattern_equal_returns actualBound state actual subject.erase "actual" "subject"
            (by simp [actualBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [actualBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          unfold validatePreviousAccept
          apply if_returns program actualBound state state state _ (Effects.boolean (decide (actual = subject.erase)))
            _ _ _ compared
          by_cases same : actual = subject.erase
          · simp only [same, decide_true, Effects.boolean]
            simpa [validateSignedReceipt?, localRead, guard, same, replayResultTerm,
              MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup, actualBound, selected, caller,
              environment, Helper.names] using
                PureData.template_return program actualBound state (a "Some" [v "predecessor"]) (some_template "predecessor")
          · simp only [same, decide_false, Effects.boolean]
            simpa [validateSignedReceipt?, localRead, guard, same, replayResultTerm,
              MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using
                symbol_returns program actualBound state "None"

/-- Compose the retained replay body from actual checked step calls. -/
private theorem replay_body_returns_of_step {Event : Type}
    (eventTerm : Event → Term) (check : PatternPlan → Event → Option PatternPlan)
    (state : State) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (stepReturns : ∀ (caller : Subst) (subject : PatternPlan) (event : Event) (arguments : List Atom),
      arguments.map (applySubst caller) =
        [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
          encoded (InferenceCettaWire.encodePattern subject.erase), encoded (eventTerm event)] →
      PureReturns program caller state (a "gslt:equation-context:validate" arguments) state
        (encoded (replayResultTerm (check subject event))))
    (subject : PatternPlan) (receipts : List Event) :
    PureReturns program (environment .replay [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (encodeList eventTerm receipts)]) state
      (equation .replay).body state
      (encoded (replayResultTerm (receipts.foldlM (init := subject) check))) := by
  induction receipts generalizing subject with
  | nil =>
      let caller := environment .replay [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded ((encodeList eventTerm) [])]
      rw [replay_shape]
      apply case_returns program caller caller state state state (v "receipts") (.symbol "LNil")
        (a "Some" [v "subject"]) _ _ replayCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "receipts"
      · simp [replayCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [replayResultTerm, List.foldlM_nil, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup,
          caller, environment, Helper.names] using
            PureData.template_return program caller state (a "Some" [v "subject"]) (some_template "subject")
  | cons receipt receipts ih =>
      let caller := environment .replay [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded ((encodeList eventTerm) (receipt :: receipts))]
      let selected := ("rest", encoded ((encodeList eventTerm) receipts)) ::
        ("receipt", encoded (eventTerm receipt)) :: caller
      rw [replay_shape]
      apply case_returns program caller selected state state state (v "receipts")
        (encoded ((encodeList eventTerm) (receipt :: receipts))) replayValidate _ _
        replayCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "receipts"
      · simp [replayCases, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · have validated := stepReturns selected subject receipt
          [v "equations", v "rows", v "subject", v "receipt"]
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        unfold replayValidate
        cases localRead : check subject receipt with
        | none =>
            apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
              replayValidateCases (read_cases_encoded _) _ _ _
            · simpa [localRead, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using validated
            · simp [replayValidateCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [replayResultTerm, List.foldlM_cons, localRead, MatchAutomataBindingExecution.patternOptionTerm,
                CettaWireAtom.encode] using symbol_returns program selected state "None"
        | some next =>
            let actual := next.erase
            let bound := ("next", encoded (InferenceCettaWire.encodePattern actual)) :: selected
            apply case_returns program selected bound state state state _
              (a "Some" [encoded (InferenceCettaWire.encodePattern actual)]) replayNext _ _
              replayValidateCases (read_cases_encoded _) _ _ _
            · simpa [localRead, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode,
                CettaWireAtom.encodeMany] using validated
            · simp [replayValidateCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, selected,
                caller, environment, Helper.names]
            · unfold replayNext
              have continued := helper_call .replay bound state
                [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
                  encoded (InferenceCettaWire.encodePattern next.erase), encoded ((encodeList eventTerm) receipts)]
                [v "equations", v "rows", v "next", v "rest"] _ rfl
                (by simp [bound, selected, caller, environment, Helper.names, actual, applySubst, Subst.lookup]) (ih next)
              simpa only [Helper.head, List.foldlM_cons, localRead, Option.bind_eq_bind,
                Option.bind_some] using continued


private theorem forward_validation_result (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (rowsFirstOrder : FirstOrderRelations (providerEnv rows)) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) :
    replayResultTerm (validateSignedReceipt? (providerEnv rows) language plans subject (.inl receipt)) =
      MatchAutomataBindingExecution.patternOptionTerm
        (validatePositionedReceipt? (providerEnv rows) language plans subject receipt) := by
  cases checked : validatePositionedReceipt? (providerEnv rows) language plans subject receipt with
  | none => simp [replayResultTerm, validateSignedReceipt?, checked]
  | some actual =>
      have firstOrder := validated_positioned_firstOrder (providerEnv rows) language rowsFirstOrder plans subject receipt actual checked
      cases compiled : compilePattern? actual with
      | none =>
          have admission := compilePattern?_isSome_eq_isMatchCorrectAux actual
          simp only [compiled, Option.isSome_none, firstOrder] at admission
          cases admission
      | some next =>
          simp only [validateSignedReceipt?, checked, compiled, Option.bind_eq_bind, Option.bind_some,
            replayResultTerm, Option.map_some, erase_of_compilePattern? actual next compiled]

private theorem forward_validation_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (rowsFirstOrder : FirstOrderRelations (providerEnv rows))
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (positionedReceiptTerm receipt)]) :
    PureReturns program caller state (a "gslt:equation-context:validate" arguments) state
      (encoded (replayResultTerm (validateSignedReceipt? (providerEnv rows) language plans subject (.inl receipt)))) := by
  rw [forward_validation_result language rows rowsFirstOrder plans subject receipt]
  exact helper_call .validate caller state _ _ _ rfl captured
    (validate_body_returns state language rows contexts plans subject receipt)

private theorem validate_signed_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (rowsFirstOrder : FirstOrderRelations (providerEnv rows))
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : SignedReceipt) :
    PureReturns program (environment .validate [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (signedReceiptTerm receipt)]) state
      (equation .validate).body state
      (encoded (replayResultTerm (validateSignedReceipt? (providerEnv rows) language plans subject receipt))) := by
  cases receipt with
  | inl receipt =>
      rw [forward_validation_result language rows rowsFirstOrder plans subject receipt]
      simpa only [signedReceiptTerm] using validate_body_returns state language rows contexts plans subject receipt
  | inr previous => exact validate_previous_body_returns state language rows contexts plans subject previous.1 previous.2

/-- Actual validation of either a forward receipt or a checked reversal. -/
theorem validate_signed_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : SignedReceipt) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (signedReceiptTerm receipt)]) :
    PureReturns program caller state (a "gslt:equation-context:validate" arguments) state
      (encoded (replayResultTerm (validateSignedReceipt? (providerEnv rows) language plans subject receipt))) :=
  helper_call .validate caller state _ _ _ rfl captured
    (validate_signed_body_returns state language rows (RuleTraceExecution.providerEnv_firstOrder rows admitted)
      contexts plans subject receipt)

private theorem replay_signed_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List SignedReceipt) :
    PureReturns program (environment .replay [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (signedReceiptsTerm receipts)]) state
      (equation .replay).body state
      (encoded (replayResultTerm (replaySignedPath? (providerEnv rows) language plans subject receipts))) := by
  simpa only [signedReceiptsTerm, replaySignedPath?] using
    replay_body_returns_of_step signedReceiptTerm (validateSignedReceipt? (providerEnv rows) language plans)
      state rows contexts plans
      (fun caller source receipt arguments captured =>
        validate_signed_captured_returns caller state language rows admitted contexts plans source receipt arguments captured)
      subject receipts

theorem replay_signed_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List SignedReceipt) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (signedReceiptsTerm receipts)]) :
    PureReturns program caller state (a "gslt:equation-context:replay" arguments) state
      (encoded (replayResultTerm (replaySignedPath? (providerEnv rows) language plans subject receipts))) :=
  helper_call .replay caller state _ _ _ rfl captured
    (replay_signed_body_returns state language rows admitted contexts plans subject receipts)

private theorem replay_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (rowsFirstOrder : FirstOrderRelations (providerEnv rows))
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List PositionedReceipt) :
    PureReturns program (environment .replay [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (positionedReceiptsTerm receipts)]) state
      (equation .replay).body state
      (encoded (replayResultTerm (replayContextPath? (providerEnv rows) language plans subject receipts))) := by
  simpa only [positionedReceiptsTerm, replayContextPath?_fold] using
    replay_body_returns_of_step positionedReceiptTerm
      (fun source receipt => validateSignedReceipt? (providerEnv rows) language plans source (.inl receipt))
      state rows contexts plans
      (fun caller source receipt arguments captured =>
        forward_validation_captured_returns caller state language rows rowsFirstOrder contexts plans source receipt arguments captured)
      subject receipts

/-- Literal-provider admission earns representability of every intermediate
subject. The actual source checks each receipt at its preceding endpoint. -/
theorem replay_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List PositionedReceipt) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (positionedReceiptsTerm receipts)]) :
    PureReturns program caller state (a "gslt:equation-context:replay" [one, two, three, four]) state
      (encoded (replayResultTerm (replayContextPath? (providerEnv rows) language plans subject receipts))) :=
  helper_call .replay caller state _ _ _ rfl captured
    (replay_body_returns state language rows (RuleTraceExecution.providerEnv_firstOrder rows admitted) contexts plans subject receipts)

def validateQueryTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (receipt : PositionedReceipt) : Term :=
  .application "gslt:equation-context:validate" [EquationExecution.equationsTerm contexts plans,
    providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase, positionedReceiptTerm receipt]

def replayQueryTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan)
    (receipts : List PositionedReceipt) : Term :=
  .application "gslt:equation-context:replay" [EquationExecution.equationsTerm contexts plans,
    providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase, positionedReceiptsTerm receipts]

theorem validate_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) :
    PureReturns program [] state (encoded (validateQueryTerm contexts plans rows subject receipt)) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validatePositionedReceipt? (providerEnv rows) language plans subject receipt))) :=
  validate_captured_returns [] state language rows contexts plans subject receipt _ _ _ _ (by simp)

theorem replay_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List PositionedReceipt) :
    PureReturns program [] state (encoded (replayQueryTerm contexts plans rows subject receipts)) state
      (encoded (replayResultTerm (replayContextPath? (providerEnv rows) language plans subject receipts))) :=
  replay_captured_returns [] state language rows admitted contexts plans subject receipts _ _ _ _ (by simp)

/-- Completed validation has exact answers, store and input/output observations. -/
theorem validate_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts plans rows subject receipt)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validatePositionedReceipt? (providerEnv rows) language plans subject receipt))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (validate_returns state language rows contexts plans subject receipt) after answers input output

theorem validate_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts plans rows subject receipt)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validatePositionedReceipt? (providerEnv rows) language plans subject receipt))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (validate_returns state language rows contexts plans subject receipt) after answers input output

theorem replay_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List PositionedReceipt) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (replayQueryTerm contexts plans rows subject receipts)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (replayResultTerm (replayContextPath? (providerEnv rows) language plans subject receipts))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (replay_returns state language rows admitted contexts plans subject receipts) after answers input output

theorem replay_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List PositionedReceipt) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (replayQueryTerm contexts plans rows subject receipts)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (replayResultTerm (replayContextPath? (providerEnv rows) language plans subject receipts))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (replay_returns state language rows admitted contexts plans subject receipts) after answers input output

/-- The whole positioned receipt is accepted by completed source execution
exactly when it belongs to the canonical physical-site equation frontier. -/
theorem validates_positioned_receipt_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : PositionedReceipt) (target : Pattern) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts plans rows subject receipt)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target])] [] []) ↔
      receipt ∈ contextualReceipts (providerEnv rows) language plans subject ∧ target = receipt.target := by
  rw [validate_derivation_iff]
  simp only [true_and, List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode]
  rw [← validatePositionedReceipt?_iff]
  cases found : validatePositionedReceipt? (providerEnv rows) language plans subject receipt with
  | none => simp [MatchAutomataBindingExecution.patternOptionTerm]
  | some actual => simp [MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePattern_injective.eq_iff, eq_comm]

open Mettapedia.GSLT.Ultrainfinite

/-- Source replay is exact for the existing finite route and its ordered
physical receipt trace. Every intermediate subject is independently admitted. -/
theorem replays_receipts_iff_route (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject target : PatternPlan) (receipts : List PositionedReceipt) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (replayQueryTerm contexts plans rows subject receipts)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target.erase])] [] []) ↔
      ∃ route : Route (CheckedPositionedReceipt (providerEnv rows) language plans) subject target,
        route.trace (fun edge => edge.receipt) = receipts := by
  rw [replay_derivation_iff state language rows admitted]
  simp only [true_and, List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode]
  rw [← replayContextPath?_iff_route]
  cases found : replayContextPath? (providerEnv rows) language plans subject receipts with
  | none => simp [replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm]
  | some actual => simp [replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
      InferenceCettaWire.encodePattern_injective.eq_iff, PatternPlan.erase_injective.eq_iff, eq_comm]

theorem validates_canonical_context_step (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) (receipt : PositionedReceipt) (target : Pattern)
    (accepted : DeclarativeSpec.Runs program
      { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject receipt)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target])] [] [])) :
    EquationContextStep (engineBasePremises (providerEnv rows)) language subject.erase target :=
  validated_positioned_step compiled subject receipt target
    ((validatePositionedReceipt?_iff _ _ _ _ _ _).mpr
      ((validates_positioned_receipt_iff state language rows contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject receipt target).mp accepted))

theorem replays_canonical_equivalence (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true) (subject target : PatternPlan) (receipts : List PositionedReceipt)
    (accepted : DeclarativeSpec.Runs program
      { state := state, control := .evaluate [] (encoded (replayQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject receipts)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target.erase])] [] [])) :
    EquationEquiv (engineBasePremises (providerEnv rows)) language subject.erase target.erase := by
  obtain ⟨route, _⟩ := (replays_receipts_iff_route state language rows admitted contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject target receipts).mp accepted
  exact checkedRoute_equivalent compiled route

/-- The context address and the complete atomic provenance remain independently
recoverable even when two sites or two derivations have the same target. -/
theorem positionedReceiptTerm_injective : Function.Injective positionedReceiptTerm := by
  have positions : Function.Injective EquationExecution.pathTerm :=
    encodeList_injective Term.natural (fun _ _ same => Term.natural.inj same)
  intro left right same
  have fields := (Term.application.inj same).2
  simp only [List.cons.injEq, and_true] at fields
  obtain ⟨position, atomic, target⟩ := fields
  cases left
  cases right
  simp only [PositionedReceipt.mk.injEq]
  exact ⟨positions position, EquationExecution.receiptTerm_injective atomic,
    InferenceCettaWire.encodePattern_injective target⟩

theorem positionedReceiptsTerm_injective : Function.Injective positionedReceiptsTerm :=
  encodeList_injective positionedReceiptTerm positionedReceiptTerm_injective

/-! ## Witnessed directed execution modulo authored equations -/

/-- Matching/execution projection with the original ordered authored equation
rows. Administrative fields are retained as supplied; this is not a full
language-wire parser or an admission of arbitrary metadata. -/
def equationLanguageTerm (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : List RulePlan) : Term :=
  MatchAutomataExecution.matchingProjectionTerm language types terms
    (EquationExecution.equationsTerm equationContexts plans) contexts fields

def directedViewTerm (language : LanguageDef) (types terms : Term)
    (contexts fields : RewriteRule → Term) : Term :=
  MatchAutomataExecution.matchingProjectionTerm (directedView language) types terms
    (.symbol "LNil") contexts fields

private def viewResult : Atom := a "GSLTLanguageDefWireV1"
  [v "name", v "types", v "terms", .symbol "LNil", v "rewrites"]
private def viewCases : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", v "equations", v "rewrites"], viewResult),
   (v "bad", .symbol "None")]
private theorem view_shape : (equation .directedView).body = a "case" [v "language",
    .expression (viewCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem view_body_returns (state : State) (language : LanguageDef) (types terms eqs : Term)
    (contexts fields : RewriteRule → Term) :
    PureReturns program (environment .directedView
      [encoded (MatchAutomataExecution.matchingProjectionTerm language types terms eqs contexts fields)]) state
      (equation .directedView).body state (encoded (directedViewTerm language types terms contexts fields)) := by
  let caller := environment .directedView
    [encoded (MatchAutomataExecution.matchingProjectionTerm language types terms eqs contexts fields)]
  let selected := ("rewrites", encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites)) ::
    ("equations", encoded eqs) :: ("terms", encoded terms) :: ("types", encoded types) ::
    ("name", encoded (.string language.name)) :: caller
  rw [view_shape]
  apply case_returns program caller selected state state state (v "language")
    (encoded (MatchAutomataExecution.matchingProjectionTerm language types terms eqs contexts fields))
    viewResult _ _ viewCases (read_cases_encoded _) _ _ _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "language"
  · simp [viewCases, MatchAutomataExecution.matchingProjectionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
      Subst.lookup, selected, caller, environment, Helper.names]
  · have inert : PureData.Template program viewResult := by
      apply data_template _ _ (by simp)
      intro atom member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact .captured _
      · exact .captured _
      · exact .captured _
      · exact .symbol _
      · exact .captured _
    simpa [viewResult, directedViewTerm, directedView, MatchAutomataExecution.matchingProjectionTerm,
      applySubst, applySubst.applySubstList, Subst.lookup, selected, caller, environment, Helper.names,
      CettaWireAtom.encode, CettaWireAtom.encodeMany] using PureData.template_return program selected state viewResult inert

/-- The actual adapter preserves each supplied directed row verbatim, as well
as supplied constructor and type metadata. It changes only the equation slot. -/
theorem directed_view_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (types terms eqs : Term) (contexts fields : RewriteRule → Term) (argument : Atom)
    (captured : applySubst caller argument =
      encoded (MatchAutomataExecution.matchingProjectionTerm language types terms eqs contexts fields)) :
    PureReturns program caller state (a "gslt:equation-context:directed-view" [argument]) state
      (encoded (directedViewTerm language types terms contexts fields)) :=
  helper_call .directedView caller state _ _ _ rfl (by simp only [List.map_cons, List.map_nil, captured])
    (view_body_returns state language types terms eqs contexts fields)

private abbrev patternsValue (results : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns results)

/-- This private selector chooses retained source bodies with the same
continuation schedule; it carries no matching or equation semantics. -/
private inductive ContinuationKind where
  | certificates | acquired
private def ContinuationKind.replayHead : ContinuationKind → String
  | .certificates => "gslt:equation-context:replay"
  | .acquired => "gslt:equation-context:acquired-replay"
private def ContinuationKind.afterHelper : ContinuationKind → Helper
  | .certificates => .afterResults
  | .acquired => .acquiredAfter
private def ContinuationKind.witnessedHelper : ContinuationKind → Helper
  | .certificates => .witnessed
  | .acquired => .acquiredWitnessed
private theorem ContinuationKind.after_names (kind : ContinuationKind) :
    kind.afterHelper.names = ["equations", "rows", "receipts", "results"] := by cases kind <;> rfl
private theorem ContinuationKind.witnessed_names (kind : ContinuationKind) :
    kind.witnessedHelper.names = ["strategy", "language", "rows", "depth", "subject", "before", "after"] := by
  cases kind <;> rfl

private def afterCheckedCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"), (a "Some" [v "target"], a "LCons" [v "target", v "tail"])]
private def afterChecked : Atom := a "case" [v "checked",
  .expression (afterCheckedCases.map fun row => .expression [row.1, row.2])]
private def afterCons (kind : ContinuationKind) : Atom := a "let*" [.expression
  [.expression [v "checked", a kind.replayHead [v "equations", v "rows", v "result", v "receipts"]],
   .expression [v "tail", a kind.afterHelper.head [v "equations", v "rows", v "receipts", v "rest"]]],
  afterChecked]
private def afterCases (kind : ContinuationKind) : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "result", v "rest"], afterCons kind), (v "bad", .symbol "LNil")]
private theorem after_shape (kind : ContinuationKind) : (equation kind.afterHelper).body = a "case" [v "results",
    .expression ((afterCases kind).map fun row => .expression [row.1, row.2])] := by cases kind <;> decide +kernel

private theorem after_body_returns_of_replay {Event : Type}
    (kind : ContinuationKind)
    (eventTerm : Event → Term) (replay : PatternPlan → List Event → Option PatternPlan)
    (state : State) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (replayReturns : ∀ (caller : Subst) (subject : PatternPlan) (events : List Event) (arguments : List Atom),
      arguments.map (applySubst caller) =
        [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
          encoded (InferenceCettaWire.encodePattern subject.erase), encoded (encodeList eventTerm events)] →
      PureReturns program caller state (a kind.replayHead arguments) state
        (encoded (replayResultTerm (replay subject events))))
    (receipts : List Event) (results : List Pattern)
    (firstOrder : ∀ result ∈ results, isMatchCorrectAux result = true) :
    PureReturns program (environment kind.afterHelper
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (encodeList eventTerm receipts),
        patternsValue results]) state (equation kind.afterHelper).body state
      (patternsValue (afterPathResults (fun subject => replay subject receipts) results)) := by
  induction results with
  | nil =>
      let caller := environment kind.afterHelper
        [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded ((encodeList eventTerm) receipts),
          patternsValue []]
      rw [after_shape kind]
      apply case_returns program caller caller state state state (v "results") (.symbol "LNil") (.symbol "LNil")
        _ _ (afterCases kind) (read_cases_encoded _) _ _ _
      · simpa [caller, environment, ContinuationKind.after_names, patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "results"
      · simp [afterCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [afterPathResults, patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns program caller state "LNil"
  | cons result results ih =>
      cases compiled : compilePattern? result with
      | none =>
          have exactAdmission := compilePattern?_isSome_eq_isMatchCorrectAux result
          simp only [compiled, Option.isSome_none, firstOrder result (by simp)] at exactAdmission
          cases exactAdmission
      | some subject =>
          have readback := erase_of_compilePattern? result subject compiled
          have remaining : ∀ result ∈ results, isMatchCorrectAux result = true := by
            intro member included
            exact firstOrder member (by simp [included])
          let caller := environment kind.afterHelper
            [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded ((encodeList eventTerm) receipts),
              patternsValue (result :: results)]
          let selected := ("rest", patternsValue results) :: ("result", encoded (InferenceCettaWire.encodePattern result)) :: caller
          let checked := replay subject receipts
          let headBound := ("checked", encoded (replayResultTerm checked)) :: selected
          let tailResults := (afterPathResults (fun subject => replay subject receipts)) results
          let tailBound := ("tail", patternsValue tailResults) :: headBound
          have replayed := replayReturns selected subject receipts
            [v "equations", v "rows", v "result", v "receipts"]
            (by simp [selected, caller, environment, ContinuationKind.after_names, applySubst, Subst.lookup, readback])
          have continued := helper_call kind.afterHelper headBound state _
            [v "equations", v "rows", v "receipts", v "rest"] _ (by rw [ContinuationKind.after_names]; rfl)
            (by simp [headBound, selected, caller, environment, ContinuationKind.after_names, applySubst, Subst.lookup]) (ih remaining)
          rw [after_shape kind]
          apply case_returns program caller selected state state state (v "results")
            (a "LCons" [encoded (InferenceCettaWire.encodePattern result), patternsValue results]) (afterCons kind) _ _
            (afterCases kind) (read_cases_encoded _) _ _ _
          · simpa [caller, environment, ContinuationKind.after_names, patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, Subst.lookup] using variable_returns program caller state "results"
          · simp [afterCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, selected, caller, environment, ContinuationKind.after_names]
          · unfold afterCons
            refine PureData.let_bindings_return
              (pairs := [(v "checked", a kind.replayHead [v "equations", v "rows", v "result", v "receipts"]),
                (v "tail", a kind.afterHelper.head [v "equations", v "rows", v "receipts", v "rest"])])
              (bindings := selected) (before := state) (middle := state) (final := tailBound) ?_ state afterChecked
                (patternsValue ((afterPathResults (fun subject => replay subject receipts)) (result :: results))) ?_
            · apply PureData.BindingsReturn.cons (bound := headBound) replayed
                (by simp [SpaceSemantics.matchBinding, headBound, checked, selected, caller, environment, ContinuationKind.after_names,
                  SpaceSemantics.matchValue, matchAtom, Subst.lookup])
              apply PureData.BindingsReturn.cons (bound := tailBound) continued
                (by simp [SpaceSemantics.matchBinding, tailBound, tailResults, headBound, selected, caller, environment, ContinuationKind.after_names,
                  SpaceSemantics.matchValue, matchAtom, Subst.lookup])
              exact .nil _ _
            · unfold afterChecked
              cases found : replay subject receipts with
              | none =>
                  apply case_returns program tailBound tailBound state state state (v "checked") (.symbol "None") (v "tail")
                    _ _ afterCheckedCases (read_cases_encoded _) _ _ _
                  · simpa [checked, found, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
                      CettaWireAtom.encode, tailBound, headBound, applySubst, Subst.lookup] using
                      variable_returns program tailBound state "checked"
                  · simp [afterCheckedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · simpa [afterPathResults, compiled, found, tailResults, tailBound, applySubst, Subst.lookup] using
                      variable_returns program tailBound state "tail"
              | some target =>
                  let targetBound := ("target", encoded (InferenceCettaWire.encodePattern target.erase)) :: tailBound
                  apply case_returns program tailBound targetBound state state state (v "checked")
                    (a "Some" [encoded (InferenceCettaWire.encodePattern target.erase)]) (a "LCons" [v "target", v "tail"])
                    _ _ afterCheckedCases (read_cases_encoded _) _ _ _
                  · simpa [checked, found, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
                      CettaWireAtom.encode, CettaWireAtom.encodeMany, tailBound, headBound, applySubst, Subst.lookup] using
                      variable_returns program tailBound state "checked"
                  · simp [afterCheckedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, targetBound, tailBound,
                      headBound, selected, caller, environment, ContinuationKind.after_names]
                  · simpa [afterPathResults, compiled, found, tailResults, tailBound, targetBound, patternsValue, encoded, applySubst,
                      applySubst.applySubstList, Subst.lookup, InferenceCettaWire.encodePatterns,
                      CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return program targetBound state (a "LCons" [v "target", v "tail"])
                        (lcons_template "target" "tail")


private theorem after_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (receipts : List PositionedReceipt) (results : List Pattern)
    (firstOrder : ∀ result ∈ results, isMatchCorrectAux result = true) :
    PureReturns program (environment .afterResults
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (positionedReceiptsTerm receipts),
        patternsValue results]) state (equation .afterResults).body state
      (patternsValue (afterReceipts (providerEnv rows) language plans receipts results)) := by
  simpa only [positionedReceiptsTerm, afterReceipts, afterPathResults, ContinuationKind.afterHelper] using
    after_body_returns_of_replay .certificates positionedReceiptTerm
      (fun source receipts => replayContextPath? (providerEnv rows) language plans source receipts)
      state rows contexts plans
      (fun caller source receipts arguments captured =>
        helper_call .replay caller state _ _ _ rfl captured
          (replay_body_returns state language rows (RuleTraceExecution.providerEnv_firstOrder rows admitted)
            contexts plans source receipts))
      receipts results firstOrder

/-- Actual post-route filtering preserves ordered successful results and
their multiplicity. First-order admission of each input is independently earned
by the directed executor's existing closure theorem at the call site. -/
theorem after_results_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (receipts : List PositionedReceipt) (results : List Pattern)
    (firstOrder : ∀ result ∈ results, isMatchCorrectAux result = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (positionedReceiptsTerm receipts), patternsValue results]) :
    PureReturns program caller state (a "gslt:equation-context:after-results" arguments) state
      (patternsValue (afterReceipts (providerEnv rows) language plans receipts results)) :=
  helper_call .afterResults caller state _ _ _ rfl captured
    (after_body_returns state language rows admitted contexts plans receipts results firstOrder)

private theorem after_results_captured_returns_of_replay {Event : Type}
    (kind : ContinuationKind)
    (eventTerm : Event → Term) (replay : PatternPlan → List Event → Option PatternPlan)
    (caller : Subst) (state : State) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (replayReturns : ∀ (caller : Subst) (subject : PatternPlan) (events : List Event) (arguments : List Atom),
      arguments.map (applySubst caller) =
        [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
          encoded (InferenceCettaWire.encodePattern subject.erase), encoded (encodeList eventTerm events)] →
      PureReturns program caller state (a kind.replayHead arguments) state
        (encoded (replayResultTerm (replay subject events))))
    (receipts : List Event) (results : List Pattern)
    (firstOrder : ∀ result ∈ results, isMatchCorrectAux result = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (encodeList eventTerm receipts), patternsValue results]) :
    PureReturns program caller state (a kind.afterHelper.head arguments) state
      (patternsValue (afterPathResults (fun subject => replay subject receipts) results)) :=
  helper_call kind.afterHelper caller state _ _ _ (by rw [ContinuationKind.after_names]; rfl) captured
    (after_body_returns_of_replay kind eventTerm replay state rows contexts plans replayReturns receipts results firstOrder)

private def witnessedAfter (kind : ContinuationKind) : Atom := a kind.afterHelper.head
  [v "equations", v "rows", v "after", v "frontier"]
private def witnessedDirected (kind : ContinuationKind) : Atom := a "let*" [.expression
  [.expression [v "view", a "gslt:equation-context:directed-view" [v "language"]],
   .expression [v "frontier", a "gslt:rule:language-contextual-reducts"
      [v "strategy", v "view", v "rows", v "depth", v "redex"]]], witnessedAfter kind]
private def witnessedBeforeCases (kind : ContinuationKind) : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "redex"], witnessedDirected kind)]
private def witnessedBefore (kind : ContinuationKind) : Atom := a "case"
  [a kind.replayHead [v "equations", v "rows", v "subject", v "before"],
   .expression ((witnessedBeforeCases kind).map fun row => .expression [row.1, row.2])]
private def witnessedCases (kind : ContinuationKind) : SpaceSemantics.Cases :=
  [(a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", v "equations", v "rewrites"], witnessedBefore kind),
   (v "bad", .symbol "LNil")]
private theorem witnessed_shape (kind : ContinuationKind) : (equation kind.witnessedHelper).body = a "case" [v "language",
    .expression ((witnessedCases kind).map fun row => .expression [row.1, row.2])] := by cases kind <;> decide +kernel

private theorem witnessed_body_returns_of_replay {Event : Type}
    (kind : ContinuationKind)
    (eventTerm : Event → Term) (replay : PatternPlan → List Event → Option PatternPlan)
    (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (replayReturns : ∀ (caller : Subst) (subject : PatternPlan) (events : List Event) (arguments : List Atom),
      arguments.map (applySubst caller) =
        [encoded (EquationExecution.equationsTerm equationContexts plans), rowsValue rows,
          encoded (InferenceCettaWire.encodePattern subject.erase), encoded (encodeList eventTerm events)] →
      PureReturns program caller state (a kind.replayHead arguments) state
        (encoded (replayResultTerm (replay subject events))))
    (depth : Nat) (subject : PatternPlan) (before after : List Event) :
    PureReturns program (environment kind.witnessedHelper
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (encodeList eventTerm before), encoded (encodeList eventTerm after)]) state
      (equation kind.witnessedHelper).body state
      (patternsValue (witnessedFrontier strategy (providerEnv rows) language depth subject
        (fun subject => replay subject before) (fun subject => replay subject after))) := by
  let caller := environment kind.witnessedHelper
    [encoded (ContextualRuleExecution.strategyTerm strategy),
      encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
      number depth, encoded (InferenceCettaWire.encodePattern subject.erase),
      encoded ((encodeList eventTerm) before), encoded ((encodeList eventTerm) after)]
  let selected := ("rewrites", encoded (MatchAutomataExecution.rewriteRowsTerm contexts fields language.rewrites)) ::
    ("equations", encoded (EquationExecution.equationsTerm equationContexts plans)) :: ("terms", encoded terms) ::
    ("types", encoded types) :: ("name", encoded (.string language.name)) :: caller
  rw [witnessed_shape kind]
  apply case_returns program caller selected state state state (v "language")
    (encoded (equationLanguageTerm language types terms equationContexts contexts fields plans)) (witnessedBefore kind) _ _
    (witnessedCases kind) (read_cases_encoded _) _ _ _
  · simpa [caller, environment, ContinuationKind.witnessed_names, applySubst, Subst.lookup] using variable_returns program caller state "language"
  · simp [witnessedCases, equationLanguageTerm, MatchAutomataExecution.matchingProjectionTerm,
      CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      selected, caller, environment, ContinuationKind.witnessed_names]
  · have started := replayReturns selected subject before
      [v "equations", v "rows", v "subject", v "before"]
      (by simp [selected, caller, environment, ContinuationKind.witnessed_names, applySubst, Subst.lookup])
    unfold witnessedBefore
    cases replayed : replay subject before with
    | none =>
        apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "LNil")
          _ _ (witnessedBeforeCases kind) (read_cases_encoded _) _ _ _
        · simpa [replayed, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using started
        · simp [witnessedBeforeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [witnessedFrontier, replayed, patternsValue, encoded, InferenceCettaWire.encodePatterns,
            CettaWireAtom.encode] using symbol_returns program selected state "LNil"
    | some redex =>
        let redexBound := ("redex", encoded (InferenceCettaWire.encodePattern redex.erase)) :: selected
        let viewBound := ("view", encoded (directedViewTerm language types terms contexts fields)) :: redexBound
        let frontier := MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises (providerEnv rows))
          (directedView language) depth redex
        let frontierBound := ("frontier", patternsValue frontier) :: viewBound
        have viewed := directed_view_captured_returns redexBound state language types terms
          (EquationExecution.equationsTerm equationContexts plans) contexts fields (v "language")
          (by simp [redexBound, selected, caller, environment, ContinuationKind.witnessed_names, equationLanguageTerm, applySubst, Subst.lookup])
        have directed : PureReturns program viewBound state (a "gslt:rule:language-contextual-reducts"
            [v "strategy", v "view", v "rows", v "depth", v "redex"]) state (patternsValue frontier) := by
          apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
          apply EquationExecutionProgram.retained_captured_returns (by decide +kernel)
          exact ContextualRuleExecution.language_contextual_captured_returns viewBound state strategy
            (directedView language) types terms contexts fields rows providerAdmitted viewAdmitted
            projected depth redex _ (by simp [viewBound, redexBound, selected, caller, environment, ContinuationKind.witnessed_names,
              directedViewTerm, applySubst, Subst.lookup])
        have frontierFirstOrder : ∀ result ∈ frontier, isMatchCorrectAux result = true := by
          intro result member
          exact MeTTaILFirstOrderContextualExecution.runAt_firstOrder strategy (providerEnv rows)
            (RuleTraceExecution.providerEnv_firstOrder rows providerAdmitted) (directedView language)
            ((ContextualRuleExecution.language_admitted_iff _).mp viewAdmitted).2.1 depth redex result member
        have finished := after_results_captured_returns_of_replay kind eventTerm replay frontierBound state rows equationContexts
          plans replayReturns after frontier frontierFirstOrder [v "equations", v "rows", v "after", v "frontier"]
          (by simp [frontierBound, viewBound, redexBound, selected, caller, environment, ContinuationKind.witnessed_names, applySubst, Subst.lookup])
        apply case_returns program selected redexBound state state state _
          (a "Some" [encoded (InferenceCettaWire.encodePattern redex.erase)]) (witnessedDirected kind) _ _
          (witnessedBeforeCases kind) (read_cases_encoded _) _ _ _
        · simpa [replayed, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using started
        · simp [witnessedBeforeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, redexBound, selected,
            caller, environment, ContinuationKind.witnessed_names]
        · unfold witnessedDirected
          refine PureData.let_bindings_return
            (pairs := [(v "view", a "gslt:equation-context:directed-view" [v "language"]),
              (v "frontier", a "gslt:rule:language-contextual-reducts"
                [v "strategy", v "view", v "rows", v "depth", v "redex"])])
            (bindings := redexBound) (before := state) (middle := state) (final := frontierBound) ?_ state (witnessedAfter kind) _ ?_
          · apply PureData.BindingsReturn.cons (bound := viewBound) viewed
              (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                viewBound, redexBound, selected, caller, environment, ContinuationKind.witnessed_names])
            apply PureData.BindingsReturn.cons (bound := frontierBound) directed
              (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                frontierBound, viewBound, redexBound, selected, caller, environment, ContinuationKind.witnessed_names])
            exact .nil _ _
          · simpa only [witnessedAfter, witnessedFrontier, replayed, frontier] using finished


private theorem witnessed_body_returns (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PositionedReceipt) :
    PureReturns program (environment .witnessed
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (positionedReceiptsTerm before), encoded (positionedReceiptsTerm after)]) state
      (equation .witnessed).body state
      (patternsValue (witnessedReducts strategy (providerEnv rows) language plans depth subject before after)) := by
  simpa only [positionedReceiptsTerm, witnessedReducts, ContinuationKind.witnessedHelper] using
    witnessed_body_returns_of_replay .certificates positionedReceiptTerm
      (fun source receipts => replayContextPath? (providerEnv rows) language plans source receipts)
      state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected
      (fun caller source receipts arguments captured =>
        helper_call .replay caller state _ _ _ rfl captured
          (replay_body_returns state language rows (RuleTraceExecution.providerEnv_firstOrder rows providerAdmitted)
            equationContexts plans source receipts))
      depth subject before after

/-- Retained-source execution of the complete witnessed equation/direct-step
composition. Equality certificates never create a directed rewrite permission. -/
theorem witnessed_reducts_captured_returns (caller : Subst) (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PositionedReceipt) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (positionedReceiptsTerm before), encoded (positionedReceiptsTerm after)]) :
    PureReturns program caller state (a "gslt:equation-context:witnessed-reducts" arguments) state
      (patternsValue (witnessedReducts strategy (providerEnv rows) language plans depth subject before after)) :=
  helper_call .witnessed caller state _ _ _ rfl captured
    (witnessed_body_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after)

def witnessedQueryTerm (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (depth : Nat)
    (subject : PatternPlan) (before after : List PositionedReceipt) : Term :=
  .application "gslt:equation-context:witnessed-reducts"
    [ContextualRuleExecution.strategyTerm strategy,
      equationLanguageTerm language types terms equationContexts contexts fields plans, providerRowsTerm rows,
      .natural depth, InferenceCettaWire.encodePattern subject.erase, positionedReceiptsTerm before, positionedReceiptsTerm after]

theorem witnessed_reducts_returns (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PositionedReceipt) :
    PureReturns program [] state (encoded (witnessedQueryTerm strategy language types terms equationContexts contexts fields
      plans rows depth subject before after)) state
      (patternsValue (witnessedReducts strategy (providerEnv rows) language plans depth subject before after)) := by
  simpa only [witnessedQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    witnessed_reducts_captured_returns [] state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after _ (by simp [applySubst, CettaWireAtom.encode])

theorem witnessed_reducts_completed_iff (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PositionedReceipt)
    (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded
      (witnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) } =
        .complete terminal answers input output) ↔
      terminal = state ∧ answers = [patternsValue (witnessedReducts strategy (providerEnv rows) language plans depth subject before after)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (witnessed_reducts_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after) terminal answers input output

theorem witnessed_reducts_derivation_iff (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PositionedReceipt)
    (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (witnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) }
        (.complete terminal answers input output) ↔
      terminal = state ∧ answers = [patternsValue (witnessedReducts strategy (providerEnv rows) language plans depth subject before after)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (witnessed_reducts_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after) terminal answers input output

/-- A member of an actually completed witnessed frontier. The before and
after certificates are inputs to that execution, with no equality oracle. -/
def ObservesWitnessedReduct (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject target : PatternPlan)
    (before after : List PositionedReceipt) : Prop :=
  ∃ depth, ∃ results : List Pattern,
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (witnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) }
        (.complete state [patternsValue results] [] []) ∧ target.erase ∈ results

/-- Preservation and reflection for the supplied finite route witnesses, with
the actual original directed step between them. This does not claim that the
forward receipts enumerate every symmetric canonical equation witness. -/
theorem observes_witnessed_iff_routes (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) (before after : List PositionedReceipt) :
    ObservesWitnessedReduct state strategy language types terms equationContexts contexts fields plans rows subject target before after ↔
      ∃ redex contractum : PatternPlan,
        (∃ route : Route (CheckedPositionedReceipt (providerEnv rows) language plans) subject redex,
          route.trace (fun edge => edge.receipt) = before) ∧
        Step (engineBasePremises (providerEnv rows)) language redex.erase contractum.erase ∧
        (∃ route : Route (CheckedPositionedReceipt (providerEnv rows) language plans) contractum target,
          route.trace (fun edge => edge.receipt) = after) := by
  rw [← witnessedReducts_iff_routes strategy (providerEnv rows) language
    ((ContextualRuleExecution.language_admitted_iff _).mp viewAdmitted).1]
  constructor
  · rintro ⟨depth, results, executed, member⟩
    have observation := (witnessed_reducts_derivation_iff state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after state [patternsValue results] [] []).mp executed
    have sameWire := CettaWireAtom.encode_injective _ _ (List.cons.inj observation.2.1).1
    have same := InferenceCettaWire.encodePatterns_injective sameWire
    exact ⟨depth, by simpa only [same] using member⟩
  · rintro ⟨depth, member⟩
    exact ⟨depth, _, (witnessed_reducts_derivation_iff state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩, member⟩

theorem observes_witnessed_gslt_step (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) (before after : List PositionedReceipt)
    (observed : ObservesWitnessedReduct state strategy language types terms equationContexts contexts fields compiled.plans rows
      subject target before after) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step subject.erase target.erase := by
  obtain ⟨redex, contractum, ⟨started, _⟩, directed, ⟨finished, _⟩⟩ :=
    (observes_witnessed_iff_routes state strategy language types terms equationContexts contexts fields (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows
      providerAdmitted viewAdmitted projected subject target before after).mp observed
  exact ⟨redex.erase, contractum.erase, checkedRoute_equivalent compiled started,
    directed, checkedRoute_equivalent compiled finished⟩


/-! ## Signed checked equation routes -/

/-- Signs and predecessors remain recoverable independently of targets. -/
theorem signedReceiptTerm_injective : Function.Injective signedReceiptTerm := by
  intro left right same
  cases left with
  | inl left =>
      cases right with
      | inl right => exact congrArg Sum.inl (positionedReceiptTerm_injective same)
      | inr right => simp [signedReceiptTerm, positionedReceiptTerm] at same
  | inr left =>
      cases right with
      | inl right => simp [signedReceiptTerm, positionedReceiptTerm] at same
      | inr right =>
          have fields := (Term.application.inj same).2
          simp only [List.cons.injEq, and_true] at fields
          obtain ⟨predecessor, receipt⟩ := fields
          exact congrArg Sum.inr (Prod.ext
            (PatternPlan.erase_injective (InferenceCettaWire.encodePattern_injective predecessor))
            (positionedReceiptTerm_injective receipt))

theorem signedReceiptsTerm_injective : Function.Injective signedReceiptsTerm :=
  encodeList_injective signedReceiptTerm signedReceiptTerm_injective

def signedValidateQueryTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (plans : List RulePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (receipt : SignedReceipt) : Term :=
  .application "gslt:equation-context:validate" [EquationExecution.equationsTerm contexts plans,
    providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase, signedReceiptTerm receipt]

def signedReplayQueryTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (plans : List RulePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (receipts : List SignedReceipt) : Term :=
  .application "gslt:equation-context:replay" [EquationExecution.equationsTerm contexts plans,
    providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase, signedReceiptsTerm receipts]

theorem validate_signed_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : SignedReceipt) :
    PureReturns program [] state (encoded (signedValidateQueryTerm contexts plans rows subject receipt)) state
      (encoded (replayResultTerm (validateSignedReceipt? (providerEnv rows) language plans subject receipt))) := by
  simpa only [signedValidateQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    validate_signed_captured_returns [] state language rows admitted contexts plans subject receipt _
      (by simp)

theorem replay_signed_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List SignedReceipt) :
    PureReturns program [] state (encoded (signedReplayQueryTerm contexts plans rows subject receipts)) state
      (encoded (replayResultTerm (replaySignedPath? (providerEnv rows) language plans subject receipts))) := by
  simpa only [signedReplayQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    replay_signed_captured_returns [] state language rows admitted contexts plans subject receipts _
      (by simp)

theorem validate_signed_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : SignedReceipt) (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded (signedValidateQueryTerm contexts plans rows subject receipt)) } = .complete terminal answers input output) ↔
      terminal = state ∧ answers = [encoded (replayResultTerm
        (validateSignedReceipt? (providerEnv rows) language plans subject receipt))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (validate_signed_returns state language rows admitted contexts plans subject receipt) terminal answers input output

theorem validate_signed_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipt : SignedReceipt) (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded (signedValidateQueryTerm contexts plans rows subject receipt)) } (.complete terminal answers input output) ↔
      terminal = state ∧ answers = [encoded (replayResultTerm
        (validateSignedReceipt? (providerEnv rows) language plans subject receipt))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (validate_signed_returns state language rows admitted contexts plans subject receipt) terminal answers input output

theorem replay_signed_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List SignedReceipt) (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded (signedReplayQueryTerm contexts plans rows subject receipts)) } = .complete terminal answers input output) ↔
      terminal = state ∧ answers = [encoded (replayResultTerm
        (replaySignedPath? (providerEnv rows) language plans subject receipts))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (replay_signed_returns state language rows admitted contexts plans subject receipts) terminal answers input output

theorem replay_signed_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject : PatternPlan) (receipts : List SignedReceipt) (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded (signedReplayQueryTerm contexts plans rows subject receipts)) } (.complete terminal answers input output) ↔
      terminal = state ∧ answers = [encoded (replayResultTerm
        (replaySignedPath? (providerEnv rows) language plans subject receipts))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (replay_signed_returns state language rows admitted contexts plans subject receipts) terminal answers input output

/-- A reversed edge is accepted only after validation of its original receipt,
including its context, branch ordinals, bindings and both claimed targets. -/
theorem validates_signed_receipt_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject target : PatternPlan) (receipt : SignedReceipt) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded (signedValidateQueryTerm contexts plans rows subject receipt)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target.erase])] [] []) ↔
      validateSignedReceipt? (providerEnv rows) language plans subject receipt = some target := by
  rw [validate_signed_derivation_iff state language rows admitted]
  simp only [true_and, List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode]
  cases found : validateSignedReceipt? (providerEnv rows) language plans subject receipt with
  | none => simp [replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm]
  | some actual => simp [replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
      InferenceCettaWire.encodePattern_injective.eq_iff, PatternPlan.erase_injective.eq_iff, eq_comm]

/-- Preservation and reflection of the checked finite signed route and its
ordered receipt trace, with actual admitted intermediate subjects. -/
theorem replays_signed_receipts_iff_route (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (subject target : PatternPlan) (receipts : List SignedReceipt) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded (signedReplayQueryTerm contexts plans rows subject receipts)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target.erase])] [] []) ↔
      ∃ route : Route (CheckedSignedReceipt (providerEnv rows) language plans) subject target,
        route.trace (fun edge => edge.val) = receipts := by
  rw [replay_signed_derivation_iff state language rows admitted]
  simp only [true_and, List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode]
  rw [← replaySignedPath?_iff_route]
  cases found : replaySignedPath? (providerEnv rows) language plans subject receipts with
  | none => simp [replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm]
  | some actual => simp [replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
      InferenceCettaWire.encodePattern_injective.eq_iff, PatternPlan.erase_injective.eq_iff, eq_comm]

theorem replays_signed_canonical_equivalence (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true) (subject target : PatternPlan) (receipts : List SignedReceipt)
    (accepted : DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded (signedReplayQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject receipts)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target.erase])] [] [])) :
    EquationEquiv (engineBasePremises (providerEnv rows)) language subject.erase target.erase := by
  obtain ⟨route, _⟩ := (replays_signed_receipts_iff_route state language rows admitted contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject target receipts).mp accepted
  exact checkedSignedRoute_equivalent compiled route

theorem after_signed_results_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (admitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : VariableEquationPlans)
    (receipts : List SignedReceipt) (results : List Pattern)
    (firstOrder : ∀ result ∈ results, isMatchCorrectAux result = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (signedReceiptsTerm receipts), patternsValue results]) :
    PureReturns program caller state (a "gslt:equation-context:after-results" arguments) state
      (patternsValue (afterSignedReceipts (providerEnv rows) language plans receipts results)) := by
  simpa only [signedReceiptsTerm, afterSignedReceipts, ContinuationKind.afterHelper, Helper.head] using
    after_results_captured_returns_of_replay .certificates signedReceiptTerm
      (fun source receipts => replaySignedPath? (providerEnv rows) language plans source receipts)
      caller state rows contexts plans
      (fun caller source receipts arguments captured =>
        replay_signed_captured_returns caller state language rows admitted contexts plans source receipts arguments captured)
      receipts results firstOrder arguments captured

private theorem signed_witnessed_body_returns (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List SignedReceipt) :
    PureReturns program (environment .witnessed
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (signedReceiptsTerm before), encoded (signedReceiptsTerm after)]) state
      (equation .witnessed).body state
      (patternsValue (signedWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)) := by
  simpa only [signedReceiptsTerm, signedWitnessedReducts, ContinuationKind.witnessedHelper] using
    witnessed_body_returns_of_replay .certificates signedReceiptTerm
      (fun source receipts => replaySignedPath? (providerEnv rows) language plans source receipts)
      state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected
      (fun caller source receipts arguments captured =>
        replay_signed_captured_returns caller state language rows providerAdmitted equationContexts plans source receipts arguments captured)
      depth subject before after

/-- Retained-source execution of the complete witnessed equation/direct-step
composition. Equality certificates never create a directed rewrite permission. -/
theorem signed_witnessed_reducts_captured_returns (caller : Subst) (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List SignedReceipt) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (signedReceiptsTerm before), encoded (signedReceiptsTerm after)]) :
    PureReturns program caller state (a "gslt:equation-context:witnessed-reducts" arguments) state
      (patternsValue (signedWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)) :=
  helper_call .witnessed caller state _ _ _ rfl captured
    (signed_witnessed_body_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after)

def signedWitnessedQueryTerm (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (depth : Nat)
    (subject : PatternPlan) (before after : List SignedReceipt) : Term :=
  .application "gslt:equation-context:witnessed-reducts"
    [ContextualRuleExecution.strategyTerm strategy,
      equationLanguageTerm language types terms equationContexts contexts fields plans, providerRowsTerm rows,
      .natural depth, InferenceCettaWire.encodePattern subject.erase, signedReceiptsTerm before, signedReceiptsTerm after]

theorem signed_witnessed_reducts_returns (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List SignedReceipt) :
    PureReturns program [] state (encoded (signedWitnessedQueryTerm strategy language types terms equationContexts contexts fields
      plans rows depth subject before after)) state
      (patternsValue (signedWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)) := by
  simpa only [signedWitnessedQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    signed_witnessed_reducts_captured_returns [] state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after _ (by simp [applySubst, CettaWireAtom.encode])

theorem signed_witnessed_reducts_completed_iff (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List SignedReceipt)
    (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded
      (signedWitnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) } =
        .complete terminal answers input output) ↔
      terminal = state ∧ answers = [patternsValue (signedWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (signed_witnessed_reducts_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after) terminal answers input output

theorem signed_witnessed_reducts_derivation_iff (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List SignedReceipt)
    (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (signedWitnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) }
        (.complete terminal answers input output) ↔
      terminal = state ∧ answers = [patternsValue (signedWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (signed_witnessed_reducts_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after) terminal answers input output

/-- A member of an actually completed witnessed frontier. The before and
after certificates are inputs to that execution, with no equality oracle. -/
def ObservesSignedWitnessedReduct (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject target : PatternPlan)
    (before after : List SignedReceipt) : Prop :=
  ∃ depth, ∃ results : List Pattern,
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (signedWitnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) }
        (.complete state [patternsValue results] [] []) ∧ target.erase ∈ results

/-- Preservation and reflection for the supplied finite route witnesses, with
the original directed step between them. This is exact for admitted signed
witnesses; unrestricted canonical equivalence also requires representable
intermediate subjects and receipts. -/
theorem observes_signed_witnessed_iff_routes (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) (before after : List SignedReceipt) :
    ObservesSignedWitnessedReduct state strategy language types terms equationContexts contexts fields plans rows subject target before after ↔
      ∃ redex contractum : PatternPlan,
        (∃ route : Route (CheckedSignedReceipt (providerEnv rows) language plans) subject redex,
          route.trace (fun edge => edge.val) = before) ∧
        Step (engineBasePremises (providerEnv rows)) language redex.erase contractum.erase ∧
        (∃ route : Route (CheckedSignedReceipt (providerEnv rows) language plans) contractum target,
          route.trace (fun edge => edge.val) = after) := by
  rw [← signedWitnessedReducts_iff_routes strategy (providerEnv rows) language
    ((ContextualRuleExecution.language_admitted_iff _).mp viewAdmitted).1]
  constructor
  · rintro ⟨depth, results, executed, member⟩
    have observation := (signed_witnessed_reducts_derivation_iff state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after state [patternsValue results] [] []).mp executed
    have sameWire := CettaWireAtom.encode_injective _ _ (List.cons.inj observation.2.1).1
    have same := InferenceCettaWire.encodePatterns_injective sameWire
    exact ⟨depth, by simpa only [same] using member⟩
  · rintro ⟨depth, member⟩
    exact ⟨depth, _, (signed_witnessed_reducts_derivation_iff state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after state _ [] []).mpr ⟨rfl, rfl, rfl, rfl⟩, member⟩

theorem observes_signed_witnessed_gslt_step (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (contexts fields : RewriteRule → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) (before after : List SignedReceipt)
    (observed : ObservesSignedWitnessedReduct state strategy language types terms equationContexts contexts fields compiled.plans rows
      subject target before after) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step subject.erase target.erase := by
  obtain ⟨redex, contractum, ⟨started, _⟩, directed, ⟨finished, _⟩⟩ :=
    (observes_signed_witnessed_iff_routes state strategy language types terms equationContexts contexts fields (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows
      providerAdmitted viewAdmitted projected subject target before after).mp observed
  exact ⟨redex.erase, contractum.erase, checkedSignedRoute_equivalent compiled started,
    directed, checkedSignedRoute_equivalent compiled finished⟩


namespace Controls

open MeTTaILFirstOrderEquationCompilation.Controls
  (language compiled pair firstTarget secondTarget firstPositioned secondPositioned atom)

abbrev rows := EquationExecution.Controls.rows
abbrev contexts := EquationExecution.Controls.contexts

theorem literal_rows_admitted : RuleTraceExecution.providerFirstOrder rows = true := by decide +kernel

theorem positioned_receipt_returns (state : State) :
    PureReturns program [] state (encoded (validateQueryTerm contexts compiled.plans rows pair firstPositioned)) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern firstTarget.erase])) := by
  simpa only [EquationExecution.Controls.provider_exact,
    MeTTaILFirstOrderEquationCompilation.Controls.positioned_receipt_accepted,
    MatchAutomataBindingExecution.patternOptionTerm] using
    validate_returns state language rows contexts (variableEquationPlans compiled.plans (by decide +kernel)) pair firstPositioned

theorem future_site_refused_returns (state : State) :
    PureReturns program [] state (encoded (validateQueryTerm contexts compiled.plans rows pair
      { firstPositioned with position := [2] })) state (encoded (.symbol "None")) := by
  simpa only [EquationExecution.Controls.provider_exact,
    MeTTaILFirstOrderEquationCompilation.Controls.positioned_future_site_refused,
    MatchAutomataBindingExecution.patternOptionTerm] using
    validate_returns state language rows contexts (variableEquationPlans compiled.plans (by decide +kernel)) pair { firstPositioned with position := [2] }

theorem wrong_sibling_refused_returns (state : State) :
    PureReturns program [] state (encoded (validateQueryTerm contexts compiled.plans rows pair
      { firstPositioned with target := (.application "pair" [.application "out" [atom "b"], atom "a"] : PatternPlan).erase }))
      state (encoded (.symbol "None")) := by
  simpa only [EquationExecution.Controls.provider_exact,
    MeTTaILFirstOrderEquationCompilation.Controls.positioned_wrong_sibling_refused,
    MatchAutomataBindingExecution.patternOptionTerm] using
    validate_returns state language rows contexts (variableEquationPlans compiled.plans (by decide +kernel)) pair
      { firstPositioned with target := (.application "pair" [.application "out" [atom "b"], atom "a"] : PatternPlan).erase }

theorem two_step_path_returns (state : State) :
    PureReturns program [] state
      (encoded (replayQueryTerm contexts compiled.plans rows pair [firstPositioned, secondPositioned])) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern secondTarget.erase])) := by
  simpa only [EquationExecution.Controls.provider_exact,
    MeTTaILFirstOrderEquationCompilation.Controls.checked_two_step_path,
    replayResultTerm, Option.map_some, MatchAutomataBindingExecution.patternOptionTerm] using
    replay_returns state language rows literal_rows_admitted contexts (variableEquationPlans compiled.plans (by decide +kernel)) pair [firstPositioned, secondPositioned]

private theorem reversed_path_refused :
    replayContextPath? (providerEnv rows) language compiled.plans pair [secondPositioned, firstPositioned] = none := by
  have site : MeTTaILSubtermMatchAutomata.selectSite? pair [0] =
      some (.apply "pair" [] .hole [(atom "a").erase], atom "a") := by
    simp [MeTTaILSubtermMatchAutomata.selectSite?, pair, erasePatterns]
  have localRead : validateReceipt? MeTTaILFirstOrderEquationCompilation.Controls.relations language (variableEquationPlans compiled.plans (by decide +kernel))
      (atom "a").erase (MeTTaILFirstOrderEquationCompilation.Controls.expected 0 2 "c") =
      some (.apply "out" [(atom "c").erase]) := by
    apply (validateReceipt?_iff _ _ _ _ _ _).mpr
    refine ⟨?_, rfl⟩
    rw [show (variableEquationPlans compiled.plans (by decide +kernel)) = [MeTTaILFirstOrderEquationCompilation.Controls.conditional] from rfl,
      MeTTaILFirstOrderEquationCompilation.Controls.conditional_frontier]
    decide +kernel
  have refused : validatePositionedReceipt? (providerEnv rows) language (variableEquationPlans compiled.plans (by decide +kernel)) pair secondPositioned = none := by
    rw [EquationExecution.Controls.provider_exact]
    simp only [validatePositionedReceipt?, secondPositioned, site, Option.bind_eq_bind, Option.bind_some, localRead]
    simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, secondTarget,
      PatternPlan.erase, erasePatterns, atom, guard]
  simp [replayContextPath?, refused]

theorem reversed_path_refused_returns (state : State) :
    PureReturns program [] state
      (encoded (replayQueryTerm contexts compiled.plans rows pair [secondPositioned, firstPositioned])) state
      (encoded (.symbol "None")) := by
  simpa only [reversed_path_refused, replayResultTerm, Option.map_none,
    MatchAutomataBindingExecution.patternOptionTerm] using
    replay_returns state language rows literal_rows_admitted contexts (variableEquationPlans compiled.plans (by decide +kernel)) pair [secondPositioned, firstPositioned]

theorem two_step_path_derivation (state : State) :
    DeclarativeSpec.Runs program
      { state := state, control := .evaluate [] (encoded (replayQueryTerm contexts (variableEquationPlans compiled.plans (by decide +kernel)) rows pair
        [firstPositioned, secondPositioned])) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern secondTarget.erase])] [] []) :=
  (pure_returns_derivation_iff program [] state state _ _ (two_step_path_returns state) state _ [] []).mpr
    ⟨rfl, rfl, rfl, rfl⟩

theorem two_step_path_equivalent (state : State) :
    EquationEquiv (engineBasePremises (providerEnv rows)) language pair.erase secondTarget.erase :=
  replays_canonical_equivalence state language rows literal_rows_admitted contexts compiled (List.all_eq_true.mp (by decide +kernel)) pair secondTarget
    [firstPositioned, secondPositioned] (two_step_path_derivation state)

private def groundPlan (name left right : String) : RulePlan :=
  ⟨name, [], [], atom left, atom right⟩
private def moduloLanguage : LanguageDef :=
  { name := "modulo", types := [], terms := [],
    equations := [equationOfPlan (groundPlan "ab" "a" "b"), equationOfPlan (groundPlan "cd" "c" "d")],
    rewrites := [(groundPlan "bc" "b" "c").erase, (groundPlan "bc" "b" "c").erase] }
private def moduloCompiled : EquationProgram moduloLanguage.equations :=
  ⟨[groundPlan "ab" "a" "b", groundPlan "cd" "c" "d"], rfl⟩
private def moduloBefore : PositionedReceipt :=
  ⟨[], ⟨0, .forward, [], [], [], (atom "b").erase⟩, (atom "b").erase⟩
private def moduloAfter : PositionedReceipt :=
  ⟨[], ⟨1, .forward, [], [], [], (atom "d").erase⟩, (atom "d").erase⟩
private abbrev moduloEqContexts (_ : Mettapedia.OSLF.MeTTaIL.Syntax.Equation) : Term := .symbol "LNil"
private abbrev moduloContexts (_ : RewriteRule) : Term := .symbol "RetainedContext"
private abbrev moduloFields (_ : RewriteRule) : Term := .symbol "LNil"
private theorem moduloProviderAdmitted : RuleTraceExecution.providerFirstOrder [] = true := by decide +kernel
private theorem moduloViewAdmitted : ContextualRuleExecution.languageAdmitted (directedView moduloLanguage) = true := by
  decide +kernel
private theorem moduloProjected : ∀ rule ∈ moduloLanguage.rewrites,
    ContextualRuleExecution.premisesTerm? rule.premises = some (moduloFields rule) := by
  intro rule member
  simp only [moduloLanguage, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst rule
  rfl
private theorem moduloBeforeChecked (language : LanguageDef) :
    validatePositionedReceipt? (providerEnv []) language moduloCompiled.plans (atom "a") moduloBefore =
      some (atom "b").erase := by
  have atomic : validateReceipt? (providerEnv []) language (variableEquationPlans moduloCompiled.plans (by decide +kernel)) (atom "a").erase
      moduloBefore.atomic = some (atom "b").erase := by
    simp [validateReceipt?, validateRowReceipt?, moduloCompiled, moduloBefore, groundPlan, orientedPlan,
      atom, PatternPlan.erase, erasePatterns, PatternPlan.run, runPlans, replayPremises?,
      PatternPlan.instantiate, guard]
  have localRead := atomic
  simp only [moduloBefore] at localRead
  simp [validatePositionedReceipt?, moduloBefore, MeTTaILSubtermMatchAutomata.selectSite?,
    localRead, guard, Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
private theorem moduloAfterChecked (language : LanguageDef) :
    validatePositionedReceipt? (providerEnv []) language moduloCompiled.plans (atom "c") moduloAfter =
      some (atom "d").erase := by
  have atomic : validateReceipt? (providerEnv []) language (variableEquationPlans moduloCompiled.plans (by decide +kernel)) (atom "c").erase
      moduloAfter.atomic = some (atom "d").erase := by
    simp [validateReceipt?, validateRowReceipt?, moduloCompiled, moduloAfter, groundPlan, orientedPlan,
      atom, PatternPlan.erase, erasePatterns, PatternPlan.run, runPlans, replayPremises?,
      PatternPlan.instantiate, guard]
  have localRead := atomic
  simp only [moduloAfter] at localRead
  simp [validatePositionedReceipt?, moduloAfter, MeTTaILSubtermMatchAutomata.selectSite?,
    localRead, guard, Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
private theorem moduloBeforeReplayed (language : LanguageDef) :
    replayContextPath? (providerEnv []) language moduloCompiled.plans (atom "a") [moduloBefore] =
      some (atom "b") := by
  simp only [replayContextPath?, moduloBeforeChecked, Option.bind_eq_bind, Option.bind_some,
    compilePattern?_erase]
private theorem moduloAfterReplayed (language : LanguageDef) :
    replayContextPath? (providerEnv []) language moduloCompiled.plans (atom "c") [moduloAfter] =
      some (atom "d") := by
  simp only [replayContextPath?, moduloAfterChecked, Option.bind_eq_bind, Option.bind_some,
    compilePattern?_erase]
private theorem moduloFrontier (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    witnessedReducts strategy (providerEnv []) moduloLanguage moduloCompiled.plans 1 (atom "a")
      [moduloBefore] [moduloAfter] = [(atom "d").erase, (atom "d").erase] := by
  have directed : MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises (providerEnv []))
      (directedView moduloLanguage) 1 (atom "b") = [(atom "c").erase, (atom "c").erase] := by
    rw [MeTTaILMatchAutomataExecution.runAt_exact]
    decide +kernel
  simp only [witnessedReducts, witnessedFrontier, moduloBeforeReplayed, directed, afterPathResults,
    List.filterMap_cons, List.filterMap_nil, compilePattern?_erase, moduloAfterReplayed,
    Option.bind_eq_bind, Option.bind_some]
  rfl

/-- Two identical directed declarations still produce two completed results
after independently validated equivalence certificates on both sides. -/
theorem modulo_duplicates_returns (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    PureReturns program [] state
      (encoded (witnessedQueryTerm strategy moduloLanguage (.symbol "RetainedTypes") (.symbol "RetainedTerms")
        moduloEqContexts moduloContexts moduloFields moduloCompiled.plans [] 1 (atom "a") [moduloBefore] [moduloAfter])) state
      (patternsValue [(atom "d").erase, (atom "d").erase]) := by
  simpa only [moduloFrontier] using witnessed_reducts_returns state strategy moduloLanguage
    (.symbol "RetainedTypes") (.symbol "RetainedTerms") moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) []
    moduloProviderAdmitted moduloViewAdmitted moduloProjected 1 (atom "a") [moduloBefore] [moduloAfter]

theorem modulo_duplicates_derivation (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded
      (witnessedQueryTerm strategy moduloLanguage (.symbol "RetainedTypes") (.symbol "RetainedTerms")
        moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) [] 1 (atom "a") [moduloBefore] [moduloAfter])) }
      (.complete state [patternsValue [(atom "d").erase, (atom "d").erase]] [] []) :=
  (pure_returns_derivation_iff program [] state state _ _ (modulo_duplicates_returns state strategy) state _ [] []).mpr
    ⟨rfl, rfl, rfl, rfl⟩

theorem modulo_duplicates_gslt_step (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv []) moduloLanguage).Step
      (atom "a").erase (atom "d").erase :=
  observes_witnessed_gslt_step state strategy moduloLanguage (.symbol "RetainedTypes") (.symbol "RetainedTerms")
    moduloEqContexts moduloContexts moduloFields moduloCompiled (List.all_eq_true.mp (by decide +kernel)) [] moduloProviderAdmitted moduloViewAdmitted moduloProjected
    (atom "a") (atom "d") [moduloBefore] [moduloAfter]
    ⟨1, [(atom "d").erase, (atom "d").erase], modulo_duplicates_derivation state strategy, by simp⟩

/-- An authored equation path does not authorize even one directed reduction
when the original presentation has no directed rows. -/
theorem equation_only_does_not_authorize_reduction (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    PureReturns program [] state
      (encoded (witnessedQueryTerm strategy { moduloLanguage with rewrites := [] }
        (.symbol "RetainedTypes") (.symbol "RetainedTerms") moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) []
        1 (atom "a") [moduloBefore] [])) state (patternsValue []) := by
  have admitted : ContextualRuleExecution.languageAdmitted (directedView { moduloLanguage with rewrites := [] }) = true := by
    decide +kernel
  have projected : ∀ rule ∈ ({ moduloLanguage with rewrites := [] } : LanguageDef).rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (moduloFields rule) := by simp
  have actual : witnessedReducts strategy (providerEnv []) { moduloLanguage with rewrites := [] } (variableEquationPlans moduloCompiled.plans (by decide +kernel))
      1 (atom "a") [moduloBefore] [] = [] := by
    have empty : MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises (providerEnv []))
        (directedView { moduloLanguage with rewrites := [] }) 1 (atom "b") = [] :=
      MeTTaILFirstOrderContextualExecution.runAt_eq_nil_of_no_root_match strategy _ _ _ _ (by simp)
    simp only [witnessedReducts, witnessedFrontier, moduloBeforeReplayed, empty, afterPathResults, List.filterMap_nil]
  simpa only [actual] using witnessed_reducts_returns state strategy { moduloLanguage with rewrites := [] }
    (.symbol "RetainedTypes") (.symbol "RetainedTerms") moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) []
    moduloProviderAdmitted admitted projected 1 (atom "a") [moduloBefore] []


open MeTTaILFirstOrderEquationCompilation.Controls
  (discardConditional discardPredecessor discardRelations discardLanguage discardCompiled discardReceipt)

private def discardRows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow :=
  [⟨"allowed", [(atom "b").erase]⟩, ⟨"allowed", [(atom "b").erase]⟩]

private theorem discard_rows_admitted : RuleTraceExecution.providerFirstOrder discardRows = true := by decide +kernel
private theorem discard_provider_exact : providerEnv discardRows = discardRelations := by
  apply congrArg Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.mk
  funext relation arguments
  by_cases selected : relation = "allowed"
  · simp [RelationPremiseExecution.providerTuples, discardRows, selected]
  · simp [RelationPremiseExecution.providerTuples, discardRows, selected, Ne.symm selected]

/-- The supplied predecessor retains the discarded x=a binding, while the
original duplicate query choice remains checked by the retained validator. -/
theorem checked_previous_returns (state : State) :
    PureReturns program [] state (encoded (signedValidateQueryTerm contexts discardCompiled.plans discardRows
      (atom "b") (.inr (discardPredecessor, discardReceipt)))) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern discardPredecessor.erase])) := by
  simpa only [discard_provider_exact,
    MeTTaILFirstOrderEquationCompilation.Controls.checked_previous_recovers_discarded_variable,
    replayResultTerm, Option.map_some, MatchAutomataBindingExecution.patternOptionTerm] using
    validate_signed_returns state discardLanguage discardRows discard_rows_admitted contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
      (atom "b") (.inr (discardPredecessor, discardReceipt))

theorem signed_roundtrip_returns (state : State) :
    PureReturns program [] state (encoded (signedReplayQueryTerm contexts discardCompiled.plans discardRows
      discardPredecessor [.inl discardReceipt, .inr (discardPredecessor, discardReceipt)])) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern discardPredecessor.erase])) := by
  simpa only [discard_provider_exact, MeTTaILFirstOrderEquationCompilation.Controls.signed_conditional_roundtrip,
    replayResultTerm, Option.map_some, MatchAutomataBindingExecution.patternOptionTerm] using
    replay_signed_returns state discardLanguage discardRows discard_rows_admitted contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
      discardPredecessor [.inl discardReceipt, .inr (discardPredecessor, discardReceipt)]

theorem signed_roundtrip_derivation (state : State) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (signedReplayQueryTerm contexts (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardRows discardPredecessor
        [.inl discardReceipt, .inr (discardPredecessor, discardReceipt)])) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern discardPredecessor.erase])] [] []) :=
  (pure_returns_derivation_iff program [] state state _ _ (signed_roundtrip_returns state) state _ [] []).mpr
    ⟨rfl, rfl, rfl, rfl⟩

theorem wrong_current_endpoint_refused_returns (state : State) :
    PureReturns program [] state (encoded (signedValidateQueryTerm contexts discardCompiled.plans discardRows
      (atom "c") (.inr (discardPredecessor, discardReceipt)))) state (encoded (.symbol "None")) := by
  simpa only [discard_provider_exact, MeTTaILFirstOrderEquationCompilation.Controls.signed_wrong_current_endpoint_refused,
    replayResultTerm, Option.map_none, MatchAutomataBindingExecution.patternOptionTerm] using
    validate_signed_returns state discardLanguage discardRows discard_rows_admitted contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
      (atom "c") (.inr (discardPredecessor, discardReceipt))

theorem forged_previous_refused_returns (state : State) :
    PureReturns program [] state (encoded (signedValidateQueryTerm contexts discardCompiled.plans discardRows
      (atom "b") (.inr (.application "drop" [atom "c", atom "b"], discardReceipt)))) state (encoded (.symbol "None")) := by
  have refused : validateSignedReceipt? discardRelations discardLanguage (variableEquationPlans discardCompiled.plans (by decide +kernel)) (atom "b")
      (.inr (.application "drop" [atom "c", atom "b"], discardReceipt)) = none :=
    MeTTaILFirstOrderEquationCompilation.Controls.signed_forged_predecessor_refused
  simpa only [discard_provider_exact, refused, replayResultTerm, Option.map_none,
    MatchAutomataBindingExecution.patternOptionTerm] using
    validate_signed_returns state discardLanguage discardRows discard_rows_admitted contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
      (atom "b") (.inr (.application "drop" [atom "c", atom "b"], discardReceipt))

theorem checked_previous_derivation (state : State) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (signedValidateQueryTerm contexts (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardRows (atom "b")
        (.inr (discardPredecessor, discardReceipt)))) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern discardPredecessor.erase])] [] []) :=
  (pure_returns_derivation_iff program [] state state _ _ (checked_previous_returns state) state _ [] []).mpr
    ⟨rfl, rfl, rfl, rfl⟩

theorem checked_previous_equivalent (state : State) :
    EquationEquiv (engineBasePremises (providerEnv discardRows)) discardLanguage
      (atom "b").erase discardPredecessor.erase :=
  validated_signed_equivalent discardCompiled _ _ _
    ((validates_signed_receipt_iff state discardLanguage discardRows discard_rows_admitted contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
      (atom "b") discardPredecessor (.inr (discardPredecessor, discardReceipt))).mp
      (checked_previous_derivation state))

end Controls

#print axioms split_captured_returns
#print axioms focus_captured_returns
#print axioms replace_captured_returns
#print axioms validate_captured_returns
#print axioms replay_captured_returns
#print axioms validate_completed_iff
#print axioms validate_derivation_iff
#print axioms replay_completed_iff
#print axioms replay_derivation_iff
#print axioms validates_positioned_receipt_iff
#print axioms replays_receipts_iff_route
#print axioms validates_canonical_context_step
#print axioms replays_canonical_equivalence
#print axioms positionedReceiptTerm_injective
#print axioms positionedReceiptsTerm_injective
#print axioms directed_view_captured_returns
#print axioms after_results_captured_returns
#print axioms witnessed_reducts_captured_returns
#print axioms witnessed_reducts_returns
#print axioms witnessed_reducts_completed_iff
#print axioms witnessed_reducts_derivation_iff
#print axioms observes_witnessed_iff_routes
#print axioms observes_witnessed_gslt_step
#print axioms Controls.positioned_receipt_returns
#print axioms Controls.future_site_refused_returns
#print axioms Controls.wrong_sibling_refused_returns
#print axioms Controls.two_step_path_returns
#print axioms Controls.reversed_path_refused_returns
#print axioms Controls.two_step_path_derivation
#print axioms Controls.two_step_path_equivalent
#print axioms Controls.modulo_duplicates_returns
#print axioms Controls.modulo_duplicates_derivation
#print axioms Controls.modulo_duplicates_gslt_step
#print axioms Controls.equation_only_does_not_authorize_reduction

#print axioms signedReceiptTerm_injective
#print axioms signedReceiptsTerm_injective
#print axioms validate_signed_captured_returns
#print axioms replay_signed_captured_returns
#print axioms validate_signed_returns
#print axioms replay_signed_returns
#print axioms validate_signed_completed_iff
#print axioms validate_signed_derivation_iff
#print axioms replay_signed_completed_iff
#print axioms replay_signed_derivation_iff
#print axioms validates_signed_receipt_iff
#print axioms replays_signed_receipts_iff_route
#print axioms replays_signed_canonical_equivalence
#print axioms after_signed_results_captured_returns
#print axioms signed_witnessed_reducts_captured_returns
#print axioms signed_witnessed_reducts_returns
#print axioms signed_witnessed_reducts_completed_iff
#print axioms signed_witnessed_reducts_derivation_iff
#print axioms observes_signed_witnessed_iff_routes
#print axioms observes_signed_witnessed_gslt_step
#print axioms Controls.checked_previous_returns
#print axioms Controls.signed_roundtrip_returns
#print axioms Controls.signed_roundtrip_derivation
#print axioms Controls.wrong_current_endpoint_refused_returns
#print axioms Controls.forged_previous_refused_returns
#print axioms Controls.checked_previous_derivation
#print axioms Controls.checked_previous_equivalent


open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open MeTTaILFirstOrderRuleCompilation MeTTaILFirstOrderEquationCompilation
open Eval _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects EquationContextExecutionProgram
open RelationPremiseExecution (providerEnv)

/-- Actual retained replay validates each independently acquired canonical
receipt. State and external input/output remain exactly those of the pure run. -/
theorem acquired_signed_route_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (viewAdmitted : (directedView language).isEquationFree = true)
    {subject target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises (providerEnv rows)) language) left.erase right.erase)) subject target)
    (receipts : List SignedReceipt)
    (acquired : compileSignedRoute? (providerEnv rows) language compiled.plans path = some receipts) :
    PureReturns program [] state (CettaWireAtom.encode (signedReplayQueryTerm contexts compiled.plans rows subject receipts)) state
      (CettaWireAtom.encode (.application "Some" [InferenceCettaWire.encodePattern target.erase])) := by
  obtain ⟨actualReceipts, actualAcquired, replayed⟩ := compileSignedRoute?_complete compiled viewAdmitted path
  have same : actualReceipts = receipts := Option.some.inj (actualAcquired.symm.trans acquired)
  subst actualReceipts
  simpa only [replayed, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm, Option.map_some] using
    replay_signed_returns state language rows providerAdmitted contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject receipts

theorem acquired_signed_route_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (viewAdmitted : (directedView language).isEquationFree = true)
    {subject target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises (providerEnv rows)) language) left.erase right.erase)) subject target)
    (receipts : List SignedReceipt)
    (acquired : compileSignedRoute? (providerEnv rows) language compiled.plans path = some receipts)
    (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (CettaWireAtom.encode (signedReplayQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject receipts)) }
      (.complete terminal answers input output) ↔
      terminal = state ∧
      answers = [CettaWireAtom.encode (.application "Some" [InferenceCettaWire.encodePattern target.erase])] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (acquired_signed_route_returns state language rows providerAdmitted contexts compiled sourceViews viewAdmitted path receipts acquired)
    terminal answers input output

/-- Completed source execution preserves and reflects independently authored
canonical routes with checked intermediate syntax admission. -/
theorem replays_some_signed_receipts_iff_admitted_canonical_route (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (viewAdmitted : (directedView language).isEquationFree = true) (subject target : PatternPlan) :
    (∃ receipts, DeclarativeSpec.Runs program
      { state, control := .evaluate [] (CettaWireAtom.encode (signedReplayQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject receipts)) }
      (.complete state [CettaWireAtom.encode (.application "Some" [InferenceCettaWire.encodePattern target.erase])] [] [])) ↔
      ∃ path : Route (fun left right => PLift (Relation.SymmGen
        (EquationContextStep (engineBasePremises (providerEnv rows)) language) left right)) subject.erase target.erase,
        routeFirstOrder? path = true := by
  rw [← replaySignedPath?_exists_iff_admitted_canonical_route compiled viewAdmitted subject target]
  constructor
  · rintro ⟨receipts, run⟩
    obtain ⟨route, trace⟩ :=
      (replays_signed_receipts_iff_route state language rows providerAdmitted contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject target receipts).mp run
    exact ⟨receipts, (replaySignedPath?_iff_route _ _ _ _ _ _).mpr ⟨route, trace⟩⟩
  · rintro ⟨receipts, accepted⟩
    exact ⟨receipts,
      (replays_signed_receipts_iff_route state language rows providerAdmitted contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject target receipts).mpr
        ((replaySignedPath?_iff_route _ _ _ _ _ _).mp accepted)⟩

/-- Actual equation-route replay around the original directed execution is
equivalent to canonical finite witnesses whose actual vertices are admitted.
The middle step is the language's directed judgment, not oriented equality. -/
theorem observes_some_signed_witnessed_iff_admitted_canonical_routes (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) :
    (∃ before after, ObservesSignedWitnessedReduct state strategy language types terms equationContexts contexts fields
      compiled.plans rows subject target before after) ↔
      ∃ redex contractum : PatternPlan,
        (∃ path : Route (fun left right => PLift (Relation.SymmGen
          (EquationContextStep (engineBasePremises (providerEnv rows)) language) left right)) subject.erase redex.erase,
          routeFirstOrder? path = true) ∧
        Step (engineBasePremises (providerEnv rows)) language redex.erase contractum.erase ∧
        (∃ path : Route (fun left right => PLift (Relation.SymmGen
          (EquationContextStep (engineBasePremises (providerEnv rows)) language) left right)) contractum.erase target.erase,
          routeFirstOrder? path = true) := by
  have equationFree := ((ContextualRuleExecution.language_admitted_iff _).mp viewAdmitted).1
  constructor
  · rintro ⟨before, after, observed⟩
    obtain ⟨redex, contractum, started, directed, finished⟩ :=
      (observes_signed_witnessed_iff_routes state strategy language types terms equationContexts contexts fields (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows
        providerAdmitted viewAdmitted projected subject target before after).mp observed
    have startReplay := (replaySignedPath?_iff_route _ _ _ _ _ _).mpr started
    have finishReplay := (replaySignedPath?_iff_route _ _ _ _ _ _).mpr finished
    exact ⟨redex, contractum,
      (replaySignedPath?_exists_iff_admitted_canonical_route compiled equationFree subject redex).mp ⟨before, startReplay⟩,
      directed,
      (replaySignedPath?_exists_iff_admitted_canonical_route compiled equationFree contractum target).mp ⟨after, finishReplay⟩⟩
  · rintro ⟨redex, contractum, started, directed, finished⟩
    obtain ⟨before, startReplay⟩ :=
      (replaySignedPath?_exists_iff_admitted_canonical_route compiled equationFree subject redex).mpr started
    obtain ⟨after, finishReplay⟩ :=
      (replaySignedPath?_exists_iff_admitted_canonical_route compiled equationFree contractum target).mpr finished
    exact ⟨before, after,
      (observes_signed_witnessed_iff_routes state strategy language types terms equationContexts contexts fields (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows
        providerAdmitted viewAdmitted projected subject target before after).mpr
          ⟨redex, contractum, (replaySignedPath?_iff_route _ _ _ _ _ _).mp startReplay, directed,
            (replaySignedPath?_iff_route _ _ _ _ _ _).mp finishReplay⟩⟩

#print axioms acquired_signed_route_returns
#print axioms acquired_signed_route_derivation_iff
#print axioms replays_some_signed_receipts_iff_admitted_canonical_route
#print axioms observes_some_signed_witnessed_iff_admitted_canonical_routes


private def liftResult : Atom :=
  a "LCons" [a "EqAt" [v "position", v "atomic", v "whole"], v "tail"]
private def liftReplaceCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"), (a "Some" [v "whole"], liftResult)]
private def liftReplace : Atom :=
  a "case" [a "gslt:equation-context:replace" [v "position", v "subject", v "target"],
    .expression (liftReplaceCases.map fun row => .expression [row.1, row.2])]
private def liftAtomicCases : SpaceSemantics.Cases :=
  [(a "EqInstance" [v "index", v "orientation", v "initial", v "choices", v "completed", v "target"], liftReplace),
    (v "bad", v "tail")]
private def liftAtomic : Atom := a "case" [v "atomic",
  .expression (liftAtomicCases.map fun row => .expression [row.1, row.2])]
private def liftCons : Atom := a "let" [v "tail",
  a "gslt:equation-context:lift" [v "position", v "subject", v "rest"], liftAtomic]
private def liftCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "atomic", v "rest"], liftCons), (v "bad", .symbol "LNil")]
private theorem lift_shape : (equation .lift).body = a "case" [v "receipts",
    .expression (liftCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem lift_result_template : PureData.Template program liftResult := by
  apply data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply data_template _ _ (by simp)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .captured _
  · exact .captured _

private theorem lift_body_returns (state : State) (position : SubtermMatching.Position)
    (subject : PatternPlan) (receipts : List Receipt) :
    PureReturns program (environment .lift [encoded (EquationExecution.pathTerm position),
      encoded (InferenceCettaWire.encodePattern subject.erase), encoded (EquationExecution.receiptsTerm receipts)]) state
      (equation .lift).body state (encoded (positionedReceiptsTerm (liftReceipts position subject receipts))) := by
  induction receipts with
  | nil =>
      let caller := environment .lift [encoded (EquationExecution.pathTerm position),
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (EquationExecution.receiptsTerm [])]
      rw [lift_shape]
      apply case_returns program caller caller state state state (v "receipts") (.symbol "LNil") (.symbol "LNil")
        _ _ liftCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, EquationExecution.receiptsTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "receipts"
      · simp [liftCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · cases selected : MeTTaILSubtermMatchAutomata.selectSite? subject position <;>
          simpa [liftReceipts, selected, positionedReceiptsTerm, encodeList, CettaWireAtom.encode] using
            symbol_returns program caller state "LNil"
  | cons receipt receipts ih =>
      let caller := environment .lift [encoded (EquationExecution.pathTerm position),
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (EquationExecution.receiptsTerm (receipt :: receipts))]
      let selected := ("rest", encoded (EquationExecution.receiptsTerm receipts)) ::
        ("atomic", encoded (EquationExecution.receiptTerm receipt)) :: caller
      let tail := liftReceipts position subject receipts
      let tailBound := ("tail", encoded (positionedReceiptsTerm tail)) :: selected
      let fieldsBound := ("target", encoded (InferenceCettaWire.encodePattern receipt.target)) ::
        ("completed", encoded (MatchAutomataBindingExecution.bindingsTerm receipt.finalBindings)) ::
        ("choices", encoded (EquationExecution.pathTerm receipt.choices)) ::
        ("initial", encoded (MatchAutomataBindingExecution.bindingsTerm receipt.initialBindings)) ::
        ("orientation", encoded (EquationExecution.orientationTerm receipt.orientation)) ::
        ("index", number receipt.equationIndex) :: tailBound
      rw [lift_shape]
      apply case_returns program caller selected state state state (v "receipts")
        (encoded (EquationExecution.receiptsTerm (receipt :: receipts))) liftCons _ _ liftCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "receipts"
      · simp [liftCases, EquationExecution.receiptsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold liftCons
        apply let_returns program selected tailBound state state state _ _ _ _ _
        · exact helper_call .lift selected state _ [v "position", v "subject", v "rest"] _ rfl
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
            selected, caller, environment, Helper.names, tail]
        · unfold liftAtomic
          apply case_returns program tailBound fieldsBound state state state (v "atomic")
            (encoded (EquationExecution.receiptTerm receipt)) liftReplace _ _ liftAtomicCases (read_cases_encoded _) _ _ _
          · simpa [tailBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns program tailBound state "atomic"
          · simp [liftAtomicCases, EquationExecution.receiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, fieldsBound, tailBound, selected, caller, environment, Helper.names]
          · have replaced := replace_captured_returns fieldsBound state position subject receipt.target
              (v "position") (v "subject") (v "target")
              (by simp [fieldsBound, tailBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            unfold liftReplace
            cases selectedSite : MeTTaILSubtermMatchAutomata.selectSite? subject position with
            | none =>
                apply case_returns program fieldsBound fieldsBound state state state _ (.symbol "None") (v "tail")
                  _ _ liftReplaceCases (read_cases_encoded _) _ _ _
                · simpa [replaceWireTerm, selectedSite, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using replaced
                · simp [liftReplaceCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · simpa [liftReceipts, selectedSite, positionedReceiptsTerm, encodeList, CettaWireAtom.encode,
                    fieldsBound, tailBound, selected, caller, environment, Helper.names, tail, applySubst, Subst.lookup] using
                      variable_returns program fieldsBound state "tail"
            | some site =>
                let whole := site.1.fill receipt.target
                let wholeBound := ("whole", encoded (InferenceCettaWire.encodePattern whole)) :: fieldsBound
                apply case_returns program fieldsBound wholeBound state state state _
                  (a "Some" [encoded (InferenceCettaWire.encodePattern whole)]) liftResult _ _ liftReplaceCases
                  (read_cases_encoded _) _ _ _
                · simpa [replaceWireTerm, selectedSite, MatchAutomataBindingExecution.patternOptionTerm,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany, whole] using replaced
                · simp [liftReplaceCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, wholeBound, fieldsBound,
                    tailBound, selected, caller, environment, Helper.names]
                · simpa [liftResult, liftReceipts, selectedSite, positionedReceiptsTerm, encodeList,
                    positionedReceiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
                    applySubst.applySubstList, Subst.lookup, wholeBound, whole, fieldsBound, tailBound,
                    selected, caller, environment, Helper.names, tail] using
                      PureData.template_return program wholeBound state liftResult lift_result_template

/-- The actual helper reconstructs each whole target through the resolved
canonical context and retains all atomic receipt occurrences. -/
theorem lift_captured_returns (caller : Subst) (state : State) (position : SubtermMatching.Position)
    (subject : PatternPlan) (receipts : List Receipt) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (EquationExecution.pathTerm position), encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (EquationExecution.receiptsTerm receipts)]) :
    PureReturns program caller state (a "gslt:equation-context:lift" [one, two, three]) state
      (encoded (positionedReceiptsTerm (liftReceipts position subject receipts))) :=
  helper_call .lift caller state _ _ _ rfl captured (lift_body_returns state position subject receipts)

#print axioms lift_captured_returns

private def frontierHead : Atom := a "let*" [
  .expression [.expression [v "atomic", a "gslt:equation:root" [v "equations", v "rows", v "focus"]],
    .expression [v "head", a "gslt:equation-context:lift" [v "position", v "subject", v "atomic"]]],
  a "gslt:automata:append" [v "head", v "tail"]]
private def frontierFocusCases : SpaceSemantics.Cases :=
  [(.symbol "None", v "tail"), (a "Some" [v "focus"], frontierHead)]
private def frontierFocus : Atom := a "case" [a "gslt:equation-context:focus" [v "position", v "subject"],
  .expression (frontierFocusCases.map fun row => .expression [row.1, row.2])]
private def frontierCons : Atom := a "let" [v "tail",
  a "gslt:equation-context:frontier-matches" [v "equations", v "rows", v "subject", v "rest"], frontierFocus]
private def frontierMatchesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "Found" [v "position", v "occurrence", v "bindings"], v "rest"], frontierCons),
    (v "bad", .symbol "LNil")]
private theorem frontier_matches_shape : (equation .frontierMatches).body = a "case" [v "matches",
    .expression (frontierMatchesCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem frontier_matches_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan)
    (foundMatches : List MeTTaILSubtermMatchAutomata.BoundMatch) :
    PureReturns program (environment .frontierMatches [encoded (EquationExecution.equationsTerm contexts plans),
      rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase),
      encoded (MatchAutomataBindingExecution.matchesTerm foundMatches)]) state
      (equation .frontierMatches).body state (encoded (positionedReceiptsTerm
        (frontierFromMatches (providerEnv rows) language plans subject foundMatches))) := by
  induction foundMatches with
  | nil =>
      let caller := environment .frontierMatches [encoded (EquationExecution.equationsTerm contexts plans),
        rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (MatchAutomataBindingExecution.matchesTerm [])]
      rw [frontier_matches_shape]
      apply case_returns program caller caller state state state (v "matches") (.symbol "LNil") (.symbol "LNil")
        _ _ frontierMatchesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, MatchAutomataBindingExecution.matchesTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "matches"
      · simp [frontierMatchesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [frontierFromMatches, positionedReceiptsTerm, encodeList, CettaWireAtom.encode] using
          symbol_returns program caller state "LNil"
  | cons found foundMatches ih =>
      let caller := environment .frontierMatches [encoded (EquationExecution.equationsTerm contexts plans),
        rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (MatchAutomataBindingExecution.matchesTerm (found :: foundMatches))]
      let selected := ("rest", encoded (MatchAutomataBindingExecution.matchesTerm foundMatches)) ::
        ("bindings", encoded (MatchAutomataBindingExecution.bindingsTerm found.bindings)) ::
        ("occurrence", number found.location.occurrence) ::
        ("position", encoded (EquationExecution.pathTerm found.location.position)) :: caller
      let tail := frontierFromMatches (providerEnv rows) language plans subject foundMatches
      let tailBound := ("tail", encoded (positionedReceiptsTerm tail)) :: selected
      rw [frontier_matches_shape]
      apply case_returns program caller selected state state state (v "matches")
        (encoded (MatchAutomataBindingExecution.matchesTerm (found :: foundMatches))) frontierCons _ _
        frontierMatchesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "matches"
      · simp [frontierMatchesCases, MatchAutomataBindingExecution.matchesTerm, MatchAutomataBindingExecution.boundMatchTerm,
          MatchAutomataDerivativeExecution.positionTerm, EquationExecution.pathTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold frontierCons
        apply let_returns program selected tailBound state state state _ _ _ _ _
        · exact helper_call .frontierMatches selected state _ [v "equations", v "rows", v "subject", v "rest"] _ rfl
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
            selected, caller, environment, Helper.names, tail]
        · have focused := focus_captured_returns tailBound state found.location.position subject (v "position") (v "subject")
              (by simp [tailBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          unfold frontierFocus
          cases selectedSite : MeTTaILSubtermMatchAutomata.selectSite? subject found.location.position with
          | none =>
              apply case_returns program tailBound tailBound state state state _ (.symbol "None") (v "tail")
                _ _ frontierFocusCases (read_cases_encoded _) _ _ _
              · simpa [focusWireTerm, selectedSite, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using focused
              · simp [frontierFocusCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [frontierFromMatches, selectedSite, List.flatMap_cons, List.nil_append,
                  tailBound, selected, caller, environment, Helper.names, tail, applySubst, Subst.lookup] using
                    variable_returns program tailBound state "tail"
          | some site =>
              let focusBound := ("focus", encoded (InferenceCettaWire.encodePattern site.2.erase)) :: tailBound
              let atomic := rootReceipts (providerEnv rows) language plans site.2.erase
              let atomicBound := ("atomic", encoded (EquationExecution.receiptsTerm atomic)) :: focusBound
              let head := liftReceipts found.location.position subject atomic
              let headBound := ("head", encoded (positionedReceiptsTerm head)) :: atomicBound
              apply case_returns program tailBound focusBound state state state _
                (a "Some" [encoded (InferenceCettaWire.encodePattern site.2.erase)]) frontierHead _ _
                frontierFocusCases (read_cases_encoded _) _ _ _
              · simpa [focusWireTerm, selectedSite, MatchAutomataBindingExecution.patternOptionTerm,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using focused
              · simp [frontierFocusCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, focusBound, tailBound,
                  selected, caller, environment, Helper.names]
              · have rooted : PureReturns program focusBound state
                    (a "gslt:equation:root" [v "equations", v "rows", v "focus"]) state
                    (encoded (EquationExecution.receiptsTerm atomic)) := by
                  apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
                  exact EquationExecution.root_captured_returns focusBound state language rows contexts plans.val plans.property site.2 _ _ _
                    (by simp [focusBound, tailBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                have lifted := lift_captured_returns atomicBound state found.location.position subject atomic
                  (v "position") (v "subject") (v "atomic")
                  (by simp [atomicBound, focusBound, tailBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                unfold frontierHead
                apply PureData.let_bindings_return
                  (pairs := [(v "atomic", a "gslt:equation:root" [v "equations", v "rows", v "focus"]),
                    (v "head", a "gslt:equation-context:lift" [v "position", v "subject", v "atomic"])])
                  (bindings := focusBound) (before := state) (middle := state) (final := headBound)
                · apply PureData.BindingsReturn.cons (bound := atomicBound) rooted
                    (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                      atomicBound, focusBound, tailBound, selected, caller, environment, Helper.names])
                  apply PureData.BindingsReturn.cons (bound := headBound) lifted
                    (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
                      headBound, atomicBound, focusBound, tailBound, selected, caller, environment, Helper.names, head])
                  exact .nil _ _
                · have appended : PureReturns program headBound state
                      (a "gslt:automata:append" [v "head", v "tail"]) state
                      (encoded (positionedReceiptsTerm (head ++ tail))) := by
                    apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
                    apply EquationExecutionProgram.retained_captured_returns (by decide +kernel)
                    apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
                    simpa only [MatchAutomataSourceExecution.listValue, positionedReceiptsTerm, ← List.map_append, encodeList_map, Function.comp_def, id_eq] using
                      MatchAutomataSourceExecution.append_captured_returns headBound state
                        (head.map positionedReceiptTerm) (tail.map positionedReceiptTerm) (v "head") (v "tail")
                        (by simp [headBound, atomicBound, focusBound, tailBound, selected, caller, environment,
                          Helper.names, applySubst, Subst.lookup, positionedReceiptsTerm, MatchAutomataSourceExecution.listValue, encodeList_map])
                  simpa only [frontierFromMatches, List.flatMap_cons, selectedSite, head, tail] using appended

/-- Authored contextual instances are enumerated from the actual retained
matcher positions; every instance keeps its physical and query occurrence. -/
theorem frontier_matches_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan)
    (foundMatches : List MeTTaILSubtermMatchAutomata.BoundMatch) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (MatchAutomataBindingExecution.matchesTerm foundMatches)]) :
    PureReturns program caller state (a "gslt:equation-context:frontier-matches" [one, two, three, four]) state
      (encoded (positionedReceiptsTerm (frontierFromMatches (providerEnv rows) language plans subject foundMatches))) :=
  helper_call .frontierMatches caller state _ _ _ rfl captured
    (frontier_matches_body_returns state language rows contexts plans subject foundMatches)

#print axioms frontier_matches_captured_returns

private def frontierCases : SpaceSemantics.Cases :=
  [(a "MatchRun" [v "matches", v "reads", v "dispatches"],
      a "gslt:equation-context:frontier-matches" [v "equations", v "rows", v "subject", v "matches"]),
    (v "bad", .symbol "LNil")]
private def frontierPattern : Atom := a "LCons" [a "FVar" [encoded (.string "EqFocus")], .symbol "LNil"]
private theorem frontier_shape : (equation .frontier).body = a "case"
    [a "gslt:automata:top" [frontierPattern, v "subject"],
      .expression (frontierCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem frontier_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) :
    PureReturns program (environment .frontier [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase)]) state (equation .frontier).body state
      (encoded (positionedReceiptsTerm (contextualReceipts (providerEnv rows) language plans subject))) := by
  let caller := environment .frontier [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase)]
  let patterns : List PatternPlan := [.metavariable "EqFocus"]
  let foundMatches := MeTTaILSubtermMatchAutomata.reference [.fvar "EqFocus"] subject
  obtain ⟨reads, dispatches, exactRun⟩ : ∃ reads dispatches,
      MatchAutomataExecution.topRunTerm patterns subject = MatchAutomataExecution.matchRunTerm foundMatches reads dispatches :=
    ⟨_, _, rfl⟩
  let selected := ("dispatches", number dispatches) :: ("reads", number reads) ::
    ("matches", encoded (MatchAutomataBindingExecution.matchesTerm foundMatches)) :: caller
  have matched : PureReturns program caller state (a "gslt:automata:top" [frontierPattern, v "subject"]) state
      (encoded (MatchAutomataExecution.matchRunTerm foundMatches reads dispatches)) := by
    apply EquationContextExecutionProgram.retained_captured_returns (by decide +kernel)
    apply EquationExecutionProgram.retained_captured_returns (by decide +kernel)
    apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
    rw [← exactRun]
    apply MatchAutomataExecution.top_captured_returns caller state patterns subject [frontierPattern, v "subject"]
    change [frontierPattern, v "subject"].map (applySubst caller) =
      [encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)), encoded (InferenceCettaWire.encodePattern subject.erase)]
    simp [frontierPattern, patterns, erasePatterns, PatternPlan.erase, InferenceCettaWire.encodePatterns,
        InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany, caller,
        environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup]
  rw [frontier_shape]
  apply case_returns program caller selected state state state _
    (encoded (MatchAutomataExecution.matchRunTerm foundMatches reads dispatches))
    (a "gslt:equation-context:frontier-matches" [v "equations", v "rows", v "subject", v "matches"])
    _ _ frontierCases (read_cases_encoded _) matched _ _
  · simp [frontierCases, MatchAutomataExecution.matchRunTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
  · have frontier := frontier_matches_captured_returns selected state language rows contexts plans subject foundMatches
      (v "equations") (v "rows") (v "subject") (v "matches")
      (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
    simpa only [foundMatches, frontierFromMatches_wildcard] using frontier

/-- The actual source entry reconstructs the canonical complete contextual
frontier through the retained matcher and atomic instance compiler. -/
theorem frontier_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:equation-context:frontier" [one, two, three]) state
      (encoded (positionedReceiptsTerm (contextualReceipts (providerEnv rows) language plans subject))) :=
  helper_call .frontier caller state _ _ _ rfl captured (frontier_body_returns state language rows contexts plans subject)

#print axioms frontier_captured_returns

private def findTargetNext : Atom := a "gslt:equation-context:find-target" [v "rest", v "target"]
private def findTargetSelect : Atom := a "if" [a "==" [v "whole", v "target"], a "Some" [v "receipt"], findTargetNext]
private def findTargetReceiptCases : SpaceSemantics.Cases :=
  [(a "EqAt" [v "position", v "atomic", v "whole"], findTargetSelect), (v "bad", findTargetNext)]
private def findTargetReceipt : Atom := a "case" [v "receipt",
  .expression (findTargetReceiptCases.map fun row => .expression [row.1, row.2])]
private def findTargetCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"), (a "LCons" [v "receipt", v "rest"], findTargetReceipt), (v "bad", .symbol "None")]
private theorem find_target_shape : (equation .findTarget).body = a "case" [v "receipts",
    .expression (findTargetCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem find_target_body_returns (state : State) (receipts : List PositionedReceipt) (target : Pattern) :
    PureReturns program (environment .findTarget [encoded (positionedReceiptsTerm receipts),
      encoded (InferenceCettaWire.encodePattern target)]) state (equation .findTarget).body state
      (encoded (encodeOption positionedReceiptTerm (receipts.find? (fun receipt => receipt.target == target)))) := by
  induction receipts with
  | nil =>
      let caller := environment .findTarget [encoded (positionedReceiptsTerm []), encoded (InferenceCettaWire.encodePattern target)]
      rw [find_target_shape]
      apply case_returns program caller caller state state state (v "receipts") (.symbol "LNil") (.symbol "None")
        _ _ findTargetCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, positionedReceiptsTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "receipts"
      · simp [findTargetCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [encodeOption, CettaWireAtom.encode] using symbol_returns program caller state "None"
  | cons receipt receipts ih =>
      let caller := environment .findTarget [encoded (positionedReceiptsTerm (receipt :: receipts)), encoded (InferenceCettaWire.encodePattern target)]
      let selected := ("rest", encoded (positionedReceiptsTerm receipts)) :: ("receipt", encoded (positionedReceiptTerm receipt)) :: caller
      let fieldsBound := ("whole", encoded (InferenceCettaWire.encodePattern receipt.target)) ::
        ("atomic", encoded (EquationExecution.receiptTerm receipt.atomic)) :: ("position", encoded (EquationExecution.pathTerm receipt.position)) :: selected
      rw [find_target_shape]
      apply case_returns program caller selected state state state (v "receipts")
        (encoded (positionedReceiptsTerm (receipt :: receipts))) findTargetReceipt _ _ findTargetCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "receipts"
      · simp [findTargetCases, positionedReceiptsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold findTargetReceipt
        apply case_returns program selected fieldsBound state state state (v "receipt")
          (encoded (positionedReceiptTerm receipt)) findTargetSelect _ _ findTargetReceiptCases (read_cases_encoded _) _ _ _
        · simpa [selected, caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program selected state "receipt"
        · simp [findTargetReceiptCases, positionedReceiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, fieldsBound, selected, caller, environment, Helper.names]
        · have compared := pattern_equal_returns fieldsBound state receipt.target target "whole" "target"
            (by simp [fieldsBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            (by simp [fieldsBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          unfold findTargetSelect
          apply if_returns program fieldsBound state state state _ (Effects.boolean (decide (receipt.target = target))) _ _ _ compared
          by_cases same : receipt.target = target
          · simp only [same, decide_true, Effects.boolean]
            change PureReturns program fieldsBound state (a "Some" [v "receipt"]) state _
            simpa [List.find?, same, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              fieldsBound, selected, caller, environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
                PureData.template_return program fieldsBound state (a "Some" [v "receipt"]) (some_template "receipt")
          · simp only [same, decide_false, Effects.boolean]
            change PureReturns program fieldsBound state findTargetNext state _
            unfold findTargetNext
            have refused : (receipt.target == target) = false := beq_eq_false_iff_ne.mpr same
            simpa only [List.find?, refused, Helper.head] using
              helper_call .findTarget fieldsBound state _ [v "rest", v "target"] _ rfl
                (by simp [fieldsBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih

/-- Ordered selection returns the first existing contextual occurrence for
this whole target. Neither equal witnesses nor duplicate rows are collapsed. -/
theorem find_target_captured_returns (caller : Subst) (state : State) (receipts : List PositionedReceipt)
    (target : Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (positionedReceiptsTerm receipts), encoded (InferenceCettaWire.encodePattern target)]) :
    PureReturns program caller state (a "gslt:equation-context:find-target" [one, two]) state
      (encoded (encodeOption positionedReceiptTerm (receipts.find? (fun receipt => receipt.target == target)))) :=
  helper_call .findTarget caller state _ _ _ rfl captured (find_target_body_returns state receipts target)

#print axioms find_target_captured_returns

private def findSignedAccept : Atom := a "if" [a "==" [v "actual", v "subject"],
  a "Some" [a "EqPrevious" [v "target", v "receipt"]], .symbol "None"]
private def findSignedValidateCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "actual"], findSignedAccept)]
private def findSignedValidate : Atom := a "case"
  [a "gslt:equation-context:validate" [v "equations", v "rows", v "target", v "receipt"],
    .expression (findSignedValidateCases.map fun row => .expression [row.1, row.2])]
private def findSignedPreviousCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "receipt"], findSignedValidate)]
private def findSignedPrevious : Atom := a "let" [v "previous",
  a "gslt:equation-context:frontier" [v "equations", v "rows", v "target"],
  a "case" [a "gslt:equation-context:find-target" [v "previous", v "subject"],
    .expression (findSignedPreviousCases.map fun row => .expression [row.1, row.2])]]
private def findSignedForwardCases : SpaceSemantics.Cases :=
  [(a "Some" [v "receipt"], a "Some" [v "receipt"]), (.symbol "None", findSignedPrevious)]
private def findSignedForward : Atom := a "case" [a "gslt:equation-context:find-target" [v "forward", v "target"],
  .expression (findSignedForwardCases.map fun row => .expression [row.1, row.2])]
private theorem find_signed_shape : (equation .findSigned).body = a "let" [v "forward",
    a "gslt:equation-context:frontier" [v "equations", v "rows", v "subject"], findSignedForward] := by decide +kernel

private theorem signed_previous_template : PureData.Template program (a "Some" [a "EqPrevious" [v "target", v "receipt"]]) := by
  apply data_template _ _ (by simp)
  intro argument member
  rw [List.mem_singleton] at member
  subst argument
  apply data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem find_signed_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject target : PatternPlan) :
    PureReturns program (environment .findSigned [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePattern target.erase)]) state
      (equation .findSigned).body state
      (encoded (encodeOption signedReceiptTerm (findSignedReceipt? (providerEnv rows) language plans subject target))) := by
  let caller := environment .findSigned [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePattern target.erase)]
  let forward := contextualReceipts (providerEnv rows) language plans subject
  let forwardBound := ("forward", encoded (positionedReceiptsTerm forward)) :: caller
  have front := frontier_captured_returns caller state language rows contexts plans subject
    (v "equations") (v "rows") (v "subject")
    (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
  rw [find_signed_shape]
  apply let_returns program caller forwardBound state state state _ _ _ _ _ front
    (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
      forwardBound, caller, environment, Helper.names, forward])
  have foundForward := find_target_captured_returns forwardBound state forward target.erase (v "forward") (v "target")
    (by simp [forwardBound, caller, environment, Helper.names, applySubst, Subst.lookup])
  change PureReturns program forwardBound state _ state
    (encoded (encodeOption positionedReceiptTerm (findPositionedReceipt? (providerEnv rows) language plans subject target.erase))) at foundForward
  unfold findSignedForward
  cases forwardRead : findPositionedReceipt? (providerEnv rows) language plans subject target.erase with
  | some receipt =>
      let receiptBound := ("receipt", encoded (positionedReceiptTerm receipt)) :: forwardBound
      apply case_returns program forwardBound receiptBound state state state _
        (a "Some" [encoded (positionedReceiptTerm receipt)]) (a "Some" [v "receipt"]) _ _
        findSignedForwardCases (read_cases_encoded _) _ _ _
      · simpa only [forwardRead, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using foundForward
      · simp [findSignedForwardCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, receiptBound, forwardBound, caller, environment, Helper.names]
      · simpa [findSignedReceipt?, forwardRead, encodeOption, signedReceiptTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          receiptBound, forwardBound, caller, environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program receiptBound state (a "Some" [v "receipt"]) (some_template "receipt")
  | none =>
      apply case_returns program forwardBound forwardBound state state state _ (.symbol "None") findSignedPrevious _ _
        findSignedForwardCases (read_cases_encoded _) _ _ _
      · simpa only [forwardRead, encodeOption, CettaWireAtom.encode] using foundForward
      · simp [findSignedForwardCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · let previous := contextualReceipts (providerEnv rows) language plans target
        let previousBound := ("previous", encoded (positionedReceiptsTerm previous)) :: forwardBound
        have prevFront := frontier_captured_returns forwardBound state language rows contexts plans target
          (v "equations") (v "rows") (v "target")
          (by simp [forwardBound, caller, environment, Helper.names, applySubst, Subst.lookup])
        unfold findSignedPrevious
        apply let_returns program forwardBound previousBound state state state _ _ _ _ _ prevFront
          (by simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
            previousBound, forwardBound, caller, environment, Helper.names, previous])
        have foundPrevious := find_target_captured_returns previousBound state previous subject.erase (v "previous") (v "subject")
          (by simp [previousBound, forwardBound, caller, environment, Helper.names, applySubst, Subst.lookup])
        change PureReturns program previousBound state _ state
          (encoded (encodeOption positionedReceiptTerm (findPositionedReceipt? (providerEnv rows) language plans target subject.erase))) at foundPrevious
        cases previousRead : findPositionedReceipt? (providerEnv rows) language plans target subject.erase with
        | none =>
            apply case_returns program previousBound previousBound state state state _ (.symbol "None") (.symbol "None") _ _
              findSignedPreviousCases (read_cases_encoded _) _ _ _
            · simpa only [previousRead, encodeOption, CettaWireAtom.encode] using foundPrevious
            · simp [findSignedPreviousCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [findSignedReceipt?, forwardRead, previousRead, encodeOption, CettaWireAtom.encode] using
                symbol_returns program previousBound state "None"
        | some receipt =>
            let receiptBound := ("receipt", encoded (positionedReceiptTerm receipt)) :: previousBound
            apply case_returns program previousBound receiptBound state state state _
              (a "Some" [encoded (positionedReceiptTerm receipt)]) findSignedValidate _ _
              findSignedPreviousCases (read_cases_encoded _) _ _ _
            · simpa only [previousRead, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using foundPrevious
            · simp [findSignedPreviousCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, receiptBound, previousBound,
                forwardBound, caller, environment, Helper.names]
            · have checked := findPositionedReceipt?_sound (providerEnv rows) language plans target subject.erase receipt previousRead
              have validated := validate_captured_returns receiptBound state language rows contexts plans target receipt
                (v "equations") (v "rows") (v "target") (v "receipt")
                (by simp [receiptBound, previousBound, forwardBound, caller, environment, Helper.names, applySubst, Subst.lookup])
              let actualBound := ("actual", encoded (InferenceCettaWire.encodePattern subject.erase)) :: receiptBound
              unfold findSignedValidate
              apply case_returns program receiptBound actualBound state state state _
                (a "Some" [encoded (InferenceCettaWire.encodePattern subject.erase)]) findSignedAccept _ _
                findSignedValidateCases (read_cases_encoded _) _ _ _
              · simpa [checked, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using validated
              · simp [findSignedValidateCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, actualBound, receiptBound,
                  previousBound, forwardBound, caller, environment, Helper.names]
              · have compared := pattern_equal_returns actualBound state subject.erase subject.erase "actual" "subject"
                  (by simp [actualBound, receiptBound, previousBound, forwardBound, caller, environment, Helper.names, applySubst, Subst.lookup])
                  (by simp [actualBound, receiptBound, previousBound, forwardBound, caller, environment, Helper.names, applySubst, Subst.lookup])
                unfold findSignedAccept
                apply if_returns program actualBound state state state _ (Effects.boolean true) _ _ _
                  (by simpa only [decide_true] using compared)
                change PureReturns program actualBound state (a "Some" [a "EqPrevious" [v "target", v "receipt"]]) state _
                simpa [findSignedReceipt?, forwardRead, previousRead, encodeOption, signedReceiptTerm,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, actualBound, receiptBound, previousBound,
                  forwardBound, caller, environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
                    PureData.template_return program actualBound state
                      (a "Some" [a "EqPrevious" [v "target", v "receipt"]]) signed_previous_template

/-- Native signed acquisition first seeks a forward occurrence, then validates
an original oriented witness at the supplied predecessor before reversing it. -/
theorem find_signed_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject target : PatternPlan) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePattern target.erase)]) :
    PureReturns program caller state (a "gslt:equation-context:find-signed" [one, two, three, four]) state
      (encoded (encodeOption signedReceiptTerm (findSignedReceipt? (providerEnv rows) language plans subject target))) :=
  helper_call .findSigned caller state _ _ _ rfl captured (find_signed_body_returns state language rows contexts plans subject target)

#print axioms find_signed_captured_returns

private def acquireResult : Atom := a "Some" [a "LCons" [v "receipt", v "receipts"]]
private def acquireRestCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "receipts"], acquireResult)]
private def acquireRest : Atom := a "case"
  [a "gslt:equation-context:acquire-path" [v "equations", v "rows", v "next", v "rest"],
    .expression (acquireRestCases.map fun row => .expression [row.1, row.2])]
private def acquireStepCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "receipt"], acquireRest)]
private def acquireStep : Atom := a "case"
  [a "gslt:equation-context:find-signed" [v "equations", v "rows", v "subject", v "next"],
    .expression (acquireStepCases.map fun row => .expression [row.1, row.2])]
private def acquireCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [.symbol "LNil"]), (a "LCons" [v "next", v "rest"], acquireStep), (v "bad", .symbol "None")]
private theorem acquire_shape : (equation .acquirePath).body = a "case" [v "endpoints",
    .expression (acquireCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem acquire_result_template : PureData.Template program acquireResult := by
  apply data_template _ _ (by simp)
  intro argument member
  rw [List.mem_singleton] at member
  subst argument
  exact lcons_template "receipt" "receipts"

private theorem acquire_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan) :
    PureReturns program (environment .acquirePath [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePatterns (erasePatterns endpoints))]) state
      (equation .acquirePath).body state
      (encoded (encodeOption signedReceiptsTerm (acquireSignedPath? (providerEnv rows) language plans subject endpoints))) := by
  induction endpoints generalizing subject with
  | nil =>
      let caller := environment .acquirePath [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePatterns (erasePatterns []))]
      rw [acquire_shape]
      apply case_returns program caller caller state state state (v "endpoints") (.symbol "LNil")
        (a "Some" [.symbol "LNil"]) _ _ acquireCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, erasePatterns, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "endpoints"
      · simp [acquireCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have inert : PureData.Template program (a "Some" [.symbol "LNil"]) := by
          apply data_template _ _ (by simp)
          intro argument member
          exact List.mem_singleton.mp member ▸ PureData.Template.symbol "LNil"
        simpa [acquireSignedPath?, encodeOption, signedReceiptsTerm, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList] using
            PureData.template_return program caller state (a "Some" [.symbol "LNil"]) inert
  | cons target targets ih =>
      let caller := environment .acquirePath [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePatterns (erasePatterns (target :: targets)))]
      let selected := ("rest", encoded (InferenceCettaWire.encodePatterns (erasePatterns targets))) ::
        ("next", encoded (InferenceCettaWire.encodePattern target.erase)) :: caller
      rw [acquire_shape]
      apply case_returns program caller selected state state state (v "endpoints")
        (encoded (InferenceCettaWire.encodePatterns (erasePatterns (target :: targets)))) acquireStep _ _
        acquireCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "endpoints"
      · simp [acquireCases, erasePatterns, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · have found := find_signed_captured_returns selected state language rows contexts plans subject target
          (v "equations") (v "rows") (v "subject") (v "next")
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        unfold acquireStep
        cases foundRead : findSignedReceipt? (providerEnv rows) language plans subject target with
        | none =>
            apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
              acquireStepCases (read_cases_encoded _) _ _ _
            · simpa [foundRead, encodeOption, CettaWireAtom.encode] using found
            · simp [acquireStepCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [acquireSignedPath?, foundRead, encodeOption, CettaWireAtom.encode] using
                symbol_returns program selected state "None"
        | some receipt =>
            let receiptBound := ("receipt", encoded (signedReceiptTerm receipt)) :: selected
            apply case_returns program selected receiptBound state state state _
              (a "Some" [encoded (signedReceiptTerm receipt)]) acquireRest _ _ acquireStepCases (read_cases_encoded _) _ _ _
            · simpa [foundRead, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using found
            · simp [acquireStepCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, receiptBound, selected, caller, environment, Helper.names]
            · have continued := helper_call .acquirePath receiptBound state _ [v "equations", v "rows", v "next", v "rest"] _ rfl
                (by simp [receiptBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (ih target)
              unfold acquireRest
              cases continuedRead : acquireSignedPath? (providerEnv rows) language plans target targets with
              | none =>
                  apply case_returns program receiptBound receiptBound state state state _ (.symbol "None") (.symbol "None") _ _
                    acquireRestCases (read_cases_encoded _) _ _ _
                  · simpa only [continuedRead, encodeOption, CettaWireAtom.encode, Helper.head] using continued
                  · simp [acquireRestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · simpa [acquireSignedPath?, foundRead, continuedRead, encodeOption, CettaWireAtom.encode] using
                      symbol_returns program receiptBound state "None"
              | some receipts =>
                  let listBound := ("receipts", encoded (signedReceiptsTerm receipts)) :: receiptBound
                  apply case_returns program receiptBound listBound state state state _
                    (a "Some" [encoded (signedReceiptsTerm receipts)]) acquireResult _ _ acquireRestCases (read_cases_encoded _) _ _ _
                  · simpa only [continuedRead, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany, Helper.head] using continued
                  · simp [acquireRestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, listBound, receiptBound,
                      selected, caller, environment, Helper.names]
                  · simpa [acquireResult, acquireSignedPath?, foundRead, continuedRead, encodeOption, signedReceiptsTerm,
                      encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, listBound, receiptBound,
                      selected, caller, environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
                        PureData.template_return program listBound state acquireResult acquire_result_template

/-- Actual native endpoint-list acquisition agrees exactly with deterministic
canonical receipt acquisition, including a refused adjacency. -/
theorem acquire_path_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), encoded (InferenceCettaWire.encodePatterns (erasePatterns endpoints))]) :
    PureReturns program caller state (a "gslt:equation-context:acquire-path" [one, two, three, four]) state
      (encoded (encodeOption signedReceiptsTerm (acquireSignedPath? (providerEnv rows) language plans subject endpoints))) :=
  helper_call .acquirePath caller state _ _ _ rfl captured (acquire_body_returns state language rows contexts plans subject endpoints)

#print axioms acquire_path_captured_returns

/-- Canonical endpoint-list input to the actual native acquisition entry. -/
def acquirePathQueryTerm (contexts : Equation → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (endpoints : List PatternPlan) : Term :=
  .application "gslt:equation-context:acquire-path" [EquationExecution.equationsTerm contexts plans,
    providerRowsTerm rows, InferenceCettaWire.encodePattern subject.erase,
    InferenceCettaWire.encodePatterns (erasePatterns endpoints)]

theorem acquire_path_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan) :
    PureReturns program [] state (encoded (acquirePathQueryTerm contexts plans rows subject endpoints)) state
      (encoded (encodeOption signedReceiptsTerm (acquireSignedPath? (providerEnv rows) language plans subject endpoints))) :=
  acquire_path_captured_returns [] state language rows contexts plans subject endpoints _ _ _ _ (by simp)

theorem acquire_path_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts plans rows subject endpoints)) } =
      .complete terminal answers input output) ↔
    terminal = state ∧ answers = [encoded (encodeOption signedReceiptsTerm
      (acquireSignedPath? (providerEnv rows) language plans subject endpoints))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (acquire_path_returns state language rows contexts plans subject endpoints) terminal answers input output

theorem acquire_path_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts plans rows subject endpoints)) }
      (.complete terminal answers input output) ↔
    terminal = state ∧ answers = [encoded (encodeOption signedReceiptsTerm
      (acquireSignedPath? (providerEnv rows) language plans subject endpoints))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (acquire_path_returns state language rows contexts plans subject endpoints) terminal answers input output

/-- Success is exactly the acquired ordered receipt list, rather than merely
a target that some unrelated equation witness could have produced. -/
theorem acquire_path_observes_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (receipts : List SignedReceipt) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts plans rows subject endpoints)) }
      (.complete state [encoded (.application "Some" [signedReceiptsTerm receipts])] [] []) ↔
    acquireSignedPath? (providerEnv rows) language plans subject endpoints = some receipts := by
  constructor
  · intro observed
    have answers := ((acquire_path_derivation_iff state language rows contexts plans subject endpoints _ _ _ _).mp observed).2.1
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj answers).1
    cases acquired : acquireSignedPath? (providerEnv rows) language plans subject endpoints with
    | none => simp only [acquired, encodeOption] at same; cases same
    | some actual =>
        have payload : signedReceiptsTerm receipts = signedReceiptsTerm actual := by
          simpa only [acquired, encodeOption, Term.application.injEq, List.cons.injEq, and_true, true_and] using same
        have exactReceipts := signedReceiptsTerm_injective payload
        simp only [exactReceipts]
  · intro acquired
    apply (acquire_path_derivation_iff state language rows contexts plans subject endpoints _ _ _ _).mpr
    simp only [acquired, encodeOption, true_and]

/-- Actual native acquisition preserves and reflects the independent canonical
finite route judgment with the supplied, ordered intermediate endpoints. -/
theorem acquire_path_observes_iff_canonical_route (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (viewAdmitted : (directedView language).isEquationFree = true) (subject : PatternPlan) (endpoints : List PatternPlan) :
    (∃ receipts : List SignedReceipt, DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject endpoints)) }
      (.complete state [encoded (.application "Some" [signedReceiptsTerm receipts])] [] [])) ↔
    ∃ target, ∃ path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises (providerEnv rows)) language) left.erase right.erase)) subject target,
      path.trace (fun {_source target} _ => target) = endpoints := by
  rw [← acquireSignedPath?_isSome_iff_route compiled viewAdmitted subject endpoints]
  constructor
  · rintro ⟨receipts, observed⟩
    have acquired := (acquire_path_observes_iff state language rows contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject endpoints receipts).mp observed
    simp only [acquired, Option.isSome_some]
  · intro supported
    cases acquired : acquireSignedPath? (providerEnv rows) language (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject endpoints with
    | none => simp only [acquired, Option.isSome_none, Bool.false_eq_true] at supported
    | some receipts => exact ⟨receipts,
        (acquire_path_observes_iff state language rows contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject endpoints receipts).mpr acquired⟩

/-- A successful native acquisition has the original equation-equivalence
meaning. Equality is never added to the directed rewrite permission list. -/
theorem observed_acquisition_equivalent (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (subject : PatternPlan) (endpoints : List PatternPlan) (receipts : List SignedReceipt)
    (observed : DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject endpoints)) }
      (.complete state [encoded (.application "Some" [signedReceiptsTerm receipts])] [] [])) :
    EquationEquiv (engineBasePremises (providerEnv rows)) language subject.erase
      (endpoints.foldl (fun _ next => next) subject).erase := by
  have acquired := (acquire_path_observes_iff state language rows contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject endpoints receipts).mp observed
  exact replaySignedPath?_sound compiled _ _ receipts
    (acquireSignedPath?_replays (providerEnv rows) language (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject endpoints receipts acquired)

/-- Every canonical finite route in the admitted profile is acquired by the
actual native program from its endpoint list and replays to its stated target. -/
theorem native_canonical_route_acquisition (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Equation → Term) (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (viewAdmitted : (directedView language).isEquationFree = true) {subject target : PatternPlan}
    (path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises (providerEnv rows)) language) left.erase right.erase)) subject target) :
    ∃ receipts, DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows subject
        (path.trace (fun {_source target} _ => target)))) }
      (.complete state [encoded (.application "Some" [signedReceiptsTerm receipts])] [] []) ∧
      replaySignedPath? (providerEnv rows) language (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject receipts = some target := by
  obtain ⟨receipts, acquired, replayed⟩ := compileSignedRoute?_complete compiled viewAdmitted path
  exact ⟨receipts, (acquire_path_observes_iff state language rows contexts (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) subject _ receipts).mpr acquired, replayed⟩

#print axioms acquire_path_returns
#print axioms acquire_path_completed_iff
#print axioms acquire_path_derivation_iff
#print axioms acquire_path_observes_iff
#print axioms acquire_path_observes_iff_canonical_route
#print axioms observed_acquisition_equivalent
#print axioms native_canonical_route_acquisition

namespace Controls

open _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls
  (language compiled atom discardPredecessor discardRelations discardLanguage discardCompiled discardReceipt)

/-- The native acquisition chooses the first duplicate query witness, although
its independent canonical evidence was built from the second witness. -/
theorem first_duplicate_acquired_derivation (state : State) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (variableEquationPlans compiled.plans (by decide +kernel)) rows
        (atom "a") [Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.conditionalTarget])) }
      (.complete state [encoded (.application "Some" [signedReceiptsTerm
        [.inl ⟨[], MeTTaILFirstOrderEquationCompilation.Controls.expected 0 0 "b", Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.conditionalTarget.erase⟩]])] [] []) := by
  apply (acquire_path_observes_iff state language rows contexts (variableEquationPlans compiled.plans (by decide +kernel)) (atom "a")
    [Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.conditionalTarget] _).mpr
  rw [EquationExecution.Controls.provider_exact]
  simpa only [compileSignedRoute?, Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.conditionalRoute, Route.trace] using
    MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.conditional_route_acquired

/-- The original predecessor supplies x=a, which matching the reverse side
cannot reconstruct. Native acquisition retains and validates that witness. -/
theorem discarded_variable_roundtrip_acquired_derivation (state : State) :
    ∃ receipts, DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardRows
        discardPredecessor [atom "b", discardPredecessor])) }
      (.complete state [encoded (.application "Some" [signedReceiptsTerm receipts])] [] []) ∧
      replaySignedPath? (providerEnv discardRows) discardLanguage (variableEquationPlans discardCompiled.plans (by decide +kernel))
        discardPredecessor receipts = some discardPredecessor ∧ receipts.length = 2 := by
  have edge : EquationContextStep (engineBasePremises (providerEnv discardRows)) discardLanguage
      discardPredecessor.erase (atom "b").erase := by
    rw [discard_provider_exact]
    exact validated_positioned_step discardCompiled discardPredecessor discardReceipt (atom "b").erase
      MeTTaILFirstOrderEquationCompilation.Controls.discarded_original_receipt_checked
  let path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises (providerEnv discardRows)) discardLanguage)
        left.erase right.erase)) discardPredecessor discardPredecessor :=
    .cons ⟨Or.inl edge⟩ (.cons ⟨Or.inr edge⟩ (.refl _))
  have admitted : (directedView discardLanguage).isEquationFree = true := by decide +kernel
  obtain ⟨receipts, observed, replayed⟩ := native_canonical_route_acquisition state discardLanguage discardRows
    contexts discardCompiled (List.all_eq_true.mp (by decide +kernel)) admitted path
  change DeclarativeSpec.Runs program
    { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardRows
      discardPredecessor [atom "b", discardPredecessor])) }
    (.complete state [encoded (.application "Some" [signedReceiptsTerm receipts])] [] []) at observed
  have acquired := (acquire_path_observes_iff state discardLanguage discardRows contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
    discardPredecessor [atom "b", discardPredecessor] receipts).mp observed
  exact ⟨receipts, observed, replayed, acquireSignedPath?_length (providerEnv discardRows) discardLanguage
    (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardPredecessor [atom "b", discardPredecessor] receipts acquired⟩

/-- Failure of one supplied adjacency refuses that path; it does not assert
inequivalence of the endpoints. -/
theorem absent_endpoint_acquisition_refused_derivation (state : State) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardRows
        (atom "b") [atom "c"])) }
      (.complete state [encoded (.symbol "None")] [] []) := by
  apply (acquire_path_derivation_iff state discardLanguage discardRows contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
    (atom "b") [atom "c"] _ _ _ _).mpr
  rw [discard_provider_exact]
  simp only [acquireSignedPath?,
    MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.absent_endpoint_refused,
    Option.bind_eq_bind, Option.bind_none, encodeOption, true_and]

/-- An accepted first edge does not authorize a later unsupported edge. -/
theorem failed_later_endpoint_acquisition_refused_derivation (state : State) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (acquirePathQueryTerm contexts (variableEquationPlans discardCompiled.plans (by decide +kernel)) discardRows
        discardPredecessor [atom "b", atom "c"])) }
      (.complete state [encoded (.symbol "None")] [] []) := by
  apply (acquire_path_derivation_iff state discardLanguage discardRows contexts (variableEquationPlans discardCompiled.plans (by decide +kernel))
    discardPredecessor [atom "b", atom "c"] _ _ _ _).mpr
  rw [discard_provider_exact]
  have refused : acquireSignedPath? discardRelations discardLanguage (variableEquationPlans discardCompiled.plans (by decide +kernel))
      discardPredecessor [atom "b", atom "c"] = none := by
    simp only [acquireSignedPath?,
      MeTTaILFirstOrderEquationCompilation.RepresentabilityControls.absent_endpoint_refused,
      Option.bind_eq_bind, Option.bind_none]
    cases findSignedReceipt? discardRelations discardLanguage (variableEquationPlans discardCompiled.plans (by decide +kernel))
      discardPredecessor (atom "b") <;> rfl
  simp only [refused, encodeOption, true_and]

end Controls

#print axioms Controls.first_duplicate_acquired_derivation
#print axioms Controls.discarded_variable_roundtrip_acquired_derivation
#print axioms Controls.absent_endpoint_acquisition_refused_derivation
#print axioms Controls.failed_later_endpoint_acquisition_refused_derivation


private abbrev endpointTerm (subject : PatternPlan) : Term := InferenceCettaWire.encodePattern subject.erase

private theorem endpointsTerm_eq (endpoints : List PatternPlan) :
    encodeList endpointTerm endpoints = InferenceCettaWire.encodePatterns (erasePatterns endpoints) := by
  rw [InferenceCettaWire.encodePatterns_eq_encodeList, erasePatterns_eq_map, encodeList_map]
  rfl

private def acquiredReplayCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "receipts"],
    a "gslt:equation-context:replay" [v "equations", v "rows", v "subject", v "receipts"])]
private theorem acquired_replay_shape : (equation .acquiredReplay).body = a "case"
    [a "gslt:equation-context:acquire-path" [v "equations", v "rows", v "subject", v "endpoints"],
      .expression (acquiredReplayCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem acquired_replay_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan) :
    PureReturns program (environment .acquiredReplay
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (endpointTerm subject),
        encoded (encodeList endpointTerm endpoints)]) state (equation .acquiredReplay).body state
      (encoded (replayResultTerm (acquireReplayPath? (providerEnv rows) language plans subject endpoints))) := by
  let caller := environment .acquiredReplay
    [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (endpointTerm subject),
      encoded (encodeList endpointTerm endpoints)]
  have acquired := acquire_path_captured_returns caller state language rows contexts plans subject endpoints
    (v "equations") (v "rows") (v "subject") (v "endpoints")
    (by simp [caller, environment, Helper.names, endpointTerm, endpointsTerm_eq, applySubst, Subst.lookup])
  rw [acquired_replay_shape]
  cases found : acquireSignedPath? (providerEnv rows) language plans subject endpoints with
  | none =>
      apply case_returns program caller caller state state state _ (.symbol "None") (.symbol "None") _ _
        acquiredReplayCases (read_cases_encoded _) _ _ _
      · simpa only [found, encodeOption, CettaWireAtom.encode] using acquired
      · simp [acquiredReplayCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [acquireReplayPath?, found, replayResultTerm, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode] using symbol_returns program caller state "None"
  | some receipts =>
      let selected := ("receipts", encoded (signedReceiptsTerm receipts)) :: caller
      apply case_returns program caller selected state state state _
        (a "Some" [encoded (signedReceiptsTerm receipts)])
        (a "gslt:equation-context:replay" [v "equations", v "rows", v "subject", v "receipts"]) _ _
        acquiredReplayCases (read_cases_encoded _) _ _ _
      · simpa only [found, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using acquired
      · simp [acquiredReplayCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · simpa only [acquireReplayPath?, found, Option.bind_eq_bind, Option.bind_some] using
          replay_signed_captured_returns selected state language rows providerAdmitted contexts plans subject receipts
            [v "equations", v "rows", v "subject", v "receipts"]
            (by simp [selected, caller, environment, Helper.names, endpointTerm, applySubst, Subst.lookup])

/-- The actual source acquires and then replays the same receipt list. Its
refusal concerns that supplied endpoint trace, not global inequivalence. -/
theorem acquired_replay_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows, encoded (endpointTerm subject),
        encoded (encodeList endpointTerm endpoints)]) :
    PureReturns program caller state (a "gslt:equation-context:acquired-replay" arguments) state
      (encoded (replayResultTerm (acquireReplayPath? (providerEnv rows) language plans subject endpoints))) :=
  helper_call .acquiredReplay caller state _ _ _ rfl captured
    (acquired_replay_body_returns state language rows providerAdmitted contexts plans subject endpoints)

/-- The shared stable post-frontier source filter acquires a continuation at
each actual result. Its representability premise is earned by the directed
executor's closure theorem in the combined source proof. -/
theorem acquired_after_results_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (endpoints : List PatternPlan) (results : List Pattern)
    (firstOrder : ∀ result ∈ results, isMatchCorrectAux result = true) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (EquationExecution.equationsTerm contexts plans), rowsValue rows,
        encoded (encodeList endpointTerm endpoints), patternsValue results]) :
    PureReturns program caller state (a "gslt:equation-context:acquired-after-results" arguments) state
      (patternsValue (acquiredAfterResults (providerEnv rows) language plans endpoints results)) := by
  simpa only [acquiredAfterResults, ContinuationKind.afterHelper, Helper.head] using
    after_results_captured_returns_of_replay .acquired endpointTerm
      (fun subject endpoints => acquireReplayPath? (providerEnv rows) language plans subject endpoints)
      caller state rows contexts plans
      (fun caller subject endpoints arguments captured =>
        acquired_replay_captured_returns caller state language rows providerAdmitted contexts plans subject endpoints
          arguments captured)
      endpoints results firstOrder arguments captured

private theorem acquired_witnessed_body_returns (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PatternPlan) :
    PureReturns program (environment .acquiredWitnessed
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (endpointTerm subject), encoded (encodeList endpointTerm before),
        encoded (encodeList endpointTerm after)]) state (equation .acquiredWitnessed).body state
      (patternsValue (acquiredWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)) := by
  simpa only [acquiredWitnessedReducts, ContinuationKind.witnessedHelper] using
    witnessed_body_returns_of_replay .acquired endpointTerm
      (fun subject endpoints => acquireReplayPath? (providerEnv rows) language plans subject endpoints)
      state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected
      (fun caller subject endpoints arguments captured =>
        acquired_replay_captured_returns caller state language rows providerAdmitted equationContexts plans subject endpoints
          arguments captured)
      depth subject before after

/-- Source execution of acquired canonical continuations around the existing
directed child firing. Every contractum is first-order by the proved executor,
not by assuming the final endpoints represent all intermediate subjects. -/
theorem acquired_witnessed_reducts_captured_returns (caller : Subst) (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (ContextualRuleExecution.strategyTerm strategy),
        encoded (equationLanguageTerm language types terms equationContexts contexts fields plans), rowsValue rows,
        number depth, encoded (endpointTerm subject), encoded (encodeList endpointTerm before),
        encoded (encodeList endpointTerm after)]) :
    PureReturns program caller state (a "gslt:equation-context:acquired-witnessed-reducts" arguments) state
      (patternsValue (acquiredWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)) :=
  helper_call .acquiredWitnessed caller state _ _ _ rfl captured
    (acquired_witnessed_body_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after)

def acquiredReplayQueryTerm (contexts : Equation → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (endpoints : List PatternPlan) : Term :=
  .application "gslt:equation-context:acquired-replay" [EquationExecution.equationsTerm contexts plans,
    providerRowsTerm rows, endpointTerm subject, encodeList endpointTerm endpoints]

theorem acquired_replay_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan) :
    PureReturns program [] state (encoded (acquiredReplayQueryTerm contexts plans rows subject endpoints)) state
      (encoded (replayResultTerm (acquireReplayPath? (providerEnv rows) language plans subject endpoints))) := by
  simpa only [acquiredReplayQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    acquired_replay_captured_returns [] state language rows providerAdmitted contexts plans subject endpoints _ (by simp)

theorem acquired_replay_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded (acquiredReplayQueryTerm contexts plans rows subject endpoints)) } = .complete terminal answers input output) ↔
      terminal = state ∧ answers = [encoded (replayResultTerm
        (acquireReplayPath? (providerEnv rows) language plans subject endpoints))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (acquired_replay_returns state language rows providerAdmitted contexts plans subject endpoints) terminal answers input output

theorem acquired_replay_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (contexts : Equation → Term) (plans : VariableEquationPlans) (subject : PatternPlan) (endpoints : List PatternPlan)
    (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded (acquiredReplayQueryTerm contexts plans rows subject endpoints)) } (.complete terminal answers input output) ↔
      terminal = state ∧ answers = [encoded (replayResultTerm
        (acquireReplayPath? (providerEnv rows) language plans subject endpoints))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (acquired_replay_returns state language rows providerAdmitted contexts plans subject endpoints) terminal answers input output

def acquiredWitnessedQueryTerm (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (depth : Nat)
    (subject : PatternPlan) (before after : List PatternPlan) : Term :=
  .application "gslt:equation-context:acquired-witnessed-reducts"
    [ContextualRuleExecution.strategyTerm strategy,
      equationLanguageTerm language types terms equationContexts contexts fields plans, providerRowsTerm rows,
      .natural depth, endpointTerm subject, encodeList endpointTerm before, encodeList endpointTerm after]

theorem acquired_witnessed_reducts_returns (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PatternPlan) :
    PureReturns program [] state (encoded (acquiredWitnessedQueryTerm strategy language types terms equationContexts contexts fields
      plans rows depth subject before after)) state
      (patternsValue (acquiredWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)) := by
  simpa only [acquiredWitnessedQueryTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
    acquired_witnessed_reducts_captured_returns [] state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after _ (by simp [applySubst, CettaWireAtom.encode])

theorem acquired_witnessed_reducts_completed_iff (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PatternPlan)
    (terminal : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded
      (acquiredWitnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) } =
        .complete terminal answers input output) ↔
      terminal = state ∧ answers = [patternsValue (acquiredWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (acquired_witnessed_reducts_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after) terminal answers input output

theorem acquired_witnessed_reducts_derivation_iff (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term) (plans : VariableEquationPlans)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (depth : Nat) (subject : PatternPlan) (before after : List PatternPlan)
    (terminal : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (acquiredWitnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) }
        (.complete terminal answers input output) ↔
      terminal = state ∧ answers = [patternsValue (acquiredWitnessedReducts strategy (providerEnv rows) language plans depth subject before after)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (acquired_witnessed_reducts_returns state strategy language types terms equationContexts contexts fields plans rows
      providerAdmitted viewAdmitted projected depth subject before after) terminal answers input output

/-- Membership in a completed acquired frontier at some finite premise depth.
The endpoint traces are actual inputs; this observation adds no equation oracle. -/
def ObservesAcquiredWitnessedReduct (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy)
    (language : LanguageDef) (types terms : Term) (equationContexts : Equation → Term)
    (contexts fields : RewriteRule → Term) (plans : List RulePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject target : PatternPlan)
    (before after : List PatternPlan) : Prop :=
  ∃ depth, ∃ results : List Pattern,
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (acquiredWitnessedQueryTerm strategy language types terms equationContexts contexts fields plans rows depth subject before after)) }
        (.complete state [patternsValue results] [] []) ∧ target.erase ∈ results

/-- Exact source preservation and reflection against independent canonical
symmetric routes with the supplied endpoint traces, around one original
directed firing. All vertices of these finite routes are admitted plans. -/
theorem observes_acquired_witnessed_iff_canonical_routes (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) (before after : List PatternPlan) :
    ObservesAcquiredWitnessedReduct state strategy language types terms equationContexts contexts fields compiled.plans rows
      subject target before after ↔
      ∃ redex contractum : PatternPlan,
        (∃ path : Route (fun left right => PLift (Relation.SymmGen
          (EquationContextStep (engineBasePremises (providerEnv rows)) language) left.erase right.erase)) subject redex,
          path.trace (fun {_source target} _ => target) = before) ∧
        Step (engineBasePremises (providerEnv rows)) language redex.erase contractum.erase ∧
        (∃ path : Route (fun left right => PLift (Relation.SymmGen
          (EquationContextStep (engineBasePremises (providerEnv rows)) language) left.erase right.erase)) contractum target,
          path.trace (fun {_source target} _ => target) = after) := by
  rw [← acquiredWitnessedReducts_iff_canonical_routes strategy (providerEnv rows) language compiled
    ((ContextualRuleExecution.language_admitted_iff _).mp viewAdmitted).1]
  constructor
  · rintro ⟨depth, results, executed, member⟩
    have observation := (acquired_witnessed_reducts_derivation_iff state strategy language types terms equationContexts contexts fields
      (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows providerAdmitted viewAdmitted projected depth subject before after state [patternsValue results] [] []).mp executed
    have sameWire := CettaWireAtom.encode_injective _ _ (List.cons.inj observation.2.1).1
    have same := InferenceCettaWire.encodePatterns_injective sameWire
    exact ⟨depth, by simpa only [same] using member⟩
  · rintro ⟨depth, member⟩
    exact ⟨depth, _, (acquired_witnessed_reducts_derivation_iff state strategy language types terms equationContexts contexts fields
      (⟨compiled.plans, sourceViews⟩ : VariableEquationPlans) rows providerAdmitted viewAdmitted projected depth subject before after state _ [] []).mpr
        ⟨rfl, rfl, rfl, rfl⟩, member⟩

theorem observes_acquired_witnessed_gslt_step (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) (language : LanguageDef) (types terms : Term)
    (equationContexts : Equation → Term) (contexts fields : RewriteRule → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (providerAdmitted : RuleTraceExecution.providerFirstOrder rows = true)
    (viewAdmitted : ContextualRuleExecution.languageAdmitted (directedView language) = true)
    (projected : ∀ rule ∈ language.rewrites, ContextualRuleExecution.premisesTerm? rule.premises = some (fields rule))
    (subject target : PatternPlan) (before after : List PatternPlan)
    (observed : ObservesAcquiredWitnessedReduct state strategy language types terms equationContexts contexts fields compiled.plans rows
      subject target before after) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv rows) language).Step subject.erase target.erase := by
  obtain ⟨redex, contractum, ⟨started, _⟩, directed, ⟨finished, _⟩⟩ :=
    (observes_acquired_witnessed_iff_canonical_routes state strategy language types terms equationContexts contexts fields compiled sourceViews rows
      providerAdmitted viewAdmitted projected subject target before after).mp observed
  exact ⟨redex.erase, contractum.erase, canonicalRoute_equivalent started,
    directed, canonicalRoute_equivalent finished⟩

#print axioms acquired_replay_captured_returns
#print axioms acquired_after_results_captured_returns
#print axioms acquired_witnessed_reducts_captured_returns
#print axioms acquired_replay_completed_iff
#print axioms acquired_replay_derivation_iff
#print axioms acquired_witnessed_reducts_completed_iff
#print axioms acquired_witnessed_reducts_derivation_iff
#print axioms observes_acquired_witnessed_iff_canonical_routes
#print axioms observes_acquired_witnessed_gslt_step

namespace Controls

private abbrev fixtureAtom (name : String) : PatternPlan :=
  _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.atom name

private theorem acquiredModuloBefore :
    acquireReplayPath? (providerEnv []) moduloLanguage moduloCompiled.plans (fixtureAtom "a") [fixtureAtom "b"] =
      some (fixtureAtom "b") := by
  apply (acquireReplayPath?_iff_canonical_route moduloCompiled (by decide +kernel) (fixtureAtom "a") (fixtureAtom "b") [fixtureAtom "b"]).mpr
  exact ⟨.cons ⟨Or.inl (validated_positioned_step moduloCompiled (fixtureAtom "a") moduloBefore (fixtureAtom "b").erase
    (moduloBeforeChecked moduloLanguage))⟩ (.refl _), rfl⟩

private theorem acquiredModuloAfter :
    acquireReplayPath? (providerEnv []) moduloLanguage moduloCompiled.plans (fixtureAtom "c") [fixtureAtom "d"] =
      some (fixtureAtom "d") := by
  apply (acquireReplayPath?_iff_canonical_route moduloCompiled (by decide +kernel) (fixtureAtom "c") (fixtureAtom "d") [fixtureAtom "d"]).mpr
  exact ⟨.cons ⟨Or.inl (validated_positioned_step moduloCompiled (fixtureAtom "c") moduloAfter (fixtureAtom "d").erase
    (moduloAfterChecked moduloLanguage))⟩ (.refl _), rfl⟩

private theorem acquiredModuloFrontier (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    acquiredWitnessedReducts strategy (providerEnv []) moduloLanguage moduloCompiled.plans 1 (fixtureAtom "a")
      [fixtureAtom "b"] [fixtureAtom "d"] = [(fixtureAtom "d").erase, (fixtureAtom "d").erase] := by
  have directed : MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises (providerEnv []))
      (directedView moduloLanguage) 1 (fixtureAtom "b") = [(fixtureAtom "c").erase, (fixtureAtom "c").erase] := by
    rw [MeTTaILMatchAutomataExecution.runAt_exact]
    decide +kernel
  simp only [acquiredWitnessedReducts, witnessedFrontier, acquiredModuloBefore, directed, afterPathResults,
    List.filterMap_cons, List.filterMap_nil, compilePattern?_erase, acquiredModuloAfter,
    Option.bind_eq_bind, Option.bind_some]
  rfl

/-- Both concrete matching strategies retain duplicate directed occurrences
after actual native acquisition and replay of the two endpoint traces. -/
theorem acquired_modulo_duplicates_derivation (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (acquiredWitnessedQueryTerm strategy moduloLanguage (.symbol "RetainedTypes") (.symbol "RetainedTerms")
        moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) [] 1 (fixtureAtom "a") [fixtureAtom "b"] [fixtureAtom "d"])) }
      (.complete state [patternsValue [(fixtureAtom "d").erase, (fixtureAtom "d").erase]] [] []) := by
  rw [acquired_witnessed_reducts_derivation_iff state strategy moduloLanguage
    (.symbol "RetainedTypes") (.symbol "RetainedTerms") moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) []
    moduloProviderAdmitted moduloViewAdmitted moduloProjected 1 (fixtureAtom "a") [fixtureAtom "b"] [fixtureAtom "d"]]
  exact ⟨rfl, by rw [acquiredModuloFrontier], rfl, rfl⟩

theorem acquired_modulo_duplicates_gslt_step (state : State) (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (providerEnv []) moduloLanguage).Step
      (fixtureAtom "a").erase (fixtureAtom "d").erase :=
  observes_acquired_witnessed_gslt_step state strategy moduloLanguage (.symbol "RetainedTypes") (.symbol "RetainedTerms")
    moduloEqContexts moduloContexts moduloFields moduloCompiled (List.all_eq_true.mp (by decide +kernel)) [] moduloProviderAdmitted moduloViewAdmitted moduloProjected
    (fixtureAtom "a") (fixtureAtom "d") [fixtureAtom "b"] [fixtureAtom "d"]
    ⟨1, [(fixtureAtom "d").erase, (fixtureAtom "d").erase], acquired_modulo_duplicates_derivation state strategy, by simp⟩

/-- Acquiring an equation path never supplies a directed row to the original
presentation. The actual combined native entry completes with an empty list. -/
theorem acquired_equation_only_does_not_authorize_reduction (state : State)
    (strategy : MeTTaILMatchAutomataExecution.Strategy) :
    PureReturns program [] state (encoded (acquiredWitnessedQueryTerm strategy { moduloLanguage with rewrites := [] }
      (.symbol "RetainedTypes") (.symbol "RetainedTerms") moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) []
      1 (fixtureAtom "a") [fixtureAtom "b"] [])) state (patternsValue []) := by
  let noDirected : LanguageDef := { moduloLanguage with rewrites := [] }
  let equations : EquationProgram noDirected.equations := ⟨(variableEquationPlans moduloCompiled.plans (by decide +kernel)), rfl⟩
  have admitted : ContextualRuleExecution.languageAdmitted (directedView noDirected) = true := by decide +kernel
  have projected : ∀ rule ∈ noDirected.rewrites,
      ContextualRuleExecution.premisesTerm? rule.premises = some (moduloFields rule) := by simp [noDirected]
  have before : acquireReplayPath? (providerEnv []) noDirected (variableEquationPlans moduloCompiled.plans (by decide +kernel)) (fixtureAtom "a") [fixtureAtom "b"] =
      some (fixtureAtom "b") := by
    apply (acquireReplayPath?_iff_canonical_route equations (by decide +kernel) (fixtureAtom "a") (fixtureAtom "b") [fixtureAtom "b"]).mpr
    exact ⟨.cons ⟨Or.inl (validated_positioned_step equations (fixtureAtom "a") moduloBefore (fixtureAtom "b").erase
      (moduloBeforeChecked noDirected))⟩ (.refl _), rfl⟩
  have empty : MeTTaILMatchAutomataExecution.runAt strategy (engineBasePremises (providerEnv []))
      (directedView noDirected) 1 (fixtureAtom "b") = [] :=
    MeTTaILFirstOrderContextualExecution.runAt_eq_nil_of_no_root_match strategy _ _ _ _ (by simp [noDirected])
  have actual : acquiredWitnessedReducts strategy (providerEnv []) noDirected (variableEquationPlans moduloCompiled.plans (by decide +kernel))
      1 (fixtureAtom "a") [fixtureAtom "b"] [] = [] := by
    simp only [acquiredWitnessedReducts, witnessedFrontier, before, empty, afterPathResults, List.filterMap_nil]
  simpa only [actual] using acquired_witnessed_reducts_returns state strategy noDirected
    (.symbol "RetainedTypes") (.symbol "RetainedTerms") moduloEqContexts moduloContexts moduloFields (variableEquationPlans moduloCompiled.plans (by decide +kernel)) []
    moduloProviderAdmitted admitted projected 1 (fixtureAtom "a") [fixtureAtom "b"] []

/-- The checked original predecessor supplies the discarded variable; the
native acquisition/replay continuation returns that exact predecessor after
a two-edge conditional roundtrip. -/
theorem acquired_discarded_variable_roundtrip_derivation (state : State) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (encoded
      (acquiredReplayQueryTerm contexts (variableEquationPlans _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardCompiled.plans (by decide +kernel)) discardRows _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor
        [fixtureAtom "b", _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor])) }
      (.complete state [encoded (.application "Some" [endpointTerm _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor])] [] []) := by
  have original := validated_positioned_step _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardCompiled _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardReceipt (fixtureAtom "b").erase
    MeTTaILFirstOrderEquationCompilation.Controls.discarded_original_receipt_checked
  let path : Route (fun left right => PLift (Relation.SymmGen
      (EquationContextStep (engineBasePremises _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardRelations) _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardLanguage) left.erase right.erase))
      _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor :=
    .cons (middle := fixtureAtom "b") ⟨Or.inl original⟩ (.cons ⟨Or.inr original⟩ (.refl _))
  have replayed : acquireReplayPath? _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardRelations _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardLanguage (variableEquationPlans _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardCompiled.plans (by decide +kernel)) _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor
      [fixtureAtom "b", _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor] = some _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor :=
    (acquireReplayPath?_iff_canonical_route _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardCompiled (by decide +kernel) _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor
      [fixtureAtom "b", _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardPredecessor]).mpr ⟨path, rfl⟩
  rw [acquired_replay_derivation_iff state _root_.Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation.Controls.discardLanguage discardRows discard_rows_admitted]
  exact ⟨rfl, by
    simp only [discard_provider_exact, replayed, replayResultTerm,
      MatchAutomataBindingExecution.patternOptionTerm]
    rfl, rfl, rfl⟩

end Controls

#print axioms Controls.acquired_modulo_duplicates_derivation
#print axioms Controls.acquired_modulo_duplicates_gslt_step
#print axioms Controls.acquired_equation_only_does_not_authorize_reduction
#print axioms Controls.acquired_discarded_variable_roundtrip_derivation

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationContextExecution
