import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecutionProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RootRuleExecution
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderEquationCompilation

/-!
# PeTTa execution of retained authored-equation witnesses

This source-derived realization decorates the existing canonical matcher and
relation-premise fold with equation and query occurrence identities. Source
declarations have exact first-order admission separately from this matching
projection; no authored equation is inserted into the directed rewrite list.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation MeTTaILFirstOrderEquationCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open EquationSemantics
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval EquationExecutionProgram
open MatchAutomataBindingExecution (bindingsTerm bindingsOptionTerm)
open RelationPremiseExecution (providerEnv providerRowsTerm premisesTerm bindingResultsTerm namesTerm VariableRuleView variableRuleView)

def pathTerm (path : List Nat) : Term := encodeList .natural path
def traceTerm (trace : List Nat × Bindings) : Term :=
  .application "EqPremises" [pathTerm trace.1, bindingsTerm trace.2]
def tracesTerm (traces : List (List Nat × Bindings)) : Term := encodeList traceTerm traces
def orientationTerm : EquationOrientation → Term
  | .forward => .symbol "EqForward"
  | .reverse => .symbol "EqReverse"
def receiptTerm (receipt : Receipt) : Term :=
  .application "EqInstance" [.natural receipt.equationIndex, orientationTerm receipt.orientation,
    bindingsTerm receipt.initialBindings, pathTerm receipt.choices, bindingsTerm receipt.finalBindings,
    InferenceCettaWire.encodePattern receipt.target]
def receiptsTerm (receipts : List Receipt) : Term := encodeList receiptTerm receipts

/-- Administrative fields are retained as supplied data. Operational admission
comes from exact `EquationProgram` readback, not this five-field projection. -/
def equationTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plan : RulePlan) : Term :=
  .application "Equation" [.string plan.name, contexts (equationOfPlan plan), premisesTerm plan.premises,
    InferenceCettaWire.encodePattern plan.left.erase, InferenceCettaWire.encodePattern plan.right.erase]
def equationsTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan) : Term :=
  encodeList (equationTerm contexts) plans

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev bindingsValue (bindings : Bindings) : Atom := encoded (bindingsTerm bindings)
private abbrev tracesValue (traces : List (List Nat × Bindings)) : Atom := encoded (tracesTerm traces)
private abbrev rowsValue (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Atom :=
  encoded (providerRowsTerm rows)
private abbrev premisesValue (plans : List PremisePlan) : Atom := encoded (premisesTerm plans)
private abbrev resultsValue (results : List Bindings) : Atom := encoded (bindingResultsTerm results)

private abbrev variablePremisesValue (plans : List VariablePremisePlan) : Atom :=
  encoded (RelationPremiseExecution.variablePremisesTerm plans)

/-- A source-shape specialization of the existing canonical trace fold. -/
def variablePremiseTraces (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (plans : List VariablePremisePlan) : Bindings → List (List Nat × Bindings) :=
  premiseTraces relations language (plans.map VariablePremisePlan.toPlan)

@[simp] theorem variablePremiseTraces_nil (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (seed : Bindings) : variablePremiseTraces relations language [] seed = [([], seed)] := rfl

@[simp] theorem variablePremiseTraces_cons (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (plan : VariablePremisePlan) (plans : List VariablePremisePlan) (seed : Bindings) :
    variablePremiseTraces relations language (plan :: plans) seed =
      traceBranches 0 (plan.run relations language seed) (variablePremiseTraces relations language plans) := by
  simp only [variablePremiseTraces, List.map_cons, premiseTraces, VariablePremisePlan.toPlan_run]

/-- Replay uses the same general checker after exact variable-source retraction. -/
def replayVariablePremises? (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (plans : List VariablePremisePlan) : Bindings → List Nat → Option Bindings :=
  replayPremises? relations language (plans.map VariablePremisePlan.toPlan)

@[simp] theorem replayVariablePremises?_nil (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (seed : Bindings) (path : List Nat) :
    replayVariablePremises? relations language [] seed path = (match path with | [] => some seed | _ => none) := by
  cases path <;> rfl

@[simp] theorem replayVariablePremises?_cons (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (language : LanguageDef) (plan : VariablePremisePlan) (plans : List VariablePremisePlan)
    (seed : Bindings) (path : List Nat) :
    replayVariablePremises? relations language (plan :: plans) seed path =
      (match path with
       | [] => none
       | index :: rest => (plan.run relations language seed)[index]?.bind
           (fun next => replayVariablePremises? relations language plans next rest)) := by
  cases path <;> simp only [replayVariablePremises?, List.map_cons, replayPremises?,
    VariablePremisePlan.toPlan_run, Option.bind_eq_bind]

private inductive Helper where
  | prefix | premises | branches | replay | instances | sides | row | rootAt | root | validate | validateSides
private def Helper.head : Helper → String
  | .prefix => "gslt:equation:trace-prefix"
  | .premises => "gslt:equation:premise-traces"
  | .branches => "gslt:equation:premise-branches"
  | .replay => "gslt:equation:replay-premises"
  | .instances => "gslt:equation:instance-results"
  | .sides => "gslt:equation:apply-sides"
  | .row => "gslt:equation:apply-row"
  | .rootAt => "gslt:equation:root-at"
  | .root => "gslt:equation:root"
  | .validate => "gslt:equation:validate"
  | .validateSides => "gslt:equation:validate-sides"
private def Helper.names : Helper → List String
  | .prefix => ["index", "traces"]
  | .premises => ["premises", "rows", "seed"]
  | .branches => ["premises", "rows", "choices", "index"]
  | .replay => ["premises", "rows", "seed", "path"]
  | .instances => ["index", "orientation", "initial", "right", "traces"]
  | .sides => ["index", "orientation", "premises", "left", "right", "rows", "subject"]
  | .row => ["index", "orientation", "equation", "rows", "subject"]
  | .rootAt => ["equations", "rows", "subject", "index"]
  | .root => ["equations", "rows", "subject"]
  | .validate => ["equations", "rows", "subject", "receipt"]
  | .validateSides => ["premises", "left", "right", "rows", "subject", "initial", "path", "completed", "target"]
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_equations (helper : Helper) :
    equations helper.head = [equation helper] := by
  cases helper <;> rfl

private theorem helper_arguments (helper : Helper) :
    (equation helper).arguments = helper.names.map Atom.var := by
  cases helper <;> rfl

private theorem helper_names_nodup (helper : Helper) : helper.names.Nodup := by
  cases helper <;> decide

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values = [.evaluate (environment helper values) (equation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [helper_equations]
  have selected := PureData.match_variable_values helper.names values [] (helper_names_nodup helper) length
    (by intro name _; rfl)
  simp only [List.append_nil] at selected
  simp [helper_arguments, selected, environment]

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
        .expression (.symbol "->" ::
          (List.replicate helper.names.length (.symbol "Atom") ++ [.symbol "%Undefined%"]))]
          ∈ program.declarations := by
      cases helper <;> decide +kernel
    apply (argumentIsRaw_iff_declaredAtom program helper.head index
      (by cases helper <;> decide)).mpr
    refine ⟨_, declared, ?_⟩
    rw [List.getElem?_append_left (by simpa using bounded)]
    simp [bounded]
  · rw [captured]
    exact helper_clause helper values length

private theorem lcons_template (head tail : String) :
    PureData.Template program (a "LCons" [v head, v tail]) := by
  apply PureData.Template.constructor _ _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private def prefixCons : Atom :=
  a "let" [v "tail", a "gslt:equation:trace-prefix" [v "index", v "rest"],
    a "LCons" [a "EqPremises" [a "LCons" [v "index", v "path"], v "bindings"], v "tail"]]
private def prefixCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "EqPremises" [v "path", v "bindings"], v "rest"], prefixCons)]

private theorem prefix_shape : (equation .prefix).body =
    a "case" [v "traces", .expression (prefixCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem prefix_template : PureData.Template program
    (a "LCons" [a "EqPremises" [a "LCons" [v "index", v "path"], v "bindings"], v "tail"]) := by
  apply PureData.Template.constructor _ _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor _ _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact lcons_template _ _
    · exact .captured _
  · exact .captured _

private theorem prefix_body_returns (state : State) (index : Nat) (traces : List (List Nat × Bindings)) :
    PureReturns program (environment .prefix [number index, tracesValue traces]) state
      (equation .prefix).body state
      (tracesValue (traces.map fun trace => (index :: trace.1, trace.2))) := by
  induction traces with
  | nil =>
      rw [prefix_shape]
      let caller := environment .prefix [number index, tracesValue []]
      apply case_returns program caller caller state state state (v "traces") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ prefixCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, tracesValue, tracesTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "traces"
      · simp [prefixCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons trace traces ih =>
      let caller := environment .prefix [number index, tracesValue (trace :: traces)]
      let selected := ("rest", tracesValue traces) :: ("bindings", bindingsValue trace.2) ::
        ("path", encoded (pathTerm trace.1)) :: caller
      let bound := ("tail", tracesValue (traces.map fun trace => (index :: trace.1, trace.2))) :: selected
      have continued := helper_call .prefix selected state [number index, tracesValue traces]
        [v "index", v "rest"] _ rfl
        (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
      rw [prefix_shape]
      apply case_returns program caller selected state state state (v "traces")
        (tracesValue (trace :: traces)) prefixCons
        (tracesValue ((trace :: traces).map fun trace => (index :: trace.1, trace.2))) _ prefixCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "traces"
      · simp [prefixCases, tracesValue, encoded, tracesTerm, traceTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold prefixCons
        apply let_returns program selected bound state state state (v "tail") _ _ _ _ continued _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, caller, environment, Helper.names]
        · simpa [bound, selected, caller, environment, Helper.names, tracesValue, encoded, tracesTerm, traceTerm,
            pathTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
            applySubst.applySubstList, Subst.lookup] using
              PureData.template_return program bound state _ prefix_template

theorem trace_prefix_captured_returns (caller : Subst) (state : State) (index : Nat)
    (traces : List (List Nat × Bindings)) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [number index, tracesValue traces]) :
    PureReturns program caller state (a "gslt:equation:trace-prefix" [one, two]) state
      (tracesValue (traces.map fun trace => (index :: trace.1, trace.2))) :=
  helper_call .prefix caller state _ _ _ rfl captured (prefix_body_returns state index traces)

private theorem traces_as_list (traces : List (List Nat × Bindings)) :
    tracesValue traces = MatchAutomataSourceExecution.listValue (traces.map traceTerm) := by
  simp only [tracesValue, tracesTerm, MatchAutomataSourceExecution.listValue, encodeList_map,
    Function.comp_def, id_eq]

private theorem append_traces_returns (caller : Subst) (state : State)
    (left right : List (List Nat × Bindings)) (first second : String)
    (captured : [v first, v second].map (applySubst caller) = [tracesValue left, tracesValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v first, v second]) state (tracesValue (left ++ right)) := by
  apply retained_captured_returns (by simp only [codeWithin, atomsWithin, expressionHeadWithin]; decide +kernel)
  apply RuleExecutionProgram.automata_captured_returns (by simp only [codeWithin, atomsWithin, expressionHeadWithin]; decide +kernel)
  simpa only [traces_as_list, List.map_append] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map traceTerm) (right.map traceTerm) (v first) (v second) (by simpa only [← traces_as_list] using captured)

private theorem successor_returns (caller : Subst) (state : State) (index : Nat)
    (captured : applySubst caller (v "index") = number index) :
    PureReturns program caller state (a "+" [v "index", number 1]) state (number (index + 1)) := by
  apply native_binary_call_returns program caller state state state state "+" (v "index") (number 1)
    (number index) (number 1) (number (index + 1))
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state "index"
  · exact grounded_returns program caller state (.int 1)
  · change (Except.ok (state, [Atom.grounded (.int ((index : Int) + 1))]) : Effects.Result) =
      Except.ok (state, [.grounded (.int ((index + 1 : Nat) : Int))])
    simp

private def branchesPairs : List (Atom × Atom) :=
  [(v "continued", a "gslt:equation:premise-traces" [v "premises", v "rows", v "seed"]),
   (v "head", a "gslt:equation:trace-prefix" [v "index", v "continued"]),
   (v "next", a "+" [v "index", number 1]),
   (v "tail", a "gslt:equation:premise-branches" [v "premises", v "rows", v "rest", v "next"])]
private def branchesCons : Atom :=
  a "let*" [.expression (branchesPairs.map fun pair => .expression [pair.1, pair.2]),
    a "gslt:automata:append" [v "head", v "tail"]]
private def branchesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "seed", v "rest"], branchesCons)]
private theorem branches_shape : (equation .branches).body =
    a "case" [v "choices", .expression (branchesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem branches_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List VariablePremisePlan)
    (continued : ∀ seed, PureReturns program (environment .premises [variablePremisesValue plans, rowsValue rows, bindingsValue seed])
      state (equation .premises).body state (tracesValue (variablePremiseTraces (providerEnv rows) language plans seed)))
    (choices : List Bindings) (index : Nat) :
    PureReturns program (environment .branches [variablePremisesValue plans, rowsValue rows, resultsValue choices, number index])
      state (equation .branches).body state
      (tracesValue (traceBranches index choices (variablePremiseTraces (providerEnv rows) language plans))) := by
  induction choices generalizing index with
  | nil =>
      rw [branches_shape]
      let caller := environment .branches [variablePremisesValue plans, rowsValue rows, resultsValue [], number index]
      apply case_returns program caller caller state state state (v "choices") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ branchesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, resultsValue, bindingResultsTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "choices"
      · simp [branchesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons seed choices ih =>
      let caller := environment .branches [variablePremisesValue plans, rowsValue rows, resultsValue (seed :: choices), number index]
      let selected := ("rest", resultsValue choices) :: ("seed", bindingsValue seed) :: caller
      let headTraces := variablePremiseTraces (providerEnv rows) language plans seed
      let prefixed := headTraces.map fun trace => (index :: trace.1, trace.2)
      let later := traceBranches (index + 1) choices (variablePremiseTraces (providerEnv rows) language plans)
      let continuedBound := ("continued", tracesValue headTraces) :: selected
      let headBound := ("head", tracesValue prefixed) :: continuedBound
      let nextBound := ("next", number (index + 1)) :: headBound
      let tailBound := ("tail", tracesValue later) :: nextBound
      have headReturned := helper_call .premises selected state
        [variablePremisesValue plans, rowsValue rows, bindingsValue seed] [v "premises", v "rows", v "seed"] _ rfl
        (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]) (continued seed)
      have prefixReturned := trace_prefix_captured_returns continuedBound state index headTraces
        (v "index") (v "continued")
        (by simp [continuedBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have nextReturned := successor_returns headBound state index
        (by simp [headBound, continuedBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have tailReturned := helper_call .branches nextBound state
        [variablePremisesValue plans, rowsValue rows, resultsValue choices, number (index + 1)]
        [v "premises", v "rows", v "rest", v "next"] _ rfl
        (by simp [nextBound, headBound, continuedBound, selected, caller, environment, Helper.names,
          applySubst, Subst.lookup]) (ih (index + 1))
      have computed : PureData.BindingsReturn program selected state branchesPairs tailBound state := by
        apply PureData.BindingsReturn.cons (bound := continuedBound) headReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, continuedBound, selected, caller, environment, Helper.names, headTraces]
        apply PureData.BindingsReturn.cons (bound := headBound) prefixReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, continuedBound, selected, caller, environment, Helper.names, prefixed]
        apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, nextBound, headBound, continuedBound, selected, caller, environment, Helper.names]
        apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, nextBound, headBound,
            continuedBound, selected, caller, environment, Helper.names, later]
        exact .nil _ _
      rw [branches_shape]
      apply case_returns program caller selected state state state (v "choices") (resultsValue (seed :: choices))
        branchesCons _ _ branchesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "choices"
      · simp [branchesCases, resultsValue, bindingResultsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold branchesCons
        apply PureData.let_bindings_return computed
        have appended := append_traces_returns tailBound state prefixed later "head" "tail"
          (by simp [tailBound, nextBound, headBound, applySubst, Subst.lookup])
        simpa only [traceBranches, List.zipIdx_cons, List.flatMap_cons, prefixed, headTraces, later] using appended

private def premisesPairs : List (Atom × Atom) :=
  [(v "names", a "gslt:rule:argument-names" [v "arguments"]),
   (v "choices", a "gslt:rule:relation-query" [v "relation", v "names", v "rows", v "seed"])]
private def premisesCons : Atom :=
  a "let*" [.expression (premisesPairs.map fun pair => .expression [pair.1, pair.2]),
    a "gslt:equation:premise-branches" [v "rest", v "rows", v "choices", number 0]]
private def premisesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "LCons" [a "EqPremises" [.symbol "LNil", v "seed"], .symbol "LNil"]),
   (a "LCons" [a "RelationQuery" [v "relation", v "arguments"], v "rest"], premisesCons)]
private theorem premises_shape : (equation .premises).body =
    a "case" [v "premises", .expression (premisesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem premises_nil_template : PureData.Template program
    (a "LCons" [a "EqPremises" [.symbol "LNil", v "seed"], .symbol "LNil"]) := by
  apply PureData.Template.constructor _ _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor _ _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .symbol _
    · exact .captured _
  · exact .symbol _

private theorem premises_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List VariablePremisePlan) (seed : Bindings) :
    PureReturns program (environment .premises [variablePremisesValue plans, rowsValue rows, bindingsValue seed])
      state (equation .premises).body state (tracesValue (variablePremiseTraces (providerEnv rows) language plans seed)) := by
  induction plans generalizing seed with
  | nil =>
      let caller := environment .premises [variablePremisesValue [], rowsValue rows, bindingsValue seed]
      rw [premises_shape]
      apply case_returns program caller caller state state state (v "premises") (.symbol "LNil")
        (a "LCons" [a "EqPremises" [.symbol "LNil", v "seed"], .symbol "LNil"]) _ _
        premisesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, variablePremisesValue, RelationPremiseExecution.variablePremisesTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "premises"
      · simp [premisesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [caller, environment, Helper.names, variablePremiseTraces_nil, tracesValue, tracesTerm, traceTerm, pathTerm,
          encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst,
          applySubst.applySubstList, Subst.lookup] using PureData.template_return program caller state _ premises_nil_template
  | cons plan plans ih =>
      let caller := environment .premises [variablePremisesValue (plan :: plans), rowsValue rows, bindingsValue seed]
      let selected := ("rest", variablePremisesValue plans) ::
        ("arguments", encoded (InferenceCettaWire.encodePatterns (plan.arguments.map Pattern.fvar))) ::
        ("relation", encoded (.string plan.relation)) :: caller
      let namesBound := ("names", encoded (namesTerm plan.arguments)) :: selected
      let choices := plan.run (providerEnv rows) language seed
      let choicesBound := ("choices", resultsValue choices) :: namesBound
      have namesReturned : PureReturns program selected state (a "gslt:rule:argument-names" [v "arguments"])
          state (encoded (namesTerm plan.arguments)) := by
        apply retained_captured_returns (by decide +kernel)
        exact RelationPremiseExecution.argument_names_captured_returns selected state plan.arguments _
          (by simp [selected, applySubst, Subst.lookup])
      have choicesReturned : PureReturns program namesBound state
          (a "gslt:rule:relation-query" [v "relation", v "names", v "rows", v "seed"]) state (resultsValue choices) := by
        apply retained_captured_returns (by decide +kernel)
        exact RelationPremiseExecution.relation_query_captured_returns namesBound state language rows plan seed _ _ _ _
          (by simp [namesBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have computed : PureData.BindingsReturn program selected state premisesPairs choicesBound state := by
        apply PureData.BindingsReturn.cons (bound := namesBound) namesReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, namesBound, selected, caller, environment, Helper.names]
        apply PureData.BindingsReturn.cons (bound := choicesBound) choicesReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, namesBound, selected, caller, environment, Helper.names]
        exact .nil _ _
      rw [premises_shape]
      apply case_returns program caller selected state state state (v "premises") (variablePremisesValue (plan :: plans))
        premisesCons _ _ premisesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "premises"
      · simp [premisesCases, variablePremisesValue, RelationPremiseExecution.variablePremisesTerm, RelationPremiseExecution.variablePremiseTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold premisesCons
        apply PureData.let_bindings_return computed
        simpa only [variablePremiseTraces_cons, choices, Helper.head] using helper_call .branches choicesBound state
          [variablePremisesValue plans, rowsValue rows, resultsValue choices, number 0]
          [v "rest", v "rows", v "choices", number 0] _ rfl
          (by simp [choicesBound, namesBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          (branches_body_returns state language rows plans ih choices 0)

/-- The actual source returns the canonical ordered premise fold decorated
with each completed query alternative's physical ordinal. -/
theorem variable_premise_traces_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List VariablePremisePlan) (seed : Bindings)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [variablePremisesValue plans, rowsValue rows, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:equation:premise-traces" [one, two, three]) state
      (tracesValue (variablePremiseTraces (providerEnv rows) language plans seed)) :=
  helper_call .premises caller state _ _ _ rfl captured (premises_body_returns state language rows plans seed)

private theorem results_as_list (values : List Bindings) :
    resultsValue values = MatchAutomataSourceExecution.listValue (values.map bindingsTerm) := by
  simp only [resultsValue, bindingResultsTerm, MatchAutomataSourceExecution.listValue, encodeList_map,
    Function.comp_def, id_eq]

private theorem lookup_bindings_returns (caller : Subst) (state : State) (index : Nat)
    (values : List Bindings) (first second : String)
    (captured : [v first, v second].map (applySubst caller) = [number index, resultsValue values]) :
    PureReturns program caller state (a "gslt:rule:row-at" [v first, v second]) state
      (encoded (bindingsOptionTerm values[index]?)) := by
  apply retained_captured_returns
    (by simp only [codeWithin, atomsWithin, expressionHeadWithin]; decide +kernel)
  have returned := RootRuleExecution.Matched.row_at_captured_returns caller state index (values.map bindingsTerm)
    (v first) (v second) (by simpa only [← results_as_list] using captured)
  cases chosen : values[index]? with
  | none =>
      simp only [List.getElem?_map, chosen, Option.map_none] at returned
      exact returned
  | some seed =>
      simp only [List.getElem?_map, chosen, Option.map_some] at returned
      exact returned

private def replayLookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"),
   (a "Some" [v "next"], a "gslt:equation:replay-premises" [v "rest", v "rows", v "next", v "remaining"])]
private def replayLookup : Atom :=
  a "case" [a "gslt:rule:row-at" [v "index", v "choices"],
    .expression (replayLookupCases.map fun row => .expression [row.1, row.2])]
private def replayCons : Atom :=
  a "let*" [.expression (premisesPairs.map fun pair => .expression [pair.1, pair.2]), replayLookup]
private def replayCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", .symbol "LNil"], a "Some" [v "seed"]),
   (.expression [a "LCons" [a "RelationQuery" [v "relation", v "arguments"], v "rest"],
      a "LCons" [v "index", v "remaining"]], replayCons),
   (v "bad", .symbol "None")]
private theorem replay_shape : (equation .replay).body =
    a "case" [.expression [v "premises", v "path"],
      .expression (replayCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem replay_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List VariablePremisePlan) (seed : Bindings) (path : List Nat) :
    PureReturns program (environment .replay [variablePremisesValue plans, rowsValue rows, bindingsValue seed, encoded (pathTerm path)])
      state (equation .replay).body state
      (encoded (bindingsOptionTerm (replayVariablePremises? (providerEnv rows) language plans seed path))) := by
  induction plans generalizing seed path with
  | nil =>
      cases path with
      | nil =>
          let caller := environment .replay [variablePremisesValue [], rowsValue rows, bindingsValue seed, encoded (pathTerm [])]
          rw [replay_shape]
          apply case_returns program caller caller state state state (.expression [v "premises", v "path"])
            (.expression [.symbol "LNil", .symbol "LNil"]) (a "Some" [v "seed"])
            (encoded (bindingsOptionTerm (some seed))) _ replayCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, variablePremisesValue, RelationPremiseExecution.variablePremisesTerm, pathTerm, encodeList,
              CettaWireAtom.encode, applySubst, Subst.lookup] using tuple_variables_return program caller state ["premises", "path"]
          · simp [replayCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom]
          · simpa [caller, environment, Helper.names, bindingsOptionTerm, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, applySubst, Subst.lookup] using
                unary_constructor_returns program caller state "Some" "seed" (by decide +kernel) (by decide)
      | cons index path =>
          let caller := environment .replay [variablePremisesValue [], rowsValue rows, bindingsValue seed, encoded (pathTerm (index :: path))]
          let value : Atom := .expression [.symbol "LNil", encoded (pathTerm (index :: path))]
          let selected := ("bad", value) :: caller
          rw [replay_shape]
          apply case_returns program caller selected state state state (.expression [v "premises", v "path"])
            value (.symbol "None") (.symbol "None") _ replayCases (read_cases_encoded _) _ _ _
          · simpa [value, caller, environment, Helper.names, variablePremisesValue, RelationPremiseExecution.variablePremisesTerm, pathTerm, encodeList,
              CettaWireAtom.encode, applySubst, Subst.lookup] using tuple_variables_return program caller state ["premises", "path"]
          · simp [replayCases, value, selected, caller, environment, Helper.names, pathTerm,
              encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · exact symbol_returns program selected state "None"
  | cons plan plans ih =>
      cases path with
      | nil =>
          let caller := environment .replay [variablePremisesValue (plan :: plans), rowsValue rows, bindingsValue seed, encoded (pathTerm [])]
          let value : Atom := .expression [variablePremisesValue (plan :: plans), .symbol "LNil"]
          let selected := ("bad", value) :: caller
          rw [replay_shape]
          apply case_returns program caller selected state state state (.expression [v "premises", v "path"])
            value (.symbol "None") (.symbol "None") _ replayCases (read_cases_encoded _) _ _ _
          · simpa [value, caller, environment, Helper.names, pathTerm, encodeList,
              CettaWireAtom.encode, applySubst, Subst.lookup] using tuple_variables_return program caller state ["premises", "path"]
          · simp [replayCases, value, selected, caller, environment, Helper.names, variablePremisesValue, RelationPremiseExecution.variablePremisesTerm,
              RelationPremiseExecution.variablePremiseTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup]
          · exact symbol_returns program selected state "None"
      | cons index path =>
          let caller := environment .replay [variablePremisesValue (plan :: plans), rowsValue rows, bindingsValue seed,
            encoded (pathTerm (index :: path))]
          let selected := ("remaining", encoded (pathTerm path)) :: ("index", number index) ::
            ("rest", variablePremisesValue plans) ::
            ("arguments", encoded (InferenceCettaWire.encodePatterns (plan.arguments.map Pattern.fvar))) ::
            ("relation", encoded (.string plan.relation)) :: caller
          let namesBound := ("names", encoded (namesTerm plan.arguments)) :: selected
          let choices := plan.run (providerEnv rows) language seed
          let choicesBound := ("choices", resultsValue choices) :: namesBound
          have namesReturned : PureReturns program selected state (a "gslt:rule:argument-names" [v "arguments"])
              state (encoded (namesTerm plan.arguments)) := by
            apply retained_captured_returns (by decide +kernel)
            exact RelationPremiseExecution.argument_names_captured_returns selected state plan.arguments _
              (by simp [selected, applySubst, Subst.lookup])
          have choicesReturned : PureReturns program namesBound state
              (a "gslt:rule:relation-query" [v "relation", v "names", v "rows", v "seed"]) state (resultsValue choices) := by
            apply retained_captured_returns (by decide +kernel)
            exact RelationPremiseExecution.relation_query_captured_returns namesBound state language rows plan seed _ _ _ _
              (by simp [namesBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          have computed : PureData.BindingsReturn program selected state premisesPairs choicesBound state := by
            apply PureData.BindingsReturn.cons (bound := namesBound) namesReturned
            · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, namesBound, selected, caller, environment, Helper.names]
            apply PureData.BindingsReturn.cons (bound := choicesBound) choicesReturned
            · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, namesBound, selected, caller, environment, Helper.names]
            exact .nil _ _
          have lookup := lookup_bindings_returns choicesBound state index choices "index" "choices"
            (by simp [choicesBound, namesBound, selected, applySubst, Subst.lookup])
          rw [replay_shape]
          apply case_returns program caller selected state state state (.expression [v "premises", v "path"])
            (.expression [variablePremisesValue (plan :: plans), encoded (pathTerm (index :: path))])
            replayCons _ _ replayCases (read_cases_encoded _) _ _ _
          · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
              tuple_variables_return program caller state ["premises", "path"]
          · simp [replayCases, selected, caller, environment, Helper.names, variablePremisesValue, RelationPremiseExecution.variablePremisesTerm,
              RelationPremiseExecution.variablePremiseTerm, pathTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · unfold replayCons
            apply PureData.let_bindings_return computed
            cases chosen : choices[index]? with
            | none =>
                have outcome : replayVariablePremises? (providerEnv rows) language (plan :: plans) seed (index :: path) = none := by
                  simp only [replayVariablePremises?_cons, choices, chosen, Option.bind_none]
                rw [outcome]
                unfold replayLookup
                apply case_returns program choicesBound choicesBound state state state _ (.symbol "None")
                  (.symbol "None") (.symbol "None") _ replayLookupCases (read_cases_encoded _) _ _ _
                · simpa [chosen, bindingsOptionTerm, encoded, CettaWireAtom.encode] using lookup
                · simp [replayLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                · exact symbol_returns program choicesBound state "None"
            | some next =>
                let selectedNext := ("next", bindingsValue next) :: choicesBound
                have outcome : replayVariablePremises? (providerEnv rows) language (plan :: plans) seed (index :: path) =
                    replayVariablePremises? (providerEnv rows) language plans next path := by
                  simp only [replayVariablePremises?_cons, choices, chosen, Option.bind_some]
                rw [outcome]
                unfold replayLookup
                apply case_returns program choicesBound selectedNext state state state _
                  (a "Some" [bindingsValue next])
                  (a "gslt:equation:replay-premises" [v "rest", v "rows", v "next", v "remaining"]) _ _
                  replayLookupCases (read_cases_encoded _) _ _ _
                · simpa [chosen, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookup
                · simp [replayLookupCases, selectedNext, SpaceSemantics.selectCase,
                    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                    choicesBound, namesBound, selected, caller, environment, Helper.names]
                · exact helper_call .replay selectedNext state
                    [variablePremisesValue plans, rowsValue rows, bindingsValue next, encoded (pathTerm path)]
                    [v "rest", v "rows", v "next", v "remaining"] _ rfl
                    (by simp [selectedNext, choicesBound, namesBound, selected, caller, environment, Helper.names,
                      applySubst, Subst.lookup]) (ih next path)

/-- The retained source replays each canonical query alternative, refusing
missing, future and extra branch ordinals. -/
theorem replay_variable_premises_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List VariablePremisePlan)
    (seed : Bindings) (path : List Nat) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [variablePremisesValue plans, rowsValue rows, bindingsValue seed, encoded (pathTerm path)]) :
    PureReturns program caller state (a "gslt:equation:replay-premises" [one, two, three, four]) state
      (encoded (bindingsOptionTerm (replayVariablePremises? (providerEnv rows) language plans seed path))) :=
  helper_call .replay caller state _ _ _ rfl captured (replay_body_returns state language rows plans seed path)

/-- Checked general plans execute through their earned names-only source view. -/
theorem premise_traces_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (view : {specialized : List VariablePremisePlan // specialized.map VariablePremisePlan.toPlan = plans})
    (seed : Bindings) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [premisesValue plans, rowsValue rows, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:equation:premise-traces" [one, two, three]) state
      (tracesValue (premiseTraces (providerEnv rows) language plans seed)) := by
  have wire : variablePremisesValue view.val = premisesValue plans := by
    simpa only [variablePremisesValue, premisesValue, view.property] using
      congrArg encoded (RelationPremiseExecution.variablePremisesTerm_toPlan view.val).symm
  have returned := variable_premise_traces_captured_returns caller state language rows view.val seed one two three
    (by simpa only [wire] using captured)
  simpa only [variablePremiseTraces, view.property] using returned

theorem replay_premises_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (view : {specialized : List VariablePremisePlan // specialized.map VariablePremisePlan.toPlan = plans})
    (seed : Bindings) (path : List Nat) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [premisesValue plans, rowsValue rows, bindingsValue seed, encoded (pathTerm path)]) :
    PureReturns program caller state (a "gslt:equation:replay-premises" [one, two, three, four]) state
      (encoded (bindingsOptionTerm (replayPremises? (providerEnv rows) language plans seed path))) := by
  have wire : variablePremisesValue view.val = premisesValue plans := by
    simpa only [variablePremisesValue, premisesValue, view.property] using
      congrArg encoded (RelationPremiseExecution.variablePremisesTerm_toPlan view.val).symm
  have returned := replay_variable_premises_captured_returns caller state language rows view.val seed path one two three four
    (by simpa only [wire] using captured)
  simpa only [replayVariablePremises?, view.property] using returned

def instanceReceipts (index : Nat) (orientation : EquationOrientation) (initial : Bindings)
    (right : PatternPlan) (traces : List (List Nat × Bindings)) : List Receipt :=
  traces.map fun trace => ⟨index, orientation, initial, trace.1, trace.2, right.instantiate trace.2⟩

private def instancesPairs : List (Atom × Atom) :=
  [(v "target", a "gslt:rule:instantiate" [v "right", v "completed"]),
   (v "tail", a "gslt:equation:instance-results" [v "index", v "orientation", v "initial", v "right", v "rest"])]
private def instancesResult : Atom :=
  a "LCons" [a "EqInstance" [v "index", v "orientation", v "initial", v "path", v "completed", v "target"], v "tail"]
private def instancesCons : Atom :=
  a "let*" [.expression (instancesPairs.map fun pair => .expression [pair.1, pair.2]), instancesResult]
private def instancesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "EqPremises" [v "path", v "completed"], v "rest"], instancesCons)]
private theorem instances_shape : (equation .instances).body =
    a "case" [v "traces", .expression (instancesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem variables_template (head : String) (names : List String)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"]) :
    PureData.Template program (a head (names.map Atom.var)) := by
  apply PureData.Template.constructor _ _ inert ordinary
  intro argument member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact .captured name

private theorem instances_template : PureData.Template program instancesResult := by
  unfold instancesResult
  apply PureData.Template.constructor _ _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact variables_template "EqInstance" ["index", "orientation", "initial", "path", "completed", "target"]
      (by decide +kernel) (by decide)
  · exact .captured _

private theorem instances_body_returns (state : State) (index : Nat) (orientation : EquationOrientation)
    (initial : Bindings) (right : PatternPlan) (traces : List (List Nat × Bindings)) :
    PureReturns program (environment .instances [number index, encoded (orientationTerm orientation),
      bindingsValue initial, encoded (InferenceCettaWire.encodePattern right.erase), tracesValue traces])
      state (equation .instances).body state
      (encoded (receiptsTerm (instanceReceipts index orientation initial right traces))) := by
  induction traces with
  | nil =>
      let caller := environment .instances [number index, encoded (orientationTerm orientation),
        bindingsValue initial, encoded (InferenceCettaWire.encodePattern right.erase), tracesValue []]
      rw [instances_shape]
      apply case_returns program caller caller state state state (v "traces") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ instancesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, tracesValue, tracesTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "traces"
      · simp [instancesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons trace traces ih =>
      let caller := environment .instances [number index, encoded (orientationTerm orientation),
        bindingsValue initial, encoded (InferenceCettaWire.encodePattern right.erase), tracesValue (trace :: traces)]
      let selected := ("rest", tracesValue traces) :: ("completed", bindingsValue trace.2) ::
        ("path", encoded (pathTerm trace.1)) :: caller
      let targetBound := ("target", encoded (InferenceCettaWire.encodePattern (right.instantiate trace.2))) :: selected
      let tailBound := ("tail", encoded (receiptsTerm (instanceReceipts index orientation initial right traces))) :: targetBound
      have targetReturned : PureReturns program selected state (a "gslt:rule:instantiate" [v "right", v "completed"])
          state (encoded (InferenceCettaWire.encodePattern (right.instantiate trace.2))) := by
        apply retained_captured_returns (by decide +kernel)
        exact RuleInstantiationExecution.instantiate_captured_returns selected state trace.2 right _ _
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have tailReturned := helper_call .instances targetBound state
        [number index, encoded (orientationTerm orientation), bindingsValue initial,
          encoded (InferenceCettaWire.encodePattern right.erase), tracesValue traces]
        [v "index", v "orientation", v "initial", v "right", v "rest"] _ rfl
        (by simp [targetBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup]) ih
      have computed : PureData.BindingsReturn program selected state instancesPairs tailBound state := by
        apply PureData.BindingsReturn.cons (bound := targetBound) targetReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, targetBound, selected, caller, environment, Helper.names]
        apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, targetBound, selected, caller, environment, Helper.names]
        exact .nil _ _
      rw [instances_shape]
      apply case_returns program caller selected state state state (v "traces") (tracesValue (trace :: traces))
        instancesCons _ _ instancesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "traces"
      · simp [instancesCases, tracesValue, encoded, tracesTerm, traceTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold instancesCons
        apply PureData.let_bindings_return computed
        simpa [instancesResult, tailBound, targetBound, selected, caller, environment, Helper.names,
          instanceReceipts, receiptsTerm, receiptTerm, pathTerm, encodeList, encoded,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program tailBound state _ instances_template

/-- Instance construction retains both binding stages and every conditional
choice while invoking the existing canonical RHS instantiator. -/
theorem instance_results_captured_returns (caller : Subst) (state : State) (index : Nat)
    (orientation : EquationOrientation) (initial : Bindings) (right : PatternPlan)
    (traces : List (List Nat × Bindings)) (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [number index, encoded (orientationTerm orientation), bindingsValue initial,
        encoded (InferenceCettaWire.encodePattern right.erase), tracesValue traces]) :
    PureReturns program caller state (a "gslt:equation:instance-results" [one, two, three, four, five]) state
      (encoded (receiptsTerm (instanceReceipts index orientation initial right traces))) :=
  helper_call .instances caller state _ _ _ rfl captured (instances_body_returns state index orientation initial right traces)

private def sidesSome : Atom :=
  a "let" [v "traces", a "gslt:equation:premise-traces" [v "premises", v "rows", v "initial"],
    a "gslt:equation:instance-results" [v "index", v "orientation", v "initial", v "right", v "traces"]]
private def sidesCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "initial"], sidesSome)]
private theorem sides_shape : (equation .sides).body =
    a "case" [a "gslt:automata:bind" [v "left", v "subject"],
      .expression (sidesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem sides_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) :
    PureReturns program (environment .sides [number index, encoded (orientationTerm orientation),
      premisesValue plan.premises, encoded (InferenceCettaWire.encodePattern (orientedPlan plan orientation).left.erase),
      encoded (InferenceCettaWire.encodePattern (orientedPlan plan orientation).right.erase), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase)]) state (equation .sides).body state
      (encoded (receiptsTerm (rowReceipts (providerEnv rows) language index orientation plan subject.erase))) := by
  let caller := environment .sides [number index, encoded (orientationTerm orientation),
    premisesValue plan.premises, encoded (InferenceCettaWire.encodePattern (orientedPlan plan orientation).left.erase),
    encoded (InferenceCettaWire.encodePattern (orientedPlan plan orientation).right.erase), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase)]
  have matchedReturned : PureReturns program caller state (a "gslt:automata:bind" [v "left", v "subject"])
      state (encoded (bindingsOptionTerm (matchPattern (orientedPlan plan orientation).left.erase subject.erase).head?)) := by
    apply retained_captured_returns (by decide +kernel)
    apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
    exact MatchAutomataBindingExecution.bind_captured_returns caller state
      (orientedPlan plan orientation).left subject _
      (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
  rw [sides_shape]
  cases found : (matchPattern (orientedPlan plan orientation).left.erase subject.erase).head? with
  | none =>
      have matchList : (orientedPlan plan orientation).left.run subject.erase = [] := by
        rw [run_eq_matchPattern, ← MatchAutomataBindingExecution.bind_matches_singleton, found]
        rfl
      apply case_returns program caller caller state state state _ (.symbol "None") (.symbol "LNil") _ _
        sidesCases (read_cases_encoded _) _ _ _
      · simpa [found, bindingsOptionTerm, encoded, CettaWireAtom.encode] using matchedReturned
      · simp [sidesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [rowReceipts, matchList, receiptsTerm, encodeList, encoded, CettaWireAtom.encode] using
          symbol_returns program caller state "LNil"
  | some initial =>
      have matchList : (orientedPlan plan orientation).left.run subject.erase = [initial] := by
        rw [run_eq_matchPattern, ← MatchAutomataBindingExecution.bind_matches_singleton, found]
        rfl
      let selected := ("initial", bindingsValue initial) :: caller
      let traces := premiseTraces (providerEnv rows) language plan.premises initial
      let bound := ("traces", tracesValue traces) :: selected
      have tracesReturned := premise_traces_captured_returns selected state language rows plan.premises view initial
        (v "premises") (v "rows") (v "initial")
        (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have instancesReturned := instance_results_captured_returns bound state index orientation initial
        (orientedPlan plan orientation).right traces (v "index") (v "orientation") (v "initial") (v "right") (v "traces")
        (by simp [bound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      apply case_returns program caller selected state state state _ (a "Some" [bindingsValue initial]) sidesSome _ _
        sidesCases (read_cases_encoded _) _ _ _
      · simpa [found, bindingsOptionTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using matchedReturned
      · simp [sidesCases, selected, caller, environment, Helper.names, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold sidesSome
        apply let_returns program selected bound state state state (v "traces") _ _ _ _ tracesReturned _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, caller, environment, Helper.names, traces]
        · simpa [rowReceipts, matchList, instanceReceipts, traces] using instancesReturned

/-- The actual orientation-specific source applies the canonical matcher,
retains conditional witnesses and constructs the opposite authored side. -/
theorem apply_sides_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan)
    (one two three four five six seven : Atom)
    (captured : [one, two, three, four, five, six, seven].map (applySubst caller) =
      [number index, encoded (orientationTerm orientation), premisesValue plan.premises,
        encoded (InferenceCettaWire.encodePattern (orientedPlan plan orientation).left.erase),
        encoded (InferenceCettaWire.encodePattern (orientedPlan plan orientation).right.erase),
        rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:equation:apply-sides" [one, two, three, four, five, six, seven]) state
      (encoded (receiptsTerm (rowReceipts (providerEnv rows) language index orientation plan subject.erase))) :=
  helper_call .sides caller state _ _ _ rfl captured (sides_body_returns state language rows index orientation plan view subject)

private def rowCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "EqForward", a "Equation" [v "name", v "context", v "premises", v "left", v "right"]],
     a "gslt:equation:apply-sides" [v "index", v "orientation", v "premises", v "left", v "right", v "rows", v "subject"]),
   (.expression [.symbol "EqReverse", a "Equation" [v "name", v "context", v "premises", v "left", v "right"]],
     a "gslt:equation:apply-sides" [v "index", v "orientation", v "premises", v "right", v "left", v "rows", v "subject"]),
   (v "bad", .symbol "LNil")]
private theorem row_shape : (equation .row).body =
    a "case" [.expression [v "orientation", v "equation"],
      .expression (rowCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem row_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) :
    PureReturns program (environment .row [number index, encoded (orientationTerm orientation),
      encoded (equationTerm contexts plan), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase)])
      state (equation .row).body state
      (encoded (receiptsTerm (rowReceipts (providerEnv rows) language index orientation plan subject.erase))) := by
  let caller := environment .row [number index, encoded (orientationTerm orientation),
    encoded (equationTerm contexts plan), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase)]
  let selected := ("right", encoded (InferenceCettaWire.encodePattern plan.right.erase)) ::
    ("left", encoded (InferenceCettaWire.encodePattern plan.left.erase)) :: ("premises", premisesValue plan.premises) ::
    ("context", encoded (contexts (equationOfPlan plan))) :: ("name", encoded (.string plan.name)) :: caller
  rw [row_shape]
  cases orientation with
  | forward =>
      apply case_returns program caller selected state state state (.expression [v "orientation", v "equation"])
        (.expression [encoded (orientationTerm .forward), encoded (equationTerm contexts plan)])
        (a "gslt:equation:apply-sides" [v "index", v "orientation", v "premises", v "left", v "right", v "rows", v "subject"])
        _ _ rowCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          tuple_variables_return program caller state ["orientation", "equation"]
      · simp [rowCases, orientationTerm, equationTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · exact apply_sides_captured_returns selected state language rows index .forward plan view subject _ _ _ _ _ _ _
          (by simp [orientedPlan, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
  | reverse =>
      apply case_returns program caller selected state state state (.expression [v "orientation", v "equation"])
        (.expression [encoded (orientationTerm .reverse), encoded (equationTerm contexts plan)])
        (a "gslt:equation:apply-sides" [v "index", v "orientation", v "premises", v "right", v "left", v "rows", v "subject"])
        _ _ rowCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          tuple_variables_return program caller state ["orientation", "equation"]
      · simp [rowCases, orientationTerm, equationTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · exact apply_sides_captured_returns selected state language rows index .reverse plan view subject _ _ _ _ _ _ _
          (by simp [orientedPlan, selected, caller, environment, Helper.names, applySubst, Subst.lookup])

/-- Physical equation identity and orientation remain explicit in the emitted
receipt; source metadata is retained independently of pattern execution. -/
theorem apply_row_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (index : Nat)
    (orientation : EquationOrientation) (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [number index, encoded (orientationTerm orientation), encoded (equationTerm contexts plan),
        rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:equation:apply-row" [one, two, three, four, five]) state
      (encoded (receiptsTerm (rowReceipts (providerEnv rows) language index orientation plan subject.erase))) :=
  helper_call .row caller state _ _ _ rfl captured (row_body_returns state language rows contexts index orientation plan view subject)

private def rootReceiptsAt (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef)
    (next : Nat) (plans : List RulePlan) (source : Pattern) : List Receipt :=
  (plans.zipIdx next).flatMap fun row =>
    rowReceipts relations language row.2 .forward row.1 source ++
      rowReceipts relations language row.2 .reverse row.1 source

private theorem receipts_as_list (receipts : List Receipt) :
    encoded (receiptsTerm receipts) = MatchAutomataSourceExecution.listValue (receipts.map receiptTerm) := by
  simp only [receiptsTerm, MatchAutomataSourceExecution.listValue, encodeList_map, Function.comp_def, id_eq]

private theorem append_receipts_returns (caller : Subst) (state : State)
    (left right : List Receipt) (first second : String)
    (captured : [v first, v second].map (applySubst caller) =
      [encoded (receiptsTerm left), encoded (receiptsTerm right)]) :
    PureReturns program caller state (a "gslt:automata:append" [v first, v second]) state
      (encoded (receiptsTerm (left ++ right))) := by
  apply retained_captured_returns
    (by simp only [codeWithin, atomsWithin, expressionHeadWithin]; decide +kernel)
  apply RuleExecutionProgram.automata_captured_returns
    (by simp only [codeWithin, atomsWithin, expressionHeadWithin]; decide +kernel)
  simpa only [receipts_as_list, List.map_append] using
    MatchAutomataSourceExecution.append_captured_returns caller state (left.map receiptTerm) (right.map receiptTerm)
      (v first) (v second) (by simpa only [← receipts_as_list] using captured)

private def rootPairs : List (Atom × Atom) :=
  [(v "forward", a "gslt:equation:apply-row" [v "index", .symbol "EqForward", v "equation", v "rows", v "subject"]),
   (v "reverse", a "gslt:equation:apply-row" [v "index", .symbol "EqReverse", v "equation", v "rows", v "subject"]),
   (v "head", a "gslt:automata:append" [v "forward", v "reverse"]),
   (v "next", a "+" [v "index", number 1]),
   (v "tail", a "gslt:equation:root-at" [v "rest", v "rows", v "subject", v "next"])]
private def rootCons : Atom :=
  a "let*" [.expression (rootPairs.map fun pair => .expression [pair.1, pair.2]),
    a "gslt:automata:append" [v "head", v "tail"]]
private def rootCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "equation", v "rest"], rootCons)]
private theorem rootAt_shape : (equation .rootAt).body =
    a "case" [v "equations", .expression (rootCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem rootAt_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true)
    (subject : PatternPlan) (index : Nat) :
    PureReturns program (environment .rootAt [encoded (equationsTerm contexts plans), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase), number index]) state (equation .rootAt).body state
      (encoded (receiptsTerm (rootReceiptsAt (providerEnv rows) language index plans subject.erase))) := by
  induction plans generalizing index with
  | nil =>
      let caller := environment .rootAt [encoded (equationsTerm contexts []), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), number index]
      rw [rootAt_shape]
      apply case_returns program caller caller state state state (v "equations") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ rootCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, equationsTerm, encodeList, encoded, CettaWireAtom.encode,
          applySubst, Subst.lookup] using variable_returns program caller state "equations"
      · simp [rootCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons plan plans ih =>
      have tailViews : ∀ row ∈ plans, row.variablePremises?.isSome = true := by
        intro row member
        exact sourceViews row (by simp [member])
      have view := variableRuleView plan (sourceViews plan (by simp))
      let caller := environment .rootAt [encoded (equationsTerm contexts (plan :: plans)), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), number index]
      let selected := ("rest", encoded (equationsTerm contexts plans)) :: ("equation", encoded (equationTerm contexts plan)) :: caller
      let forward := rowReceipts (providerEnv rows) language index .forward plan subject.erase
      let reverse := rowReceipts (providerEnv rows) language index .reverse plan subject.erase
      let later := rootReceiptsAt (providerEnv rows) language (index + 1) plans subject.erase
      let forwardBound := ("forward", encoded (receiptsTerm forward)) :: selected
      let reverseBound := ("reverse", encoded (receiptsTerm reverse)) :: forwardBound
      let headBound := ("head", encoded (receiptsTerm (forward ++ reverse))) :: reverseBound
      let nextBound := ("next", number (index + 1)) :: headBound
      let tailBound := ("tail", encoded (receiptsTerm later)) :: nextBound
      have forwardReturned := apply_row_captured_returns selected state language rows contexts index .forward plan view subject
        (v "index") (.symbol "EqForward") (v "equation") (v "rows") (v "subject")
        (by simp [orientationTerm, encoded, CettaWireAtom.encode, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have reverseReturned := apply_row_captured_returns forwardBound state language rows contexts index .reverse plan view subject
        (v "index") (.symbol "EqReverse") (v "equation") (v "rows") (v "subject")
        (by simp [orientationTerm, encoded, CettaWireAtom.encode, forwardBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have headReturned := append_receipts_returns reverseBound state forward reverse "forward" "reverse"
        (by simp [reverseBound, forwardBound, applySubst, Subst.lookup])
      have nextReturned := successor_returns headBound state index
        (by simp [headBound, reverseBound, forwardBound, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
      have tailReturned := helper_call .rootAt nextBound state
        [encoded (equationsTerm contexts plans), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase), number (index + 1)]
        [v "rest", v "rows", v "subject", v "next"] _ rfl
        (by simp [nextBound, headBound, reverseBound, forwardBound, selected, caller, environment, Helper.names,
          applySubst, Subst.lookup]) (ih tailViews (index + 1))
      have computed : PureData.BindingsReturn program selected state rootPairs tailBound state := by
        apply PureData.BindingsReturn.cons (bound := forwardBound) forwardReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, forwardBound, selected, caller, environment, Helper.names, forward]
        apply PureData.BindingsReturn.cons (bound := reverseBound) reverseReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, reverseBound, forwardBound, selected, caller, environment, Helper.names, reverse]
        apply PureData.BindingsReturn.cons (bound := headBound) headReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, reverseBound, forwardBound, selected, caller, environment, Helper.names]
        apply PureData.BindingsReturn.cons (bound := nextBound) nextReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, nextBound, headBound, reverseBound,
            forwardBound, selected, caller, environment, Helper.names]
        apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, nextBound, headBound, reverseBound,
            forwardBound, selected, caller, environment, Helper.names, later]
        exact .nil _ _
      rw [rootAt_shape]
      apply case_returns program caller selected state state state (v "equations")
        (encoded (equationsTerm contexts (plan :: plans))) rootCons _ _ rootCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "equations"
      · simp [rootCases, equationsTerm, encodeList, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · unfold rootCons
        apply PureData.let_bindings_return computed
        have appended := append_receipts_returns tailBound state (forward ++ reverse) later "head" "tail"
          (by simp [tailBound, nextBound, headBound, applySubst, Subst.lookup])
        simpa only [rootReceiptsAt, List.zipIdx_cons, List.flatMap_cons, forward, reverse, later] using appended

private theorem root_shape : (equation .root).body =
    a "gslt:equation:root-at" [v "equations", v "rows", v "subject", number 0] := by
  decide +kernel

private theorem root_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) :
    PureReturns program (environment .root [encoded (equationsTerm contexts plans), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase)]) state (equation .root).body state
      (encoded (receiptsTerm (rootReceipts (providerEnv rows) language plans subject.erase))) := by
  let caller := environment .root [encoded (equationsTerm contexts plans), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase)]
  rw [root_shape]
  exact helper_call .rootAt caller state
    [encoded (equationsTerm contexts plans), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase), number 0]
    [v "equations", v "rows", v "subject", number 0] _ rfl
    (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
    (rootAt_body_returns state language rows contexts plans sourceViews subject 0)

/-- Completed source execution is the complete ordered canonical authored
instance frontier: equation order, forward/reverse order and premise witnesses. -/
theorem root_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan)
    (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (equationsTerm contexts plans), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase)]) :
    PureReturns program caller state (a "gslt:equation:root" [one, two, three]) state
      (encoded (receiptsTerm (rootReceipts (providerEnv rows) language plans subject.erase))) :=
  helper_call .root caller state _ _ _ rfl captured (root_body_returns state language rows contexts plans sourceViews subject)

private theorem bindings_equal_returns (caller : Subst) (state : State)
    (left right : Bindings) (first second : String)
    (one : applySubst caller (v first) = bindingsValue left)
    (two : applySubst caller (v second) = bindingsValue right) :
    PureReturns program caller state (a "==" [v first, v second]) state
      (Effects.boolean (decide (left = right))) := by
  have exactEquality : bindingsTerm left = bindingsTerm right ↔ left = right :=
    ⟨fun same => MatchAutomataBindingExecution.bindingsTerm_injective same, congrArg bindingsTerm⟩
  simpa only [exactEquality] using CettaWireAtom.equality_captured_returns program caller state
    (bindingsTerm left) (bindingsTerm right) first second one two

private theorem patterns_equal_returns (caller : Subst) (state : State)
    (left right : Pattern) (first second : String)
    (one : applySubst caller (v first) = encoded (InferenceCettaWire.encodePattern left))
    (two : applySubst caller (v second) = encoded (InferenceCettaWire.encodePattern right)) :
    PureReturns program caller state (a "==" [v first, v second]) state
      (Effects.boolean (decide (left = right))) := by
  have exactEquality : InferenceCettaWire.encodePattern left = InferenceCettaWire.encodePattern right ↔ left = right :=
    ⟨fun same => InferenceCettaWire.encodePattern_injective same, congrArg InferenceCettaWire.encodePattern⟩
  simpa only [exactEquality] using CettaWireAtom.equality_captured_returns program caller state
    (InferenceCettaWire.encodePattern left) (InferenceCettaWire.encodePattern right) first second one two

private def validateActual : Atom :=
  a "let" [v "actual", a "gslt:rule:instantiate" [v "right", v "final"],
    a "if" [a "==" [v "actual", v "target"], a "Some" [v "actual"], .symbol "None"]]
private def validateFinal : Atom :=
  a "if" [a "==" [v "final", v "completed"], validateActual, .symbol "None"]
private def validateReplayCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "final"], validateFinal)]
private def validateReplay : Atom :=
  a "case" [a "gslt:equation:replay-premises" [v "premises", v "rows", v "initial", v "path"],
    .expression (validateReplayCases.map fun row => .expression [row.1, row.2])]
private def validateMatched : Atom :=
  a "if" [a "==" [v "matched", v "initial"], validateReplay, .symbol "None"]
private def validateSidesCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "matched"], validateMatched)]
private theorem validateSides_shape : (equation .validateSides).body =
    a "case" [a "gslt:automata:bind" [v "left", v "subject"],
      .expression (validateSidesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem validateActual_returns (caller : Subst) (state : State)
    (right : PatternPlan) (final : Bindings) (target : Pattern)
    (freshActual : Subst.lookup caller "actual" = none)
    (rightCaptured : applySubst caller (v "right") = encoded (InferenceCettaWire.encodePattern right.erase))
    (finalCaptured : applySubst caller (v "final") = bindingsValue final)
    (targetCaptured : applySubst caller (v "target") = encoded (InferenceCettaWire.encodePattern target)) :
    PureReturns program caller state validateActual state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (if right.instantiate final = target then some (right.instantiate final) else none))) := by
  let actual := right.instantiate final
  let bound := ("actual", encoded (InferenceCettaWire.encodePattern actual)) :: caller
  have instantiated : PureReturns program caller state
      (a "gslt:rule:instantiate" [v "right", v "final"]) state
      (encoded (InferenceCettaWire.encodePattern actual)) := by
    apply retained_captured_returns (by decide +kernel)
    exact RuleInstantiationExecution.instantiate_captured_returns caller state final right _ _
      (by simp only [List.map_cons, List.map_nil, rightCaptured, finalCaptured])
  unfold validateActual
  apply let_returns program caller bound state state state _ _ _ _ _ instantiated _ _
  · simp [SpaceSemantics.matchValue, matchAtom, freshActual, bound]
  · have equality := patterns_equal_returns bound state actual target "actual" "target"
      (by simp [bound, applySubst, Subst.lookup])
      (by simpa [bound, applySubst, Subst.lookup] using targetCaptured)
    apply if_returns program bound state state state _ _ _ _ _ equality
    by_cases same : actual = target
    · simpa [same, actual, MatchAutomataBindingExecution.patternOptionTerm, encoded, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup, bound] using
        PureData.template_return program bound state _
          (variables_template "Some" ["actual"] (by decide +kernel) (by decide))
    · simpa [same, actual, Effects.boolean, MatchAutomataBindingExecution.patternOptionTerm, encoded, CettaWireAtom.encode] using
        symbol_returns program bound state "None"

private theorem validateSides_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) (initial completed : Bindings)
    (path : List Nat) (target : Pattern) :
    PureReturns program (environment .validateSides [premisesValue plan.premises,
      encoded (InferenceCettaWire.encodePattern plan.left.erase), encoded (InferenceCettaWire.encodePattern plan.right.erase),
      rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase), bindingsValue initial,
      encoded (pathTerm path), bindingsValue completed, encoded (InferenceCettaWire.encodePattern target)])
      state (equation .validateSides).body state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateRowReceipt? (providerEnv rows) language plan subject.erase initial path completed target))) := by
  let caller := environment .validateSides [premisesValue plan.premises,
    encoded (InferenceCettaWire.encodePattern plan.left.erase), encoded (InferenceCettaWire.encodePattern plan.right.erase),
    rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase), bindingsValue initial,
    encoded (pathTerm path), bindingsValue completed, encoded (InferenceCettaWire.encodePattern target)]
  have matchedReturned : PureReturns program caller state (a "gslt:automata:bind" [v "left", v "subject"])
      state (encoded (bindingsOptionTerm (matchPattern plan.left.erase subject.erase).head?)) := by
    apply retained_captured_returns (by decide +kernel)
    apply RuleExecutionProgram.automata_captured_returns (by decide +kernel)
    exact MatchAutomataBindingExecution.bind_captured_returns caller state plan.left subject _
      (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
  rw [validateSides_shape]
  cases found : (matchPattern plan.left.erase subject.erase).head? with
  | none =>
      have matchList : plan.left.run subject.erase = [] := by
        rw [run_eq_matchPattern, ← MatchAutomataBindingExecution.bind_matches_singleton, found]
        rfl
      apply case_returns program caller caller state state state _ (.symbol "None") (.symbol "None") _ _
        validateSidesCases (read_cases_encoded _) _ _ _
      · simpa [found, bindingsOptionTerm, encoded, CettaWireAtom.encode] using matchedReturned
      · simp [validateSidesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [validateRowReceipt?, matchList, guard, MatchAutomataBindingExecution.patternOptionTerm,
          encoded, CettaWireAtom.encode] using symbol_returns program caller state "None"
  | some matched =>
      have matchList : plan.left.run subject.erase = [matched] := by
        rw [run_eq_matchPattern, ← MatchAutomataBindingExecution.bind_matches_singleton, found]
        rfl
      let selected := ("matched", bindingsValue matched) :: caller
      apply case_returns program caller selected state state state _ (a "Some" [bindingsValue matched])
        validateMatched _ _ validateSidesCases (read_cases_encoded _) _ _ _
      · simpa [found, bindingsOptionTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using matchedReturned
      · simp [validateSidesCases, selected, caller, environment, Helper.names, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · have equality := bindings_equal_returns selected state matched initial "matched" "initial"
          (by simp [selected, applySubst, Subst.lookup])
          (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
        unfold validateMatched
        apply if_returns program selected state state state _ _ _ _ _ equality
        by_cases same : matched = initial
        · have accepted : initial ∈ plan.left.run subject.erase := by simp [matchList, same]
          simp only [same, decide_true, beq_self_eq_true, ite_true]
          have replayed := replay_premises_captured_returns selected state language rows plan.premises view initial path
            (v "premises") (v "rows") (v "initial") (v "path")
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          unfold validateReplay
          cases replay : replayPremises? (providerEnv rows) language plan.premises initial path with
          | none =>
              apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
                validateReplayCases (read_cases_encoded _) _ _ _
              · simpa [replay, bindingsOptionTerm, encoded, CettaWireAtom.encode] using replayed
              · simp [validateReplayCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · simpa [validateRowReceipt?, accepted, guard, replay, MatchAutomataBindingExecution.patternOptionTerm,
                  encoded, CettaWireAtom.encode] using symbol_returns program selected state "None"
          | some final =>
              let chosen := ("final", bindingsValue final) :: selected
              apply case_returns program selected chosen state state state _ (a "Some" [bindingsValue final])
                validateFinal _ _ validateReplayCases (read_cases_encoded _) _ _ _
              · simpa [replay, bindingsOptionTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using replayed
              · simp [validateReplayCases, chosen, selected, caller, environment, Helper.names,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup]
              · have completedEqual := bindings_equal_returns chosen state final completed "final" "completed"
                  (by simp [chosen, applySubst, Subst.lookup])
                  (by simp [chosen, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                unfold validateFinal
                apply if_returns program chosen state state state _ _ _ _ _ completedEqual
                by_cases finished : final = completed
                · have actualReturned := validateActual_returns chosen state plan.right final target
                    (by simp [chosen, selected, caller, environment, Helper.names, Subst.lookup])
                    (by simp [chosen, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                    (by simp [chosen, applySubst, Subst.lookup])
                    (by simp [chosen, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                  by_cases exactTarget : plan.right.instantiate completed = target
                  · simpa [validateRowReceipt?, accepted, guard, replay, finished, exactTarget] using actualReturned
                  · simpa [validateRowReceipt?, accepted, guard, replay, finished, exactTarget] using actualReturned
                · simpa [validateRowReceipt?, accepted, guard, replay, finished, Effects.boolean,
                    MatchAutomataBindingExecution.patternOptionTerm, encoded, CettaWireAtom.encode] using
                    symbol_returns program chosen state "None"
        · simpa [validateRowReceipt?, matchList, guard, same, Ne.symm same, Effects.boolean,
            MatchAutomataBindingExecution.patternOptionTerm, encoded, CettaWireAtom.encode] using
            symbol_returns program selected state "None"

/-- The retained validator checks the canonical matcher, exact branch replay,
completed binding list and instantiated target, preserving the supplied state. -/
theorem validate_sides_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan)
    (initial completed : Bindings) (path : List Nat) (target : Pattern)
    (one two three four five six seven eight nine : Atom)
    (captured : [one, two, three, four, five, six, seven, eight, nine].map (applySubst caller) =
      [premisesValue plan.premises, encoded (InferenceCettaWire.encodePattern plan.left.erase),
        encoded (InferenceCettaWire.encodePattern plan.right.erase), rowsValue rows,
        encoded (InferenceCettaWire.encodePattern subject.erase), bindingsValue initial,
        encoded (pathTerm path), bindingsValue completed, encoded (InferenceCettaWire.encodePattern target)]) :
    PureReturns program caller state (a "gslt:equation:validate-sides" [one, two, three, four, five, six, seven, eight, nine]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateRowReceipt? (providerEnv rows) language plan subject.erase initial path completed target))) :=
  helper_call .validateSides caller state _ _ _ rfl captured
    (validateSides_body_returns state language rows plan view subject initial completed path target)

private def equationOptionTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) : Option RulePlan → Term
  | none => .symbol "None"
  | some plan => .application "Some" [equationTerm contexts plan]

private theorem equations_as_list (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan) :
    encoded (equationsTerm contexts plans) =
      MatchAutomataSourceExecution.listValue (plans.map (equationTerm contexts)) := by
  simp only [equationsTerm, MatchAutomataSourceExecution.listValue, encodeList_map, Function.comp_def, id_eq]

private theorem lookup_equation_returns (caller : Subst) (state : State) (index : Nat)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (captured : [v "index", v "equations"].map (applySubst caller) =
      [number index, encoded (equationsTerm contexts plans)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [v "index", v "equations"]) state
      (encoded (equationOptionTerm contexts plans[index]?)) := by
  apply retained_captured_returns (by decide +kernel)
  have returned := RootRuleExecution.Matched.row_at_captured_returns caller state index
    (plans.map (equationTerm contexts)) (v "index") (v "equations")
    (by simpa only [← equations_as_list] using captured)
  cases chosen : plans[index]? with
  | none =>
      simp only [List.getElem?_map, chosen, Option.map_none] at returned
      exact returned
  | some plan =>
      simp only [List.getElem?_map, chosen, Option.map_some] at returned
      exact returned

private def validateRowCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "EqForward", a "Equation" [v "name", v "context", v "premises", v "left", v "right"]],
     a "gslt:equation:validate-sides" [v "premises", v "left", v "right", v "rows", v "subject",
       v "initial", v "path", v "completed", v "target"]),
   (.expression [.symbol "EqReverse", a "Equation" [v "name", v "context", v "premises", v "left", v "right"]],
     a "gslt:equation:validate-sides" [v "premises", v "right", v "left", v "rows", v "subject",
       v "initial", v "path", v "completed", v "target"]),
   (v "bad", .symbol "None")]
private def validateRow : Atom :=
  a "case" [.expression [v "orientation", v "equation"],
    .expression (validateRowCases.map fun row => .expression [row.1, row.2])]
private def validateLookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "equation"], validateRow)]
private def validateLookup : Atom :=
  a "case" [a "gslt:rule:row-at" [v "index", v "equations"],
    .expression (validateLookupCases.map fun row => .expression [row.1, row.2])]
private def validateCases : SpaceSemantics.Cases :=
  [(a "EqInstance" [v "index", v "orientation", v "initial", v "path", v "completed", v "target"], validateLookup),
    (v "bad", .symbol "None")]
private theorem validate_shape : (equation .validate).body =
    a "case" [v "receipt", .expression (validateCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem validateRow_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plan : RulePlan) (view : VariableRuleView plan) (subject : PatternPlan) (receipt : Receipt)
    (captured : [v "orientation", v "equation", v "rows", v "subject", v "initial", v "path", v "completed", v "target"].map
        (applySubst caller) = [encoded (orientationTerm receipt.orientation), encoded (equationTerm contexts plan),
          rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase), bindingsValue receipt.initialBindings,
          encoded (pathTerm receipt.choices), bindingsValue receipt.finalBindings,
          encoded (InferenceCettaWire.encodePattern receipt.target)])
    (fresh : ∀ name ∈ ["name", "context", "premises", "left", "right"], Subst.lookup caller name = none) :
    PureReturns program caller state validateRow state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateRowReceipt? (providerEnv rows) language (orientedPlan plan receipt.orientation) subject.erase
          receipt.initialBindings receipt.choices receipt.finalBindings receipt.target))) := by
  let selected := ("right", encoded (InferenceCettaWire.encodePattern plan.right.erase)) ::
    ("left", encoded (InferenceCettaWire.encodePattern plan.left.erase)) :: ("premises", premisesValue plan.premises) ::
    ("context", encoded (contexts (equationOfPlan plan))) :: ("name", encoded (.string plan.name)) :: caller
  have entries := List.cons.inj captured
  have orientationCaptured := entries.1
  have equationCaptured := (List.cons.inj entries.2).1
  have rowsCaptured := (List.cons.inj (List.cons.inj entries.2).2).1
  have subjectCaptured := (List.cons.inj (List.cons.inj (List.cons.inj entries.2).2).2).1
  have initialCaptured := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj entries.2).2).2).2).1
  have pathCaptured := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj entries.2).2).2).2).2).1
  have completedCaptured := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj entries.2).2).2).2).2).2).1
  have targetCaptured := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj entries.2).2).2).2).2).2).2).1
  simp only [applySubst, Subst.lookup] at rowsCaptured subjectCaptured initialCaptured pathCaptured completedCaptured targetCaptured
  have freshName := fresh "name" (by simp)
  have freshContext := fresh "context" (by simp)
  have freshPremises := fresh "premises" (by simp)
  have freshLeft := fresh "left" (by simp)
  have freshRight := fresh "right" (by simp)
  simp only [Subst.lookup] at freshName freshContext freshPremises freshLeft freshRight
  unfold validateRow
  cases oriented : receipt.orientation with
  | forward =>
      apply case_returns program caller selected state state state _
        (.expression [encoded (orientationTerm .forward), encoded (equationTerm contexts plan)])
        (a "gslt:equation:validate-sides" [v "premises", v "left", v "right", v "rows", v "subject",
          v "initial", v "path", v "completed", v "target"]) _ _
        validateRowCases (read_cases_encoded _) _ _ _
      · simpa [oriented, orientationCaptured, equationCaptured] using
          tuple_variables_return program caller state ["orientation", "equation"]
      · simp [validateRowCases, orientationTerm, equationTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, freshName, freshContext, freshPremises, freshLeft, freshRight, Subst.lookup]
      · simpa only [oriented, orientedPlan] using validate_sides_captured_returns selected state language rows plan view subject
          receipt.initialBindings receipt.finalBindings receipt.choices receipt.target
          (v "premises") (v "left") (v "right") (v "rows") (v "subject") (v "initial") (v "path") (v "completed") (v "target")
          (by simp [selected, applySubst, Subst.lookup, rowsCaptured, subjectCaptured, initialCaptured,
              pathCaptured, completedCaptured, targetCaptured])
  | reverse =>
      apply case_returns program caller selected state state state _
        (.expression [encoded (orientationTerm .reverse), encoded (equationTerm contexts plan)])
        (a "gslt:equation:validate-sides" [v "premises", v "right", v "left", v "rows", v "subject",
          v "initial", v "path", v "completed", v "target"]) _ _
        validateRowCases (read_cases_encoded _) _ _ _
      · simpa [oriented, orientationCaptured, equationCaptured] using
          tuple_variables_return program caller state ["orientation", "equation"]
      · simp [validateRowCases, orientationTerm, equationTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, freshName, freshContext, freshPremises, freshLeft, freshRight, Subst.lookup]
      · simpa only [oriented, orientedPlan] using validate_sides_captured_returns selected state language rows
          (orientedPlan plan .reverse)
          ⟨view.val, by simpa only [orientedPlan_premises] using view.property⟩ subject receipt.initialBindings receipt.finalBindings receipt.choices receipt.target
          (v "premises") (v "right") (v "left") (v "rows") (v "subject") (v "initial") (v "path") (v "completed") (v "target")
          (by simp [orientedPlan, selected, applySubst, Subst.lookup, rowsCaptured, subjectCaptured, initialCaptured,
              pathCaptured, completedCaptured, targetCaptured])

private theorem validate_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) (receipt : Receipt) :
    PureReturns program (environment .validate [encoded (equationsTerm contexts plans), rowsValue rows,
      encoded (InferenceCettaWire.encodePattern subject.erase), encoded (receiptTerm receipt)])
      state (equation .validate).body state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateReceipt? (providerEnv rows) language plans subject.erase receipt))) := by
  let caller := environment .validate [encoded (equationsTerm contexts plans), rowsValue rows,
    encoded (InferenceCettaWire.encodePattern subject.erase), encoded (receiptTerm receipt)]
  let selected := ("target", encoded (InferenceCettaWire.encodePattern receipt.target)) ::
    ("completed", bindingsValue receipt.finalBindings) :: ("path", encoded (pathTerm receipt.choices)) ::
    ("initial", bindingsValue receipt.initialBindings) :: ("orientation", encoded (orientationTerm receipt.orientation)) ::
    ("index", number receipt.equationIndex) :: caller
  rw [validate_shape]
  apply case_returns program caller selected state state state (v "receipt") (encoded (receiptTerm receipt))
    validateLookup _ _ validateCases (read_cases_encoded _) _ _ _
  · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "receipt"
  · simp [validateCases, receiptTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, selected, caller, environment, Helper.names, Subst.lookup]
  · have lookedUp := lookup_equation_returns selected state receipt.equationIndex contexts plans
      (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])
    unfold validateLookup
    cases chosen : plans[receipt.equationIndex]? with
    | none =>
        apply case_returns program selected selected state state state _ (.symbol "None") (.symbol "None") _ _
          validateLookupCases (read_cases_encoded _) _ _ _
        · simpa [chosen, equationOptionTerm, encoded, CettaWireAtom.encode] using lookedUp
        · simp [validateLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [validateReceipt?, chosen, MatchAutomataBindingExecution.patternOptionTerm, encoded, CettaWireAtom.encode] using
            symbol_returns program selected state "None"
    | some plan =>
        let declared := ("equation", encoded (equationTerm contexts plan)) :: selected
        apply case_returns program selected declared state state state _ (a "Some" [encoded (equationTerm contexts plan)])
          validateRow _ _ validateLookupCases (read_cases_encoded _) _ _ _
        · simpa [chosen, equationOptionTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookedUp
        · simp [validateLookupCases, declared, selected, caller, environment, Helper.names,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · simpa only [validateReceipt?, chosen, Option.bind_eq_bind, Option.bind_some] using
            validateRow_returns declared state language rows contexts plan
              (variableRuleView plan (sourceViews plan (List.mem_of_getElem? chosen))) subject receipt
              (by simp [declared, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              (by intro name member; simp at member; rcases member with rfl | rfl | rfl | rfl | rfl <;>
                  simp [declared, selected, caller, environment, Helper.names, Subst.lookup])

/-- Every encoded receipt is checked against its physical authored row,
orientation, initial match, complete premise replay and actual target. -/
theorem validate_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) (receipt : Receipt)
    (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (equationsTerm contexts plans), rowsValue rows, encoded (InferenceCettaWire.encodePattern subject.erase),
        encoded (receiptTerm receipt)]) :
    PureReturns program caller state (a "gslt:equation:validate" [one, two, three, four]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateReceipt? (providerEnv rows) language plans subject.erase receipt))) :=
  helper_call .validate caller state _ _ _ rfl captured
    (validate_body_returns state language rows contexts plans sourceViews subject receipt)

/-- Full equation receipts remain distinguishable even when their targets agree. -/
theorem receiptTerm_injective : Function.Injective receiptTerm := by
  have direction : Function.Injective orientationTerm := by
    intro left right same
    cases left <;> cases right <;> simp_all [orientationTerm]
  have paths : Function.Injective pathTerm :=
    encodeList_injective Term.natural (fun _ _ same => Term.natural.inj same)
  intro left right same
  have fields := (Term.application.inj same).2
  simp only [List.cons.injEq, and_true] at fields
  obtain ⟨index, orientation, initial, path, final, target⟩ := fields
  cases left
  cases right
  simp only [Receipt.mk.injEq]
  exact ⟨Term.natural.inj index, direction orientation,
    MatchAutomataBindingExecution.bindingsTerm_injective initial, paths path,
    MatchAutomataBindingExecution.bindingsTerm_injective final, InferenceCettaWire.encodePattern_injective target⟩

theorem receiptsTerm_injective : Function.Injective receiptsTerm :=
  encodeList_injective receiptTerm receiptTerm_injective

/-- Closed source query for an admitted equation-plan list. -/
def rootQueryTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (plans : List RulePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (subject : PatternPlan) : Term :=
  .application "gslt:equation:root" [equationsTerm contexts plans, providerRowsTerm rows,
    InferenceCettaWire.encodePattern subject.erase]

def validateQueryTerm (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (plans : List RulePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (subject : PatternPlan) (receipt : Receipt) : Term :=
  .application "gslt:equation:validate" [equationsTerm contexts plans, providerRowsTerm rows,
    InferenceCettaWire.encodePattern subject.erase, receiptTerm receipt]

theorem root_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan) :
    PureReturns program [] state (encoded (rootQueryTerm contexts plans rows subject)) state
      (encoded (receiptsTerm (rootReceipts (providerEnv rows) language plans subject.erase))) := by
  exact root_captured_returns [] state language rows contexts plans sourceViews subject _ _ _
    (by simp)

theorem validate_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true)
    (subject : PatternPlan) (receipt : Receipt) :
    PureReturns program [] state (encoded (validateQueryTerm contexts plans rows subject receipt)) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateReceipt? (providerEnv rows) language plans subject.erase receipt))) := by
  exact validate_captured_returns [] state language rows contexts plans sourceViews subject receipt _ _ _ _
    (by simp)

/-- Completion is exact in the store, answers and input/output observations. -/
theorem root_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (rootQueryTerm contexts plans rows subject)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (receiptsTerm (rootReceipts (providerEnv rows) language plans subject.erase))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (root_returns state language rows contexts plans sourceViews subject) after answers input output

theorem root_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state := state, control := .evaluate [] (encoded (rootQueryTerm contexts plans rows subject)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (receiptsTerm (rootReceipts (providerEnv rows) language plans subject.erase))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (root_returns state language rows contexts plans sourceViews subject) after answers input output

theorem validate_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true)
    (subject : PatternPlan) (receipt : Receipt) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts plans rows subject receipt)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateReceipt? (providerEnv rows) language plans subject.erase receipt))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (validate_returns state language rows contexts plans sourceViews subject receipt) after answers input output

theorem validate_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true)
    (subject : PatternPlan) (receipt : Receipt) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts plans rows subject receipt)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (MatchAutomataBindingExecution.patternOptionTerm
        (validateReceipt? (providerEnv rows) language plans subject.erase receipt))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (validate_returns state language rows contexts plans sourceViews subject receipt) after answers input output

/-- Targets observed in actual retained source runs, rather than a separately
supplied or evaluated reference frontier. -/
def ObservesRootInstance (state : State) (_language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (source : PatternPlan) (target : Pattern) : Prop :=
  ∃ observed : List Receipt,
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (rootQueryTerm contexts plans rows source)) }
      (.complete state [encoded (receiptsTerm observed)] [] []) ∧ target ∈ observed.map Receipt.target

/-- The independently generated canonical authored relation is both preserved
and reflected by completed source observations. -/
theorem observes_root_iff_instance (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true) (source : PatternPlan) (target : Pattern) :
    ObservesRootInstance state language rows contexts compiled.plans source target ↔
      EquationInstance (engineBasePremises (providerEnv rows)) language source.erase target := by
  rw [← rootReceipts_iff_instance compiled]
  constructor
  · rintro ⟨observed, executed, member⟩
    have exactRun := (root_derivation_iff state language rows contexts compiled.plans sourceViews source state _ [] []).mp executed
    have sameAtom := (List.cons.inj exactRun.2.1).1
    have sameWire := CettaWireAtom.encode_injective _ _ sameAtom
    have same := receiptsTerm_injective sameWire
    simpa only [same] using member
  · intro member
    exact ⟨_, (root_derivation_iff state language rows contexts compiled.plans sourceViews source state _ [] []).mpr
      ⟨rfl, rfl, rfl, rfl⟩, member⟩

/-- The complete receipt is accepted by actual source execution exactly when
it belongs to the canonical ordered authored instance frontier. -/
theorem validates_receipt_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term) (plans : List RulePlan)
    (sourceViews : ∀ plan ∈ plans, plan.variablePremises?.isSome = true)
    (subject : PatternPlan) (receipt : Receipt) (target : Pattern) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts plans rows subject receipt)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target])] [] []) ↔
      receipt ∈ rootReceipts (providerEnv rows) language plans subject.erase ∧ target = receipt.target := by
  rw [validate_derivation_iff state language rows contexts plans sourceViews subject receipt]
  simp only [true_and, List.cons.injEq, and_true, CettaWireAtom.encode_eq_encode]
  rw [← validateReceipt?_iff]
  cases found : validateReceipt? (providerEnv rows) language plans subject.erase receipt with
  | none => simp [MatchAutomataBindingExecution.patternOptionTerm]
  | some actual => simp [MatchAutomataBindingExecution.patternOptionTerm, InferenceCettaWire.encodePattern_injective.eq_iff, eq_comm]

/-- Literal query premises give the same authored support at every canonical
premise depth; source execution has its separate instruction budget. -/
theorem observes_root_iff_instanceAt (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true) (source : PatternPlan) (target : Pattern) (fuel : Nat) :
    ObservesRootInstance state language rows contexts compiled.plans source target ↔
      EquationInstanceAt (engineBasePremises (providerEnv rows)) language fuel source.erase target :=
  (observes_root_iff_instance state language rows contexts compiled sourceViews source target).trans
    ((rootReceipts_iff_instance compiled source.erase target).symm.trans
      (rootReceipts_iff_instanceAt compiled source.erase target fuel))

/-- Actual source validation supplies the existing canonical contextual
witness. No reduction-context permission follows from this equation law. -/
theorem validates_context_step (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term)
    (compiled : EquationProgram language.equations)
    (sourceViews : ∀ plan ∈ compiled.plans, plan.variablePremises?.isSome = true) (source : PatternPlan) (receipt : Receipt) (target : Pattern)
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (accepted : DeclarativeSpec.Runs program
      { state := state, control := .evaluate [] (encoded (validateQueryTerm contexts compiled.plans rows source receipt)) }
      (.complete state [encoded (.application "Some" [InferenceCettaWire.encodePattern target])] [] [])) :
    EquationContextStep (engineBasePremises (providerEnv rows)) language
      (context.fill source.erase) (context.fill target) := by
  have checked := (validates_receipt_iff state language rows contexts compiled.plans sourceViews source receipt target).mp accepted
  exact validated_context_step compiled context source.erase target receipt
    ((validateReceipt?_iff _ _ _ _ _ _).mpr checked)

namespace Controls

def rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow :=
  [⟨"choose", [(MeTTaILFirstOrderEquationCompilation.Controls.atom "a").erase,
    (MeTTaILFirstOrderEquationCompilation.Controls.atom "b").erase]⟩,
   ⟨"choose", [(MeTTaILFirstOrderEquationCompilation.Controls.atom "a").erase,
    (MeTTaILFirstOrderEquationCompilation.Controls.atom "b").erase]⟩,
   ⟨"choose", [(MeTTaILFirstOrderEquationCompilation.Controls.atom "a").erase,
    (MeTTaILFirstOrderEquationCompilation.Controls.atom "c").erase]⟩]

def contexts : Mettapedia.OSLF.MeTTaIL.Syntax.Equation → Term := fun _ => .symbol "LNil"

theorem provider_exact : providerEnv rows = MeTTaILFirstOrderEquationCompilation.Controls.relations := by
  apply congrArg Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.mk
  funext relation arguments
  by_cases selected : relation = "choose"
  · simp [RelationPremiseExecution.providerTuples, rows, selected]
  · simp [RelationPremiseExecution.providerTuples, rows, selected, Ne.symm selected]

theorem duplicate_declarations_returns (state : State) :
    PureReturns program [] state
      (encoded (rootQueryTerm contexts [MeTTaILFirstOrderEquationCompilation.Controls.conditional,
        MeTTaILFirstOrderEquationCompilation.Controls.conditional] rows
        (MeTTaILFirstOrderEquationCompilation.Controls.atom "a"))) state
      (encoded (receiptsTerm
        [MeTTaILFirstOrderEquationCompilation.Controls.expected 0 0 "b",
          MeTTaILFirstOrderEquationCompilation.Controls.expected 0 1 "b",
          MeTTaILFirstOrderEquationCompilation.Controls.expected 0 2 "c",
          MeTTaILFirstOrderEquationCompilation.Controls.expected 1 0 "b",
          MeTTaILFirstOrderEquationCompilation.Controls.expected 1 1 "b",
          MeTTaILFirstOrderEquationCompilation.Controls.expected 1 2 "c"])) := by
  simpa only [provider_exact, MeTTaILFirstOrderEquationCompilation.Controls.duplicate_declaration_occurrences] using
    root_returns state MeTTaILFirstOrderEquationCompilation.Controls.language rows contexts
      [MeTTaILFirstOrderEquationCompilation.Controls.conditional,
        MeTTaILFirstOrderEquationCompilation.Controls.conditional]
      (by intro plan member; simp at member; subst plan; decide +kernel)
      (MeTTaILFirstOrderEquationCompilation.Controls.atom "a")

theorem valid_receipt_returns (state : State) :
    PureReturns program [] state
      (encoded (validateQueryTerm contexts [MeTTaILFirstOrderEquationCompilation.Controls.conditional] rows
        (MeTTaILFirstOrderEquationCompilation.Controls.atom "a")
        (MeTTaILFirstOrderEquationCompilation.Controls.expected 0 1 "b"))) state
      (encoded (.application "Some" [InferenceCettaWire.encodePattern
        (.apply "out" [(MeTTaILFirstOrderEquationCompilation.Controls.atom "b").erase])])) := by
  simpa only [provider_exact, ← show MeTTaILFirstOrderEquationCompilation.Controls.compiled.plans =
      [MeTTaILFirstOrderEquationCompilation.Controls.conditional] from rfl,
    MeTTaILFirstOrderEquationCompilation.Controls.receipt_accepted, MatchAutomataBindingExecution.patternOptionTerm] using
    validate_returns state MeTTaILFirstOrderEquationCompilation.Controls.language rows contexts
      MeTTaILFirstOrderEquationCompilation.Controls.compiled.plans
      (by intro plan member; simp [MeTTaILFirstOrderEquationCompilation.Controls.compiled] at member; subst plan; decide +kernel)
      (MeTTaILFirstOrderEquationCompilation.Controls.atom "a")
      (MeTTaILFirstOrderEquationCompilation.Controls.expected 0 1 "b")

theorem altered_target_refused_returns (state : State) :
    PureReturns program [] state
      (encoded (validateQueryTerm contexts [MeTTaILFirstOrderEquationCompilation.Controls.conditional] rows
        (MeTTaILFirstOrderEquationCompilation.Controls.atom "a")
        { MeTTaILFirstOrderEquationCompilation.Controls.expected 0 1 "b" with
          target := .apply "out" [(MeTTaILFirstOrderEquationCompilation.Controls.atom "c").erase] })) state
      (.symbol "None") := by
  change PureReturns program [] state
    (encoded (validateQueryTerm contexts [MeTTaILFirstOrderEquationCompilation.Controls.conditional] rows
      (MeTTaILFirstOrderEquationCompilation.Controls.atom "a")
      { MeTTaILFirstOrderEquationCompilation.Controls.expected 0 1 "b" with
        target := .apply "out" [(MeTTaILFirstOrderEquationCompilation.Controls.atom "c").erase] })) state
    (encoded (.symbol "None"))
  simpa only [provider_exact, ← show MeTTaILFirstOrderEquationCompilation.Controls.compiled.plans =
      [MeTTaILFirstOrderEquationCompilation.Controls.conditional] from rfl,
    MeTTaILFirstOrderEquationCompilation.Controls.wrong_target_refused, MatchAutomataBindingExecution.patternOptionTerm] using
    validate_returns state MeTTaILFirstOrderEquationCompilation.Controls.language rows contexts
      MeTTaILFirstOrderEquationCompilation.Controls.compiled.plans
      (by intro plan member; simp [MeTTaILFirstOrderEquationCompilation.Controls.compiled] at member; subst plan; decide +kernel)
      (MeTTaILFirstOrderEquationCompilation.Controls.atom "a")
      { MeTTaILFirstOrderEquationCompilation.Controls.expected 0 1 "b" with
        target := .apply "out" [(MeTTaILFirstOrderEquationCompilation.Controls.atom "c").erase] }

end Controls

#print axioms premise_traces_captured_returns
#print axioms replay_premises_captured_returns
#print axioms root_captured_returns
#print axioms root_returns
#print axioms root_completed_iff
#print axioms root_derivation_iff
#print axioms validate_captured_returns
#print axioms validate_returns
#print axioms validate_completed_iff
#print axioms validate_derivation_iff
#print axioms observes_root_iff_instance
#print axioms observes_root_iff_instanceAt
#print axioms validates_receipt_iff
#print axioms validates_context_step
#print axioms receiptTerm_injective
#print axioms Controls.duplicate_declarations_returns
#print axioms Controls.valid_receipt_returns
#print axioms Controls.altered_target_refused_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecution
