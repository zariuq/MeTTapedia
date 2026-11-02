import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core

/-! Native environment metadata, provider validation, and ground-pattern traversal. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)
open CettaWire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open GeneralPremise (Environment)
open GeneralPremise.Execution (Goal Result StepCall Continuation Task Obligation)

private def environmentDataHeads : List String :=
  ["Some", "LCons", "GrammarTypingV1", "GrammarTypingWrappedV1", "TBase", "PremiseSignature"]

private theorem environment_data_template (head : String) (arguments : List Atom)
    (supported : head ∈ environmentDataHeads)
    (children : ∀ child ∈ arguments, PureData.Template Base.runtime child) :
    PureData.Template Base.runtime (Base.a head arguments) := by
  have checked : environmentDataHeads.all (fun name => decide
      ((ioHead name || StdLib.known name || Base.runtime.equations.any (·.head == name)) = false ∧
        name ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"])) = true := by
    decide +kernel
  have row := List.all_eq_true.mp checked head supported
  rw [decide_eq_true_eq] at row
  exact .constructor head arguments row.1 row.2 children

local macro "environment_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply environment_data_template _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private inductive EnvHelper where
  | constructors | sourceType | specification | signatureCandidates | signature | values | row | ground | groundList

private def EnvHelper.head : EnvHelper → String
  | .constructors => "gslt:premise:constructor-declarations"
  | .sourceType => "gslt:premise:source-type"
  | .specification => "gslt:premise:specification"
  | .signatureCandidates => "gslt:premise:signature-candidates"
  | .signature => "gslt:premise:signature"
  | .values => "gslt:premise:check-values"
  | .row => "gslt:premise:check-row"
  | .ground => "gslt:premise:ground-at"
  | .groundList => "gslt:premise:ground-list-at"
private def EnvHelper.names : EnvHelper → List String
  | .constructors => ["constructor", "declarations"]
  | .sourceType => ["declarations", "rule", "source"]
  | .specification => ["index", "specifications"]
  | .signatureCandidates => ["relation", "arity", "signatures"]
  | .signature => ["relation", "arity", "provider"]
  | .values => ["declarations", "free", "bound", "values", "types"]
  | .row => ["declarations", "free", "bound", "signature", "row"]
  | .ground => ["depth", "pattern"]
  | .groundList => ["depth", "patterns"]
private def envEquation (helper : EnvHelper) : SpaceSemantics.Equation :=
  (Base.equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def envCaptured (helper : EnvHelper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem env_clause (helper : EnvHelper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses Base.runtime helper.head values =
      [.evaluate (envCaptured helper values) (envEquation helper).body] :=
  PureData.named_equation_clause Base.runtime helper.head (envEquation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

set_option maxHeartbeats 4000000 in
private theorem env_raw (helper : EnvHelper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw Base.runtime helper.head index = true := by
  cases helper <;> simp only [EnvHelper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl <;> first | omega | decide +kernel

private theorem env_call (helper : EnvHelper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns Base.runtime (envCaptured helper values) state (envEquation helper).body state answer) :
    PureReturns Base.runtime caller state (Base.a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return Base.runtime caller (envCaptured helper values) state state
    helper.head arguments (envEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply env_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact env_clause helper values length
  · exact returned

private theorem env_capture (helper : EnvHelper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns Base.runtime [] state (Base.a helper.head values) state answer) :
    PureReturns Base.runtime caller state (Base.a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns Base.runtime [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact env_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private abbrev specificationsValue (specifications : List (Nat × RuleBindingSpec)) : Atom :=
  Base.encoded (encodeList specificationTerm specifications)
private abbrev specificationOptionValue (found : Option RuleBindingSpec) : Atom :=
  Base.encoded (encodeOption InferenceCettaWire.AuthoredRule.bindingSpecTerm found)
private def specificationConsBody : Atom :=
  Base.a "if" [Base.a "==" [Base.v "position", Base.v "index"], Base.a "Some" [Base.v "spec"],
    Base.a "gslt:premise:specification" [Base.v "index", Base.v "rest"]]
private def specificationCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"),
    (Base.a "LCons" [Base.a "PremiseSpecification" [Base.v "position", Base.v "spec"], Base.v "rest"], specificationConsBody),
    (Base.v "bad", .symbol "None")]
private theorem specification_shape : (envEquation .specification).body =
    Base.caseData (Base.v "specifications") specificationCases := by decide +kernel

/-- Declaration-position lookup reads the first stored specification without
renaming declarations or collapsing duplicate physical rows. -/
theorem specification_list_returns (state : State) (index : Nat)
    (specifications : List (Nat × RuleBindingSpec)) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:specification" [Base.number index, specificationsValue specifications]) state
      (specificationOptionValue ((specifications.find? fun entry => entry.1 == index).map Prod.snd)) := by
  induction specifications with
  | nil =>
      let caller := envCaptured .specification [Base.number index, specificationsValue []]
      apply env_call .specification [] state _ _ _ rfl (Base.captured_closed _)
      rw [specification_shape]
      apply Base.branch_returns caller caller state _ (.symbol "LNil") specificationCases (.symbol "None") _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup, specificationsValue,
          encodeList, CettaWireAtom.encode] using variable_returns Base.runtime caller state "specifications"
      · simp [specificationCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns Base.runtime caller state "None"
  | cons entry rest ih =>
      rcases entry with ⟨position, spec⟩
      let caller := envCaptured .specification [Base.number index, specificationsValue ((position, spec) :: rest)]
      let selected := [("rest", specificationsValue rest), ("spec", Base.specValue spec), ("position", Base.number position)] ++ caller
      apply env_call .specification [] state _ _ _ rfl (Base.captured_closed _)
      rw [specification_shape]
      apply Base.branch_returns caller selected state _ (specificationsValue ((position, spec) :: rest))
        specificationCases specificationConsBody _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "specifications"
      · simp [specificationCases, specificationTerm, specificationsValue, Base.specValue,
          encodeList, selected, caller, envCaptured, EnvHelper.names, Base.number,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have tested := Base.natural_equal_returns selected state position index "position" "index"
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        unfold specificationConsBody
        apply Base.bool_if_returns selected state _ (position == index) _ _ _ tested
        cases same : position == index with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, List.find?_cons, same]
            exact env_capture .specification selected state [Base.v "index", Base.v "rest"]
              [Base.number index, specificationsValue rest] _ rfl
              (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) ih
        | true =>
            simp only [↓reduceIte, List.find?_cons, same, Option.map_some]
            have templated : PureData.Template Base.runtime (Base.a "Some" [Base.v "spec"]) := by environment_template
            simpa [specificationOptionValue, encodeOption, Base.specValue, selected, caller, envCaptured,
              EnvHelper.names, applySubst, applySubst.applySubstList, Subst.lookup,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return Base.runtime selected state _ templated

theorem specification_returns (state : State) (env : Environment) (index : Nat) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:specification" [Base.number index, specificationsValue env.specifications]) state
      (specificationOptionValue (GeneralPremise.specification? env index)) :=
  specification_list_returns state index env.specifications

#print axioms specification_list_returns
#print axioms specification_returns

private abbrev declarationsListValue (declarations : List GrammarRule) : Atom :=
  Base.encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm declarations)
private abbrev parametersValue (parameters : List TermParam) : Atom :=
  Base.encoded (InferenceCettaWire.encodeList InferenceCettaWire.AuthoredRule.parameterTerm parameters)
private def constructorsConsData (mode : CollectionRepresentation) : Atom :=
  Base.a "LCons" [Base.a (match mode with | .bare => "GrammarTypingV1" | .wrapped => "GrammarTypingWrappedV1") [Base.v "label", Base.v "category", Base.v "parameters"], Base.v "filtered"]
private def constructorsIncludedBody (mode : CollectionRepresentation) : Atom :=
  Base.a "let" [Base.v "filtered", Base.a "gslt:premise:constructor-declarations" [Base.v "constructor", Base.v "rest"],
    constructorsConsData mode]
private def constructorsConsBody (mode : CollectionRepresentation) : Atom :=
  Base.a "if" [Base.a "==" [Base.v "label", Base.v "constructor"], constructorsIncludedBody mode,
    Base.a "gslt:premise:constructor-declarations" [Base.v "constructor", Base.v "rest"]]
private def constructorsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (Base.a "LCons" [Base.a "GrammarTypingV1" [Base.v "label", Base.v "category", Base.v "parameters"], Base.v "rest"], constructorsConsBody .bare),
    (Base.a "LCons" [Base.a "GrammarTypingWrappedV1" [Base.v "label", Base.v "category", Base.v "parameters"], Base.v "rest"], constructorsConsBody .wrapped),
    (Base.v "bad", .symbol "LNil")]
private theorem constructors_shape : (envEquation .constructors).body =
    Base.caseData (Base.v "declarations") constructorsCases := by decide +kernel

private theorem env_string_equal_returns (caller : Subst) (state : State)
    (left right one two : String)
    (first : applySubst caller (Base.v one) = Base.stringValue left)
    (second : applySubst caller (Base.v two) = Base.stringValue right) :
    PureReturns Base.runtime caller state (Base.a "==" [Base.v one, Base.v two]) state
      (Effects.boolean (decide (left = right))) := by
  have tested := CettaWireAtom.equality_captured_returns Base.runtime caller state
    (.string left) (.string right) one two first second
  have same : Term.string left = Term.string right ↔ left = right := by simp
  simpa only [same] using tested

/-- Constructor selection retains every physical authored declaration whose
label matches. Syntax and evaluation metadata are unused by the source check. -/
theorem constructor_declarations_returns (state : State) (constructor : String)
    (declarations : List GrammarRule) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:constructor-declarations" [Base.stringValue constructor, declarationsListValue declarations]) state
      (declarationsListValue (declarations.filter fun declaration => declaration.label == constructor)) := by
  induction declarations with
  | nil =>
      let caller := envCaptured .constructors [Base.stringValue constructor, declarationsListValue []]
      apply env_call .constructors [] state _ _ _ rfl (Base.captured_closed _)
      rw [constructors_shape]
      apply Base.branch_returns caller caller state _ (.symbol "LNil") constructorsCases (.symbol "LNil") _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup,
          declarationsListValue, encodeList, CettaWireAtom.encode] using
          variable_returns Base.runtime caller state "declarations"
      · simp [constructorsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns Base.runtime caller state "LNil"
  | cons declaration declarations ih =>
      let caller := envCaptured .constructors
        [Base.stringValue constructor, declarationsListValue (declaration :: declarations)]
      let selected := [("rest", declarationsListValue declarations), ("parameters", parametersValue declaration.params),
        ("category", Base.stringValue declaration.category), ("label", Base.stringValue declaration.label)] ++ caller
      let filtered := ("filtered", declarationsListValue (declarations.filter fun declaration => declaration.label == constructor)) :: selected
      apply env_call .constructors [] state _ _ _ rfl (Base.captured_closed _)
      rw [constructors_shape]
      apply Base.branch_returns caller selected state _ (declarationsListValue (declaration :: declarations))
        constructorsCases (constructorsConsBody declaration.collectionRepresentation) _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "declarations"
      · cases mode : declaration.collectionRepresentation <;> simp [mode, constructorsCases, declarationsListValue, InferenceCettaWire.AuthoredRule.typingDeclarationTerm,
          encodeList, selected, caller, envCaptured, EnvHelper.names, Base.stringValue, parametersValue,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have compared := env_string_equal_returns selected state declaration.label constructor "label" "constructor"
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        unfold constructorsConsBody
        apply Base.bool_if_returns selected state _ (decide (declaration.label = constructor)) _ _ _ compared
        by_cases same : declaration.label = constructor
        · simp only [same, decide_true, ↓reduceIte, List.filter_cons]
          unfold constructorsIncludedBody
          apply let_returns Base.runtime selected filtered state state state (Base.v "filtered")
            (Base.a "gslt:premise:constructor-declarations" [Base.v "constructor", Base.v "rest"])
            (constructorsConsData declaration.collectionRepresentation) (declarationsListValue (declarations.filter fun declaration => declaration.label == constructor)) _
          · exact env_capture .constructors selected state _ _ _ rfl
              (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) ih
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, filtered,
              selected, caller, envCaptured, EnvHelper.names, Subst.lookup]
          · have templated : PureData.Template Base.runtime (constructorsConsData declaration.collectionRepresentation) := by
              cases declaration.collectionRepresentation <;> unfold constructorsConsData <;> environment_template
            cases mode : declaration.collectionRepresentation <;>
              simpa [mode, Base.encoded, constructorsConsData, declarationsListValue, InferenceCettaWire.AuthoredRule.typingDeclarationTerm,
              encodeList, filtered, selected, caller, envCaptured, EnvHelper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, parametersValue, Base.stringValue,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using
              PureData.template_return Base.runtime filtered state _ templated
        · have excluded : (declaration.label == constructor) = false := by simp [same]
          simp only [same, decide_false, List.filter_cons, excluded]
          exact env_capture .constructors selected state _ _ _ rfl
            (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) ih

theorem constructor_declarations_captured_returns (caller : Subst) (state : State)
    (constructor : String) (declarations : List GrammarRule) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [Base.stringValue constructor, declarationsListValue declarations]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:constructor-declarations" [one, two]) state
      (declarationsListValue (declarations.filter fun declaration => declaration.label == constructor)) :=
  env_capture .constructors caller state _ _ _ rfl captured
    (constructor_declarations_returns state constructor declarations)

private theorem lookup_find_map (context : List (String × TypeExpr)) (name : String) :
    (context.find? fun entry => entry.1 == name).map Prod.snd = context.lookup name := by
  induction context with
  | nil => rfl
  | cons entry context ih =>
      rcases entry with ⟨declared, type⟩
      by_cases same : declared = name
      · subst declared
        simp
      · have forward : (declared == name) = false := by simp [same]
        have reverse : (name == declared) = false := by simp [Ne.symm same]
        simp only [List.find?_cons, forward, List.lookup_cons, reverse, ih]

#print axioms constructor_declarations_returns
#print axioms constructor_declarations_captured_returns

private def sourceVariableCases : SpaceSemantics.Cases :=
  [(Base.a "ScopedRewriteRuleV1" [Base.v "ruleName", Base.v "types", Base.v "premises", Base.v "left", Base.v "right", Base.v "bindings"],
    Base.a "gslt:premise:type-context-lookup" [Base.v "name", Base.v "types"]), (Base.v "badRule", .symbol "None")]
private def sourceConstructorData : Atom := Base.a "Some" [Base.a "TBase" [Base.v "category"]]
private def sourceConstructorCases : SpaceSemantics.Cases :=
  [(Base.a "LCons" [Base.a "GrammarTypingV1" [Base.v "label", Base.v "category", Base.v "parameters"], .symbol "LNil"],
    sourceConstructorData),
    (Base.a "LCons" [Base.a "GrammarTypingWrappedV1" [Base.v "label", Base.v "category", Base.v "parameters"], .symbol "LNil"],
    sourceConstructorData), (Base.v "ambiguous", .symbol "None")]
private def sourceCases : SpaceSemantics.Cases :=
  [(Base.a "FVar" [Base.v "name"], Base.caseData (Base.v "rule") sourceVariableCases),
    (Base.a "PApp" [Base.v "constructor", Base.v "arguments"],
      Base.caseData (Base.a "gslt:premise:constructor-declarations" [Base.v "constructor", Base.v "declarations"])
        sourceConstructorCases), (Base.v "unavailable", .symbol "None")]
private theorem source_type_shape : (envEquation .sourceType).body = Base.caseData (Base.v "source") sourceCases := by
  decide +kernel

/-- An explicit metavariable uses first-match rule typing. A constructor
requires exactly one physical authored declaration, including duplicates. -/
theorem source_type_returns (state : State) (language : LanguageDef) (rule : RewriteRule) (source : Pattern) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:source-type" [declarationsListValue language.terms, Base.ruleValue rule, Base.patternValue source]) state
      (Base.typeOptionValue (GeneralPremise.sourceType? language rule source)) := by
  let caller := envCaptured .sourceType [declarationsListValue language.terms, Base.ruleValue rule, Base.patternValue source]
  apply env_call .sourceType [] state _ _ _ rfl (Base.captured_closed _)
  rw [source_type_shape]
  cases source with
  | fvar name =>
      let selected := ("name", Base.stringValue name) :: caller
      let contextual := Base.assignmentRuleCaller rule selected
      apply Base.branch_returns caller selected state _ (Base.patternValue (.fvar name)) sourceCases
        (Base.caseData (Base.v "rule") sourceVariableCases) _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "source"
      · simp [sourceCases, Base.patternValue, InferenceCettaWire.encodePattern, selected, caller,
          envCaptured, EnvHelper.names, Base.stringValue, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · apply Base.branch_returns selected contextual state _ (Base.ruleValue rule) sourceVariableCases
          (Base.a "gslt:premise:type-context-lookup" [Base.v "name", Base.v "types"]) _
        · simpa [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
            variable_returns Base.runtime selected state "rule"
        · simp [sourceVariableCases, contextual, Base.assignmentRuleCaller, selected, caller,
            envCaptured, EnvHelper.names, Base.ruleValue, InferenceCettaWire.AuthoredRule.rewriteTerm,
            Base.stringValue, Base.typesValue, Base.patternValue, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup]
        · simpa only [GeneralPremise.sourceType?, GeneralPremise.lookupRuleType?, lookup_find_map] using
            type_context_lookup_captured_returns contextual state name rule.typeContext
              (Base.v "name") (Base.v "types") (by
                simp [contextual, Base.assignmentRuleCaller, selected, caller, envCaptured, EnvHelper.names,
                  applySubst, Subst.lookup])
  | apply constructor arguments =>
      let selected := [("arguments", Base.patternsValue arguments), ("constructor", Base.stringValue constructor)] ++ caller
      apply Base.branch_returns caller selected state _ (Base.patternValue (.apply constructor arguments)) sourceCases
        (Base.caseData (Base.a "gslt:premise:constructor-declarations" [Base.v "constructor", Base.v "declarations"])
          sourceConstructorCases) _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "source"
      · simp [sourceCases, Base.patternValue, InferenceCettaWire.encodePattern, selected, caller,
          envCaptured, EnvHelper.names, Base.stringValue, Base.patternsValue, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · have computed := constructor_declarations_captured_returns selected state constructor language.terms
          (Base.v "constructor") (Base.v "declarations") (by
            simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        cases found : language.terms.filter (fun declaration => declaration.label == constructor) with
        | nil =>
            let unavailable := ("ambiguous", declarationsListValue []) :: selected
            apply Base.branch_returns selected unavailable state _ (declarationsListValue []) sourceConstructorCases (.symbol "None") _
            · simpa only [found] using computed
            · simp [sourceConstructorCases, unavailable, selected, caller, envCaptured, EnvHelper.names,
                declarationsListValue, encodeList, CettaWireAtom.encode, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · simpa [GeneralPremise.sourceType?, found, Base.typeOptionValue, encodeOption, CettaWireAtom.encode] using
                symbol_returns Base.runtime unavailable state "None"
        | cons declaration declarations =>
            cases declarations with
            | nil =>
                let typed := [("parameters", parametersValue declaration.params), ("category", Base.stringValue declaration.category),
                  ("label", Base.stringValue declaration.label)] ++ selected
                apply Base.branch_returns selected typed state _ (declarationsListValue [declaration])
                  sourceConstructorCases sourceConstructorData _
                · simpa only [found] using computed
                · cases mode : declaration.collectionRepresentation <;> simp [mode, sourceConstructorCases, typed, selected, caller, envCaptured, EnvHelper.names,
                    declarationsListValue, InferenceCettaWire.AuthoredRule.typingDeclarationTerm, parametersValue,
                    Base.stringValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                    matchAtom, Subst.lookup]
                · have templated : PureData.Template Base.runtime sourceConstructorData := by
                    unfold sourceConstructorData
                    environment_template
                  simpa [sourceConstructorData, GeneralPremise.sourceType?, found, Base.typeOptionValue, encodeOption,
                    InferenceCettaWire.AuthoredRule.typeTerm, typed, selected, caller, envCaptured, EnvHelper.names,
                    applySubst, applySubst.applySubstList, Subst.lookup, Base.stringValue,
                    CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                    PureData.template_return Base.runtime typed state _ templated
            | cons next declarations =>
                let unavailable := ("ambiguous", declarationsListValue (declaration :: next :: declarations)) :: selected
                apply Base.branch_returns selected unavailable state _ (declarationsListValue (declaration :: next :: declarations))
                  sourceConstructorCases (.symbol "None") _
                · simpa only [found] using computed
                · cases mode : declaration.collectionRepresentation <;> simp [mode, sourceConstructorCases, unavailable, selected, caller, envCaptured, EnvHelper.names,
                    declarationsListValue, InferenceCettaWire.AuthoredRule.typingDeclarationTerm,
                    encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                    matchAtom, Subst.lookup]
                · simpa [GeneralPremise.sourceType?, found, Base.typeOptionValue, encodeOption, CettaWireAtom.encode] using
                    symbol_returns Base.runtime unavailable state "None"
  | bvar index | lambda binder body | multiLambda arity binders body | subst body replacement | collection kind elements rest =>
      let unavailable := ("unavailable", applySubst caller (Base.v "source")) :: caller
      apply Base.branch_returns caller unavailable state _ _ sourceCases (.symbol "None") _
      · exact variable_returns Base.runtime caller state "source"
      · simp [sourceCases, unavailable, caller, envCaptured, EnvHelper.names,
          Base.patternValue, InferenceCettaWire.encodePattern, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, applySubst]
      · simpa [GeneralPremise.sourceType?, Base.typeOptionValue, encodeOption, CettaWireAtom.encode] using
          symbol_returns Base.runtime unavailable state "None"

theorem source_type_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rule : RewriteRule) (source : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [declarationsListValue language.terms, Base.ruleValue rule, Base.patternValue source]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:source-type" [one, two, three]) state
      (Base.typeOptionValue (GeneralPremise.sourceType? language rule source)) :=
  env_capture .sourceType caller state _ _ _ rfl captured (source_type_returns state language rule source)

#print axioms source_type_returns
#print axioms source_type_captured_returns

private abbrev signatureValue (signature : GeneralPremise.Signature) : Atom := Base.encoded (signatureTerm signature)
private abbrev signaturesValue (signatures : List GeneralPremise.Signature) : Atom :=
  Base.encoded (encodeList signatureTerm signatures)
private abbrev modesValue (modes : List RelationArgMode) : Atom := Base.encoded (encodeList modeTerm modes)
private abbrev providerValue (provider : GeneralPremise.ProviderSnapshot) : Atom := Base.encoded (providerTerm provider)
private abbrev signatureOptionValue (signature : Option GeneralPremise.Signature) : Atom :=
  Base.encoded (encodeOption signatureTerm signature)

private theorem env_length_returns {α : Type} (encoder : α → Term)
    (caller : Subst) (state : State) (values : List α) (name : String)
    (captured : applySubst caller (Base.v name) = Base.encoded (encodeList encoder values)) :
    PureReturns Base.runtime caller state (Base.a "gslt:automata:length" [Base.v name]) state (Base.number values.length) := by
  have returned := MatchAutomataSourceExecution.length_captured_returns caller state
    (values.map encoder) (Base.v name) (by
      simpa only [MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map,
        Function.id_comp] using captured)
  have transferred := Base.previous_returns (by simp [codeWithin, expressionHeadWithin, Base.previousHeads])
    (RuleExecutionProgram.automata_captured_returns (by simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead]) returned)
  simpa only [List.length_map] using transferred

private theorem env_string_beq_returns (caller : Subst) (state : State)
    (left right one two : String)
    (first : applySubst caller (Base.v one) = Base.stringValue left)
    (second : applySubst caller (Base.v two) = Base.stringValue right) :
    PureReturns Base.runtime caller state (Base.a "==" [Base.v one, Base.v two]) state (Effects.boolean (left == right)) := by
  have compared : decide (left = right) = (left == right) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
  simpa only [compared] using env_string_equal_returns caller state left right one two first second

private def signaturesConsData : Atom :=
  Base.a "LCons" [Base.a "PremiseSignature" [Base.v "declared", Base.v "types", Base.v "modes"], Base.v "filtered"]
private def signaturesIncludedBody : Atom :=
  Base.a "let" [Base.v "filtered", Base.a "gslt:premise:signature-candidates" [Base.v "relation", Base.v "arity", Base.v "rest"],
    signaturesConsData]
private def signaturesArityBody : Atom :=
  Base.a "if" [Base.a "==" [Base.v "count", Base.v "arity"], signaturesIncludedBody,
    Base.a "gslt:premise:signature-candidates" [Base.v "relation", Base.v "arity", Base.v "rest"]]
private def signaturesConsBody : Atom :=
  Base.a "if" [Base.a "==" [Base.v "declared", Base.v "relation"],
    Base.a "let" [Base.v "count", Base.a "gslt:automata:length" [Base.v "types"], signaturesArityBody],
    Base.a "gslt:premise:signature-candidates" [Base.v "relation", Base.v "arity", Base.v "rest"]]
private def signaturesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (Base.a "LCons" [Base.a "PremiseSignature" [Base.v "declared", Base.v "types", Base.v "modes"], Base.v "rest"], signaturesConsBody),
    (Base.v "bad", .symbol "LNil")]
private theorem signatures_shape : (envEquation .signatureCandidates).body =
    Base.caseData (Base.v "signatures") signaturesCases := by decide +kernel

/-- Signature filtering retains physical order and duplicate declarations. -/
theorem signature_candidates_returns (state : State) (relation : String) (arity : Nat)
    (signatures : List GeneralPremise.Signature) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:signature-candidates" [Base.stringValue relation, Base.number arity, signaturesValue signatures]) state
      (signaturesValue (signatures.filter fun signature =>
        signature.relation == relation && signature.argumentTypes.length == arity)) := by
  induction signatures with
  | nil =>
      let caller := envCaptured .signatureCandidates [Base.stringValue relation, Base.number arity, signaturesValue []]
      apply env_call .signatureCandidates [] state _ _ _ rfl (Base.captured_closed _)
      rw [signatures_shape]
      apply Base.branch_returns caller caller state _ (.symbol "LNil") signaturesCases (.symbol "LNil") _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup, signaturesValue,
          encodeList, CettaWireAtom.encode] using variable_returns Base.runtime caller state "signatures"
      · simp [signaturesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns Base.runtime caller state "LNil"
  | cons signature signatures ih =>
      let filtered := signatures.filter fun candidate =>
        candidate.relation == relation && candidate.argumentTypes.length == arity
      let caller := envCaptured .signatureCandidates
        [Base.stringValue relation, Base.number arity, signaturesValue (signature :: signatures)]
      let selected := [("rest", signaturesValue signatures), ("modes", modesValue signature.modes),
        ("types", Base.boundValue signature.argumentTypes), ("declared", Base.stringValue signature.relation)] ++ caller
      let counted := ("count", Base.number signature.argumentTypes.length) :: selected
      let retained := ("filtered", signaturesValue filtered) :: counted
      apply env_call .signatureCandidates [] state _ _ _ rfl (Base.captured_closed _)
      rw [signatures_shape]
      apply Base.branch_returns caller selected state _ (signaturesValue (signature :: signatures))
        signaturesCases signaturesConsBody _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "signatures"
      · simp [signaturesCases, signatureTerm, signaturesValue, modesValue, Base.boundValue, Base.typesTerm,
          encodeList, selected, caller, envCaptured, EnvHelper.names, Base.stringValue, Base.number,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup]
      · have relationCheck := env_string_beq_returns selected state signature.relation relation "declared" "relation"
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        unfold signaturesConsBody
        apply Base.bool_if_returns selected state _ (signature.relation == relation) _ _ _ relationCheck
        cases sameRelation : signature.relation == relation with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, sameRelation, Bool.false_and]
            exact env_capture .signatureCandidates selected state _ _ _ rfl
              (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) ih
        | true =>
            simp only [↓reduceIte, List.filter_cons, sameRelation, Bool.true_and]
            apply let_returns Base.runtime selected counted state state state (Base.v "count")
              (Base.a "gslt:automata:length" [Base.v "types"]) signaturesArityBody _ _
            · exact env_length_returns InferenceCettaWire.AuthoredRule.typeTerm selected state
                signature.argumentTypes "types" (by
                  simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup, Base.boundValue])
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, counted, selected, caller, envCaptured, EnvHelper.names, Subst.lookup]
            · have arityCheck := Base.natural_equal_returns counted state signature.argumentTypes.length arity "count" "arity"
                (by simp [counted, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
                (by simp [counted, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
              unfold signaturesArityBody
              apply Base.bool_if_returns counted state _ (signature.argumentTypes.length == arity) _ _ _ arityCheck
              cases sameArity : signature.argumentTypes.length == arity with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact env_capture .signatureCandidates counted state _ _ _ rfl
                    (by simp [counted, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) ih
              | true =>
                  simp only [↓reduceIte]
                  unfold signaturesIncludedBody
                  apply let_returns Base.runtime counted retained state state state (Base.v "filtered")
                    (Base.a "gslt:premise:signature-candidates" [Base.v "relation", Base.v "arity", Base.v "rest"])
                    signaturesConsData (signaturesValue filtered) _
                  · exact env_capture .signatureCandidates counted state _ _ _ rfl
                      (by simp [counted, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) ih
                  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, retained, counted, selected, caller, envCaptured, EnvHelper.names, Subst.lookup]
                  · have templated : PureData.Template Base.runtime signaturesConsData := by
                      unfold signaturesConsData
                      environment_template
                    simpa [signaturesConsData, signaturesValue, signatureTerm, encodeList, filtered,
                      retained, counted, selected, caller, envCaptured, EnvHelper.names,
                      applySubst, applySubst.applySubstList, Subst.lookup, Base.boundValue, modesValue,
                      Base.stringValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return Base.runtime retained state _ templated

theorem signature_candidates_captured_returns (caller : Subst) (state : State)
    (relation : String) (arity : Nat) (signatures : List GeneralPremise.Signature) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [Base.stringValue relation, Base.number arity, signaturesValue signatures]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:signature-candidates" [one, two, three]) state
      (signaturesValue (signatures.filter fun signature =>
        signature.relation == relation && signature.argumentTypes.length == arity)) :=
  env_capture .signatureCandidates caller state _ _ _ rfl captured
    (signature_candidates_returns state relation arity signatures)

#print axioms signature_candidates_returns
#print axioms signature_candidates_captured_returns

private abbrev providerRowsValue (rows : List GeneralPremise.ProviderRow) : Atom :=
  Base.encoded (encodeList providerRowTerm rows)
private def signatureSomeData : Atom :=
  Base.a "Some" [Base.a "PremiseSignature" [Base.v "declared", Base.v "types", Base.v "modes"]]
private def signatureCountedBody : Atom :=
  Base.a "if" [Base.a "==" [Base.v "count", Base.v "arity"], signatureSomeData, .symbol "None"]
private def signatureSingletonBody : Atom :=
  Base.a "let" [Base.v "count", Base.a "gslt:automata:length" [Base.v "modes"], signatureCountedBody]
private def signatureSelectedCases : SpaceSemantics.Cases :=
  [(Base.a "LCons" [Base.a "PremiseSignature" [Base.v "declared", Base.v "types", Base.v "modes"], .symbol "LNil"], signatureSingletonBody),
    (Base.v "unavailable", .symbol "None")]
private def signatureProviderBody : Atom :=
  Base.caseData (Base.a "gslt:premise:signature-candidates" [Base.v "relation", Base.v "arity", Base.v "signatures"])
    signatureSelectedCases
private def signatureProviderCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseProvider" [Base.v "signatures", Base.v "rows"], signatureProviderBody), (Base.v "bad", .symbol "None")]
private theorem signature_shape : (envEquation .signature).body =
    Base.caseData (Base.v "provider") signatureProviderCases := by decide +kernel

/-- A signature is available only for a unique physical candidate with a
matching number of execution modes. -/
theorem signature_returns (state : State) (provider : GeneralPremise.ProviderSnapshot)
    (relation : String) (arity : Nat) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:signature" [Base.stringValue relation, Base.number arity, providerValue provider]) state
      (signatureOptionValue (GeneralPremise.signature? provider relation arity)) := by
  let caller := envCaptured .signature [Base.stringValue relation, Base.number arity, providerValue provider]
  let parsed := [("rows", providerRowsValue provider.rows), ("signatures", signaturesValue provider.signatures)] ++ caller
  apply env_call .signature [] state _ _ _ rfl (Base.captured_closed _)
  rw [signature_shape]
  apply Base.branch_returns caller parsed state _ (providerValue provider)
    signatureProviderCases signatureProviderBody _
  · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "provider"
  · simp [signatureProviderCases, providerValue, providerTerm, providerRowsValue, signaturesValue,
      parsed, caller, envCaptured, EnvHelper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup]
  · unfold signatureProviderBody
    have computed := signature_candidates_captured_returns parsed state relation arity provider.signatures
      (Base.v "relation") (Base.v "arity") (Base.v "signatures") (by
        simp [parsed, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
    cases found : provider.signatures.filter (fun signature =>
        signature.relation == relation && signature.argumentTypes.length == arity) with
    | nil =>
        let unavailable := ("unavailable", signaturesValue []) :: parsed
        apply Base.branch_returns parsed unavailable state _ (signaturesValue []) signatureSelectedCases (.symbol "None") _
        · simpa only [found] using computed
        · simp [signatureSelectedCases, unavailable, parsed, caller, envCaptured, EnvHelper.names, Subst.lookup, signaturesValue, encodeList,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, CettaWireAtom.encode]
        · simpa [GeneralPremise.signature?, found, signatureOptionValue, encodeOption, CettaWireAtom.encode] using
            symbol_returns Base.runtime unavailable state "None"
    | cons signature signatures =>
        cases signatures with
        | nil =>
            let selected := [("modes", modesValue signature.modes), ("types", Base.boundValue signature.argumentTypes),
              ("declared", Base.stringValue signature.relation)] ++ parsed
            let counted := ("count", Base.number signature.modes.length) :: selected
            apply Base.branch_returns parsed selected state _ (signaturesValue [signature])
              signatureSelectedCases signatureSingletonBody _
            · simpa only [found] using computed
            · simp [signatureSelectedCases, signaturesValue, signatureTerm, Base.boundValue, Base.typesTerm, modesValue,
                selected, parsed, caller, envCaptured, EnvHelper.names, Subst.lookup, encodeList, Base.stringValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · unfold signatureSingletonBody
              apply let_returns Base.runtime selected counted state state state (Base.v "count")
                (Base.a "gslt:automata:length" [Base.v "modes"]) signatureCountedBody (Base.number signature.modes.length) _
              · exact env_length_returns modeTerm selected state signature.modes "modes" (by
                  simp [selected, modesValue, applySubst, Subst.lookup])
              · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, counted, selected, parsed, caller, envCaptured, EnvHelper.names, Subst.lookup]
              · have tested := Base.natural_equal_returns counted state signature.modes.length arity "count" "arity"
                  (by simp [counted, applySubst, Subst.lookup])
                  (by simp [counted, selected, parsed, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
                unfold signatureCountedBody
                apply Base.bool_if_returns counted state _ (signature.modes.length == arity) _ _ _ tested
                cases sameModes : signature.modes.length == arity with
                | false =>
                    simpa [GeneralPremise.signature?, found, sameModes, signatureOptionValue, encodeOption,
                      CettaWireAtom.encode] using symbol_returns Base.runtime counted state "None"
                | true =>
                    have templated : PureData.Template Base.runtime signatureSomeData := by
                      unfold signatureSomeData
                      environment_template
                    simpa [signatureSomeData, GeneralPremise.signature?, found, sameModes,
                      signatureOptionValue, encodeOption, signatureTerm, counted, selected, parsed, caller,
                      envCaptured, EnvHelper.names, applySubst, applySubst.applySubstList, Subst.lookup,
                      Base.boundValue, modesValue, Base.stringValue, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                      PureData.template_return Base.runtime counted state _ templated
        | cons next signatures =>
            let unavailable := ("unavailable", signaturesValue (signature :: next :: signatures)) :: parsed
            apply Base.branch_returns parsed unavailable state _ (signaturesValue (signature :: next :: signatures))
              signatureSelectedCases (.symbol "None") _
            · simpa only [found] using computed
            · simp [signatureSelectedCases, unavailable, parsed, caller, envCaptured, EnvHelper.names, signaturesValue, signatureTerm, encodeList,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
            · simpa [GeneralPremise.signature?, found, signatureOptionValue, encodeOption, CettaWireAtom.encode] using
                symbol_returns Base.runtime unavailable state "None"

theorem signature_captured_returns (caller : Subst) (state : State)
    (provider : GeneralPremise.ProviderSnapshot) (relation : String) (arity : Nat) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [Base.stringValue relation, Base.number arity, providerValue provider]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:signature" [one, two, three]) state
      (signatureOptionValue (GeneralPremise.signature? provider relation arity)) :=
  env_capture .signature caller state _ _ _ rfl captured (signature_returns state provider relation arity)

#print axioms signature_returns
#print axioms signature_captured_returns

private def valuesEmptyTypesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .grounded (.bool true)), (Base.v "mismatch", .grounded (.bool false))]
private def valuesConsBody : Atom :=
  Base.a "if" [Base.a "gslt:premise:open-well-sorted" [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "type", Base.v "value"],
    Base.a "gslt:premise:check-values" [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "restValues", Base.v "restTypes"],
    .grounded (.bool false)]
private def valuesConsTypesCases : SpaceSemantics.Cases :=
  [(Base.a "LCons" [Base.v "type", Base.v "restTypes"], valuesConsBody), (Base.v "mismatch", .grounded (.bool false))]
private def valuesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", Base.caseData (Base.v "types") valuesEmptyTypesCases),
    (Base.a "LCons" [Base.v "value", Base.v "restValues"], Base.caseData (Base.v "types") valuesConsTypesCases),
    (Base.v "bad", .grounded (.bool false))]
private theorem values_shape : (envEquation .values).body = Base.caseData (Base.v "values") valuesCases := by
  decide +kernel

/-- Heterogeneous provider values use the original open typing check at each
physical position and reject unequal argument lengths. -/
theorem check_values_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (values : List Pattern) (types : List TypeExpr) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:check-values" [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound,
        Base.patternsValue values, Base.boundValue types]) state
      (Effects.boolean (GeneralPremise.checkValues language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound values types)) := by
  induction values generalizing types with
  | nil =>
      let caller := envCaptured .values
        [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound, Base.patternsValue [], Base.boundValue types]
      apply env_call .values [] state _ _ _ rfl (Base.captured_closed _)
      rw [values_shape]
      apply Base.branch_returns caller caller state _ (.symbol "LNil") valuesCases
        (Base.caseData (Base.v "types") valuesEmptyTypesCases) _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup, Base.patternsValue,
          Base.patternsTerm, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          variable_returns Base.runtime caller state "values"
      · simp [valuesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · cases types with
        | nil =>
            apply Base.branch_returns caller caller state _ (.symbol "LNil") valuesEmptyTypesCases (.grounded (.bool true)) _
            · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup, Base.boundValue,
                Base.typesTerm, encodeList, CettaWireAtom.encode] using variable_returns Base.runtime caller state "types"
            · simp [valuesEmptyTypesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact grounded_returns Base.runtime caller state (.bool true)
        | cons type types =>
            let mismatch := ("mismatch", Base.boundValue (type :: types)) :: caller
            apply Base.branch_returns caller mismatch state _ (Base.boundValue (type :: types))
              valuesEmptyTypesCases (.grounded (.bool false)) _
            · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
                variable_returns Base.runtime caller state "types"
            · simp [valuesEmptyTypesCases, mismatch, caller, envCaptured, EnvHelper.names, Subst.lookup, Base.boundValue, Base.typesTerm, encodeList, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact grounded_returns Base.runtime mismatch state (.bool false)
  | cons value values ih =>
      let caller := envCaptured .values
        [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound, Base.patternsValue (value :: values), Base.boundValue types]
      let selected := [("restValues", Base.patternsValue values), ("value", Base.patternValue value)] ++ caller
      apply env_call .values [] state _ _ _ rfl (Base.captured_closed _)
      rw [values_shape]
      apply Base.branch_returns caller selected state _ (Base.patternsValue (value :: values)) valuesCases
        (Base.caseData (Base.v "types") valuesConsTypesCases) _
      · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
          variable_returns Base.runtime caller state "values"
      · simp [valuesCases, Base.patternsValue, Base.patternsTerm, InferenceCettaWire.encodePatterns, Base.patternValue,
          selected, caller, envCaptured, EnvHelper.names, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · cases types with
        | nil =>
            let mismatch := ("mismatch", .symbol "LNil") :: selected
            apply Base.branch_returns selected mismatch state _ (.symbol "LNil") valuesConsTypesCases (.grounded (.bool false)) _
            · simpa [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup,
                Base.boundValue, Base.typesTerm, encodeList, CettaWireAtom.encode] using variable_returns Base.runtime selected state "types"
            · simp [valuesConsTypesCases, mismatch, selected, caller, envCaptured, EnvHelper.names, Subst.lookup, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact grounded_returns Base.runtime mismatch state (.bool false)
        | cons type types =>
            let typed := [("restTypes", Base.boundValue types), ("type", Base.typeValue type)] ++ selected
            apply Base.branch_returns selected typed state _ (Base.boundValue (type :: types)) valuesConsTypesCases valuesConsBody _
            · simpa [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
                variable_returns Base.runtime selected state "types"
            · simp [valuesConsTypesCases, typed, selected, caller, envCaptured, EnvHelper.names, Subst.lookup, Base.boundValue, Base.typesTerm, Base.typeValue, encodeList,
                CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
            · have tested := Base.previous_returns (by decide +kernel)
                (DeclarationTyping.check_open_pattern_captured_returns typed state language free bound type value
                  (Base.v "declarations") (Base.v "free") (Base.v "bound") (Base.v "type") (Base.v "value") (by
                    simp [typed, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup, Base.typesTerm, DeclarationTyping.boundContextTerm]))
              unfold valuesConsBody
              apply Base.bool_if_returns typed state _ _ _ _ _ tested
              cases checked : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted language
                  (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound type value with
              | false =>
                  simpa only [GeneralPremise.checkValues, checked, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Effects.boolean] using
                    grounded_returns Base.runtime typed state (.bool false)
              | true =>
                  simp only [GeneralPremise.checkValues, checked, Bool.true_and, ↓reduceIte]
                  exact env_capture .values typed state _ _ _ rfl
                    (by simp [typed, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup]) (ih types)

theorem check_values_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (values : List Pattern) (types : List TypeExpr)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound, Base.patternsValue values, Base.boundValue types]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:check-values" [one, two, three, four, five]) state
      (Effects.boolean (GeneralPremise.checkValues language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound values types)) :=
  env_capture .values caller state _ _ _ rfl captured (check_values_returns state language free bound values types)

#print axioms check_values_returns
#print axioms check_values_captured_returns

private abbrev providerRowValue (row : GeneralPremise.ProviderRow) : Atom := Base.encoded (providerRowTerm row)
private def rowCheckedBody : Atom :=
  Base.a "if" [Base.a "==" [Base.v "relation", Base.v "declared"],
    Base.a "gslt:premise:check-values" [Base.v "declarations", Base.v "free", Base.v "bound", Base.v "values", Base.v "types"],
    .grounded (.bool false)]
private def rowCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseProviderRow" [Base.v "relation", Base.v "values"], rowCheckedBody), (Base.v "badRow", .grounded (.bool false))]
private def rowSignatureBody : Atom := Base.caseData (Base.v "row") rowCases
private def rowSignatureCases : SpaceSemantics.Cases :=
  [(Base.a "PremiseSignature" [Base.v "declared", Base.v "types", Base.v "modes"], rowSignatureBody),
    (Base.v "badSignature", .grounded (.bool false))]
private theorem row_shape : (envEquation .row).body = Base.caseData (Base.v "signature") rowSignatureCases := by
  decide +kernel

/-- Provider row validation checks its relation and all typed values in the
caller context without deduplicating or normalizing the snapshot. -/
theorem check_row_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (signature : GeneralPremise.Signature) (row : GeneralPremise.ProviderRow) :
    PureReturns Base.runtime [] state
      (Base.a "gslt:premise:check-row" [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound,
        signatureValue signature, providerRowValue row]) state
      (Effects.boolean (GeneralPremise.checkRow language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound signature row)) := by
  let caller := envCaptured .row [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound,
    signatureValue signature, providerRowValue row]
  let selected := [("modes", modesValue signature.modes), ("types", Base.boundValue signature.argumentTypes),
    ("declared", Base.stringValue signature.relation)] ++ caller
  let valued := [("values", Base.patternsValue row.values), ("relation", Base.stringValue row.relation)] ++ selected
  apply env_call .row [] state _ _ _ rfl (Base.captured_closed _)
  rw [row_shape]
  apply Base.branch_returns caller selected state _ (signatureValue signature) rowSignatureCases rowSignatureBody _
  · simpa [caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
      variable_returns Base.runtime caller state "signature"
  · simp [rowSignatureCases, signatureValue, signatureTerm, modesValue, Base.boundValue, Base.typesTerm,
      selected, caller, envCaptured, EnvHelper.names, Base.stringValue, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup]
  · unfold rowSignatureBody
    apply Base.branch_returns selected valued state _ (providerRowValue row) rowCases rowCheckedBody _
    · simpa [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
        variable_returns Base.runtime selected state "row"
    · simp [rowCases, providerRowValue, providerRowTerm, Base.patternsValue, Base.patternsTerm, valued, selected, caller, envCaptured, EnvHelper.names, Subst.lookup,
        Base.stringValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
    · have tested := env_string_beq_returns valued state row.relation signature.relation "relation" "declared"
        (by simp [valued, applySubst, Subst.lookup])
        (by simp [valued, selected, applySubst, Subst.lookup])
      unfold rowCheckedBody
      apply Base.bool_if_returns valued state _ (row.relation == signature.relation) _ _ _ tested
      cases same : row.relation == signature.relation with
      | false =>
          simpa only [GeneralPremise.checkRow, same, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Effects.boolean] using
            grounded_returns Base.runtime valued state (.bool false)
      | true =>
          simp only [GeneralPremise.checkRow, same, Bool.true_and, ↓reduceIte]
          exact check_values_captured_returns valued state language free bound row.values signature.argumentTypes
            (Base.v "declarations") (Base.v "free") (Base.v "bound") (Base.v "values") (Base.v "types") (by
              simp [valued, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])

theorem check_row_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (signature : GeneralPremise.Signature) (row : GeneralPremise.ProviderRow) (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [Base.declarationsValue language, Base.freeValue free, Base.boundValue bound, signatureValue signature, providerRowValue row]) :
    PureReturns Base.runtime caller state (Base.a "gslt:premise:check-row" [one, two, three, four, five]) state
      (Effects.boolean (GeneralPremise.checkRow language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound signature row)) :=
  env_capture .row caller state _ _ _ rfl captured (check_row_returns state language free bound signature row)

#print axioms check_row_returns
#print axioms check_row_captured_returns

attribute [local simp] Base.a Base.v Base.encoded Base.number Base.patternValue Base.patternsValue

private theorem ground_named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns Base.runtime caller state expression state value)
    (continued : PureReturns Base.runtime ((name, value) :: caller) state body state answer) :
    PureReturns Base.runtime caller state (Base.a "let" [Base.v name, expression, body]) state answer := by
  apply let_returns Base.runtime caller ((name, value) :: caller) state state state
    (Base.v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem ground_add_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (Base.v first) = Base.number left)
    (rightCaptured : applySubst caller (Base.v second) = Base.number right) :
    PureReturns Base.runtime caller state (Base.a "+" [Base.v first, Base.v second]) state (Base.number (left + right)) := by
  apply native_variable_call_returns Base.runtime caller state state "+" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simpa only [Base.number, Base.encoded, CettaWireAtom.encode, Int.natCast_add] using
    StdLib.integer_addition state (left : Int) (right : Int)

private theorem ground_lt_variables_returns (caller : Subst) (state : State) (left right : Nat)
    (first second : String)
    (leftCaptured : applySubst caller (Base.v first) = Base.number left)
    (rightCaptured : applySubst caller (Base.v second) = Base.number right) :
    PureReturns Base.runtime caller state (Base.a "<" [Base.v first, Base.v second]) state
      (Effects.boolean (decide (left < right))) := by
  apply native_variable_call_returns Base.runtime caller state state "<" [first, second] _
    (by decide) (by decide) _ (by decide)
  simp only [List.map_cons, List.map_nil, leftCaptured, rightCaptured]
  simp [Base.number, Base.encoded, CettaWireAtom.encode]

private inductive GroundForm where | pattern | patterns

private def GroundForm.helper : GroundForm → EnvHelper
  | .pattern => .ground
  | .patterns => .groundList

private def GroundForm.formal : GroundForm → String
  | .pattern => "pattern"
  | .patterns => "patterns"

attribute [local simp] GroundForm.helper GroundForm.formal

private def groundBinderBody (many : Bool) : Atom :=
  Base.a "let" [Base.v "next", Base.a "+" [Base.v "depth", if many then Base.v "arity" else Base.number 1],
    Base.a EnvHelper.ground.head [Base.v "next", Base.v "body"]]

private def groundSubstBody : Atom :=
  Base.a "let" [Base.v "next", Base.a "+" [Base.v "depth", Base.number 1],
    Base.a "if" [Base.a EnvHelper.ground.head [Base.v "next", Base.v "body"],
      Base.a EnvHelper.ground.head [Base.v "depth", Base.v "replacement"], (Effects.boolean false)]]

private def groundListBody : Atom :=
  Base.a "if" [Base.a EnvHelper.ground.head [Base.v "depth", Base.v "pattern"],
    Base.a EnvHelper.groundList.head [Base.v "depth", Base.v "rest"], (Effects.boolean false)]

private def groundCollectionCases : SpaceSemantics.Cases :=
  [(.symbol "RNone", Base.a "gslt:premise:ground-list-at" [Base.v "depth", Base.v "elements"]),
    (Base.v "open", Effects.boolean false)]
private def groundCollectionBody : Atom := Base.caseData (Base.v "rest") groundCollectionCases

private def groundCases : GroundForm → SpaceSemantics.Cases
  | .pattern =>
      [(Base.a "Var" [Base.v "index"], Base.a "<" [Base.v "index", Base.v "depth"]),
       (Base.a "FVar" [Base.v "name"], (Effects.boolean false)),
       (Base.a "PApp" [Base.v "head", Base.v "children"], Base.a EnvHelper.groundList.head [Base.v "depth", Base.v "children"]),
       (Base.a "PLam" [Base.v "binder", Base.v "body"], groundBinderBody false),
       (Base.a "PMultiLam" [Base.v "arity", Base.v "binders", Base.v "body"], groundBinderBody true),
       (Base.a "PSubst" [Base.v "body", Base.v "replacement"], groundSubstBody),
       (Base.a "PCollection" [Base.v "kind", Base.v "elements", Base.v "rest"],
         groundCollectionBody),
       (Base.v "invalid", (Effects.boolean false))]
  | .patterns =>
      [(.symbol "LNil", (Effects.boolean true)),
       (Base.a "LCons" [Base.v "pattern", Base.v "rest"], groundListBody),
       (Base.v "invalid", (Effects.boolean false))]

private theorem ground_shape (form : GroundForm) : (envEquation form.helper).body =
    Base.a "case" [Base.v form.formal,
      .expression ((groundCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> decide +kernel

private theorem ground_case_returns (form : GroundForm) (state : State) (depth : Nat)
    (value : Atom) (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (envCaptured form.helper [Base.number depth, value])
      value (groundCases form) = some (selected, body))
    (returned : PureReturns Base.runtime selected state body state answer) :
    PureReturns Base.runtime [] state (Base.a form.helper.head [Base.number depth, value]) state answer := by
  apply env_call form.helper [] state [Base.number depth, value] [Base.number depth, value] answer
    (by cases form <;> rfl) (by simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]) ?_
  rw [ground_shape]
  apply case_returns Base.runtime (envCaptured form.helper [Base.number depth, value]) selected state state state
    (Base.v form.formal) value body answer _ (groundCases form) (read_cases_encoded _) _ matched returned
  cases form with
  | pattern =>
      simpa [envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
        variable_returns Base.runtime (envCaptured .ground [Base.number depth, value]) state "pattern"
  | patterns =>
      simpa [envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
        variable_returns Base.runtime (envCaptured .groundList [Base.number depth, value]) state "patterns"

private theorem ground_capture (form : GroundForm) (caller : Subst) (state : State)
    (depth : Nat) (value one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [Base.number depth, value])
    (returned : PureReturns Base.runtime [] state (Base.a form.helper.head [Base.number depth, value]) state answer) :
    PureReturns Base.runtime caller state (Base.a form.helper.head [one, two]) state answer :=
  env_capture form.helper caller state [one, two] [Base.number depth, value] answer
    (by cases form <;> rfl) captured returned

private theorem ground_list_from_elements (state : State) (depth : Nat) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns Base.runtime [] state
      (Base.a EnvHelper.ground.head [Base.number depth, Base.patternValue pattern]) state
      (Effects.boolean (pattern.isGroundAt depth))) :
    PureReturns Base.runtime [] state (Base.a EnvHelper.groundList.head [Base.number depth, Base.patternsValue patterns]) state
      (Effects.boolean (Pattern.isGroundListAt depth patterns)) := by
  induction patterns with
  | nil =>
      simp only [Base.patternsValue, Base.encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
        Pattern.isGroundListAt]
      change PureReturns Base.runtime [] state (Base.a EnvHelper.groundList.head [Base.number depth, .symbol "LNil"])
        state (Effects.boolean true)
      apply ground_case_returns .patterns state depth (.symbol "LNil")
        (envCaptured .groundList [Base.number depth, .symbol "LNil"]) ((Effects.boolean true))
      · simp [groundCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns Base.runtime _ state (.bool true)
  | cons pattern patterns ih =>
      let caller := envCaptured .groundList [Base.number depth, Base.patternsValue (pattern :: patterns)]
      let selected := ("rest", Base.patternsValue patterns) :: ("pattern", Base.patternValue pattern) :: caller
      apply ground_case_returns .patterns state depth (Base.patternsValue (pattern :: patterns))
        selected groundListBody
      · simp [groundCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · apply Base.bool_if_returns selected state _ (pattern.isGroundAt depth) _ _ _
        · exact ground_capture .pattern selected state depth (Base.patternValue pattern) (Base.v "depth")
            (Base.v "pattern") _ (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst,
              Subst.lookup]) (elements pattern (by simp))
        · cases scopeResult : pattern.isGroundAt depth with
          | false =>
              simpa [Effects.boolean, groundListBody, scopeResult, Pattern.isGroundListAt] using
                grounded_returns Base.runtime selected state (.bool false)
          | true =>
              simpa [Effects.boolean, groundListBody, scopeResult, Pattern.isGroundListAt] using
                ground_capture .patterns selected state depth (Base.patternsValue patterns) (Base.v "depth")
                  (Base.v "rest") _ (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst,
                    Subst.lookup]) (ih (fun child member => elements child (List.mem_cons_of_mem _ member)))

theorem ground_at_returns (state : State) (pattern : Pattern) (depth : Nat) :
    PureReturns Base.runtime [] state (Atom.expression (Atom.symbol "gslt:premise:ground-at" :: [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePattern pattern)])) state
      (Effects.boolean (pattern.isGroundAt depth)) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.bvar index)]
      let selected := ("index", Base.number index) :: caller
      apply ground_case_returns .pattern state depth (Base.patternValue (.bvar index)) selected
        (Base.a "<" [Base.v "index", Base.v "depth"])
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · exact ground_lt_variables_returns selected state index depth "index" "depth"
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
          (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
  | hfvar name =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.fvar name)]
      let selected := ("name", Base.encoded (.string name)) :: caller
      apply ground_case_returns .pattern state depth (Base.patternValue (.fvar name)) selected ((Effects.boolean false))
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · exact grounded_returns Base.runtime selected state (.bool false)
  | happly head children ih =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.apply head children)]
      let selected := ("children", Base.patternsValue children) :: ("head", Base.encoded (.string head)) :: caller
      apply ground_case_returns .pattern state depth (Base.patternValue (.apply head children)) selected
        (Base.a EnvHelper.groundList.head [Base.v "depth", Base.v "children"])
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · exact ground_capture .patterns selected state depth (Base.patternsValue children) (Base.v "depth")
          (Base.v "children") _ (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst,
            Subst.lookup]) (ground_list_from_elements state depth children (fun child member => ih child member depth))
  | hlambda binder body ih =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.lambda binder body)]
      let selected := ("body", Base.patternValue body) ::
        ("binder", Base.encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      let bound := ("next", Base.number (depth + 1)) :: selected
      apply ground_case_returns .pattern state depth (Base.patternValue (.lambda binder body)) selected
        (groundBinderBody false)
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · apply ground_named_let_returns selected state "next" _ (Base.number (depth + 1))
        · simp [selected, caller, envCaptured, EnvHelper.names, Subst.lookup]
        · exact Base.add_one_returns selected state depth "depth"
            (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        · exact ground_capture .pattern bound state (depth + 1) (Base.patternValue body)
            (Base.v "next") (Base.v "body") _ (by simp [bound, selected, caller, envCaptured, EnvHelper.names,
              applySubst, Subst.lookup]) (ih (depth + 1))
  | hmultiLambda arity binders body ih =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.multiLambda arity binders body)]
      let selected := ("body", Base.patternValue body) ::
        ("binders", Base.encoded (InferenceCettaWire.encodeList Term.string binders)) :: ("arity", Base.number arity) :: caller
      let bound := ("next", Base.number (depth + arity)) :: selected
      apply ground_case_returns .pattern state depth (Base.patternValue (.multiLambda arity binders body)) selected
        (groundBinderBody true)
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · apply ground_named_let_returns selected state "next" _ (Base.number (depth + arity))
        · simp [selected, caller, envCaptured, EnvHelper.names, Subst.lookup]
        · exact ground_add_variables_returns selected state depth arity "depth" "arity"
            (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
            (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        · exact ground_capture .pattern bound state (depth + arity) (Base.patternValue body)
            (Base.v "next") (Base.v "body") _ (by simp [bound, selected, caller, envCaptured, EnvHelper.names,
              applySubst, Subst.lookup]) (ih (depth + arity))
  | hsubst body replacement bodyIH replacementIH =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.subst body replacement)]
      let selected := ("replacement", Base.patternValue replacement) :: ("body", Base.patternValue body) :: caller
      let bound := ("next", Base.number (depth + 1)) :: selected
      apply ground_case_returns .pattern state depth (Base.patternValue (.subst body replacement)) selected groundSubstBody
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · apply ground_named_let_returns selected state "next" _ (Base.number (depth + 1))
        · simp [selected, caller, envCaptured, EnvHelper.names, Subst.lookup]
        · exact Base.add_one_returns selected state depth "depth"
            (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
        · apply Base.bool_if_returns bound state _ (body.isGroundAt (depth + 1))
          · exact ground_capture .pattern bound state (depth + 1) (Base.patternValue body)
              (Base.v "next") (Base.v "body") _ (by simp [bound, selected, caller, envCaptured, EnvHelper.names,
                applySubst, Subst.lookup]) (bodyIH (depth + 1))
          · cases scopeResult : body.isGroundAt (depth + 1) with
            | false =>
                simpa [Effects.boolean, scopeResult, Pattern.isGroundAt] using grounded_returns Base.runtime bound state (.bool false)
            | true =>
                simpa [Effects.boolean, scopeResult, Pattern.isGroundAt] using
                  ground_capture .pattern bound state depth (Base.patternValue replacement)
                    (Base.v "depth") (Base.v "replacement") _
                    (by simp [bound, selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup])
                    (replacementIH depth)
  | hcollection kind elements rest ih =>
      let caller := envCaptured .ground [Base.number depth, Base.patternValue (.collection kind elements rest)]
      let selected := ("rest", Base.encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", Base.patternsValue elements) :: ("kind", Base.encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      apply ground_case_returns .pattern state depth (Base.patternValue (.collection kind elements rest)) selected
        groundCollectionBody
      · simp [groundCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller,
          envCaptured, EnvHelper.names]
      · unfold groundCollectionBody
        cases rest with
        | none =>
            apply Base.branch_returns selected selected state _ (.symbol "RNone") groundCollectionCases
              (Base.a "gslt:premise:ground-list-at" [Base.v "depth", Base.v "elements"]) _
            · simpa [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup,
                InferenceCettaWire.encodeRest, CettaWireAtom.encode] using variable_returns Base.runtime selected state "rest"
            · simp [groundCollectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa only [Pattern.isGroundAt, Option.isNone_none, Bool.and_true, GroundForm.helper, EnvHelper.head] using
                ground_capture .patterns selected state depth (Base.patternsValue elements) (Base.v "depth")
                  (Base.v "elements") _ (by simp [selected, caller, envCaptured, EnvHelper.names, applySubst,
                    Subst.lookup]) (ground_list_from_elements state depth elements (fun child member => ih child member depth))
        | some name =>
            let opened := ("open", Base.encoded (InferenceCettaWire.encodeRest (some name))) :: selected
            apply Base.branch_returns selected opened state _ (Base.encoded (InferenceCettaWire.encodeRest (some name)))
              groundCollectionCases (Effects.boolean false) _
            · simpa [selected, caller, envCaptured, EnvHelper.names, applySubst, Subst.lookup] using
                variable_returns Base.runtime selected state "rest"
            · simp [groundCollectionCases, opened, selected, caller, envCaptured, EnvHelper.names,
                InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · simpa only [Pattern.isGroundAt, Option.isNone_some, Bool.and_false, Effects.boolean] using
                grounded_returns Base.runtime opened state (.bool false)

theorem ground_list_at_returns (state : State) (patterns : List Pattern) (depth : Nat) :
    PureReturns Base.runtime [] state (Atom.expression (Atom.symbol "gslt:premise:ground-list-at" :: [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns patterns)])) state
      (Effects.boolean (Pattern.isGroundListAt depth patterns)) :=
  ground_list_from_elements state depth patterns (fun pattern _ => ground_at_returns state pattern depth)

theorem ground_at_captured_returns (caller : Subst) (state : State) (pattern : Pattern) (depth : Nat)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePattern pattern)]) :
    PureReturns Base.runtime caller state (Atom.expression (Atom.symbol "gslt:premise:ground-at" :: [one, two])) state
      (Effects.boolean (pattern.isGroundAt depth)) :=
  ground_capture .pattern caller state depth (Base.patternValue pattern) one two _ captured
    (ground_at_returns state pattern depth)

theorem ground_list_at_captured_returns (caller : Subst) (state : State) (patterns : List Pattern) (depth : Nat)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [CettaWireAtom.encode (.natural depth), CettaWireAtom.encode (InferenceCettaWire.encodePatterns patterns)]) :
    PureReturns Base.runtime caller state (Atom.expression (Atom.symbol "gslt:premise:ground-list-at" :: [one, two])) state
      (Effects.boolean (Pattern.isGroundListAt depth patterns)) :=
  ground_capture .patterns caller state depth (Base.patternsValue patterns) one two _ captured
    (ground_list_at_returns state patterns depth)

#print axioms ground_at_returns
#print axioms ground_list_at_returns
#print axioms ground_at_captured_returns
#print axioms ground_list_at_captured_returns


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.GeneralExecution
