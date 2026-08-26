import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# ParserPack and occurrence-preserving JSON native-type diagnostics

The parser machine and JSON value carrier are separate authored languages.
ParserPack produces a complete packed forest or an explicit rejection/fault;
a later elaboration maps a selected JSON CST into the occurrence-preserving
value carrier.  Neither generalized parser backend defines these semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.JSONParserPackNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

private def v (name : String) : Pattern := .fvar name
private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments
private def query (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

private def running (grammar input worklist forest fuel : Pattern) : Pattern :=
  a "parser:running" [grammar, input, worklist, forest, fuel]

private def halted (outcome : Pattern) : Pattern :=
  a "parser:halted" [outcome]

/-- Backend-neutral operational ParserPack target.  `Forest` is deliberately
not quotiented to one tree: ambiguity and derivation multiplicity remain in
the authored result. -/
def parserPack : LanguageDef := {
  name := "ParserPack"
  types := [
    "Grammar", "Input", "Worklist", "Forest", "Fuel", "Diagnostic",
    "Fault", "Outcome", "Config"]
  terms := [
    ctor "parser:fuel-zero" "Fuel" [],
    ctor "parser:fuel-succ" "Fuel" [("prior", "Fuel")],
    ctor "parser:parse" "Config"
      [("grammar", "Grammar"), ("input", "Input"), ("fuel", "Fuel")]
      (some .rewrite),
    ctor "parser:running" "Config"
      [("grammar", "Grammar"), ("input", "Input"),
       ("worklist", "Worklist"), ("forest", "Forest"),
       ("fuel", "Fuel")] (some .rewrite),
    ctor "parser:completed" "Outcome" [("forest", "Forest")],
    ctor "parser:rejected" "Outcome" [("diagnostic", "Diagnostic")],
    ctor "parser:engine-fault" "Outcome" [("fault", "Fault")],
    ctor "parser:resource-fault" "Outcome" [("fault", "Fault")],
    ctor "parser:halted" "Config" [("outcome", "Outcome")]
  ]
  equations := []
  rewrites := [
    { name := "parser:initialize"
      typeContext := [
        ("grammar", .base "Grammar"), ("input", .base "Input"),
        ("fuel", .base "Fuel"), ("worklist", .base "Worklist"),
        ("forest", .base "Forest")]
      premises := [query "ParserPackInitialize"
        [v "grammar", v "input", v "worklist", v "forest"]]
      left := a "parser:parse" [v "grammar", v "input", v "fuel"]
      right := running (v "grammar") (v "input") (v "worklist")
        (v "forest") (v "fuel") },
    { name := "parser:advance"
      typeContext := [
        ("grammar", .base "Grammar"), ("input", .base "Input"),
        ("worklist", .base "Worklist"), ("nextWorklist", .base "Worklist"),
        ("forest", .base "Forest"), ("nextForest", .base "Forest"),
        ("fuel", .base "Fuel"), ("nextFuel", .base "Fuel")]
      premises := [
        query "ParserPackConsumeFuel" [v "fuel", v "nextFuel"],
        query "ParserPackAdvance"
          [v "grammar", v "input", v "worklist", v "forest",
           v "nextWorklist", v "nextForest"]]
      left := running (v "grammar") (v "input") (v "worklist")
        (v "forest") (v "fuel")
      right := running (v "grammar") (v "input") (v "nextWorklist")
        (v "nextForest") (v "nextFuel") },
    { name := "parser:complete"
      typeContext := [
        ("grammar", .base "Grammar"), ("input", .base "Input"),
        ("worklist", .base "Worklist"), ("forest", .base "Forest"),
        ("fuel", .base "Fuel"), ("nextFuel", .base "Fuel")]
      premises := [
        query "ParserPackConsumeFuel" [v "fuel", v "nextFuel"],
        query "ParserPackComplete"
          [v "grammar", v "input", v "worklist", v "forest"]]
      left := running (v "grammar") (v "input") (v "worklist")
        (v "forest") (v "fuel")
      right := halted (a "parser:completed" [v "forest"]) },
    { name := "parser:reject"
      typeContext := [
        ("grammar", .base "Grammar"), ("input", .base "Input"),
        ("worklist", .base "Worklist"), ("forest", .base "Forest"),
        ("fuel", .base "Fuel"), ("nextFuel", .base "Fuel"),
        ("diagnostic", .base "Diagnostic")]
      premises := [
        query "ParserPackConsumeFuel" [v "fuel", v "nextFuel"],
        query "ParserPackReject"
          [v "grammar", v "input", v "worklist", v "forest",
           v "diagnostic"]]
      left := running (v "grammar") (v "input") (v "worklist")
        (v "forest") (v "fuel")
      right := halted (a "parser:rejected" [v "diagnostic"]) },
    { name := "parser:engine-fault"
      typeContext := [
        ("grammar", .base "Grammar"), ("input", .base "Input"),
        ("worklist", .base "Worklist"), ("forest", .base "Forest"),
        ("fuel", .base "Fuel"), ("fault", .base "Fault")]
      premises := [query "ParserPackEngineFault"
        [v "grammar", v "input", v "worklist", v "forest", v "fault"]]
      left := running (v "grammar") (v "input") (v "worklist")
        (v "forest") (v "fuel")
      right := halted (a "parser:engine-fault" [v "fault"]) },
    { name := "parser:fuel-exhausted"
      typeContext := [
        ("grammar", .base "Grammar"), ("input", .base "Input"),
        ("worklist", .base "Worklist"), ("forest", .base "Forest"),
        ("fault", .base "Fault")]
      premises := [query "ParserPackStepLimitFault" [v "fault"]]
      left := running (v "grammar") (v "input") (v "worklist")
        (v "forest") (a "parser:fuel-zero")
      right := halted (a "parser:resource-fault" [v "fault"]) }
  ]
}

theorem parserPack_inventory :
    parserPack.types.length = 9 ∧ parserPack.terms.length = 9 ∧
    parserPack.rewrites.length = 6 := by
  decide

theorem forest_outcome_crossing :
    ("parser:completed", "Forest", "Outcome") ∈
      unaryCrossings parserPack := by
  decide

theorem outcome_config_crossing :
    ("parser:halted", "Outcome", "Config") ∈
      unaryCrossings parserPack := by
  decide

/-- A forest cannot bypass the explicit completed outcome. -/
theorem no_forest_config_crossing :
    ("parser:invented-forest-config", "Forest", "Config") ∉
      unaryCrossings parserPack := by
  decide

private def demoGrammar : Pattern := a "parser:demo-grammar"
private def demoInput : Pattern := a "parser:demo-input"
private def demoWorklist : Pattern := a "parser:demo-worklist"
private def demoForest : Pattern := a "parser:demo-packed-forest"
private def fuelZero : Pattern := a "parser:fuel-zero"
private def fuelOne : Pattern := a "parser:fuel-succ" [fuelZero]
private def stepLimitFault : Pattern := a "parser:step-limit"

def parserDemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "ParserPackInitialize" then
      [[demoGrammar, demoInput, demoWorklist, demoForest]]
    else if relation == "ParserPackConsumeFuel" then
      [[fuelOne, fuelZero]]
    else if relation == "ParserPackComplete" then
      [[demoGrammar, demoInput, demoWorklist, demoForest]]
    else if relation == "ParserPackStepLimitFault" then
      [[stepLimitFault]]
    else
      []

/-! ## Effective operational structure -/

/-- The GSLT denoted by ParserPack relative to a supplied finite relation
environment.  The environment is semantic input: changing it changes the
denoted transition system. -/
def parserPackTheoryUsing (relationEnv : RelationEnv) :
    Mettapedia.GSLT.GSLT :=
  languageGSLTUsing relationEnv parserPack
    (ReductionRespectsEquationsUsing.of_no_equations _ rfl)

/-- The small concrete environment below is a positive and negative control,
not the authority for ParserPack's effective structure. -/
abbrev parserPackTheory : Mettapedia.GSLT.GSLT :=
  parserPackTheoryUsing parserDemoRelationEnv

private theorem parserPack_rules_noncontextual :
    ∀ rule, rule ∈ parserPack.rewrites →
      NoncontextualPremises rule.premises := by
  intro rule ruleMember
  simp only [parserPack, List.mem_cons, List.mem_nil_iff, or_false] at ruleMember
  rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .relationQuery .nil
  · exact .relationQuery (.relationQuery .nil)
  · exact .relationQuery (.relationQuery .nil)
  · exact .relationQuery (.relationQuery .nil)
  · exact .relationQuery .nil
  · exact .relationQuery .nil

private theorem parserPack_rootStep_iff_mem_executor_using
    (relationEnv : RelationEnv)
    (source target : Pattern) :
    RootStep relationEnv parserPack source target ↔
      target ∈ rewriteStepWithPremisesUsing
        relationEnv parserPack source := by
  simp [RootStep, rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing]

/-- The generic finite root executor enumerates exactly the one-step relation
of the authored ParserPack GSLT for every supplied finite relation
environment. -/
theorem parserPackTheoryUsing_step_iff_mem_executor
    (relationEnv : RelationEnv)
    (source target : Pattern) :
    (parserPackTheoryUsing relationEnv).Step source target ↔
      target ∈ rewriteStepWithPremisesUsing
        relationEnv parserPack source := by
  change langReducesUsing relationEnv parserPack source target ↔ _
  unfold langReducesUsing
  rw [step_iff_rootStep_of_noncontextualRules
    parserPack_rules_noncontextual]
  exact parserPack_rootStep_iff_mem_executor_using
    relationEnv source target

/-- ParserPack earns finite exact successor enumeration for every supplied
`RelationEnv`: each relation answer is an explicit finite list, and the
authored rule executor is complete for ParserPack's noncontextual premises. -/
def parserPackSuccessorEnumerationUsing (relationEnv : RelationEnv) :
    EffectiveStructure.SuccessorEnumeration
      (parserPackTheoryUsing relationEnv) where
  successors source :=
    rewriteStepWithPremisesUsing relationEnv parserPack source
  mem_iff source target :=
    (parserPackTheoryUsing_step_iff_mem_executor
      relationEnv source target).symm

/-- Exact direct step decision derived from the finite enumeration theorem. -/
def parserPackStepDecisionUsing (relationEnv : RelationEnv) :
    EffectiveStructure.StepDecision
      (parserPackTheoryUsing relationEnv) := by
  letI : DecidableEq (parserPackTheoryUsing relationEnv).Term :=
    inferInstanceAs (DecidableEq Pattern)
  exact (parserPackSuccessorEnumerationUsing relationEnv).toStepDecision

abbrev parserPackSuccessorEnumeration :
    EffectiveStructure.SuccessorEnumeration parserPackTheory :=
  parserPackSuccessorEnumerationUsing parserDemoRelationEnv

abbrev parserPackStepDecision :
    EffectiveStructure.StepDecision parserPackTheory :=
  parserPackStepDecisionUsing parserDemoRelationEnv

def parserPackOSLFUsing (relationEnv : RelationEnv) :=
  langOSLFUsing relationEnv parserPack "Config"

abbrev parserPackOSLF := parserPackOSLFUsing parserDemoRelationEnv

theorem parserPack_galois_using (relationEnv : RelationEnv) :
    GaloisConnection
      (langDiamondUsing relationEnv parserPack)
      (langBoxUsing relationEnv parserPack) :=
  langGaloisUsing relationEnv parserPack

theorem parserPack_galois :
    GaloisConnection
      (langDiamondUsing parserDemoRelationEnv parserPack)
      (langBoxUsing parserDemoRelationEnv parserPack) :=
  parserPack_galois_using parserDemoRelationEnv

private def demoRunning : Pattern :=
  running demoGrammar demoInput demoWorklist demoForest fuelOne

private def demoCompleted : Pattern :=
  halted (a "parser:completed" [demoForest])

theorem complete_forest_exact :
    rewriteAt (engineBasePremises parserDemoRelationEnv)
        parserPack 1 demoRunning = [demoCompleted] := by
  decide +kernel

theorem completed_is_normal :
    rewriteAt (engineBasePremises parserDemoRelationEnv)
        parserPack 1 demoCompleted = [] := by
  decide +kernel

theorem demo_completion_is_decided :
    parserPackStepDecision.decideStep demoRunning demoCompleted = true := by
  apply (parserPackStepDecision.correct demoRunning demoCompleted).2
  change langReducesUsing parserDemoRelationEnv parserPack
    demoRunning demoCompleted
  apply exec_to_langReducesUsing
  refine ⟨1, ?_⟩
  rw [complete_forest_exact]
  simp

/-- Negative environment-sensitivity control: without the authored completion
row, the same ParserPack state has no completion successor. -/
theorem empty_environment_does_not_complete :
    demoCompleted ∉ rewriteStepWithPremisesUsing
      RelationEnv.empty parserPack demoRunning := by
  decide +kernel

/-! ## Occurrence-preserving JSON value carrier -/

/-- JSON values preserve exact number lexemes and object-member occurrence
identity.  Map, first-wins, last-wins, and duplicate-rejecting views are later
explicit projections rather than constructors of this carrier. -/
def jsonValue : LanguageDef := {
  name := "OccurrencePreservingJSON"
  types := [
    { name := "Bool", carrier := .builtinBool },
    { name := "NumberLexeme", carrier := .tokenRaw },
    { name := "OccurrenceId", carrier := .tokenProof },
    { name := "SourceSpan", carrier := .tokenPath },
    { name := "UnicodeScalars", carrier := .ast },
    { name := "Nat", carrier := .builtinInt },
    "Value", "Member", "MemberList", "ValueList"]
  terms := [
    ctor "JsonNullV1" "Value" [],
    ctor "JsonBoolV1" "Value" [("value", "Bool")],
    ctor "JsonStringV1" "Value" [("scalars", "UnicodeScalars")],
    ctor "JsonNumberV1" "Value" [("lexeme", "NumberLexeme")],
    ctor "JsonArrayV1" "Value" [("elements", "ValueList")],
    ctor "JsonObjectV1" "Value" [("members", "MemberList")],
    ctor "JsonMemberV1" "Member"
      [("occurrence", "OccurrenceId"), ("key", "Value"),
       ("value", "Value"), ("span", "SourceSpan")],
    ctor "JsonSourceSpanV1" "SourceSpan"
      [("start", "Nat"), ("stop", "Nat")],
    ctor "JsonNoSourceSpanV1" "SourceSpan" []
  ]
  equations := []
  rewrites := []
}

theorem jsonValue_inventory :
    jsonValue.types.length = 10 ∧ jsonValue.terms.length = 9 := by
  decide

theorem raw_number_value_crossing :
    ("JsonNumberV1", "NumberLexeme", "Value") ∈
      unaryCrossings jsonValue := by
  decide

theorem object_members_value_crossing :
    ("JsonObjectV1", "MemberList", "Value") ∈
      unaryCrossings jsonValue := by
  decide

theorem no_string_direct_object_crossing :
    ("json:invented-string-object", "String", "MemberList") ∉
      unaryCrossings jsonValue := by
  decide

/-! ## Native theory of occurrence-preserving values -/

/-- JSON values are authored structural data.  Parsing and elaboration occur
in separate presentations, so this carrier intentionally has no reduction
steps of its own. -/
def jsonValueTheory : Mettapedia.GSLT.GSLT :=
  languageGSLT jsonValue
    (ReductionRespectsEquations.of_no_equations rfl)

theorem jsonValueTheory_no_step (source target : Pattern) :
    ¬ jsonValueTheory.Step source target := by
  intro reduction
  change langReducesUsing RelationEnv.empty jsonValue source target at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

/-- Exact decision for the intentionally inert value carrier. -/
def jsonValueStepDecision :
    EffectiveStructure.StepDecision jsonValueTheory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact jsonValueTheory_no_step source target

def jsonValueOSLF := langOSLF jsonValue "Value"

theorem jsonValue_galois :
    GaloisConnection (langDiamond jsonValue) (langBox jsonValue) :=
  langGalois jsonValue

private def occurrenceZero : Pattern := a "json:occurrence-0"
private def occurrenceOne : Pattern := a "json:occurrence-1"
private def keyX : Pattern := a "json:key-x"
private def spanZero : Pattern := a "json:span-0"
private def spanOne : Pattern := a "json:span-1"
private def numberOne : Pattern := a "JsonNumberV1" [a "json:lexeme-1"]
private def numberTwo : Pattern := a "JsonNumberV1" [a "json:lexeme-2"]
private def memberZero : Pattern :=
  a "JsonMemberV1" [occurrenceZero, keyX, numberOne, spanZero]
private def memberOne : Pattern :=
  a "JsonMemberV1" [occurrenceOne, keyX, numberTwo, spanOne]
private def memberNil : Pattern := a "json:member-nil"
private def duplicateObject : Pattern :=
  a "JsonObjectV1"
    [a "json:member-cons"
      [memberZero, a "json:member-cons" [memberOne, memberNil]]]
private def collapsedObject : Pattern :=
  a "JsonObjectV1" [a "json:member-cons" [memberOne, memberNil]]

/-- Equal keys do not collapse distinct member occurrences. -/
theorem duplicate_occurrences_are_not_collapsed :
    duplicateObject ≠ collapsedObject := by
  decide

/-- A pure JSON value is a normal form until an explicit transformation or
projection language is composed with it. -/
theorem duplicate_object_is_normal :
    rewriteAt (engineBasePremises RelationEnv.empty)
        jsonValue 1 duplicateObject = [] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.JSONParserPackNTT
