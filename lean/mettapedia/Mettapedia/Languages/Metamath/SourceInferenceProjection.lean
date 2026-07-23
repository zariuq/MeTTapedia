import Mettapedia.Languages.Metamath.InferenceProjection

/-!
# Source-owned Metamath inference projection

The executable inference development originally generated its checker
presentation from an `mm-lean4` runtime database.  This file introduces the
source-side waist needed to reverse that authority direction.  Frames,
assertions, and database prefixes are represented without runtime arrays or a
runtime object map, and the generated assertion rules encode those source
objects directly.

The agreement theorems then show that translating a source prefix into the
runtime projection carrier preserves the complete generated presentation.
They do not yet construct a source prefix from a raw-byte parse; that is the
next composition boundary.
-/

namespace Mettapedia.Languages.Metamath.SourceInferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceEncoding.Builder
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.InferenceProjection

abbrev SourceRuleId := Mettapedia.OSLF.MeTTaIL.Syntax.RuleId
abbrev SourceRuleSchema := Mettapedia.OSLF.MeTTaIL.Syntax.RuleSchema
abbrev SourcePresentation :=
  Mettapedia.GSLT.LanguageDef.InferenceChecker.Presentation

/-! ## Source-owned semantic carriers -/

/-- Ordered source representation of the active Metamath frame. -/
structure SourceFrame where
  distinctVariables : List (String × String)
  hypothesisLabels : List String
deriving DecidableEq, Repr

/-- Representation map into the verified implementation carrier. -/
def SourceFrame.toRuntime (frame : SourceFrame) : RuntimeFrame :=
  { dj := frame.distinctVariables.toArray
    hyps := frame.hypothesisLabels.toArray }

/-- Direct GSLT data encoding of a source frame. -/
def encodeSourceFrame (frame : SourceFrame) : Pattern :=
  Builder.frame
    (encodeListWith encodeDVPair frame.distinctVariables)
    (encodeListWith encodeString frame.hypothesisLabels)

@[simp] theorem encodeSourceFrame_eq_encodeFrame_toRuntime
    (frame : SourceFrame) :
    encodeSourceFrame frame = encodeFrame frame.toRuntime := by
  simp [encodeSourceFrame, SourceFrame.toRuntime, encodeFrame]

/-- One prior assertion in a source-owned scoped prefix. -/
structure SourceAssertion where
  label : String
  formula : ConstantHeadedFormula
  frame : SourceFrame
  hypotheses : List HypothesisView

/-- Finite source prefix from which the indexed checker GSLT is generated. -/
structure SourcePrefix where
  declaredConstants : List String
  declaredVariables : List String
  callerFrame : SourceFrame
  activeHypotheses : List HypothesisView
  assertions : List SourceAssertion

def SourceAssertion.toProjectionView
    (assertion : SourceAssertion) : AssertionView :=
  { label := assertion.label
    formula := assertion.formula
    frame := assertion.frame.toRuntime
    hypotheses := assertion.hypotheses }

def SourcePrefix.toProjection (source : SourcePrefix) : PrefixProjection :=
  { declaredConstants := source.declaredConstants
    declaredVariables := source.declaredVariables
    callerFrame := source.callerFrame.toRuntime
    activeHypotheses := source.activeHypotheses
    assertions := source.assertions.map SourceAssertion.toProjectionView }

/-! ## Source-side validity -/

def sourceFrameDVValid (frame : SourceFrame)
    (floatingVariables : List String) : Bool :=
  frame.distinctVariables.all fun pair =>
    decide (pair.1 < pair.2) &&
      floatingVariables.contains pair.1 &&
      floatingVariables.contains pair.2

def sourceFrameValid (frame : SourceFrame)
    (hypotheses : List HypothesisView) : Bool :=
  let floatingVariables := floatingVariableNames hypotheses
  hasUniqueLabels hypotheses &&
    hasUniqueFloatingVariables hypotheses &&
    hypothesesPrefixScoped hypotheses &&
    (hypotheses.map HypothesisView.label == frame.hypothesisLabels) &&
    hypotheses.all
      (formulaSymbolsRespectFrame floatingVariables ∘ HypothesisView.formula) &&
    sourceFrameDVValid frame floatingVariables

@[simp] theorem sourceFrameDVValid_eq_runtime
    (frame : SourceFrame) (floatingVariables : List String) :
    sourceFrameDVValid frame floatingVariables =
      frameDVValid frame.toRuntime floatingVariables := by
  simp [sourceFrameDVValid, frameDVValid, SourceFrame.toRuntime]
  rfl

@[simp] theorem sourceFrameValid_eq_runtime
    (frame : SourceFrame) (hypotheses : List HypothesisView) :
    sourceFrameValid frame hypotheses =
      frameProjectionValid frame.toRuntime hypotheses := by
  simp [sourceFrameValid, frameProjectionValid]
  rfl

def sourceAssertionValid
    (declaredConstants declaredVariables : List String)
    (assertion : SourceAssertion) : Bool :=
  sourceFrameValid assertion.frame assertion.hypotheses &&
    formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses) assertion.formula &&
    assertion.hypotheses.all
      (formulaSymbolsRespectDeclarations declaredConstants declaredVariables ∘
        HypothesisView.formula) &&
    formulaSymbolsRespectDeclarations declaredConstants declaredVariables
      assertion.formula

@[simp] theorem sourceAssertionValid_eq_runtime
    (declaredConstants declaredVariables : List String)
    (assertion : SourceAssertion) :
    sourceAssertionValid declaredConstants declaredVariables assertion =
      assertionViewValid declaredConstants declaredVariables
        assertion.toProjectionView := by
  simp [sourceAssertionValid, assertionViewValid,
    SourceAssertion.toProjectionView]

def sourcePrefixRuleLabels (source : SourcePrefix) : List String :=
  source.activeHypotheses.map HypothesisView.label ++
    source.assertions.map SourceAssertion.label

@[simp] theorem sourcePrefixRuleLabels_eq_runtime (source : SourcePrefix) :
    sourcePrefixRuleLabels source =
      sourceRuleLabels source.toProjection := by
  simp [sourcePrefixRuleLabels, sourceRuleLabels, SourcePrefix.toProjection,
    SourceAssertion.toProjectionView]

def sourcePrefixValid (source : SourcePrefix) : Bool :=
  source.declaredConstants.eraseDups.length ==
      source.declaredConstants.length &&
    source.declaredVariables.eraseDups.length ==
      source.declaredVariables.length &&
    source.declaredConstants.all (fun constantName =>
      !(source.declaredVariables.contains constantName)) &&
    sourceFrameValid source.callerFrame source.activeHypotheses &&
    source.activeHypotheses.all
      (formulaSymbolsRespectDeclarations source.declaredConstants
        source.declaredVariables ∘ HypothesisView.formula) &&
    source.assertions.all
      (sourceAssertionValid source.declaredConstants
        source.declaredVariables) &&
    sourceRuleLabelsValid (sourcePrefixRuleLabels source)

@[simp] theorem sourcePrefixValid_eq_runtime (source : SourcePrefix) :
    sourcePrefixValid source =
      prefixProjectionValid source.toProjection := by
  have hassertions :
      source.assertions.all
          (sourceAssertionValid source.declaredConstants
            source.declaredVariables) =
        (source.assertions.map SourceAssertion.toProjectionView).all
          (assertionViewValid source.declaredConstants
            source.declaredVariables) := by
    induction source.assertions with
    | nil => rfl
    | cons assertion assertions ih =>
        simp only [List.all_cons, List.map_cons]
        rw [sourceAssertionValid_eq_runtime, ih]
  simp [sourcePrefixValid, prefixProjectionValid, SourcePrefix.toProjection,
    hassertions]

/-! ## Direct source vocabulary -/

def stringsOfSourceFrame (frame : SourceFrame) : List String :=
  frame.distinctVariables.flatMap (fun pair => [pair.1, pair.2]) ++
    frame.hypothesisLabels

def stringsOfSourceAssertion (assertion : SourceAssertion) : List String :=
  assertion.label ::
    (stringsOfFormula assertion.formula ++
      stringsOfSourceFrame assertion.frame ++
      assertion.hypotheses.flatMap stringsOfHypothesis)

def sourcePrefixVocabulary (source : SourcePrefix) : List String :=
  (stringsOfSourceFrame source.callerFrame ++
      source.activeHypotheses.flatMap stringsOfHypothesis ++
      source.assertions.flatMap stringsOfSourceAssertion)
    |>.eraseDups
    |> sortStrings

@[simp] theorem stringsOfSourceFrame_eq_runtime (frame : SourceFrame) :
    stringsOfSourceFrame frame = stringsOfFrame frame.toRuntime := by
  simp [stringsOfSourceFrame, stringsOfFrame, SourceFrame.toRuntime]
  rfl

@[simp] theorem stringsOfSourceAssertion_eq_runtime
    (assertion : SourceAssertion) :
    stringsOfSourceAssertion assertion =
      stringsOfAssertion assertion.toProjectionView := by
  simp [stringsOfSourceAssertion, stringsOfAssertion,
    SourceAssertion.toProjectionView]

@[simp] theorem sourcePrefixVocabulary_eq_runtime (source : SourcePrefix) :
    sourcePrefixVocabulary source = sourceVocabulary source.toProjection := by
  have hassertions :
      source.assertions.flatMap stringsOfSourceAssertion =
        (source.assertions.map SourceAssertion.toProjectionView).flatMap
          stringsOfAssertion := by
    induction source.assertions with
    | nil => rfl
    | cons assertion assertions ih =>
        simp only [List.flatMap_cons, List.map_cons]
        rw [stringsOfSourceAssertion_eq_runtime, ih]
  simp [sourcePrefixVocabulary, sourceVocabulary, SourcePrefix.toProjection,
    hassertions]

/-! ## Source-generated checker rules -/

private def sourceRuleId (value : String) : SourceRuleId := { value }
private def sourceMetavariable (name : String) : Pattern := .fvar name
private def sourceFormal (name : String) : String × Nat := (name, 0)

def sourceAssertionSubstitution (assertion : SourceAssertion) : Pattern :=
  Builder.substitution
    (encodeListWith id (assertionBindingsFrom 0 assertion.hypotheses))

def sourceAssertionRule (callerFrame : SourceFrame)
    (assertion : SourceAssertion) : SourceRuleSchema :=
  let substitution := sourceAssertionSubstitution assertion
  let resultFormula :=
    Builder.formula (encodeString assertion.formula.typecode)
      (sourceMetavariable conclusionBodyFormalName)
  { id := sourceRuleId assertion.label
    metavariables :=
      assertionHypothesisFormalsFrom 0 assertion.hypotheses ++
        [sourceFormal conclusionBodyFormalName]
    premises :=
      assertionHypothesisProvesFrom 0 assertion.hypotheses ++
        assertionEssentialChecksFrom substitution 0 assertion.hypotheses ++
        [ dvOK substitution (encodeSourceFrame callerFrame)
            (encodeSourceFrame assertion.frame)
        , applySubst substitution (encodeFormula assertion.formula)
            resultFormula ]
    conclusion := proves resultFormula }

def sourceGeneratedRules (source : SourcePrefix) : List SourceRuleSchema :=
  source.activeHypotheses.map activeHypothesisRule ++
    source.assertions.map (sourceAssertionRule source.callerFrame)

@[simp] theorem sourceAssertionSubstitution_eq_runtime
    (assertion : SourceAssertion) :
    sourceAssertionSubstitution assertion =
      assertionSubstitution assertion.toProjectionView := by
  rfl

theorem sourceAssertionRule_eq_runtime
    (callerFrame : SourceFrame) (assertion : SourceAssertion) :
    sourceAssertionRule callerFrame assertion =
      assertionRule callerFrame.toRuntime assertion.toProjectionView := by
  simp [sourceAssertionRule, assertionRule,
    sourceAssertionSubstitution, sourceRuleId, sourceMetavariable,
    sourceFormal, SourceAssertion.toProjectionView]
  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem sourceGeneratedRules_eq_runtime (source : SourcePrefix) :
    sourceGeneratedRules source =
      generatedSourceRules source.toProjection := by
  simp [sourceGeneratedRules, generatedSourceRules,
    SourcePrefix.toProjection, sourceAssertionRule_eq_runtime]

/-! ## Source-owned indexed presentation -/

def presentationOfSourcePrefix? (source : SourcePrefix) :
    Option SourcePresentation := do
  guard (sourcePrefixValid source)
  let vocabulary := sourcePrefixVocabulary source
  guard (sourceVocabularyValid vocabulary)
  let sourceRules := sourceGeneratedRules source
  guard (sourceRuleIdsDisjoint
    (sourceRules.map Mettapedia.OSLF.MeTTaIL.Syntax.RuleSchema.id))
  some
    { language :=
        { languageWithSourceVocabulary vocabulary with
          judgments := judgmentDecls ++ [provesDecl]
          inferenceRules := sideRules ++ sourceRules } }

/-- The source-owned and runtime-projection presentation generators agree
extensionally, although their input authority and frame representations are
independent. -/
theorem presentationOfSourcePrefix?_eq_runtime
    (source : SourcePrefix) :
    presentationOfSourcePrefix? source =
      presentationOfProjection? source.toProjection := by
  simp [presentationOfSourcePrefix?, presentationOfProjection?]

/-- A source presentation carries exactly the generic side calculus followed
by the rules generated from that source prefix. -/
theorem rules_eq_of_presentationOfSourcePrefix?_eq_some
    (source : SourcePrefix) (presentation : SourcePresentation)
    (hsource :
      presentationOfSourcePrefix? source = some presentation) :
    presentation.rules = sideRules ++ sourceGeneratedRules source := by
  unfold presentationOfSourcePrefix? at hsource
  simp only [Option.bind_eq_bind] at hsource
  rw [Option.bind_eq_some_iff] at hsource
  rcases hsource with ⟨_, _, hsource⟩
  rw [Option.bind_eq_some_iff] at hsource
  rcases hsource with ⟨_, _, hsource⟩
  rw [Option.bind_eq_some_iff] at hsource
  rcases hsource with ⟨_, _, hsource⟩
  simp at hsource
  cases hsource
  exact congrArg (fun rules => sideRules ++ rules)
    (sourceGeneratedRules_eq_runtime source).symm

/-! ## Executable positive and negative boundaries -/

def exampleSourcePrefix : SourcePrefix :=
  { declaredConstants := ["wff"]
    declaredVariables := ["ph"]
    callerFrame :=
      { distinctVariables := []
        hypothesisLabels := ["wph"] }
    activeHypotheses := [.floating "wph" "wff" "ph"]
    assertions := [] }

def duplicateLabelSourcePrefix : SourcePrefix :=
  { exampleSourcePrefix with
    callerFrame :=
      { distinctVariables := []
        hypothesisLabels := ["wph", "wph"] }
    activeHypotheses :=
      [.floating "wph" "wff" "ph", .floating "wph" "wff" "ph"] }

example : sourcePrefixValid exampleSourcePrefix = true := by
  decide

example : sourcePrefixValid duplicateLabelSourcePrefix = false := by
  decide

end Mettapedia.Languages.Metamath.SourceInferenceProjection
