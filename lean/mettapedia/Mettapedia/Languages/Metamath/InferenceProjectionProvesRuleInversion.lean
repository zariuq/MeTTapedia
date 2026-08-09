import Mettapedia.Languages.Metamath.InferenceProjectionSideConservativity

/-!
# Root-rule inversion for projected `Proves` applications

A successful Metamath prefix projection has three rule-table regions: the
standalone side calculus, active-hypothesis rules, and assertion rules.  This
module proves that an arbitrary generic rule application whose conclusion is
headed by `Proves` comes from exactly one of the two generated source regions.

The assertion branch deliberately retains raw `Pattern` arguments and the
ordinary schema-instantiation witnesses.  In particular, this classification
does not decode assertion bodies as Metamath formulas and does not import any
runtime checker agreement.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditions

/-! ## Static source-rule views -/

/-- Raw application data for a projected active-hypothesis rule. -/
def ActiveHypothesisApplicationView
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (formulaPattern : Pattern) : Prop :=
  ∃ hypothesis : HypothesisView,
    hypothesis ∈ projection.activeHypotheses ∧
    target.1.lookupRule? ruleInstance.ruleId =
      some (activeHypothesisRule hypothesis) ∧
    argumentsValidAt (activeHypothesisRule hypothesis).metavariables
      ruleInstance.arguments = true ∧
    InstantiatesList (activeHypothesisRule hypothesis).metavariables
      ruleInstance.arguments (activeHypothesisRule hypothesis).premises
      premises ∧
    Instantiates (activeHypothesisRule hypothesis).metavariables
      ruleInstance.arguments (activeHypothesisRule hypothesis).conclusion
      (proves formulaPattern)

/-- Raw application data for a projected assertion rule.  The selected
`AssertionView` exposes its authored metadata, while the instance arguments
and all instantiated patterns remain uninterpreted syntax. -/
def AssertionApplicationView
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (formulaPattern : Pattern) : Prop :=
  ∃ assertion : AssertionView,
    assertion ∈ projection.assertions ∧
    target.1.lookupRule? ruleInstance.ruleId =
      some (assertionRule projection.callerFrame assertion) ∧
    argumentsValidAt
      (assertionRule projection.callerFrame assertion).metavariables
      ruleInstance.arguments = true ∧
    InstantiatesList
      (assertionRule projection.callerFrame assertion).metavariables
      ruleInstance.arguments
      (assertionRule projection.callerFrame assertion).premises premises ∧
    Instantiates
      (assertionRule projection.callerFrame assertion).metavariables
      ruleInstance.arguments
      (assertionRule projection.callerFrame assertion).conclusion
      (proves formulaPattern)

/-- A reflected active-hypothesis view reconstructs the exact generic local
application. -/
theorem ActiveHypothesisApplicationView.toRuleApplication
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (view : ActiveHypothesisApplicationView projection target ruleInstance
      premises formulaPattern) :
    RuleApplication target ruleInstance premises (proves formulaPattern) := by
  rcases view with
    ⟨hypothesis, _hmember, hlookup, harguments, hpremises, hconclusion⟩
  exact RuleApplication.intro (activeHypothesisRule hypothesis) hlookup
    harguments rfl hpremises hconclusion

/-- A reflected assertion view reconstructs the exact generic local
application without strengthening any raw argument into a decoded formula. -/
theorem AssertionApplicationView.toRuleApplication
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (view : AssertionApplicationView projection target ruleInstance premises
      formulaPattern) :
    RuleApplication target ruleInstance premises (proves formulaPattern) := by
  rcases view with
    ⟨assertion, _hmember, hlookup, harguments, hpremises, hconclusion⟩
  exact RuleApplication.intro
    (assertionRule projection.callerFrame assertion) hlookup
      harguments rfl hpremises hconclusion

/-! ## Excluding the side calculus -/

/-- Every standalone side-rule conclusion has one of the reserved
side-judgment heads.  This follows from V2 validation of the whole side
presentation rather than an enumeration of the current rule table. -/
theorem sideRule_conclusion_isSideJudgment
    {rule : RuleSchema} (hmember : rule ∈ sideRules) :
    IsSideJudgment rule.conclusion := by
  have hvalid := rule_isValidIn_of_mem validatedSidePresentation (by
    simpa [validatedSidePresentation, sidePresentation, sideCalculus]
      using hmember)
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at hvalid
  have hconclusionValid :
      sidePresentation.judgmentSchemaValid rule.conclusion = true :=
    (List.all_eq_true.mp hvalid.2.1) rule.conclusion (by
      simp [RuleSchema.patterns])
  exact isSideJudgment_of_sidePresentation_hasJudgmentShape
    (Presentation.hasJudgmentShape_of_judgmentSchemaValid hconclusionValid)

/-- No standalone side rule can instantiate its conclusion to a `Proves`
judgment. -/
theorem sideRule_cannot_instantiate_proves
    {rule : RuleSchema} (hmember : rule ∈ sideRules)
    {arguments : List Pattern} {formulaPattern : Pattern}
    (hinstantiates :
      Instantiates rule.metavariables arguments rule.conclusion
        (proves formulaPattern)) : False := by
  exact proves_not_isSideJudgment formulaPattern
    (isSideJudgment_of_instantiatesAt
      (sideRule_conclusion_isSideJudgment hmember) hinstantiates)

/-! ## Complete root classification -/

/-- Any projected local application concluding `Proves` selects either an
active hypothesis or an assertion.  The side-rule prefix is impossible, and
the assertion branch makes no formula-decoding claim. -/
theorem ruleApplication_proves_cases
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (application :
      RuleApplication target ruleInstance premises (proves formulaPattern)) :
    ActiveHypothesisApplicationView projection target ruleInstance premises
        formulaPattern ∨
      AssertionApplicationView projection target ruleInstance premises
        formulaPattern := by
  cases application with
  | intro rule hlookup harguments _hsideConditions hpremises hconclusion =>
      have hmember : rule ∈ target.1.rules :=
        List.mem_of_find?_eq_some hlookup
      rw [rules_eq_of_presentationOfProjection?_eq_some
        projection target.1 hprojection] at hmember
      rcases List.mem_append.mp hmember with hside | hsource
      · exact False.elim
          (sideRule_cannot_instantiate_proves hside hconclusion)
      · simp only [generatedSourceRules, List.mem_append, List.mem_map] at hsource
        rcases hsource with
          ⟨hypothesis, hhypothesis, rfl⟩ |
          ⟨assertion, hassertion, rfl⟩
        · exact Or.inl
            ⟨hypothesis, hhypothesis, hlookup, harguments, hpremises,
              hconclusion⟩
        · exact Or.inr
            ⟨assertion, hassertion, hlookup, harguments, hpremises,
              hconclusion⟩

/-- Exact local characterization: projected `Proves` rule applications are
precisely the union of the two raw generated-source views. -/
theorem ruleApplication_proves_iff_sourceView
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern} :
    RuleApplication target ruleInstance premises (proves formulaPattern) ↔
      ActiveHypothesisApplicationView projection target ruleInstance premises
          formulaPattern ∨
        AssertionApplicationView projection target ruleInstance premises
          formulaPattern := by
  constructor
  · exact ruleApplication_proves_cases projection target hprojection
  · rintro (view | view)
    · exact view.toRuleApplication
    · exact view.toRuleApplication

/-- Active-hypothesis and assertion schemas cannot be equal: an assertion
always has the final result-body formal, whereas an active hypothesis has no
formals. -/
theorem activeHypothesisRule_ne_assertionRule
    (hypothesis : HypothesisView) (callerFrame : RuntimeFrame)
    (assertion : AssertionView) :
    activeHypothesisRule hypothesis ≠ assertionRule callerFrame assertion := by
  intro hequal
  have hmetavariables := congrArg RuleSchema.metavariables hequal
  simp [activeHypothesisRule, assertionRule] at hmetavariables

/-- The two branches of root classification are disjoint. -/
theorem sourceApplicationViews_exclusive
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern} :
    ¬ (ActiveHypothesisApplicationView projection target ruleInstance premises
          formulaPattern ∧
        AssertionApplicationView projection target ruleInstance premises
          formulaPattern) := by
  rintro ⟨
    ⟨hypothesis, _hhypothesis, hactiveLookup, _hactiveArguments,
      _hactivePremises, _hactiveConclusion⟩,
    ⟨assertion, _hassertion, hassertionLookup, _hassertionArguments,
      _hassertionPremises, _hassertionConclusion⟩⟩
  apply activeHypothesisRule_ne_assertionRule hypothesis
    projection.callerFrame assertion
  exact Option.some.inj (hactiveLookup.symm.trans hassertionLookup)

/-- Root classification lifts directly from local applications to arbitrary
generic derivations.  Child reflection remains a separate recursive theorem. -/
theorem provesDerivation_root_cases
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection :
      presentationOfProjection? projection = some target.1)
    {formulaPattern : Pattern}
    (derivation : Derivation target (proves formulaPattern)) :
    ∃ ruleInstance premises,
      ActiveHypothesisApplicationView projection target ruleInstance premises
          formulaPattern ∨
        AssertionApplicationView projection target ruleInstance premises
          formulaPattern := by
  cases derivation with
  | byRule ruleInstance application _children =>
      exact ⟨ruleInstance, _,
        ruleApplication_proves_cases projection target hprojection application⟩

/-! ## Positive and negative boundaries -/

/-- Positive: a genuinely witnessed generic `Proves` application exposes one
of the two projected source-schema shapes. -/
example (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (formulaPattern : Pattern)
    (application :
      RuleApplication target ruleInstance premises (proves formulaPattern)) :
    ActiveHypothesisApplicationView projection target ruleInstance premises
        formulaPattern ∨
      AssertionApplicationView projection target ruleInstance premises
        formulaPattern :=
  ruleApplication_proves_cases projection target hprojection application

private def boundaryFrame : RuntimeFrame := ⟨#[], #[]⟩

private def boundaryAssertion : AssertionView :=
  { label := "ax-boundary"
    formula := ⟨"|-", []⟩
    frame := boundaryFrame
    hypotheses := [] }

/-- Negative decoding boundary: even the nullary assertion schema accepts an
arbitrary ground pattern as its result-body argument.  Formula decoding must
therefore come from the final `ApplySubst` child derivation, not root-rule
classification. -/
example :
    argumentsValidAt (assertionRule boundaryFrame boundaryAssertion).metavariables
      [.apply "unclassified-ground-pattern" []] = true := by
  decide

/-- Negative source boundary: a side-rule instantiation can never masquerade
as either generated `Proves` branch. -/
example {rule : RuleSchema} (hmember : rule ∈ sideRules)
    {arguments : List Pattern} {formulaPattern : Pattern} :
    ¬ Instantiates rule.metavariables arguments rule.conclusion
      (proves formulaPattern) := by
  intro hinstantiates
  exact sideRule_cannot_instantiate_proves hmember hinstantiates

end Mettapedia.Languages.Metamath.InferenceProjection
