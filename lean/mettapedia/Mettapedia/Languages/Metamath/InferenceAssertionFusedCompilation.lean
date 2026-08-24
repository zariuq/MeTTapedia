import Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation
import Mettapedia.Languages.Metamath.InferenceAssertionProjectionInvariants

/-!
# Fused compilation of Metamath assertion substitution

The independent Metamath assertion semantics is relational: a finite ordered
substitution relates source formulas to their instantiated results.  The
generic first-order frame compiler supplies an allocation-free template
consumer.  This module proves the exact adapter between them.

The only functionality premise is already imposed by successful Metamath
projection: floating-variable names are distinct.  Under that premise,
deterministic lookup into the ordered finite substitution agrees with the
relational lookup judgment, fused essential-hypothesis comparison agrees with
`EssentialMatches`, and direct conclusion instantiation agrees with
`FormulaSubstitutionSemantics`.  Disjoint-variable checking remains an
orthogonal proof obligation and is retained unchanged.

A duplicate-key counterexample shows why the functionality premise is
necessary: the relational source semantics may select either occurrence,
whereas a deterministic compiler must select one.
-/

namespace Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation

open Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics

/-! ## Exact flat representation -/

/-- Constants remain literal cells; Metamath variables become typed template
holes. -/
def templateAtom : RuntimeSym → TemplateAtom RuntimeSym String
  | .const name => .literal (.const name)
  | .var name => .hole name

def bodyTemplate (body : List RuntimeSym) : Template RuntimeSym String :=
  body.map templateAtom

/-- The constant typecode participates in comparison as the first literal
cell.  It is not placed in the substitution range. -/
def formulaTemplate (formula : ConstantHeadedFormula) :
    Template RuntimeSym String :=
  .literal (.const formula.typecode) :: bodyTemplate formula.body

/-- Exact flat input consumed by the generic frame matcher. -/
def formulaTokens (formula : ConstantHeadedFormula) : List RuntimeSym :=
  .const formula.typecode :: formula.body

/-! ## Deterministic view of the relational finite substitution -/

/-- First-occurrence lookup of a replacement body.  The relational source
keeps duplicate bindings visible; exact projected assertions prove that this
functionality choice is observationally irrelevant. -/
def lookupBody? : FiniteSubstitution → String → Option (List RuntimeSym)
  | [], _ => none
  | binding :: rest, variableName =>
      if binding.variableName = variableName then
        some binding.replacement.body
      else
        lookupBody? rest variableName

/-- Every successful deterministic lookup originates in a visible relational
binding.  This direction does not require key uniqueness. -/
theorem lookupBody?_origin
    {substitution : FiniteSubstitution} {variableName : String}
    {body : List RuntimeSym}
    (selected : lookupBody? substitution variableName = some body) :
    ∃ replacement : ConstantHeadedFormula,
      LookupSemantics substitution variableName replacement ∧
        replacement.body = body := by
  induction substitution with
  | nil => simp [lookupBody?] at selected
  | cons binding rest inductionHypothesis =>
      rcases binding with ⟨bindingName, bindingReplacement⟩
      by_cases same : bindingName = variableName
      · subst bindingName
        simp [lookupBody?] at selected
        refine ⟨bindingReplacement, ?_, selected⟩
        simp [LookupSemantics]
      · simp [lookupBody?, same] at selected
        obtain ⟨replacement, member, bodyEq⟩ :=
          inductionHypothesis selected
        exact ⟨replacement, by
          simp only [LookupSemantics, List.mem_cons]
          exact Or.inr member, bodyEq⟩

/-- A visible relational binding guarantees that deterministic lookup finds
some body, even before uniqueness selects which one. -/
theorem lookupBody?_isSome_of_semantics
    {substitution : FiniteSubstitution} {variableName : String}
    {replacement : ConstantHeadedFormula}
    (member : LookupSemantics substitution variableName replacement) :
    (lookupBody? substitution variableName).isSome = true := by
  induction substitution with
  | nil => simp [LookupSemantics] at member
  | cons binding rest inductionHypothesis =>
      simp only [LookupSemantics, List.mem_cons] at member
      rcases member with same | member
      · subst binding
        simp [lookupBody?]
      · by_cases nameEq : binding.variableName = variableName
        · simp [lookupBody?, nameEq]
        · simp [lookupBody?, nameEq,
            inductionHypothesis member]

/-- Unique keys make deterministic lookup exactly equivalent to relational
membership at the body observation. -/
theorem lookupBody?_eq_some_iff_of_unique
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (variableName : String) (body : List RuntimeSym) :
    lookupBody? substitution variableName = some body ↔
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution variableName replacement ∧
          replacement.body = body := by
  constructor
  · exact fun selected => lookupBody?_origin selected
  · rintro ⟨replacement, member, rfl⟩
    have isSome := lookupBody?_isSome_of_semantics member
    cases selectedEq : lookupBody? substitution variableName with
    | none => simp [selectedEq] at isSome
    | some selectedBody =>
        obtain ⟨selectedReplacement, selectedMember, selectedBodyEq⟩ :=
          lookupBody?_origin selectedEq
        have replacementEq : selectedReplacement = replacement :=
          lookupSemantics_functional unique selectedMember member
        subst selectedReplacement
        exact congrArg some selectedBodyEq.symm

/-! ## Body and formula adequacy -/

/-- Relational body substitution is executed exactly by generic template
instantiation when source keys are unique. -/
theorem instantiate_bodyTemplate_of_semantics
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    {source result : List RuntimeSym}
    (semantics : BodySubstitution substitution source result) :
    instantiate (lookupBody? substitution) (bodyTemplate source) =
      some result := by
  induction semantics with
  | nil => rfl
  | const tail inductionHypothesis =>
      simp [bodyTemplate, templateAtom, instantiate]
      simpa only [bodyTemplate] using inductionHypothesis
  | @var variableName replacement sourceTail resultTail member tail
      inductionHypothesis =>
      have selected :
          lookupBody? substitution variableName = some replacement.body :=
        (lookupBody?_eq_some_iff_of_unique unique variableName
          replacement.body).2 ⟨replacement, member, rfl⟩
      change
        (do
          let image ← lookupBody? substitution variableName
          let resultTail ← instantiate (lookupBody? substitution)
            (bodyTemplate sourceTail)
          pure (image ++ resultTail)) = some (replacement.body ++ resultTail)
      rw [selected, inductionHypothesis]
      rfl

/-- Successful generic template instantiation always reflects a relational
body substitution.  Since deterministic lookup exposes a visible origin,
this direction does not need uniqueness. -/
theorem bodySubstitution_of_instantiate_bodyTemplate
    (substitution : FiniteSubstitution) {source result : List RuntimeSym}
    (instantiated :
      instantiate (lookupBody? substitution) (bodyTemplate source) =
        some result) :
    BodySubstitution substitution source result := by
  induction source generalizing result with
  | nil =>
      simp [bodyTemplate, instantiate] at instantiated
      subst result
      exact .nil
  | cons symbol sourceTail inductionHypothesis =>
      cases symbol with
      | const name =>
          change
            (do
              let resultTail ← instantiate (lookupBody? substitution)
                (bodyTemplate sourceTail)
              pure (.const name :: resultTail)) = some result at instantiated
          cases tailEq :
              instantiate (lookupBody? substitution)
                (bodyTemplate sourceTail) with
          | none => simp [tailEq] at instantiated
          | some resultTail =>
              simp [tailEq] at instantiated
              rw [← instantiated]
              exact .const (inductionHypothesis tailEq)
      | var variableName =>
          change
            (do
              let image ← lookupBody? substitution variableName
              let resultTail ← instantiate (lookupBody? substitution)
                (bodyTemplate sourceTail)
              pure (image ++ resultTail)) = some result at instantiated
          cases selectedEq : lookupBody? substitution variableName with
          | none => simp [selectedEq] at instantiated
          | some selectedBody =>
              cases tailEq :
                  instantiate (lookupBody? substitution)
                    (bodyTemplate sourceTail) with
              | none => simp [selectedEq, tailEq] at instantiated
              | some resultTail =>
                  simp [selectedEq, tailEq] at instantiated
                  obtain ⟨replacement, member, bodyEq⟩ :=
                    lookupBody?_origin selectedEq
                  rw [← instantiated, ← bodyEq]
                  exact .var member (inductionHypothesis tailEq)

theorem instantiate_bodyTemplate_iff
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (source result : List RuntimeSym) :
    instantiate (lookupBody? substitution) (bodyTemplate source) =
        some result ↔
      BodySubstitution substitution source result := by
  constructor
  · exact bodySubstitution_of_instantiate_bodyTemplate substitution
  · exact instantiate_bodyTemplate_of_semantics unique

/-- Whole-formula instantiation preserves and checks the constant typecode in
addition to the relational body substitution. -/
theorem instantiate_formulaTemplate_iff
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (source result : ConstantHeadedFormula) :
    instantiate (lookupBody? substitution) (formulaTemplate source) =
        some (formulaTokens result) ↔
      FormulaSubstitutionSemantics substitution source result := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  rcases result with ⟨resultTypecode, resultBody⟩
  constructor
  · intro instantiated
    unfold formulaTemplate formulaTokens at instantiated
    simp only [instantiate] at instantiated
    cases bodyEq :
        instantiate (lookupBody? substitution) (bodyTemplate sourceBody) with
    | none => simp [bodyEq] at instantiated
    | some instantiatedBody =>
        simp [bodyEq] at instantiated
        obtain ⟨typecodeEq, bodyResultEq⟩ := instantiated
        cases typecodeEq
        cases bodyResultEq
        exact ⟨rfl,
          (instantiate_bodyTemplate_iff unique sourceBody resultBody).1
            bodyEq⟩
  · rintro ⟨typecodeEq, bodySemantics⟩
    cases typecodeEq
    unfold formulaTemplate formulaTokens
    simp [instantiate,
      instantiate_bodyTemplate_of_semantics unique bodySemantics]

/-- The generic allocation-free matcher is exactly Metamath formula
substitution on projected unique-key substitutions. -/
theorem fusedMatch_formula_iff
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (source result : ConstantHeadedFormula) :
    fusedMatch (lookupBody? substitution) (formulaTemplate source)
        (formulaTokens result) = some () ↔
      FormulaSubstitutionSemantics substitution source result := by
  exact (fusedMatch_eq_some_iff
    (lookupBody? substitution) (formulaTemplate source)
    (formulaTokens result)).trans
      (instantiate_formulaTemplate_iff unique source result)

/-! ## Exact assertion-level fusion -/

/-- Fused checks retain exact hypothesis order.  Floating hypotheses build
the already-supplied substitution and therefore require no comparison in this
phase; essential hypotheses consume their corresponding actual formula. -/
def runFusedEssentialMatches (substitution : FiniteSubstitution) :
    List HypothesisView → List ConstantHeadedFormula → Option Unit
  | [], [] => some ()
  | .floating _ _ _ :: hypotheses, _ :: actuals =>
      runFusedEssentialMatches substitution hypotheses actuals
  | .essential _ formula :: hypotheses, actual :: actuals => do
      let _ ← fusedMatch (lookupBody? substitution)
        (formulaTemplate formula) (formulaTokens actual)
      runFusedEssentialMatches substitution hypotheses actuals
  | _, _ => none

theorem runFusedEssentialMatches_iff
    {substitution : FiniteSubstitution}
    (unique : SubstitutionKeysUnique substitution)
    (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula) :
    runFusedEssentialMatches substitution hypotheses actuals = some () ↔
      EssentialMatches substitution hypotheses actuals := by
  induction hypotheses generalizing actuals with
  | nil => cases actuals <;> simp [runFusedEssentialMatches, EssentialMatches]
  | cons hypothesis hypotheses inductionHypothesis =>
      cases actuals with
      | nil =>
          cases hypothesis <;>
            simp [runFusedEssentialMatches, EssentialMatches]
      | cons actual actuals =>
          cases hypothesis with
          | floating label typecode variableName =>
              simpa [runFusedEssentialMatches, EssentialMatches] using
                inductionHypothesis actuals
          | essential label formula =>
              simp [runFusedEssentialMatches, EssentialMatches,
                fusedMatch_formula_iff unique formula actual,
                inductionHypothesis actuals]

/-- The compiled assertion meaning changes only the representation of
substitution and essential-hypothesis comparison.  Mandatory-hypothesis
instances, DV evidence, and the exact final result remain first-class. -/
def FusedAssertionApplicationSemantics (callerFrame : RuntimeFrame)
    (assertion : AssertionView) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) : Prop :=
  ∃ substitution,
    HypothesisInstances assertion.hypotheses actuals substitution ∧
      runFusedEssentialMatches substitution assertion.hypotheses actuals =
        some () ∧
      DVOKSemantics substitution callerFrame assertion.frame ∧
      instantiate (lookupBody? substitution)
        (formulaTemplate assertion.formula) = some (formulaTokens result)

/-- Exact Metamath assertion fusion.  Successful projection supplies the
distinct-floating-name premise through its existing validation invariant. -/
theorem assertionApplicationSemantics_iff_fused
    (callerFrame : RuntimeFrame) (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (uniqueNames : (floatingVariableNames assertion.hypotheses).Nodup) :
    AssertionApplicationSemantics callerFrame assertion actuals result ↔
      FusedAssertionApplicationSemantics callerFrame assertion actuals
        result := by
  constructor
  · rintro ⟨substitution, instances, essential, dv, resultSemantics⟩
    have unique : SubstitutionKeysUnique substitution :=
      instances.substitutionKeysUnique uniqueNames
    exact ⟨substitution, instances,
      (runFusedEssentialMatches_iff unique assertion.hypotheses actuals).2
        essential,
      dv,
      (instantiate_formulaTemplate_iff unique assertion.formula result).2
        resultSemantics⟩
  · rintro ⟨substitution, instances, essential, dv, resultCompiled⟩
    have unique : SubstitutionKeysUnique substitution :=
      instances.substitutionKeysUnique uniqueNames
    exact ⟨substitution, instances,
      (runFusedEssentialMatches_iff unique assertion.hypotheses actuals).1
        essential,
      dv,
      (instantiate_formulaTemplate_iff unique assertion.formula result).1
        resultCompiled⟩

/-- Every assertion retained by a successful live-prefix projection receives
the fused implementation theorem automatically.  The projection invariant,
not a caller assertion, discharges unique-key functionality. -/
theorem projected_assertionApplicationSemantics_iff_fused
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (projected : projectPrefix? db = some projection)
    (member : assertion ∈ projection.assertions)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    AssertionApplicationSemantics projection.callerFrame assertion actuals
        result ↔
      FusedAssertionApplicationSemantics projection.callerFrame assertion
        actuals result :=
  assertionApplicationSemantics_iff_fused projection.callerFrame assertion
    actuals result
    (projectedAssertion_floatingVariableNames_nodup db projection assertion
      projected member)

/-! ## Positive and refusing controls -/

namespace Examples

private def emptyFrame : RuntimeFrame := ⟨#[], #[]⟩

private def replacementA : ConstantHeadedFormula :=
  ⟨"wff", [.const "A"]⟩

private def essentialTemplate : ConstantHeadedFormula :=
  ⟨"|-", [.var "x"]⟩

private def resultA : ConstantHeadedFormula :=
  ⟨"|-", [.const "A"]⟩

private def assertion : AssertionView :=
  { label := "ax-fused"
    formula := essentialTemplate
    frame := emptyFrame
    hypotheses :=
      [.floating "wx" "wff" "x",
       .essential "hx" essentialTemplate] }

private def actuals : List ConstantHeadedFormula :=
  [replacementA, resultA]

private def sourceSemantics :
    AssertionApplicationSemantics emptyFrame assertion actuals resultA := by
  let substitution : FiniteSubstitution := [⟨"x", replacementA⟩]
  refine ⟨substitution, .floating rfl (.essential rfl .nil), ?_, ?_, ?_⟩
  · refine ⟨⟨rfl, ?_⟩, trivial⟩
    change BodySubstitution substitution [.var "x"] [.const "A"]
    apply BodySubstitution.var (replacement := replacementA)
    · show ({ variableName := "x", replacement := replacementA } :
        FormulaBinding) ∈ substitution
      simp [substitution]
    · exact .nil
  · change DVListsSemantics substitution [] []
    intro pair member
    simp at member
  · refine ⟨rfl, ?_⟩
    change BodySubstitution substitution [.var "x"] [.const "A"]
    apply BodySubstitution.var (replacement := replacementA)
    · show ({ variableName := "x", replacement := replacementA } :
        FormulaBinding) ∈ substitution
      simp [substitution]
    · exact .nil

/-- Positive: one floating binding is reused by both an essential-hypothesis
comparison and the assertion conclusion without materializing either
substituted template. -/
theorem fused_assertion_positive :
    FusedAssertionApplicationSemantics emptyFrame assertion actuals resultA :=
  (assertionApplicationSemantics_iff_fused emptyFrame assertion actuals
    resultA (by decide)).1 sourceSemantics

private def replacementB : ConstantHeadedFormula :=
  ⟨"wff", [.const "B"]⟩

private def duplicateSubstitution : FiniteSubstitution :=
  [⟨"x", replacementA⟩, ⟨"x", replacementB⟩]

private def variableFormula : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

/-- The relational source may select the later duplicate occurrence. -/
theorem duplicate_relationally_selects_later :
    FormulaSubstitutionSemantics duplicateSubstitution variableFormula
      replacementB := by
  refine ⟨rfl, ?_⟩
  change BodySubstitution duplicateSubstitution [.var "x"] [.const "B"]
  apply BodySubstitution.var (replacement := replacementB)
  · show ({ variableName := "x", replacement := replacementB } :
      FormulaBinding) ∈ duplicateSubstitution
    simp [duplicateSubstitution]
  · exact .nil

/-- The deterministic fused compiler selects the first occurrence instead.
This is the concrete obstruction discharged by projection's unique-key
invariant. -/
theorem duplicate_fused_refuses_later :
    fusedMatch (lookupBody? duplicateSubstitution)
      (formulaTemplate variableFormula) (formulaTokens replacementB) = none := by
  rfl

theorem duplicate_keys_not_unique :
    ¬ SubstitutionKeysUnique duplicateSubstitution := by
  intro unique
  simp [SubstitutionKeysUnique, duplicateSubstitution] at unique

end Examples

#print axioms lookupBody?_eq_some_iff_of_unique
#print axioms instantiate_bodyTemplate_iff
#print axioms fusedMatch_formula_iff
#print axioms runFusedEssentialMatches_iff
#print axioms assertionApplicationSemantics_iff_fused
#print axioms projected_assertionApplicationSemantics_iff_fused
#print axioms Examples.fused_assertion_positive
#print axioms Examples.duplicate_relationally_selects_later
#print axioms Examples.duplicate_fused_refuses_later

end Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation
