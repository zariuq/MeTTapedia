import Mettapedia.Languages.Metamath.InferenceAssertionApplication
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants

/-!
# Projection invariants for instantiated Metamath assertions

`HypothesisInstances` constructs the concrete finite substitution used by a
generated assertion node.  This module proves that its keys are exactly the
authored floating-variable names, in source order, and transfers the
projector's distinct-name invariant to `SubstitutionKeysUnique`.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- The concrete binding-list keys are precisely the floating mandatory
hypothesis names; essential hypotheses contribute no key.  Both lists retain
source order. -/
theorem HypothesisInstances.substitutionKeys_eq
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution) :
    substitution.map FormulaBinding.variableName =
      floatingVariableNames hypotheses := by
  induction instances with
  | nil => rfl
  | floating _ _ ih =>
      simp [floatingVariableNames, HypothesisView.floatingVariable?, ih]
  | essential _ _ ih =>
      simpa [floatingVariableNames, HypothesisView.floatingVariable?] using ih

/-- Distinct authored floating names transfer exactly to the finite
substitution constructed from actual hypothesis instances. -/
theorem HypothesisInstances.substitutionKeysUnique
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (hnames : (floatingVariableNames hypotheses).Nodup) :
    SubstitutionKeysUnique substitution := by
  unfold SubstitutionKeysUnique
  rw [instances.substitutionKeys_eq]
  exact hnames

/-- Revalidation of an assertion view supplies unique keys for every one of
its concrete hypothesis-instance substitutions. -/
theorem HypothesisInstances.substitutionKeysUnique_of_assertionViewValid
    (declaredConstants declaredVariables : List String)
    {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hvalid :
      assertionViewValid declaredConstants declaredVariables assertion = true) :
    SubstitutionKeysUnique substitution :=
  instances.substitutionKeysUnique
    (assertion_floatingVariableNames_nodup_of_assertionViewValid
      declaredConstants declaredVariables assertion hvalid)

/-- A retained assertion in a successful live-prefix projection therefore
constructs only unique-key substitutions. -/
theorem HypothesisInstances.substitutionKeysUnique_of_projectedAssertion
    (db : RuntimeDB) (projection : PrefixProjection)
    {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    SubstitutionKeysUnique substitution :=
  instances.substitutionKeysUnique
    (projectedAssertion_floatingVariableNames_nodup
      db projection assertion hproject hmember)

/-- The same invariant is available from exact successful presentation
generation, before composing with generic node evidence. -/
theorem HypothesisInstances.substitutionKeysUnique_of_generatedAssertion
    (projection : PrefixProjection) (presentation : CalculusLanguageDef)
    {assertion : AssertionView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hprojection :
      calculusLanguageDefOfProjection? projection = some presentation)
    (hmember : assertion ∈ projection.assertions) :
    SubstitutionKeysUnique substitution :=
  instances.substitutionKeysUnique
    (generatedAssertion_floatingVariableNames_nodup
      projection presentation assertion hprojection hmember)

section Examples

private def actualX : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

private def actualY : ConstantHeadedFormula :=
  ⟨"wff", [.var "y"]⟩

private def distinctInstances :
    HypothesisInstances
      [.floating "wx" "wff" "x", .floating "wy" "wff" "y"]
      [actualX, actualY]
      [⟨"x", actualX⟩, ⟨"y", actualY⟩] :=
  .floating rfl (.floating rfl .nil)

/-- Positive boundary: distinct projected names become unique concrete keys. -/
example :
    SubstitutionKeysUnique [⟨"x", actualX⟩, ⟨"y", actualY⟩] := by
  apply distinctInstances.substitutionKeysUnique
  decide

private def duplicateInstances :
    HypothesisInstances
      [.floating "wx" "wff" "x", .floating "wx2" "wff" "x"]
      [actualX, actualY]
      [⟨"x", actualX⟩, ⟨"x", actualY⟩] :=
  .floating rfl (.floating rfl .nil)

/-- Negative boundary: the instance relation alone deliberately permits a
duplicate authored key; only successful projection rules it out. -/
example :
    ¬SubstitutionKeysUnique [⟨"x", actualX⟩, ⟨"x", actualY⟩] := by
  simp [SubstitutionKeysUnique]

example :
    [⟨"x", actualX⟩, ⟨"x", actualY⟩].map
        FormulaBinding.variableName = ["x", "x"] :=
  duplicateInstances.substitutionKeys_eq

end Examples

end Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
