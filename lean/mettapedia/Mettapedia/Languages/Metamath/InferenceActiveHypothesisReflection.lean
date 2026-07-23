import Mettapedia.Languages.Metamath.InferenceProjectionProvesRuleInversion
import Mettapedia.Languages.Metamath.InferenceActiveHypothesisLeaf
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesTree

/-!
# Reflection of active-hypothesis derivation roots

The raw active-hypothesis branch of projected `Proves` root classification is
rigid: it has the canonical rule instance, no premises, and the exact encoded
hypothesis formula.  Consequently an arbitrary generic derivation whose root
has that classification reflects to the corresponding source-pinned active
leaf with exactly the same raw erasure.

This module is static.  It imports neither live proof-state execution nor
runtime checker agreement, and it makes no claim about assertion roots or
recursive reflection of arbitrary child derivations.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

/-! ## Exact active-application data -/

/-- An active-hypothesis application view determines every generic root
output: its source hypothesis, canonical nullary rule instance, empty premise
list, and exact encoded conclusion. -/
theorem ActiveHypothesisApplicationView.exact
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (view : ActiveHypothesisApplicationView projection target ruleInstance
      premises formulaPattern) :
    ∃ hypothesis : HypothesisView,
      hypothesis ∈ projection.activeHypotheses ∧
      ruleInstance = activeHypothesisRuleInstance hypothesis ∧
      premises = [] ∧
      formulaPattern = encodeFormula hypothesis.formula := by
  rcases view with
    ⟨hypothesis, hmember, hlookup, harguments, hpremises, hconclusion⟩
  have hargumentsEq : ruleInstance.arguments = [] := by
    cases hargs : ruleInstance.arguments with
    | nil => rfl
    | cons argument arguments =>
        simp [activeHypothesisRule, argumentsValidAt, hargs] at harguments
  have hlookupFind :
      List.find? (fun candidate : RuleSchema =>
        decide (candidate.id = ruleInstance.ruleId)) target.1.rules =
          some (activeHypothesisRule hypothesis) := by
    simpa [Presentation.lookupRule?] using hlookup
  have hidBool :
      decide ((activeHypothesisRule hypothesis).id =
        ruleInstance.ruleId) = true := by
    exact List.find?_some
      (p := fun candidate : RuleSchema =>
        decide (candidate.id = ruleInstance.ruleId))
      (a := activeHypothesisRule hypothesis) hlookupFind
  have hid :
      (activeHypothesisRule hypothesis).id = ruleInstance.ruleId :=
    of_decide_eq_true hidBool
  have hruleInstance :
      ruleInstance = activeHypothesisRuleInstance hypothesis := by
    rcases ruleInstance with ⟨ruleId, arguments⟩
    change arguments = [] at hargumentsEq
    change (activeHypothesisRule hypothesis).id = ruleId at hid
    subst arguments
    subst ruleId
    rfl
  have application :
      RuleApplication target ruleInstance premises
        (proves formulaPattern) :=
    ActiveHypothesisApplicationView.toRuleApplication
      ⟨hypothesis, hmember, hlookup, harguments, hpremises, hconclusion⟩
  have canonicalApplication :
      RuleApplication target (activeHypothesisRuleInstance hypothesis)
        premises (proves formulaPattern) := by
    simpa [hruleInstance] using application
  have houtputs := canonicalApplication.outputs_unique
    (activeHypothesisRule_application projection target hprojection hmember)
  have hformula :
      formulaPattern = encodeFormula hypothesis.formula := by
    simpa [proves] using houtputs.2
  exact ⟨hypothesis, hmember, hruleInstance, houtputs.1, hformula⟩

/-! ## Active-root reflection -/

/-- Evidence that the actual root of a generic `Proves` derivation is the
active branch of projected source-rule classification.  The constructor keeps
the classifier attached to the same dependent root data; it does not assume
canonical outputs. -/
inductive ActiveHypothesisDerivationRootView
    (projection : PrefixProjection) (target : ValidatedPresentation)
    {formulaPattern : Pattern} :
    Derivation target (proves formulaPattern) → Prop where
  | intro {ruleInstance : RuleInstance} {premises : List Pattern}
      (application :
        RuleApplication target ruleInstance premises
          (proves formulaPattern))
      (children : DerivationList target premises)
      (view : ActiveHypothesisApplicationView projection target ruleInstance
        premises formulaPattern) :
      ActiveHypothesisDerivationRootView projection target
        (.byRule ruleInstance application children)

/-- Reflect an arbitrary generic derivation with an active-classified root to
the corresponding canonical generated active leaf.  The reflected leaf and
the original derivation have exactly equal raw erasures. -/
theorem ActiveHypothesisDerivationRootView.reflect
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulaPattern : Pattern}
    (derivation : Derivation target (proves formulaPattern))
    (rootView :
      ActiveHypothesisDerivationRootView projection target derivation) :
    ∃ hypothesis : HypothesisView,
      ∃ hmember : hypothesis ∈ projection.activeHypotheses,
        formulaPattern = encodeFormula hypothesis.formula ∧
        ∃ tree : GeneratedProvesTree projection target hypothesis.formula,
          tree = .active hypothesis hmember ∧
          derivation.erase = (tree.toDerivation hprojection).erase := by
  cases rootView with
  | @intro ruleInstance premises application children view =>
      rcases view.exact hprojection with
        ⟨hypothesis, hmember, hruleInstance, hpremises, hformula⟩
      let tree : GeneratedProvesTree projection target hypothesis.formula :=
        .active hypothesis hmember
      refine ⟨hypothesis, hmember, hformula, tree, rfl, ?_⟩
      subst premises
      cases children with
      | nil =>
          change .node ruleInstance [] =
            (tree.toDerivation hprojection).erase
          rw [hruleInstance]
          simpa [tree, GeneratedProvesTree.canonicalRawProof] using
            (tree.erase_toDerivation hprojection).symm

/-- The root classifier is inhabited by every canonical generated active
hypothesis leaf. -/
theorem activeHypothesisDerivation_rootView
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    ActiveHypothesisDerivationRootView projection target
      (activeHypothesisDerivation projection target hprojection hmember) := by
  have application :=
    activeHypothesisRule_application projection target hprojection hmember
  have view : ActiveHypothesisApplicationView projection target
      (activeHypothesisRuleInstance hypothesis) []
      (encodeFormula hypothesis.formula) := by
    cases application with
    | intro rule hlookup harguments _hsideConditions hpremises hconclusion =>
        have hcanonicalLookup := lookup_activeHypothesisRule_of_projection
          projection target hprojection hmember
        have hrule : rule = activeHypothesisRule hypothesis :=
          Option.some.inj (hlookup.symm.trans hcanonicalLookup)
        subst rule
        exact ⟨hypothesis, hmember, hlookup, harguments, hpremises,
          hconclusion⟩
  exact .intro
    (activeHypothesisRule_application projection target hprojection hmember)
    .nil view

/-! ## Positive and negative boundaries -/

/-- Positive boundary: the exact active-root result is available from raw
classification evidence alone. -/
example {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (view : ActiveHypothesisApplicationView projection target ruleInstance
      premises formulaPattern) :
    ∃ hypothesis : HypothesisView,
      hypothesis ∈ projection.activeHypotheses ∧
      ruleInstance = activeHypothesisRuleInstance hypothesis ∧
      premises = [] ∧
      formulaPattern = encodeFormula hypothesis.formula :=
  view.exact hprojection

/-- Negative boundary: a rule instance with any argument cannot be an active
hypothesis root, since every generated active-hypothesis schema is nullary. -/
theorem not_activeHypothesisApplicationView_of_arguments_ne_nil
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {formulaPattern : Pattern}
    (harguments : ruleInstance.arguments ≠ []) :
    ¬ ActiveHypothesisApplicationView projection target ruleInstance
      premises formulaPattern := by
  intro view
  rcases view.exact hprojection with
    ⟨hypothesis, _hmember, hruleInstance, _hpremises, _hformula⟩
  apply harguments
  rw [hruleInstance]
  rfl

/-- Negative boundary: an active-classified root cannot conclude a pattern
different from every retained active hypothesis encoding. -/
theorem not_activeHypothesisDerivationRootView_of_formula_mismatch
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulaPattern : Pattern}
    (derivation : Derivation target (proves formulaPattern))
    (hmismatch : ∀ hypothesis : HypothesisView,
      hypothesis ∈ projection.activeHypotheses →
      formulaPattern ≠ encodeFormula hypothesis.formula) :
    ¬ ActiveHypothesisDerivationRootView projection target derivation := by
  intro rootView
  rcases rootView.reflect hprojection derivation with
    ⟨hypothesis, hmember, hformula, _tree, _htree, _herase⟩
  exact hmismatch hypothesis hmember hformula

end Mettapedia.Languages.Metamath.InferenceProjection
