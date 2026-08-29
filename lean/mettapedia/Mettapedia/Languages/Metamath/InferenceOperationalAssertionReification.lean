import Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification

open Mettapedia.GSLT.LanguageDef

/-!
# Canonical assertion evidence from operational Metamath data

This file reifies the operational mandatory-hypothesis vector, result, finite
substitution, and side conditions of one assertion application.  The caller
and callee classifications remain explicit: operational expressions erase
symbol tags, so reverse construction requires the source formulas' tags to
respect the callee frame and their surviving constants to avoid caller-active
names.

The endpoint constructs a local proof-relevant generated assertion node under
those conditions.  It does not yet invert an arbitrary singleton proof step,
recover an erased source label, identify an operational suffix with a runtime
prefix, or provide recursive proofs of the leading `Proves` premises.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceOperationalExprReification
open Mettapedia.Languages.Metamath.InferenceOperationalSubstitutionReification

/-! ## Canonical mandatory actuals and result -/

/-- Reify the exact operational mandatory-hypothesis instance in authored
order.  The callee active-name list controls source substitution; the caller
active-name list controls the reconstructed tags of each resulting formula. -/
def reifyOperationalActuals (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst) :
    List HypothesisView → List ConstantHeadedFormula
  | [] => []
  | .floating _label _typecode variableName :: hypotheses =>
      reifyOperationalExpr callerActiveNames
          (specSubstitution ⟨variableName⟩) ::
        reifyOperationalActuals callerActiveNames calleeActiveNames
          specSubstitution hypotheses
  | .essential _label formula :: hypotheses =>
      reifyOperationalExpr callerActiveNames
          (Metamath.Spec.applySubst
            (calleeActiveNames.map Metamath.Spec.Variable.mk)
            specSubstitution (operationalExpr formula)) ::
        reifyOperationalActuals callerActiveNames calleeActiveNames
          specSubstitution hypotheses

/-- The canonical reified conclusion of an operational assertion
application. -/
def reifyOperationalResult (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (formula : ConstantHeadedFormula) : ConstantHeadedFormula :=
  reifyOperationalExpr callerActiveNames
    (Metamath.Spec.applySubst
      (calleeActiveNames.map Metamath.Spec.Variable.mk)
      specSubstitution (operationalExpr formula))

/-- Erasing the canonical actual vector gives exactly the operational
authored-order mandatory vector. -/
theorem map_operationalExpr_reifyOperationalActuals
    (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView) :
    (reifyOperationalActuals callerActiveNames calleeActiveNames
        specSubstitution hypotheses).map operationalExpr =
      (hypotheses.map operationalHyp).map fun hypothesis =>
        match hypothesis with
        | .floating _ variableName => specSubstitution variableName
        | .essential expression =>
            Metamath.Spec.applySubst
              (calleeActiveNames.map Metamath.Spec.Variable.mk)
              specSubstitution expression := by
  induction hypotheses with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [reifyOperationalActuals, operationalHyp, ih]

@[simp] theorem operationalExpr_reifyOperationalResult
    (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (formula : ConstantHeadedFormula) :
    operationalExpr
        (reifyOperationalResult callerActiveNames calleeActiveNames
          specSubstitution formula) =
      Metamath.Spec.applySubst
        (calleeActiveNames.map Metamath.Spec.Variable.mk)
        specSubstitution (operationalExpr formula) := by
  simp [reifyOperationalResult]

/-! ## Reified independent semantics -/

/-- Operational floating-type evidence constructs the exact generated
hypothesis-instance relation for the canonical actual vector. -/
theorem hypothesisInstances_reifyOperationalActuals
    (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (htyped : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈
          hypotheses.map operationalHyp →
        (specSubstitution variableName).typecode = typecode) :
    HypothesisInstances hypotheses
      (reifyOperationalActuals callerActiveNames calleeActiveNames
        specSubstitution hypotheses)
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses) := by
  induction hypotheses with
  | nil => exact .nil
  | cons hypothesis hypotheses ih =>
      have htailTyped : ∀ typecode variableName,
          Metamath.Spec.Hyp.floating typecode variableName ∈
              hypotheses.map operationalHyp →
            (specSubstitution variableName).typecode = typecode := by
        intro typecode variableName hmember
        exact htyped typecode variableName (by simp [hmember])
      cases hypothesis with
      | floating label typecode variableName =>
          have hheadTyped := htyped ⟨typecode⟩ ⟨variableName⟩ (by
            simp [operationalHyp])
          have htypecode :
              (reifyOperationalExpr callerActiveNames
                (specSubstitution ⟨variableName⟩)).typecode = typecode := by
            exact congrArg Metamath.Spec.Constant.c hheadTyped
          exact .floating htypecode (ih htailTyped)
      | essential label formula =>
          have htypecode :
              (reifyOperationalExpr callerActiveNames
                (Metamath.Spec.applySubst
                  (calleeActiveNames.map Metamath.Spec.Variable.mk)
                  specSubstitution (operationalExpr formula))).typecode =
                formula.typecode := by
            simp [Metamath.Spec.applySubst]
          exact .essential htypecode (ih htailTyped)

/-- Any hypothesis-instance witness over the canonical actual vector has
exactly the authored canonical finite substitution.  This makes the finite
syntax public rather than leaving it hidden behind an existential node. -/
theorem hypothesisInstances_reifyOperationalActuals_substitution_eq
    (callerActiveNames calleeActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (finiteSubstitution : FiniteSubstitution)
    (instances : HypothesisInstances hypotheses
      (reifyOperationalActuals callerActiveNames calleeActiveNames
        specSubstitution hypotheses)
      finiteSubstitution) :
    finiteSubstitution =
      reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses := by
  induction hypotheses generalizing finiteSubstitution with
  | nil =>
      cases instances
      rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis with
      | floating label typecode variableName =>
          cases instances with
          | floating _ tail =>
              simp only [reifyOperationalSubstitution,
                List.cons.injEq, true_and]
              exact ih _ tail
      | essential label formula =>
          cases instances with
          | essential _ tail =>
              simpa only [reifyOperationalActuals,
                reifyOperationalSubstitution] using ih _ tail

/-- Reifying every operational essential-hypothesis instance constructs the
exact independent essential-match relation against the full authored finite
substitution. -/
theorem essentialMatches_reifyOperationalActuals
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (fullHypotheses hypotheses : List HypothesisView)
    (hnames : (floatingVariableNames fullHypotheses).Nodup)
    (hrespect : ∀ hypothesis, hypothesis ∈ hypotheses →
      formulaSymbolsRespectFrame
        (floatingVariableNames fullHypotheses) hypothesis.formula = true)
    (hconstants : ∀ hypothesis, hypothesis ∈ hypotheses →
      FormulaConstantsAvoid callerActiveNames hypothesis.formula) :
    EssentialMatches
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        fullHypotheses)
      hypotheses
      (reifyOperationalActuals callerActiveNames
        (floatingVariableNames fullHypotheses) specSubstitution hypotheses) := by
  induction hypotheses with
  | nil => trivial
  | cons hypothesis hypotheses ih =>
      have htailRespect : ∀ tailHypothesis,
          tailHypothesis ∈ hypotheses →
            formulaSymbolsRespectFrame
              (floatingVariableNames fullHypotheses)
              tailHypothesis.formula = true := by
        intro tailHypothesis hmember
        exact hrespect tailHypothesis (List.mem_cons_of_mem _ hmember)
      have htailConstants : ∀ tailHypothesis,
          tailHypothesis ∈ hypotheses →
            FormulaConstantsAvoid callerActiveNames tailHypothesis.formula := by
        intro tailHypothesis hmember
        exact hconstants tailHypothesis (List.mem_cons_of_mem _ hmember)
      cases hypothesis with
      | floating label typecode variableName =>
          exact ih htailRespect htailConstants
      | essential label formula =>
          constructor
          · exact spec_applySubst_to_formulaSubstitutionSemantics
              callerActiveNames specSubstitution fullHypotheses hnames formula
              (hrespect (.essential label formula) List.mem_cons_self)
              (hconstants (.essential label formula) List.mem_cons_self)
          · exact ih htailRespect htailConstants

/-- The same construction supplies result substitution semantics. -/
theorem formulaSubstitutionSemantics_reifyOperationalResult
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hypotheses : List HypothesisView)
    (hnames : (floatingVariableNames hypotheses).Nodup)
    (formula : ConstantHeadedFormula)
    (hrespect : formulaSymbolsRespectFrame
      (floatingVariableNames hypotheses) formula = true)
    (hconstants : FormulaConstantsAvoid callerActiveNames formula) :
    FormulaSubstitutionSemantics
      (reifyOperationalSubstitution callerActiveNames specSubstitution
        hypotheses)
      formula
      (reifyOperationalResult callerActiveNames
        (floatingVariableNames hypotheses) specSubstitution formula) := by
  exact spec_applySubst_to_formulaSubstitutionSemantics
    callerActiveNames specSubstitution hypotheses hnames formula hrespect
      hconstants

/-! ## Conditional local generated-node reconstruction -/

/-- Operational typing, substitution, and DV data reconstruct the complete
independent local assertion semantics under the explicit tag-classification
boundary. -/
theorem assertionApplicationSemantics_of_operational
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (callerFrame : RuntimeFrame) (assertion : AssertionView)
    (hnames : (floatingVariableNames assertion.hypotheses).Nodup)
    (htyped : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈
          assertion.hypotheses.map operationalHyp →
        (specSubstitution variableName).typecode = typecode)
    (hhypRespect : ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      formulaSymbolsRespectFrame
        (floatingVariableNames assertion.hypotheses)
        hypothesis.formula = true)
    (hhypConstants : ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      FormulaConstantsAvoid callerActiveNames hypothesis.formula)
    (hresultRespect : formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses)
      assertion.formula = true)
    (hresultConstants :
      FormulaConstantsAvoid callerActiveNames assertion.formula)
    (hcalleeDV : frameDVValid assertion.frame
      (floatingVariableNames assertion.hypotheses) = true)
    (hdv : Metamath.Spec.dvOK
      (callerActiveNames.map Metamath.Spec.Variable.mk)
      (ToSpecDVPairs assertion.frame.dj.toList)
      (ToSpecDVPairs callerFrame.dj.toList) specSubstitution) :
    AssertionApplicationSemantics callerFrame assertion
      (reifyOperationalActuals callerActiveNames
        (floatingVariableNames assertion.hypotheses) specSubstitution
        assertion.hypotheses)
      (reifyOperationalResult callerActiveNames
        (floatingVariableNames assertion.hypotheses) specSubstitution
        assertion.formula) := by
  let finiteSubstitution := reifyOperationalSubstitution callerActiveNames
    specSubstitution assertion.hypotheses
  refine ⟨finiteSubstitution, ?_, ?_, ?_, ?_⟩
  · exact hypothesisInstances_reifyOperationalActuals callerActiveNames
      (floatingVariableNames assertion.hypotheses) specSubstitution
      assertion.hypotheses htyped
  · exact essentialMatches_reifyOperationalActuals callerActiveNames
      specSubstitution assertion.hypotheses assertion.hypotheses hnames
      hhypRespect hhypConstants
  · exact spec_dvOK_to_dvOKSemantics callerActiveNames specSubstitution
      assertion.hypotheses callerFrame assertion.frame
      (dvVariablesCovered_of_frameDVValid assertion.hypotheses
        assertion.frame hcalleeDV)
      hdv
  · exact formulaSubstitutionSemantics_reifyOperationalResult
      callerActiveNames specSubstitution assertion.hypotheses hnames
      assertion.formula hresultRespect hresultConstants

/-- Under a successful presentation projection, the same operational package
constructs a proof-relevant local generated assertion node.  Leading native
proofs of the actual formulas remain external. -/
theorem generatedAssertionNode_of_operational
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions)
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hnames : (floatingVariableNames assertion.hypotheses).Nodup)
    (htyped : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈
          assertion.hypotheses.map operationalHyp →
        (specSubstitution variableName).typecode = typecode)
    (hhypRespect : ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      formulaSymbolsRespectFrame
        (floatingVariableNames assertion.hypotheses)
        hypothesis.formula = true)
    (hhypConstants : ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      FormulaConstantsAvoid callerActiveNames hypothesis.formula)
    (hresultRespect : formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses)
      assertion.formula = true)
    (hresultConstants :
      FormulaConstantsAvoid callerActiveNames assertion.formula)
    (hcalleeDV : frameDVValid assertion.frame
      (floatingVariableNames assertion.hypotheses) = true)
    (hdv : Metamath.Spec.dvOK
      (callerActiveNames.map Metamath.Spec.Variable.mk)
      (ToSpecDVPairs assertion.frame.dj.toList)
      (ToSpecDVPairs projection.callerFrame.dj.toList) specSubstitution) :
    Nonempty
      (Σ finiteSubstitution : FiniteSubstitution,
        GeneratedAssertionNode projection target assertion
          (reifyOperationalActuals callerActiveNames
            (floatingVariableNames assertion.hypotheses) specSubstitution
            assertion.hypotheses)
          (reifyOperationalResult callerActiveNames
            (floatingVariableNames assertion.hypotheses) specSubstitution
            assertion.formula)
          finiteSubstitution) := by
  apply (generatedAssertionNode_nonempty_iff_semantics projection target
    hprojection hmember _ _).2
  exact assertionApplicationSemantics_of_operational callerActiveNames
    specSubstitution projection.callerFrame assertion hnames htyped
    hhypRespect hhypConstants hresultRespect hresultConstants hcalleeDV
    hdv

/-- Exact-witness form of the operational constructor: the generated node is
indexed by the canonical authored finite substitution itself, not merely by an
existential finite substitution that happens to be constructed canonically. -/
theorem generatedAssertionNode_of_operational_exact
    (projection : PrefixProjection) (target : ValidatedCalculusLanguageDef)
    (hprojection : calculusLanguageDefOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (hmember : assertion ∈ projection.assertions)
    (callerActiveNames : List String)
    (specSubstitution : Metamath.Spec.Subst)
    (hnames : (floatingVariableNames assertion.hypotheses).Nodup)
    (htyped : ∀ typecode variableName,
      Metamath.Spec.Hyp.floating typecode variableName ∈
          assertion.hypotheses.map operationalHyp →
        (specSubstitution variableName).typecode = typecode)
    (hhypRespect : ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      formulaSymbolsRespectFrame
        (floatingVariableNames assertion.hypotheses)
        hypothesis.formula = true)
    (hhypConstants : ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      FormulaConstantsAvoid callerActiveNames hypothesis.formula)
    (hresultRespect : formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses)
      assertion.formula = true)
    (hresultConstants :
      FormulaConstantsAvoid callerActiveNames assertion.formula)
    (hcalleeDV : frameDVValid assertion.frame
      (floatingVariableNames assertion.hypotheses) = true)
    (hdv : Metamath.Spec.dvOK
      (callerActiveNames.map Metamath.Spec.Variable.mk)
      (ToSpecDVPairs assertion.frame.dj.toList)
      (ToSpecDVPairs projection.callerFrame.dj.toList) specSubstitution) :
    Nonempty
      (GeneratedAssertionNode projection target assertion
        (reifyOperationalActuals callerActiveNames
          (floatingVariableNames assertion.hypotheses) specSubstitution
          assertion.hypotheses)
        (reifyOperationalResult callerActiveNames
          (floatingVariableNames assertion.hypotheses) specSubstitution
          assertion.formula)
        (reifyOperationalSubstitution callerActiveNames specSubstitution
          assertion.hypotheses)) := by
  rcases generatedAssertionNode_of_operational projection target hprojection
      assertion hmember callerActiveNames specSubstitution hnames htyped
      hhypRespect hhypConstants hresultRespect hresultConstants hcalleeDV
      hdv with
    ⟨⟨finiteSubstitution, node⟩⟩
  have instances :=
    (assertionRuleApplication_iff_instances projection target hprojection
      hmember).mp node.application |>.1
  have hfinite :=
    hypothesisInstances_reifyOperationalActuals_substitution_eq
      callerActiveNames (floatingVariableNames assertion.hypotheses)
      specSubstitution assertion.hypotheses finiteSubstitution instances
  subst finiteSubstitution
  exact ⟨node⟩

end Mettapedia.Languages.Metamath.InferenceOperationalAssertionReification
