import Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants
import Metamath.Spec.Equivalence

/-!
# Declarative adequacy of source-owned Metamath inference

This file connects the source-derived checker GSLT semantics to Metamath's
declarative semantics.  All database, frame, declaration, and disjointness
premises are derived from the same validated `SourcePrefix`; no runtime parser
database is used to supply them.
-/

namespace Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceOperationalExprReification
open Mettapedia.Languages.Metamath.InferenceOperationalProjectionReification
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
open Metamath.Spec.Equivalence

/-! ## Source-derived declaration semantics -/

/-- The global constant predicate authored by a source prefix. -/
def sourceConstantSet (source : SourcePrefix) : Metamath.Spec.ConstSet :=
  fun symbol => symbol ∈ source.declaredConstants

/-- A tagged source formula accepted by both the declaration and frame gates
has all operational variables in scope. -/
theorem operationalExpr_varsInScope_of_sourceGates
    (declaredConstants declaredVariables : List String)
    (frame : SourceFrame) (hypotheses : List HypothesisView)
    (formula : InferenceEncoding.ConstantHeadedFormula)
    (hframe :
      formulaSymbolsRespectFrame
        (floatingVariableNames hypotheses) formula = true)
    (hdeclarations :
      formulaSymbolsRespectDeclarations
        declaredConstants declaredVariables formula = true) :
    Metamath.Spec.ExprVarsInScope
      (fun symbol => symbol ∈ declaredConstants)
      (sourceOperationalFrame frame hypotheses)
      (operationalExpr formula) := by
  intro symbol hsymbol
  rw [operationalExpr_syms] at hsymbol
  rcases List.mem_map.mp hsymbol with
    ⟨taggedSymbol, htagged, hvalue⟩
  subst symbol
  cases taggedSymbol with
  | const constantName =>
      right
      simp only [formulaSymbolsRespectDeclarations, Bool.and_eq_true]
        at hdeclarations
      exact List.contains_iff_mem.mp
        (List.all_eq_true.mp hdeclarations.2
          (.const constantName) htagged)
  | var variableName =>
      left
      rw [show
        (sourceOperationalFrame frame hypotheses).vars =
          (floatingVariableNames hypotheses).map
            Metamath.Spec.Variable.mk by
          exact operationalFrame_vars frame.toRuntime hypotheses]
      apply List.mem_map.mpr
      refine ⟨variableName, ?_, rfl⟩
      simp only [formulaSymbolsRespectFrame] at hframe
      exact List.contains_iff_mem.mp
        (List.all_eq_true.mp hframe (.var variableName) htagged)

/-- Frame variables accepted by the declaration partition cannot also be
global constants. -/
theorem sourceOperationalFrame_varsDisjointConsts
    (declaredConstants declaredVariables : List String)
    (frame : SourceFrame) (hypotheses : List HypothesisView)
    (hseparate :
      declaredConstants.all (fun constantName =>
        !(declaredVariables.contains constantName)) = true)
    (hhypothesesDeclared :
      hypotheses.all
        (formulaSymbolsRespectDeclarations declaredConstants
          declaredVariables ∘ HypothesisView.formula) = true) :
    Metamath.Spec.FrameVarsDisjointConsts
      (fun symbol => symbol ∈ declaredConstants)
      (sourceOperationalFrame frame hypotheses) := by
  intro sourceVariable hvariable hconstant
  rw [show
    (sourceOperationalFrame frame hypotheses).vars =
      (floatingVariableNames hypotheses).map
        Metamath.Spec.Variable.mk by
      exact operationalFrame_vars frame.toRuntime hypotheses] at hvariable
  rcases List.mem_map.mp hvariable with
    ⟨variableName, hvariableName, hvariable⟩
  cases hvariable
  have hdeclaredVariable :
      variableName ∈ declaredVariables :=
    floatingVariable_mem_declaredVariables_of_declarations
      declaredConstants declaredVariables hypotheses
      hhypothesesDeclared hvariableName
  have hnotVariable :=
    List.all_eq_true.mp hseparate variableName hconstant
  have hcontains :
      declaredVariables.contains variableName = true :=
    List.contains_iff_mem.mpr hdeclaredVariable
  rw [hcontains] at hnotVariable
  contradiction

/-! ## Source frame structural invariants -/

@[simp] theorem floatList_sourceOperationalFrame
    (frame : SourceFrame) (hypotheses : List HypothesisView) :
    (floatList (sourceOperationalFrame frame hypotheses)).map Prod.snd =
      (floatingVariableNames hypotheses).map Metamath.Spec.Variable.mk := by
  induction hypotheses with
  | nil =>
      rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [floatList, sourceOperationalFrame, operationalFrame,
          operationalHyp, floatingVariableNames,
          HypothesisView.floatingVariable?] at ih ⊢ <;>
        exact ih

/-- Membership of an operational floating hypothesis exposes its authored
floating-variable name. -/
private theorem floatingName_mem_of_operationalHyp_mem
    (hypotheses : List HypothesisView)
    {typecode : Metamath.Spec.Constant}
    {variableName : Metamath.Spec.Variable}
    (hmember :
      Metamath.Spec.Hyp.floating typecode variableName ∈
        hypotheses.map operationalHyp) :
    variableName.v ∈ floatingVariableNames hypotheses := by
  rcases List.mem_map.mp hmember with
    ⟨hypothesis, hhypothesis, heq⟩
  cases hypothesis with
  | floating label authoredTypecode authoredVariable =>
      simp only [operationalHyp, Metamath.Spec.Hyp.floating.injEq] at heq
      rcases heq with ⟨_htypecode, hvariable⟩
      cases hvariable
      simp only [floatingVariableNames, List.mem_filterMap]
      exact
        ⟨.floating label authoredTypecode authoredVariable, hhypothesis,
          rfl⟩
  | essential label formula =>
      simp [operationalHyp] at heq

/-- Distinct authored floating names determine a unique typecode for every
operational variable. -/
private theorem operationalFloatUnique_of_floatingNames_nodup :
    (hypotheses : List HypothesisView) →
      (floatingVariableNames hypotheses).Nodup →
      ∀ typecode typecode' variableName,
        Metamath.Spec.Hyp.floating typecode variableName ∈
            hypotheses.map operationalHyp →
        Metamath.Spec.Hyp.floating typecode' variableName ∈
            hypotheses.map operationalHyp →
        typecode = typecode'
  | [], _, _, _, _, hleft, _ => by simp at hleft
  | .essential label formula :: hypotheses, hnames,
      typecode, typecode', variableName, hleft, hright => by
      simp only [List.map_cons, operationalHyp, List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft
      · contradiction
      · rcases hright with hright | hright
        · contradiction
        · exact operationalFloatUnique_of_floatingNames_nodup
            hypotheses (by
              simpa [floatingVariableNames,
                HypothesisView.floatingVariable?] using hnames)
            typecode typecode' variableName hleft hright
  | .floating label authoredTypecode authoredVariable :: hypotheses,
      hnames, typecode, typecode', variableName, hleft, hright => by
      have hnames' :
          authoredVariable ∉ floatingVariableNames hypotheses ∧
            (floatingVariableNames hypotheses).Nodup := by
        simpa [floatingVariableNames, HypothesisView.floatingVariable?]
          using hnames
      simp only [List.map_cons, operationalHyp, List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft
      · rcases hright with hright | hright
        · cases hleft
          cases hright
          rfl
        · cases hleft
          exact False.elim
            (hnames'.1
              (floatingName_mem_of_operationalHyp_mem hypotheses hright))
      · rcases hright with hright | hright
        · cases hright
          exact False.elim
            (hnames'.1
              (floatingName_mem_of_operationalHyp_mem hypotheses hleft))
        · exact operationalFloatUnique_of_floatingNames_nodup
            hypotheses hnames'.2 typecode typecode' variableName hleft hright

/-- The Boolean source-frame gate entails mm-lean4's two floating-hypothesis
well-formedness conditions. -/
theorem sourceOperationalFrame_frameWellFormed
    (frame : SourceFrame) (hypotheses : List HypothesisView)
    (hvalid : sourceFrameValid frame hypotheses = true) :
    FloatUnique (sourceOperationalFrame frame hypotheses) ∧
      FloatVarNoDup (sourceOperationalFrame frame hypotheses) := by
  have hvalid' := hvalid
  simp only [sourceFrameValid, Bool.and_eq_true] at hvalid'
  have hnames :
      (floatingVariableNames hypotheses).Nodup :=
    floatingVariableNames_nodup_of_hasUniqueFloatingVariables hypotheses
      hvalid'.1.1.1.1.2
  constructor
  · intro typecode typecode' variableName hleft hright
    exact operationalFloatUnique_of_floatingNames_nodup hypotheses hnames
      typecode typecode' variableName hleft hright
  · unfold FloatVarNoDup
    rw [floatList_sourceOperationalFrame]
    have hinjective : Function.Injective Metamath.Spec.Variable.mk := by
      intro left right heq
      exact congrArg Metamath.Spec.Variable.v heq
    exact List.Pairwise.map Metamath.Spec.Variable.mk
      (fun left right hne heq => hne (hinjective heq)) hnames

/-! ## Source frame semantic well-formedness -/

/-- The source frame and declaration gates entail operational scope
well-formedness for an assertion conclusion and every mandatory hypothesis. -/
theorem sourceOperationalFrame_exprsInScope
    (declaredConstants declaredVariables : List String)
    (frame : SourceFrame) (hypotheses : List HypothesisView)
    (formula : InferenceEncoding.ConstantHeadedFormula)
    (hframeValid : sourceFrameValid frame hypotheses = true)
    (hhypothesesDeclared :
      hypotheses.all
        (formulaSymbolsRespectDeclarations declaredConstants
          declaredVariables ∘ HypothesisView.formula) = true)
    (hformulaFrame :
      formulaSymbolsRespectFrame
        (floatingVariableNames hypotheses) formula = true)
    (hformulaDeclared :
      formulaSymbolsRespectDeclarations
        declaredConstants declaredVariables formula = true) :
    Metamath.Spec.FrameExprsInScope
      (fun symbol => symbol ∈ declaredConstants)
      (sourceOperationalFrame frame hypotheses)
      (operationalExpr formula) := by
  have hframeValid' := hframeValid
  simp only [sourceFrameValid, Bool.and_eq_true] at hframeValid'
  have hhypothesesFrame :
      hypotheses.all
        (formulaSymbolsRespectFrame
          (floatingVariableNames hypotheses) ∘ HypothesisView.formula) =
        true :=
    hframeValid'.1.2
  constructor
  · exact operationalExpr_varsInScope_of_sourceGates
      declaredConstants declaredVariables frame hypotheses formula
      hformulaFrame hformulaDeclared
  · intro operationalHypothesis hmember
    change operationalHypothesis ∈ hypotheses.map operationalHyp at hmember
    rcases List.mem_map.mp hmember with
      ⟨hypothesis, hhypothesis, heq⟩
    cases hypothesis with
    | floating label typecode variableName =>
        simp only [operationalHyp] at heq
        cases heq
        trivial
    | essential label hypothesisFormula =>
        simp only [operationalHyp] at heq
        cases heq
        apply operationalExpr_varsInScope_of_sourceGates
          declaredConstants declaredVariables frame hypotheses
          hypothesisFormula
        · exact List.all_eq_true.mp hhypothesesFrame
            (.essential label hypothesisFormula) hhypothesis
        · exact List.all_eq_true.mp hhypothesesDeclared
            (.essential label hypothesisFormula) hhypothesis

/-- The source DV gate entails the operational frame's DV well-formedness:
both endpoints are scoped floating variables and no self-pair is admitted. -/
theorem sourceOperationalFrame_dvWellFormed
    (frame : SourceFrame) (hypotheses : List HypothesisView)
    (hvalid :
      sourceFrameDVValid frame (floatingVariableNames hypotheses) = true) :
    DVWellFormed (sourceOperationalFrame frame hypotheses) := by
  have hvariables :
      (sourceOperationalFrame frame hypotheses).vars =
        (floatingVariableNames hypotheses).map
          Metamath.Spec.Variable.mk :=
    operationalFrame_vars frame.toRuntime hypotheses
  constructor
  · intro left right hpair
    change (left, right) ∈ ToSpecDVPairs frame.distinctVariables at hpair
    unfold ToSpecDVPairs at hpair
    rcases List.mem_map.mp hpair with
      ⟨⟨leftName, rightName⟩, hsourcePair, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hleft, hright⟩
    subst left
    subst right
    have hpairValid :=
      List.all_eq_true.mp hvalid (leftName, rightName) hsourcePair
    simp only [Bool.and_eq_true] at hpairValid
    constructor
    · rw [hvariables]
      exact List.mem_map.mpr
        ⟨leftName, List.contains_iff_mem.mp hpairValid.1.2, rfl⟩
    · rw [hvariables]
      exact List.mem_map.mpr
        ⟨rightName, List.contains_iff_mem.mp hpairValid.2, rfl⟩
  · intro variableName hself
    change
      (variableName, variableName) ∈
        ToSpecDVPairs frame.distinctVariables at hself
    unfold ToSpecDVPairs at hself
    rcases List.mem_map.mp hself with
      ⟨⟨leftName, rightName⟩, hsourcePair, heq⟩
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨hleft, hright⟩
    have hnamesEqual : leftName = rightName :=
      congrArg Metamath.Spec.Variable.v (hleft.trans hright.symm)
    have hpairValid :=
      List.all_eq_true.mp hvalid (leftName, rightName) hsourcePair
    simp only [Bool.and_eq_true] at hpairValid
    have hstrict : leftName < rightName :=
      of_decide_eq_true hpairValid.1.1
    subst rightName
    exact String.lt_irrefl leftName hstrict

/-! ## Source-prefix well-formedness -/

/-- Every assertion retained by a valid source prefix supplies all four
operational/declarative structural obligations from source-owned data. -/
theorem sourceAssertion_operationalWellFormed
    (source : SourcePrefix) (assertion : SourceAssertion)
    (hvalid : sourcePrefixValid source = true)
    (hmember : assertion ∈ source.assertions) :
    Metamath.Spec.FrameExprsInScope
        (sourceConstantSet source)
        (sourceOperationalFrame assertion.frame assertion.hypotheses)
        (operationalExpr assertion.formula) ∧
      Metamath.Spec.FrameVarsDisjointConsts
        (sourceConstantSet source)
        (sourceOperationalFrame assertion.frame assertion.hypotheses) ∧
      FrameWellFormed
        (sourceOperationalFrame assertion.frame assertion.hypotheses) ∧
      DVWellFormed
        (sourceOperationalFrame assertion.frame assertion.hypotheses) := by
  have hprefix := hvalid
  simp only [sourcePrefixValid, Bool.and_eq_true] at hprefix
  have hseparate :
      source.declaredConstants.all (fun constantName =>
        !(source.declaredVariables.contains constantName)) = true :=
    hprefix.1.1.1.1.2
  have hassertionValid :
      sourceAssertionValid source.declaredConstants source.declaredVariables
        assertion = true :=
    List.all_eq_true.mp hprefix.1.2 assertion hmember
  simp only [sourceAssertionValid, Bool.and_eq_true] at hassertionValid
  have hframeValid :
      sourceFrameValid assertion.frame assertion.hypotheses = true :=
    hassertionValid.1.1.1
  have hformulaFrame :
      formulaSymbolsRespectFrame
        (floatingVariableNames assertion.hypotheses)
        assertion.formula = true :=
    hassertionValid.1.1.2
  have hhypothesesDeclared :
      assertion.hypotheses.all
        (formulaSymbolsRespectDeclarations source.declaredConstants
          source.declaredVariables ∘ HypothesisView.formula) = true :=
    hassertionValid.1.2
  have hformulaDeclared :
      formulaSymbolsRespectDeclarations source.declaredConstants
        source.declaredVariables assertion.formula = true :=
    hassertionValid.2
  have hframeValid' := hframeValid
  simp only [sourceFrameValid, Bool.and_eq_true] at hframeValid'
  refine ⟨?_, ?_, ?_, ?_⟩
  · change
      Metamath.Spec.FrameExprsInScope
        (fun symbol => symbol ∈ source.declaredConstants)
        (sourceOperationalFrame assertion.frame assertion.hypotheses)
        (operationalExpr assertion.formula)
    exact sourceOperationalFrame_exprsInScope
      source.declaredConstants source.declaredVariables assertion.frame
      assertion.hypotheses assertion.formula hframeValid
      hhypothesesDeclared hformulaFrame hformulaDeclared
  · change
      Metamath.Spec.FrameVarsDisjointConsts
        (fun symbol => symbol ∈ source.declaredConstants)
        (sourceOperationalFrame assertion.frame assertion.hypotheses)
    exact sourceOperationalFrame_varsDisjointConsts
      source.declaredConstants source.declaredVariables assertion.frame
      assertion.hypotheses hseparate hhypothesesDeclared
  · exact sourceOperationalFrame_frameWellFormed assertion.frame
      assertion.hypotheses hframeValid
  · exact sourceOperationalFrame_dvWellFormed assertion.frame
      assertion.hypotheses hframeValid'.2

/-- The active caller frame of a valid source prefix supplies its
declarative structural obligations directly. -/
theorem sourceCaller_operationalWellFormed
    (source : SourcePrefix)
    (hvalid : sourcePrefixValid source = true) :
    Metamath.Spec.FrameVarsDisjointConsts
        (sourceConstantSet source)
        (sourceOperationalCallerFrame source) ∧
      FrameWellFormed (sourceOperationalCallerFrame source) ∧
      DVWellFormed (sourceOperationalCallerFrame source) := by
  have hprefix := hvalid
  simp only [sourcePrefixValid, Bool.and_eq_true] at hprefix
  have hseparate :
      source.declaredConstants.all (fun constantName =>
        !(source.declaredVariables.contains constantName)) = true :=
    hprefix.1.1.1.1.2
  have hframeValid :
      sourceFrameValid source.callerFrame source.activeHypotheses = true :=
    hprefix.1.1.1.2
  have hhypothesesDeclared :
      source.activeHypotheses.all
        (formulaSymbolsRespectDeclarations source.declaredConstants
          source.declaredVariables ∘ HypothesisView.formula) = true :=
    hprefix.1.1.2
  have hframeValid' := hframeValid
  simp only [sourceFrameValid, Bool.and_eq_true] at hframeValid'
  refine ⟨?_, ?_, ?_⟩
  · change
      Metamath.Spec.FrameVarsDisjointConsts
        (fun symbol => symbol ∈ source.declaredConstants)
        (sourceOperationalFrame source.callerFrame source.activeHypotheses)
    exact sourceOperationalFrame_varsDisjointConsts
      source.declaredConstants source.declaredVariables source.callerFrame
      source.activeHypotheses hseparate hhypothesesDeclared
  · change
      FloatUnique
          (sourceOperationalFrame source.callerFrame
            source.activeHypotheses) ∧
        FloatVarNoDup
          (sourceOperationalFrame source.callerFrame
            source.activeHypotheses)
    exact sourceOperationalFrame_frameWellFormed source.callerFrame
      source.activeHypotheses hframeValid
  · simpa [sourceOperationalCallerFrame] using
      sourceOperationalFrame_dvWellFormed source.callerFrame
        source.activeHypotheses hframeValid'.2

/-- A valid source prefix makes its directly generated operational assertion
database strongly well-formed; no parser-produced runtime database is used. -/
theorem sourceOperationalDatabase_wellFormedStrong
    (source : SourcePrefix)
    (hvalid : sourcePrefixValid source = true) :
    WellFormedDatabaseStrong
      (sourceOperationalDatabase source) (sourceConstantSet source) := by
  constructor
  · constructor
    · intro label frame expression hlookup
      rcases sourceOperationalDatabase_lookup_exists source label
          (frame, expression) hlookup with
        ⟨assertion, hmember, _hlabel, hpayload⟩
      cases hpayload
      exact
        (sourceAssertion_operationalWellFormed source assertion
          hvalid hmember).1
    · intro label frame expression hlookup
      rcases sourceOperationalDatabase_lookup_exists source label
          (frame, expression) hlookup with
        ⟨assertion, hmember, _hlabel, hpayload⟩
      cases hpayload
      exact
        (sourceAssertion_operationalWellFormed source assertion
          hvalid hmember).2.1
  · intro label frame expression hlookup
    rcases sourceOperationalDatabase_lookup_exists source label
        (frame, expression) hlookup with
      ⟨assertion, hmember, _hlabel, hpayload⟩
    cases hpayload
    exact
      ⟨(sourceAssertion_operationalWellFormed source assertion
          hvalid hmember).2.2.1,
        (sourceAssertion_operationalWellFormed source assertion
          hvalid hmember).2.2.2⟩

/-! ## Source-owned declarative adequacy -/

/-- Operational provability over the source-derived database is equivalent to
mm-lean4's derivation-locally supported declarative semantics.  All semantic
well-formedness premises are discharged from `sourcePrefixValid`. -/
theorem sourceOperationalProvable_iff_supportedDeclarative
    (source : SourcePrefix)
    (hvalid : sourcePrefixValid source = true)
    (expression : Metamath.Spec.Expr) :
    Metamath.Spec.Provable
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        expression ↔
      SupportedProvable
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        (exprToFormula
          (varMapOfFrame (sourceOperationalCallerFrame source))
          expression) := by
  have hdatabase :=
    sourceOperationalDatabase_wellFormedStrong source hvalid
  have hcaller := sourceCaller_operationalWellFormed source hvalid
  constructor
  · exact operational_to_supported hdatabase hcaller.1
  · exact mario_to_proofValid hdatabase hcaller.2.1.2 hcaller.1

/-- Source-owned proof-occurrence trees and the supported declarative
Metamath semantics define exactly the same proof language. -/
theorem sourceGeneratedProvesTree_nonempty_iff_supportedDeclarative
    (source : SourcePrefix) (target : ValidatedPresentation)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (formula : InferenceEncoding.ConstantHeadedFormula)
    (hrespect :
      formulaSymbolsRespectFrame
        (floatingVariableNames source.activeHypotheses) formula = true) :
    Nonempty (SourceGeneratedProvesTree source target formula) ↔
      SupportedProvable
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        (exprToFormula
          (varMapOfFrame (sourceOperationalCallerFrame source))
          (operationalExpr formula)) := by
  have hvalid :
      sourcePrefixValid source = true :=
    sourcePrefixValid_of_presentationOfSourcePrefix?_eq_some
      source target hsource
  exact
    (sourceGeneratedProvesTree_nonempty_iff_sourceOperationalProvable
      source target hsource formula hrespect).trans
      (sourceOperationalProvable_iff_supportedDeclarative
        source hvalid (operationalExpr formula))

/-- Forgetting derivation-local support yields Mario Carneiro's canonical
declarative provability theorem for every source-owned proof tree. -/
theorem sourceGeneratedProvesTree_to_semanticProvable
    (source : SourcePrefix) (target : ValidatedPresentation)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (formula : InferenceEncoding.ConstantHeadedFormula)
    (hrespect :
      formulaSymbolsRespectFrame
        (floatingVariableNames source.activeHypotheses) formula = true)
    (htree : Nonempty
      (SourceGeneratedProvesTree source target formula)) :
    Metamath.Spec.Semantic.Provable
      (dbToAxioms (sourceOperationalDatabase source))
      (frameToContext (sourceOperationalCallerFrame source))
      (exprToFormula
        (varMapOfFrame (sourceOperationalCallerFrame source))
        (operationalExpr formula)) := by
  exact
    ((sourceGeneratedProvesTree_nonempty_iff_supportedDeclarative
      source target hsource formula hrespect).mp htree).toSemantic

/-! ## Verified implementation refinement -/

/-- The verified mm-lean4 normal-proof fold accepts some exact authored label
trace if and only if the same source-derived checker semantics has a supported
declarative derivation.  The implementation database is related to the source
prefix only through the independently checked projection theorem. -/
theorem mmLean4_normalFold_exists_iff_supportedDeclarative
    (database : MMLean4Bridge.RuntimeDB)
    (source : SourcePrefix) (target : ValidatedPresentation)
    (base : MMLean4Bridge.RuntimeProofState)
    (formula : InferenceEncoding.ConstantHeadedFormula)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject :
      projectPrefix? database = some source.toProjection)
    (hbaseStack : base.stack = #[])
    (hrespect :
      formulaSymbolsRespectFrame
        (floatingVariableNames source.activeHypotheses) formula = true) :
    (∃ labels : List String,
        labels.foldlM
            (fun state label => database.stepNormal state label) base =
          .ok (base.push formula.toRuntime)) ↔
      SupportedProvable
        (sourceOperationalDatabase source)
        (sourceOperationalCallerFrame source)
        (exprToFormula
          (varMapOfFrame (sourceOperationalCallerFrame source))
          (operationalExpr formula)) := by
  constructor
  · rintro ⟨labels, hfold⟩
    have hexact :=
      (normalFold_accepts_iff_exactSourceTree
        database source target base formula labels hsource hproject
          hbaseStack).mp hfold
    rcases hexact with ⟨⟨tree, _hlabels⟩⟩
    exact
      (sourceGeneratedProvesTree_nonempty_iff_supportedDeclarative
        source target hsource formula hrespect).mp ⟨tree⟩
  · intro hdeclarative
    rcases
        (sourceGeneratedProvesTree_nonempty_iff_supportedDeclarative
          source target hsource formula hrespect).mpr hdeclarative with
      ⟨tree⟩
    refine ⟨tree.labels, ?_⟩
    exact
      (normalFold_accepts_iff_exactSourceTree
        database source target base formula tree.labels hsource hproject
          hbaseStack).mpr
        ⟨⟨tree, rfl⟩⟩

/-! ## Boundary of the unrestricted declarative relation -/

/-- Every variable reference generated by a finite frame map has an index
strictly below the end of that finite enumeration. -/
private theorem varMapOfFrameAux_index_lt
    {start : Nat} {floats : List (Metamath.Spec.Constant ×
      Metamath.Spec.Variable)}
    {sourceVariable : Metamath.Spec.Variable} {reference : Metamath.VR}
    (hmember :
      (sourceVariable, reference) ∈ varMapOfFrameAux start floats) :
    reference.i < start + floats.length := by
  induction floats generalizing start with
  | nil =>
      simp [varMapOfFrameAux] at hmember
  | cons head floats ih =>
      rcases head with ⟨typecode, authoredVariable⟩
      simp only [varMapOfFrameAux, List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · have href :
          reference = ⟨typecode.c, start⟩ :=
          (Prod.mk.injEq _ _ _ _).mp hhead |>.2
        subst reference
        simp
      · have hbound := ih (start := start + 1) htail
        simp only [List.length_cons]
        omega

/-- The global support premise used by mm-lean4's unrestricted
operational/declarative biconditional is impossible for every finite frame:
there is always a fresh semantic variable index outside the frame map. -/
theorem not_semanticFrameSupported
    (database : Metamath.Spec.Database) (frame : Metamath.Spec.Frame) :
    ¬SemanticFrameSupported database frame := by
  intro hsupported
  let freshReference : Metamath.VR :=
    ⟨"", (floatList frame).length⟩
  rcases hsupported freshReference with
    ⟨sourceVariable, hfind⟩
  have hmember :
      (sourceVariable, freshReference) ∈ varMapOfFrame frame :=
    findVar_mem_of_some hfind
  change
    (sourceVariable, freshReference) ∈
      varMapOfFrameAux 0 (floatList frame) at hmember
  have hbound :=
    varMapOfFrameAux_index_lt hmember
  change (floatList frame).length <
    0 + (floatList frame).length at hbound
  omega

end Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy
