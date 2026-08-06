import Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement

/-!
# Soundness of projected Metamath steps in the operational specification

This file maps projected hypothesis and assertion evidence directly to the
one-step constructors of `Metamath.Spec.ProofValidFrom`.  The operational
stack is top-first, so mandatory hypotheses retained in authored order occur
as `needed.reverse` at the head of that stack.

The assertion theorem is forward-only.  Its explicit actual-formula frame
condition is the boundary between the generated calculus's tagged variables
and the operational specification's classification of erased symbol names.
Recursive proof execution supplies this condition from its stack invariant.
-/

namespace Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
open Mettapedia.Languages.Metamath.InferenceAssertionStepForward
open Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceVariableClassification

/-! ## Exact operational images -/

/-- Erase runtime symbol tags through the verified mm-lean4 expression map. -/
def operationalExpr (formula : ConstantHeadedFormula) : Metamath.Spec.Expr :=
  Metamath.Kernel.toExpr formula.toRuntime

/-- The operational hypothesis represented by one projected hypothesis. -/
def operationalHyp : HypothesisView → Metamath.Spec.Hyp
  | .floating _ typecode variableName =>
      .floating ⟨typecode⟩ ⟨variableName⟩
  | .essential _ formula => .essential (operationalExpr formula)

/-- The exact operational frame image of a runtime frame and its ordered
projected hypotheses. -/
def operationalFrame (frame : RuntimeFrame)
    (hypotheses : List HypothesisView) : Metamath.Spec.Frame :=
  { hyps := hypotheses.map operationalHyp
    dv := ToSpecDVPairs frame.dj.toList }

@[simp] theorem operationalExpr_typecode
    (formula : ConstantHeadedFormula) :
    (operationalExpr formula).typecode = ⟨formula.typecode⟩ := by
  rcases formula with ⟨typecode, body⟩
  simp [operationalExpr, ConstantHeadedFormula.toRuntime,
    Metamath.Kernel.toExpr, Metamath.Verify.Sym.value]

@[simp] theorem operationalExpr_syms
    (formula : ConstantHeadedFormula) :
    (operationalExpr formula).syms =
      formula.body.map Metamath.Verify.Sym.value := by
  rcases formula with ⟨typecode, body⟩
  simp [operationalExpr, ConstantHeadedFormula.toRuntime,
    Metamath.Kernel.toExpr, Metamath.Kernel.toSym]

@[simp] theorem operationalFrame_vars
    (frame : RuntimeFrame) (hypotheses : List HypothesisView) :
    (operationalFrame frame hypotheses).vars =
      (floatingVariableNames hypotheses).map Metamath.Spec.Variable.mk := by
  induction hypotheses with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      unfold operationalFrame Metamath.Spec.Frame.vars at ih ⊢
      cases hypothesis <;>
        simp [operationalHyp, floatingVariableNames,
          HypothesisView.floatingVariable?, ih]

theorem convertHyp_of_projectHypothesis
    (db : RuntimeDB) (label : String) (hypothesis : HypothesisView)
    (hproject : projectHypothesis? db label = some hypothesis) :
    Metamath.Kernel.convertHyp db label = some (operationalHyp hypothesis) := by
  obtain ⟨runtimeFormula, hfind, hdecode, hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity db label hypothesis hproject
  have hruntime : runtimeFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula hypothesis.formula).mp hdecode
  subst runtimeFormula
  cases hypothesis with
  | floating viewLabel typecode variableName =>
      simp only [hypothesisEssentialBit, HypothesisView.formula,
        HypothesisView.label] at hfind hlabel
      subst viewLabel
      simp [Metamath.Kernel.convertHyp, hfind, operationalHyp,
        Metamath.Kernel.toExprOpt, ConstantHeadedFormula.toRuntime,
        Metamath.Kernel.toSym, Metamath.Verify.Sym.value]
  | essential viewLabel formula =>
      simp only [hypothesisEssentialBit, HypothesisView.formula,
        HypothesisView.label] at hfind hlabel
      subst viewLabel
      simp [Metamath.Kernel.convertHyp, hfind, operationalHyp,
        operationalExpr, Metamath.Kernel.toExprOpt,
        ConstantHeadedFormula.toRuntime, Metamath.Kernel.toExpr]

private theorem mapM_convertHyp_of_forall₂
    (db : RuntimeDB) {labels : List String}
    {hypotheses : List HypothesisView}
    (hordered : List.Forall₂
      (fun label hypothesis =>
        projectHypothesis? db label = some hypothesis)
      labels hypotheses) :
    labels.mapM (Metamath.Kernel.convertHyp db) =
      some (hypotheses.map operationalHyp) := by
  induction hordered with
  | nil => rfl
  | cons hhead _htail ih =>
      simp [convertHyp_of_projectHypothesis db _ _ hhead, ih]

/-- Successful hypothesis projection determines the exact mm-lean4
operational frame conversion, including hypothesis and DV order. -/
theorem toFrame_of_projectHypotheses
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses) :
    Metamath.Kernel.toFrame db frame =
      some (operationalFrame frame hypotheses) := by
  have hmap := mapM_convertHyp_of_forall₂ db
    (projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject)
  simp [Metamath.Kernel.toFrame, hmap, operationalFrame,
    ToSpecDVPairs, Metamath.Kernel.convertDV]

/-- The ambient caller frame of a successful projection has the exact
operational image used below. -/
theorem projectedCaller_toFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    Metamath.Kernel.toFrame db projection.callerFrame =
      some (operationalFrame projection.callerFrame
        projection.activeHypotheses) := by
  have hfields := projectPrefix?_eq_some_fields db projection hproject
  have hcaller :
      projection.callerFrame = proofFacingCallerFrame db := hfields.2.2.1
  have hactive :
      projectHypotheses? db db.frame.hyps.toList =
        some projection.activeHypotheses := hfields.2.2.2.1
  rw [hcaller]
  apply toFrame_of_projectHypotheses db (proofFacingCallerFrame db)
    projection.activeHypotheses
  simpa [proofFacingCallerFrame] using hactive

/-- A retained assertion's mandatory frame has the exact operational image. -/
theorem projectedAssertion_toFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    Metamath.Kernel.toFrame db assertion.frame =
      some (operationalFrame assertion.frame assertion.hypotheses) := by
  exact toFrame_of_projectHypotheses db assertion.frame assertion.hypotheses
    (projectedAssertion_database_fidelity db projection assertion hproject
      hmember).2.1

/-- The total operational database contains the exact projected assertion
image.  This is the database inside the definitionally successful
`Kernel.toDatabase` bridge. -/
theorem projectedAssertion_toDatabaseTotal_lookup
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    Metamath.Kernel.toDatabaseTotal db assertion.label =
      some
        ( operationalFrame assertion.frame assertion.hypotheses
        , operationalExpr assertion.formula ) := by
  have hfidelity := projectedAssertion_database_fidelity
    db projection assertion hproject hmember
  have hframe := projectedAssertion_toFrame
    db projection assertion hproject hmember
  unfold Metamath.Kernel.toDatabaseTotal
  rw [hfidelity.1]
  simp [hframe, operationalExpr, Metamath.Kernel.toExprOpt,
    ConstantHeadedFormula.toRuntime, Metamath.Kernel.toExpr]

/-! ## Finite substitutions and operational substitution -/

/-- Totalize a finite generated substitution with an explicit fallback.
Projected assertion variables are all bound, so the fallback is never
observed by an assertion constructor. -/
def operationalSubstitution (fallback : Metamath.Spec.Subst) :
    FiniteSubstitution → Metamath.Spec.Subst
  | [], v => fallback v
  | binding :: substitution, v =>
      if binding.variableName = v.v then
        operationalExpr binding.replacement
      else
        operationalSubstitution fallback substitution v

/-- Unique finite lookup determines the exact operational substitution image. -/
theorem operationalSubstitution_eq_of_lookup
    (fallback : Metamath.Spec.Subst)
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {variableName : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics substitution variableName replacement) :
    operationalSubstitution fallback substitution ⟨variableName⟩ =
      operationalExpr replacement := by
  induction substitution with
  | nil => simp [LookupSemantics] at hlookup
  | cons binding substitution ih =>
      rcases binding with ⟨bindingName, bindingReplacement⟩
      have huniqueFull :
          SubstitutionKeysUnique
            (⟨bindingName, bindingReplacement⟩ :: substitution) := hunique
      simp only [SubstitutionKeysUnique, List.map_cons, List.nodup_cons]
        at hunique
      rcases hunique with ⟨hhead, htailUnique⟩
      by_cases hname : bindingName = variableName
      · have hheadLookup :
            LookupSemantics
              (⟨bindingName, bindingReplacement⟩ :: substitution)
              variableName bindingReplacement := by
          change
            FormulaBinding.mk variableName bindingReplacement ∈
              FormulaBinding.mk bindingName bindingReplacement ::
                substitution
          simp [hname]
        have hreplacement : replacement = bindingReplacement :=
          lookupSemantics_functional
            (substitution :=
              (⟨bindingName, bindingReplacement⟩ :: substitution))
            huniqueFull hlookup hheadLookup
        subst replacement
        simp [operationalSubstitution, hname]
      · have htailLookup :
            LookupSemantics substitution variableName replacement := by
          change
            FormulaBinding.mk variableName replacement ∈
              FormulaBinding.mk bindingName bindingReplacement ::
                substitution at hlookup
          rcases List.mem_cons.mp hlookup with hsame | htail
          · have : variableName = bindingName :=
              congrArg FormulaBinding.variableName hsame
            exact (hname this.symm).elim
          · exact htail
        simp [operationalSubstitution, hname,
          ih htailUnique htailLookup]

/-- The fallback choice is observationally irrelevant on every generated
finite binding. -/
theorem operationalSubstitution_fallback_irrelevant_of_lookup
    (firstFallback secondFallback : Metamath.Spec.Subst)
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    {variableName : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics substitution variableName replacement) :
    operationalSubstitution firstFallback substitution ⟨variableName⟩ =
      operationalSubstitution secondFallback substitution ⟨variableName⟩ := by
  rw [operationalSubstitution_eq_of_lookup firstFallback hunique hlookup,
    operationalSubstitution_eq_of_lookup secondFallback hunique hlookup]

private theorem bodySubstitution_to_operational
    (fallback : Metamath.Spec.Subst)
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    (floatingVariables : List String)
    {source result : List RuntimeSym}
    (hrespect : source.all
      (symbolRespectsFrame floatingVariables) = true)
    (semantics : BodySubstitution substitution source result) :
    (source.map Metamath.Verify.Sym.value).flatMap
        (fun name =>
          if Metamath.Spec.Variable.mk name ∈
              floatingVariables.map Metamath.Spec.Variable.mk then
            (operationalSubstitution fallback substitution
              (Metamath.Spec.Variable.mk name)).syms
          else [name]) =
      result.map Metamath.Verify.Sym.value := by
  induction semantics with
  | nil => rfl
  | @const name sourceTail resultTail tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrespect
      have hnameAbsent : name ∉ floatingVariables := by
        simp [symbolRespectsFrame] at hrespect
        exact hrespect.1
      have hvariableAbsent :
          Metamath.Spec.Variable.mk name ∉
            floatingVariables.map Metamath.Spec.Variable.mk := by
        simpa using hnameAbsent
      simp only [List.map_cons, Metamath.Verify.Sym.value,
        List.flatMap_cons]
      rw [if_neg hvariableAbsent]
      simp only [List.singleton_append, List.cons.injEq, true_and]
      exact ih hrespect.2
  | @var name replacement sourceTail resultTail binding tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrespect
      have hnamePresent : name ∈ floatingVariables := by
        simpa [symbolRespectsFrame] using hrespect.1
      have hvariablePresent :
          Metamath.Spec.Variable.mk name ∈
            floatingVariables.map Metamath.Spec.Variable.mk := by
        simpa using hnamePresent
      simp only [List.map_cons, Metamath.Verify.Sym.value,
        List.flatMap_cons]
      rw [if_pos hvariablePresent,
        operationalSubstitution_eq_of_lookup fallback hunique binding,
        operationalExpr_syms, List.map_append, ih hrespect.2]

/-- Tagged formula substitution agrees with the operational specification
whenever the source tags respect the same variable-name classification. -/
private theorem operationalExpr_ext
    {left right : Metamath.Spec.Expr}
    (htypecode : left.typecode = right.typecode)
    (hsyms : left.syms = right.syms) : left = right := by
  cases left
  cases right
  simp_all

theorem formulaSubstitutionSemantics_to_spec_applySubst
    (fallback : Metamath.Spec.Subst)
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution)
    (floatingVariables : List String)
    {source result : ConstantHeadedFormula}
    (hrespect :
      formulaSymbolsRespectFrame floatingVariables source = true)
    (semantics : FormulaSubstitutionSemantics substitution source result) :
    Metamath.Spec.applySubst
        (floatingVariables.map Metamath.Spec.Variable.mk)
        (operationalSubstitution fallback substitution)
        (operationalExpr source) =
      operationalExpr result := by
  rcases source with ⟨sourceTypecode, sourceBody⟩
  rcases result with ⟨resultTypecode, resultBody⟩
  rcases semantics with ⟨htypecode, hbody⟩
  dsimp only [ConstantHeadedFormula.typecode] at htypecode
  subst resultTypecode
  apply operationalExpr_ext
  · simp [Metamath.Spec.applySubst]
  · simpa [Metamath.Spec.applySubst, operationalExpr_syms] using
      bodySubstitution_to_operational fallback hunique floatingVariables
        hrespect hbody

/-! ## Ordered mandatory hypotheses -/

theorem floating_binding_of_hypothesisInstances
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    {label typecode variableName : String}
    (hmember : .floating label typecode variableName ∈ hypotheses) :
    ∃ actual,
      actual ∈ actuals ∧
      LookupSemantics substitution variableName actual ∧
      actual.typecode = typecode := by
  induction instances with
  | nil => simp at hmember
  | @floating headLabel headTypecode headVariable headActual tailHypotheses
      tailActuals tailSubstitution headTypecodeEq tailInstances ih =>
      rcases List.mem_cons.mp hmember with hhead | htail
      · injection hhead with hlabel htypecode hvariable
        subst label
        subst typecode
        subst variableName
        exact ⟨headActual, by simp,
          by simp [LookupSemantics], headTypecodeEq⟩
      · obtain ⟨actual, hactual, hlookup, htypecode⟩ := ih htail
        exact ⟨actual, List.mem_cons_of_mem headActual hactual,
          by
            change FormulaBinding.mk variableName actual ∈
              FormulaBinding.mk headVariable headActual :: tailSubstitution
            exact List.mem_cons_of_mem _ hlookup,
          htypecode⟩
  | @essential headLabel headFormula headActual tailHypotheses tailActuals
      substitution headTypecodeEq tailInstances ih =>
      rcases List.mem_cons.mp hmember with hhead | htail
      · contradiction
      · obtain ⟨actual, hactual, hlookup, htypecode⟩ := ih htail
        exact ⟨actual, List.mem_cons_of_mem headActual hactual,
          hlookup, htypecode⟩

/-- Ordered generated instances give the upstream floating-hypothesis typing
condition for the exact totalized substitution. -/
theorem hypothesisInstances_operational_typed
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (hunique : SubstitutionKeysUnique substitution)
    (fallback : Metamath.Spec.Subst) :
    ∀ c v,
      Metamath.Spec.Hyp.floating c v ∈
          (hypotheses.map operationalHyp) →
        (operationalSubstitution fallback substitution v).typecode = c := by
  intro c v hmember
  rcases List.mem_map.mp hmember with ⟨hypothesis, hhypothesis, himage⟩
  cases hypothesis with
  | floating label typecode variableName =>
      simp only [operationalHyp] at himage
      injection himage with htypecode hvariable
      obtain ⟨actual, _hactual, hlookup, hactualTypecode⟩ :=
        floating_binding_of_hypothesisInstances instances hhypothesis
      have hsubstitution :=
        operationalSubstitution_eq_of_lookup fallback hunique hlookup
      cases hvariable
      cases htypecode
      rw [hsubstitution, operationalExpr_typecode, hactualTypecode,
        Metamath.Spec.Constant.mk.injEq]
  | essential label formula =>
      simp [operationalHyp] at himage

private theorem hypothesisInstances_needed_eq_aux
    (fallback : Metamath.Spec.Subst)
    (floatingVariables : List String)
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution fullSubstitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (hsubset : ∀ binding, binding ∈ substitution →
      binding ∈ fullSubstitution)
    (hunique : SubstitutionKeysUnique fullSubstitution)
    (hessential :
      EssentialMatches fullSubstitution hypotheses actuals)
    (hrespect : ∀ hypothesis, hypothesis ∈ hypotheses →
      formulaSymbolsRespectFrame floatingVariables hypothesis.formula = true) :
    (hypotheses.map operationalHyp).map
        (fun hypothesis =>
          match hypothesis with
          | .floating _ v =>
              operationalSubstitution fallback fullSubstitution v
          | .essential formula =>
              Metamath.Spec.applySubst
                (floatingVariables.map Metamath.Spec.Variable.mk)
                (operationalSubstitution fallback fullSubstitution) formula) =
      actuals.map operationalExpr := by
  induction instances generalizing fullSubstitution with
  | nil => rfl
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecodeEq tail ih =>
      change EssentialMatches fullSubstitution hypotheses actuals at hessential
      have hheadLookup :
          LookupSemantics fullSubstitution variableName actual := by
        apply hsubset (FormulaBinding.mk variableName actual)
        simp
      have htailSubset : ∀ binding, binding ∈ substitution →
          binding ∈ fullSubstitution := by
        intro binding hbinding
        apply hsubset binding
        exact List.mem_cons_of_mem _ hbinding
      have htailRespect : ∀ hypothesis, hypothesis ∈ hypotheses →
          formulaSymbolsRespectFrame floatingVariables
            hypothesis.formula = true := by
        intro hypothesis hhypothesis
        exact hrespect hypothesis (List.mem_cons_of_mem _ hhypothesis)
      simp only [List.map_cons, operationalHyp]
      rw [operationalSubstitution_eq_of_lookup fallback hunique hheadLookup,
        ih htailSubset hunique hessential htailRespect]
  | @essential label formula actual hypotheses actuals substitution
      typecodeEq tail ih =>
      change
        FormulaSubstitutionSemantics fullSubstitution formula actual ∧
          EssentialMatches fullSubstitution hypotheses actuals at hessential
      have htailRespect : ∀ hypothesis, hypothesis ∈ hypotheses →
          formulaSymbolsRespectFrame floatingVariables
            hypothesis.formula = true := by
        intro hypothesis hhypothesis
        exact hrespect hypothesis (List.mem_cons_of_mem _ hhypothesis)
      have hheadRespect :
          formulaSymbolsRespectFrame floatingVariables formula = true :=
        hrespect (.essential label formula) List.mem_cons_self
      simp only [List.map_cons, operationalHyp]
      rw [formulaSubstitutionSemantics_to_spec_applySubst fallback hunique
          floatingVariables hheadRespect hessential.1,
        ih hsubset hunique hessential.2 htailRespect]

/-- The operational `needed` vector is exactly the generated actual vector in
authored mandatory-hypothesis order. -/
theorem hypothesisInstances_operational_needed_eq
    {frame : RuntimeFrame}
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    (hunique : SubstitutionKeysUnique substitution)
    (fallback : Metamath.Spec.Subst)
    (hessential : EssentialMatches substitution hypotheses actuals)
    (hrespect : ∀ hypothesis, hypothesis ∈ hypotheses →
      formulaSymbolsRespectFrame (floatingVariableNames hypotheses)
        hypothesis.formula = true) :
    Metamath.Bridge.needed
        (operationalFrame frame hypotheses).vars
        (operationalFrame frame hypotheses)
        (operationalSubstitution fallback substitution) =
      actuals.map operationalExpr := by
  unfold Metamath.Bridge.needed
  rw [operationalFrame_vars]
  change List.map _ (List.map operationalHyp hypotheses) = _
  rw [List.map_map]
  have hneeded := hypothesisInstances_needed_eq_aux fallback
    (floatingVariableNames hypotheses) instances
    (fun _ hbinding => hbinding) hunique hessential hrespect
  convert hneeded using 1
  rw [List.map_map]
  apply List.map_congr_left
  intro hypothesis _hmember
  cases operationalHyp hypothesis <;> rfl

/-! ## Active-hypothesis constructors -/

/-- A projected active hypothesis is exactly one upstream operational
hypothesis step from any initial stack. -/
theorem activeHypothesis_toProofValidFrom
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses)
    (remaining : List Metamath.Spec.Expr) :
    Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      remaining (operationalExpr hypothesis.formula :: remaining)
      [Metamath.Spec.ProofStep.useHyp (operationalHyp hypothesis)] := by
  have _hframe := projectedCaller_toFrame db projection hproject
  cases hypothesis with
  | floating label typecode variableName =>
      have hin :
          Metamath.Spec.Hyp.floating ⟨typecode⟩ ⟨variableName⟩ ∈
            (operationalFrame projection.callerFrame
              projection.activeHypotheses).hyps := by
        apply List.mem_map.mpr
        exact ⟨.floating label typecode variableName, hmember, rfl⟩
      have hnil := Metamath.Spec.ProofValidFrom.nil
        (Γ := Metamath.Kernel.toDatabaseTotal db)
        (operationalFrame projection.callerFrame
          projection.activeHypotheses) remaining
      have hstep := Metamath.Spec.ProofValidFrom.useFloating
        (Γ := Metamath.Kernel.toDatabaseTotal db)
        (fr := operationalFrame projection.callerFrame
          projection.activeHypotheses)
        (stk := remaining) (stack := remaining) (steps := [])
        (c := Metamath.Spec.Constant.mk typecode)
        (v := Metamath.Spec.Variable.mk variableName) hin hnil
      simpa [HypothesisView.formula, operationalHyp, operationalExpr,
        ConstantHeadedFormula.toRuntime, Metamath.Kernel.toExpr,
        Metamath.Kernel.toSym, Metamath.Verify.Sym.value] using hstep
  | essential label formula =>
      have hin :
          Metamath.Spec.Hyp.essential (operationalExpr formula) ∈
            (operationalFrame projection.callerFrame
              projection.activeHypotheses).hyps := by
        apply List.mem_map.mpr
        exact ⟨.essential label formula, hmember, rfl⟩
      exact Metamath.Spec.ProofValidFrom.useEssential
        (Γ := Metamath.Kernel.toDatabaseTotal db)
        (fr := operationalFrame projection.callerFrame
          projection.activeHypotheses)
        (stk := remaining) (stack := remaining) (steps := [])
        (e := operationalExpr formula) hin
        (Metamath.Spec.ProofValidFrom.nil
          (Γ := Metamath.Kernel.toDatabaseTotal db)
          (operationalFrame projection.callerFrame
            projection.activeHypotheses) remaining)

/-! ## Assertion constructors -/

theorem projectedAssertion_hypothesisFormula_respects
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    ∀ hypothesis, hypothesis ∈ assertion.hypotheses →
      formulaSymbolsRespectFrame
        (floatingVariableNames assertion.hypotheses)
        hypothesis.formula = true := by
  have hvalid := projectedAssertion_viewValid
    db projection assertion hproject hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hvalid
  have hframe :
      frameProjectionValid assertion.frame assertion.hypotheses = true :=
    hvalid.1.1.1
  simp only [frameProjectionValid, Bool.and_eq_true] at hframe
  exact List.all_eq_true.mp hframe.1.2

theorem projectedAssertion_formula_respects
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    formulaSymbolsRespectFrame
      (floatingVariableNames assertion.hypotheses)
      assertion.formula = true := by
  have hvalid := projectedAssertion_viewValid
    db projection assertion hproject hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.1.2

/-- Exact forward soundness of one independent generated assertion
application in the upstream operational specification.  The actuals are in
mandatory-hypothesis appearance order; the upstream top-first stack consumes
their reverse and leaves the arbitrary older `remaining` suffix untouched. -/
theorem assertionApplication_toProofValidFrom
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (fallback : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hinstances :
      HypothesisInstances assertion.hypotheses actuals substitution)
    (hessential :
      EssentialMatches substitution assertion.hypotheses actuals)
    (hdv :
      DVOKSemantics substitution projection.callerFrame assertion.frame)
    (hresult :
      FormulaSubstitutionSemantics substitution assertion.formula result)
    (hactualsRespect : ∀ actual, actual ∈ actuals →
      formulaSymbolsRespectFrame
        (floatingVariableNames projection.activeHypotheses) actual = true) :
    Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      ((actuals.map operationalExpr).reverse ++ remaining)
      (operationalExpr result :: remaining)
      [Metamath.Spec.ProofStep.useAssertion assertion.label
        (operationalSubstitution fallback substitution)] := by
  let callerSpec := operationalFrame projection.callerFrame
    projection.activeHypotheses
  let calleeSpec := operationalFrame assertion.frame assertion.hypotheses
  let specSubstitution := operationalSubstitution fallback substitution
  have hcallerFrame := projectedCaller_toFrame db projection hproject
  have hcalleeFrame := projectedAssertion_toFrame
    db projection assertion hproject hmember
  have hunique : SubstitutionKeysUnique substitution :=
    hinstances.substitutionKeysUnique_of_projectedAssertion
      db projection hproject hmember
  have htyped :
      ∀ c v, Metamath.Spec.Hyp.floating c v ∈ calleeSpec.hyps →
        (specSubstitution v).typecode = c := by
    simpa [calleeSpec, specSubstitution, operationalFrame] using
      hypothesisInstances_operational_typed hinstances hunique fallback
  have hhypothesisRespect :=
    projectedAssertion_hypothesisFormula_respects
      db projection assertion hproject hmember
  have hneeded :
      Metamath.Bridge.needed calleeSpec.vars calleeSpec specSubstitution =
        actuals.map operationalExpr := by
    simpa [calleeSpec, specSubstitution] using
      hypothesisInstances_operational_needed_eq
        (frame := assertion.frame) hinstances hunique fallback hessential
          hhypothesisRespect
  have hsourceRespect := projectedAssertion_formula_respects
    db projection assertion hproject hmember
  have hresultSpec :
      Metamath.Spec.applySubst calleeSpec.vars specSubstitution
          (operationalExpr assertion.formula) = operationalExpr result := by
    simpa [calleeSpec, specSubstitution] using
      formulaSubstitutionSemantics_to_spec_applySubst fallback hunique
        (floatingVariableNames assertion.hypotheses) hsourceRespect hresult
  have hcallerDistinct :
      DVPairNamesDistinct projection.callerFrame.dj.toList :=
    dvPairNamesDistinct_of_strictOrderAll projection.callerFrame.dj.toList
      (projectedCallerFrame_dvStrict db projection hproject)
  have hcallerNames :
      Metamath.Kernel.varNames callerSpec.vars =
        floatingVariableNames projection.activeHypotheses := by
    simp [callerSpec, operationalFrame_vars, Metamath.Kernel.varNames,
      Function.comp_def]
  have hsubstitutionImage : ∀ name replacement,
      LookupSemantics substitution name replacement →
        specSubstitution ⟨name⟩ = operationalExpr replacement := by
    intro name replacement hlookup
    exact operationalSubstitution_eq_of_lookup fallback hunique hlookup
  have hreplacementRespect : ∀ name replacement,
      LookupSemantics substitution name replacement →
        formulaSymbolsRespectFrame
          (floatingVariableNames projection.activeHypotheses)
          replacement = true := by
    intro name replacement hlookup
    exact hactualsRespect replacement
      (hypothesisInstances_lookup_replacement_mem_actuals
        hinstances hlookup)
  have hclassification : ∀ name replacement,
      LookupSemantics substitution name replacement →
        Metamath.Spec.varsInExpr callerSpec.vars
            (specSubstitution ⟨name⟩) =
          (BodyVariables replacement.body).map
            Metamath.Spec.Variable.mk :=
    lookup_varsInExpr_classification substitution callerSpec.vars
      (floatingVariableNames projection.activeHypotheses)
      specSubstitution hcallerNames hsubstitutionImage hreplacementRespect
  have hdvSpec :
      Metamath.Spec.dvOK callerSpec.vars calleeSpec.dv callerSpec.dv
        specSubstitution := by
    simpa [callerSpec, calleeSpec, operationalFrame] using
      dvOKSemantics_implies_spec_dvOK substitution projection.callerFrame
        assertion.frame callerSpec.vars specSubstitution hcallerDistinct
          hclassification hdv
  have hlookup :
      Metamath.Kernel.toDatabaseTotal db assertion.label =
        some (calleeSpec, operationalExpr assertion.formula) := by
    simpa [calleeSpec] using projectedAssertion_toDatabaseTotal_lookup
      db projection assertion hproject hmember
  have hbase := Metamath.Spec.ProofValidFrom.nil
    (Γ := Metamath.Kernel.toDatabaseTotal db)
    callerSpec ((actuals.map operationalExpr).reverse ++ remaining)
  have hneededConstructor :
      actuals.map operationalExpr =
        calleeSpec.hyps.map (fun hypothesis =>
          match hypothesis with
          | .essential formula =>
              Metamath.Spec.applySubst calleeSpec.vars specSubstitution formula
          | .floating _ v => specSubstitution v) := by
    convert hneeded.symm using 1
    apply List.map_congr_left
    intro hypothesis _hmember
    cases hypothesis <;> rfl
  have hstep := Metamath.Spec.ProofValidFrom.useAxiom
    (Γ := Metamath.Kernel.toDatabaseTotal db)
    (fr := callerSpec)
    (stk := (actuals.map operationalExpr).reverse ++ remaining)
    (stack := (actuals.map operationalExpr).reverse ++ remaining)
    (steps := []) (l := assertion.label) (fr' := calleeSpec)
    (e := operationalExpr assertion.formula) (σ := specSubstitution)
    hlookup hdvSpec htyped hbase
    (actuals.map operationalExpr) hneededConstructor remaining rfl
  rw [hresultSpec] at hstep
  simpa [callerSpec, calleeSpec, specSubstitution] using hstep

/-- A proof-relevant generated assertion node, rather than a bare rule
application, supplies all essential, DV, and result-substitution evidence
needed by the exact upstream `useAxiom` constructor. -/
theorem generatedAssertionNode_toProofValidFrom
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (fallback : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hactualsRespect : ∀ actual, actual ∈ actuals →
      formulaSymbolsRespectFrame
        (floatingVariableNames projection.activeHypotheses) actual = true) :
    Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      ((actuals.map operationalExpr).reverse ++ remaining)
      (operationalExpr result :: remaining)
      [Metamath.Spec.ProofStep.useAssertion assertion.label
        (operationalSubstitution fallback substitution)] := by
  rcases (assertionRuleApplication_iff_instances projection target
      hprojection hmember).mp node.application with
    ⟨hinstances, _hresultTypecode⟩
  rcases (assertionSideEvidence_nonempty_iff_semantics projection target
      hprojection hinstances).mp ⟨node.sideEvidence⟩ with
    ⟨hessential, hdv, hresult⟩
  exact assertionApplication_toProofValidFrom db projection assertion
    actuals result substitution fallback remaining hproject hmember
      hinstances hessential hdv hresult hactualsRespect

/-- With the recursive stack invariant, the same generated node gives both
the direct operational-spec constructor and the already-proved exact live
transition. -/
theorem generatedAssertionNode_toSpec_and_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (node : GeneratedAssertionNode projection target assertion actuals
      result substitution)
    (fallback : Metamath.Spec.Subst)
    (remaining : List Metamath.Spec.Expr)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hstackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    Metamath.Spec.ProofValidFrom
        (Metamath.Kernel.toDatabaseTotal db)
        (operationalFrame projection.callerFrame
          projection.activeHypotheses)
        ((actuals.map operationalExpr).reverse ++ remaining)
        (operationalExpr result :: remaining)
        [Metamath.Spec.ProofStep.useAssertion assertion.label
          (operationalSubstitution fallback substitution)] ∧
      db.stepNormal pr assertion.label = .ok
        { pr with
          stack :=
            (pr.stack.shrink
              (pr.stack.size - assertion.frame.hyps.size)).push
                result.toRuntime } := by
  have hfields := projectPrefix?_eq_some_fields db projection hproject
  have hactualsRuntime := actuals_respect_callerFrame_of_stack_window
    db pr.stack (pr.stack.size - assertion.frame.hyps.size) actuals
      hwindow hstackRespects
  have hfloatingNames :
      db.frameFloatVars db.frame =
        floatingVariableNames projection.activeHypotheses :=
    frameFloatVars_eq_floatingVariableNames_of_projectHypotheses
      db db.frame projection.activeHypotheses hfields.2.2.2.1
  have hactualsRespect : ∀ actual, actual ∈ actuals →
      formulaSymbolsRespectFrame
        (floatingVariableNames projection.activeHypotheses) actual = true := by
    intro actual hactual
    rw [← hfloatingNames]
    exact hactualsRuntime actual hactual
  constructor
  · exact generatedAssertionNode_toProofValidFrom db projection target
      hprojection assertion actuals result substitution node fallback
        remaining hproject hmember hactualsRespect
  · exact (generatedAssertionNode_nonempty_iff_stepNormal db projection
      target hprojection assertion pr actuals result hproject hmember hwindow
        hstackRespects).mp ⟨⟨substitution, node⟩⟩

/-! ## Negative boundaries -/

/-- An empty operational proof-step list cannot change its initial stack. -/
private theorem proofValidFrom_empty_steps_eq
    {database : Metamath.Spec.Database} {frame : Metamath.Spec.Frame}
    {initial result : List Metamath.Spec.Expr}
    (valid :
      Metamath.Spec.ProofValidFrom database frame initial result []) :
    result = initial := by
  cases valid
  rfl

/-- A singleton upstream hypothesis step has one forced stack result. -/
theorem proofValidFrom_single_useHyp_result
    {database : Metamath.Spec.Database} {frame : Metamath.Spec.Frame}
    {initial result : List Metamath.Spec.Expr}
    {hypothesis : Metamath.Spec.Hyp}
    (valid : Metamath.Spec.ProofValidFrom database frame initial result
      [Metamath.Spec.ProofStep.useHyp hypothesis]) :
    result =
      (match hypothesis with
       | .essential formula => formula
       | .floating typecode v =>
          ({ typecode, syms := [v.v] } : Metamath.Spec.Expr)) ::
        initial := by
  cases valid with
  | useEssential stack steps formula hmember previous =>
      have hstack := proofValidFrom_empty_steps_eq previous
      subst stack
      rfl
  | useFloating stack steps typecode v hmember previous =>
      have hstack := proofValidFrom_empty_steps_eq previous
      subst stack
      rfl

/-- A single projected active-hypothesis constructor cannot end with a
different stack head. -/
theorem activeHypothesis_wrong_head_impossible
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView)
    (_hproject : projectPrefix? db = some projection)
    (_hmember : hypothesis ∈ projection.activeHypotheses)
    (remaining : List Metamath.Spec.Expr)
    (wrong : Metamath.Spec.Expr)
    (hne : wrong ≠ operationalExpr hypothesis.formula) :
    ¬Metamath.Spec.ProofValidFrom
      (Metamath.Kernel.toDatabaseTotal db)
      (operationalFrame projection.callerFrame
        projection.activeHypotheses)
      remaining (wrong :: remaining)
      [Metamath.Spec.ProofStep.useHyp (operationalHyp hypothesis)] := by
  intro hwrong
  have hresult := proofValidFrom_single_useHyp_result hwrong
  cases hypothesis with
  | floating label typecode variableName =>
      apply hne
      have hhead := congrArg List.head? hresult
      simpa [operationalHyp, HypothesisView.formula, operationalExpr,
        ConstantHeadedFormula.toRuntime, Metamath.Kernel.toExpr,
        Metamath.Kernel.toSym, Metamath.Verify.Sym.value] using hhead
  | essential label formula =>
      apply hne
      have hhead := congrArg List.head? hresult
      simpa [operationalHyp, HypothesisView.formula] using hhead

/-- One tag/name mismatch refutes the assertion theorem's explicit
actual-formula frame condition. -/
theorem not_all_actuals_respect_of_member_mismatch
    (floatingVariables : List String)
    (actuals : List ConstantHeadedFormula)
    (actual : ConstantHeadedFormula)
    (hmember : actual ∈ actuals)
    (hmismatch :
      formulaSymbolsRespectFrame floatingVariables actual = false) :
    ¬(∀ candidate, candidate ∈ actuals →
      formulaSymbolsRespectFrame floatingVariables candidate = true) := by
  intro hall
  have := hall actual hmember
  rw [hmismatch] at this
  contradiction

end Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
