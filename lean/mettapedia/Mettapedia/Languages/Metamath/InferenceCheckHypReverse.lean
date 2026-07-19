import Mettapedia.Languages.Metamath.InferenceAssertionProjectionInvariants
import Mettapedia.Languages.Metamath.InferenceCheckHypGraph
import Mettapedia.Languages.Metamath.InferenceProjectionFidelity
import Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
import Mathlib.Data.List.Forall2

/-!
# Reverse bridge from `DB.checkHyp` to assertion-instance semantics

This module reflects successful execution of the live hypothesis checker for a
successfully projected assertion.  The exact decoded stack window determines
the authored-order finite substitution; the result exposes ordered hypothesis
instances, essential-hypothesis substitution semantics, and exact extensional
correspondence with the live output map.
-/

namespace Mettapedia.Languages.Metamath.InferenceCheckHypReverse

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceCheckHypGraph
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge
open Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation

/-! ## Executable graph facts -/

/-- Starting from the verifier's canonical prefix map, the successful graph
must return the complete source-order insertion fold. -/
private theorem checkHypOK_output_eq_sigmaFromHypsPrefix
    (db : RuntimeDB) (hyps : Array String) (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + hyps.size = stack.size})
    (index : Nat) (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hindex : index ≤ hyps.size)
    (hgraph :
      Metamath.Kernel.CheckHypOK db hyps stack off index
        (Metamath.Kernel.sigmaFromHypsPrefix db hyps stack off index)
        runtimeSubstitution) :
    runtimeSubstitution =
      Metamath.Kernel.sigmaFromHypsPrefix db hyps stack off hyps.size := by
  generalize hfuel : hyps.size - index = fuel
  induction fuel generalizing index with
  | zero =>
      have hindexEq : index = hyps.size := by omega
      subst index
      unfold Metamath.Kernel.CheckHypOK at hgraph
      simp at hgraph
      exact hgraph
  | succ fuel ih =>
      have hlt : index < hyps.size := by omega
      unfold Metamath.Kernel.CheckHypOK at hgraph
      simp only [hlt, dite_true] at hgraph
      cases hfind : db.find? hyps[index]! with
      | none => simp [hfind] at hgraph
      | some object =>
          cases object with
          | const name => simp [hfind] at hgraph
          | var name => simp [hfind] at hgraph
          | assert formula frame label => simp [hfind] at hgraph
          | hyp essential formula label =>
              cases essential with
              | false =>
                  simp only [hfind] at hgraph
                  rcases hgraph with
                    ⟨_hstack, _hshape, _htypecode, _hduplicate, htail⟩
                  have hnextMap :
                      Metamath.Kernel.sigmaFromHypsPrefix db hyps stack off
                          (index + 1) =
                        (Metamath.Kernel.sigmaFromHypsPrefix
                          db hyps stack off index).insert formula[1]!.value
                            (stack[off.1 + index]!) := by
                    simp [Metamath.Kernel.sigmaFromHypsPrefix_succ, hfind]
                  rw [← hnextMap] at htail
                  exact ih (index + 1) (by omega) htail (by omega)
              | true =>
                  simp only [hfind, ↓reduceIte] at hgraph
                  rcases hgraph with
                    ⟨_hstack, _hhead, _hsymbols, _htypecode,
                      _hsubstitution, htail⟩
                  have hnextMap :
                      Metamath.Kernel.sigmaFromHypsPrefix db hyps stack off
                          (index + 1) =
                        Metamath.Kernel.sigmaFromHypsPrefix
                          db hyps stack off index := by
                    simp [Metamath.Kernel.sigmaFromHypsPrefix_succ, hfind]
                  rw [← hnextMap] at htail
                  exact ih (index + 1) (by omega) htail (by omega)

/-- Every visited hypothesis exposes the live checker's typecode equality,
independently of the substitution accumulated before that index. -/
private theorem checkHypOK_head_eq_at
    (db : RuntimeDB) (hyps : Array String) (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + hyps.size = stack.size})
    (start target : Nat)
    (substitutionIn substitutionOut : Std.HashMap String RuntimeFormula)
    (hstart : start ≤ target) (htarget : target < hyps.size)
    (hgraph : Metamath.Kernel.CheckHypOK db hyps stack off start
      substitutionIn substitutionOut)
    (essential : Bool) (formula : RuntimeFormula) (label : String)
    (hfind : db.find? hyps[target]! = some (.hyp essential formula label)) :
    formula[0]! = stack[off.1 + target]![0]! := by
  generalize hdistance : target - start = distance
  induction distance generalizing start substitutionIn with
  | zero =>
      have hstartEq : start = target := by omega
      subst start
      unfold Metamath.Kernel.CheckHypOK at hgraph
      simp only [htarget, dite_true, hfind] at hgraph
      cases essential with
      | false =>
          rcases hgraph with
            ⟨_hstack, _hshape, htypecode, _hduplicate, _htail⟩
          exact LawfulBEq.eq_of_beq htypecode
      | true =>
          rcases hgraph with
            ⟨_hstack, _hhead, _hsymbols, htypecode,
              _hsubstitution, _htail⟩
          exact LawfulBEq.eq_of_beq htypecode
  | succ distance ih =>
      have hstartTarget : start < target := by omega
      have hstartBound : start < hyps.size := hstartTarget.trans htarget
      unfold Metamath.Kernel.CheckHypOK at hgraph
      simp only [hstartBound, dite_true] at hgraph
      cases hcurrent : db.find? hyps[start]! with
      | none => simp [hcurrent] at hgraph
      | some object =>
          cases object with
          | const name => simp [hcurrent] at hgraph
          | var name => simp [hcurrent] at hgraph
          | assert currentFormula frame currentLabel =>
              simp [hcurrent] at hgraph
          | hyp currentEssential currentFormula currentLabel =>
              cases currentEssential with
              | false =>
                  simp only [hcurrent] at hgraph
                  rcases hgraph with
                    ⟨_hstack, _hshape, _htypecode, _hduplicate, htail⟩
                  exact ih (start + 1)
                    (substitutionIn.insert currentFormula[1]!.value
                      (stack[off.1 + start]!))
                    (by omega) htail (by omega)
              | true =>
                  simp only [hcurrent, ↓reduceIte] at hgraph
                  rcases hgraph with
                    ⟨_hstack, _hhead, _hsymbols, _htypecode,
                      _hsubstitution, htail⟩
                  exact ih (start + 1) substitutionIn
                    (by omega) htail (by omega)

/-! ## Projection and exact-window facts -/

private theorem stack_get_of_exact_window
    (stack : Array RuntimeFormula) (off : Nat)
    (actuals : List ConstantHeadedFormula)
    (hwindow :
      stack.extract off stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    {index : Nat} (hindex : index < actuals.length) :
    stack[off + index]! =
      (actuals.get ⟨index, hindex⟩).toRuntime := by
  have hwindowIndex :=
    congrArg (fun formulas : Array RuntimeFormula => formulas[index]!) hwindow
  have hbound : index < stack.size - off := by
    have hsize : stack.size - off = actuals.length := by
      simpa using congrArg Array.size hwindow
    omega
  rw [Metamath.Kernel.getElem!_extract_lt stack off stack.size index
      hbound (Nat.le_refl _)] at hwindowIndex
  simpa [hindex] using hwindowIndex

private theorem runtime_fidelity_of_projectHypothesis
    (db : RuntimeDB) (label : String) (hypothesis : HypothesisView)
    (hproject : projectHypothesis? db label = some hypothesis) :
    db.find? label = some (.hyp (hypothesisEssentialBit hypothesis)
      hypothesis.formula.toRuntime label) := by
  obtain ⟨runtimeFormula, hfind, hdecode, _hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity db label hypothesis hproject
  have hruntime : runtimeFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula hypothesis.formula).mp hdecode
  simpa [hruntime] using hfind

private theorem projected_hypothesis_at
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    {index : Nat} (hindex : index < frame.hyps.size)
    (hhypothesis : index < hypotheses.length) :
    projectHypothesis? db frame.hyps[index]! =
      some (hypotheses.get ⟨index, hhypothesis⟩) := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hpoint := hordered.get (by simpa using hindex) hhypothesis
  simpa [hindex] using hpoint

private theorem wellFormed_of_projectPrefix
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectPrefix? db = some projection) :
    db.wellFormed? = true := by
  unfold projectPrefix? at hproject
  simp only [bind, Option.bind_eq_some_iff] at hproject
  obtain ⟨_guardError, _herror, _guardWellFormed, hwellFormed,
    _guardDV, _hdv, _guardEmbedded, _hembedded, _guardDeclarations,
    _hdeclarations, activeHypotheses, _hactive, _guardFrame, _hframe,
    assertions, _hassertions, _guardProjection, _hprojectionValid,
    hprojection⟩ := hproject
  cases hprojection
  unfold guard at hwellFormed
  split at hwellFormed
  · assumption
  · simp at hwellFormed

private theorem assertionViewValid_of_projectPrefix
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    assertionViewValid projection.declaredConstants
      projection.declaredVariables assertion = true := by
  have hvalid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection hproject
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  exact List.all_eq_true.mp hvalid.1.2 assertion hmember

private theorem frameProjectionValid_of_projectedAssertion
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    frameProjectionValid assertion.frame assertion.hypotheses = true := by
  have hvalid := assertionViewValid_of_projectPrefix
    db projection assertion hproject hmember
  simp only [assertionViewValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.1.1

private theorem wellFormedAssertionFrame_of_projectPrefix
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions) :
    Metamath.WF.WellFormedFrame db assertion.frame := by
  have hdatabase := Metamath.WF.wellFormedDB_of_wellFormed?
    (wellFormed_of_projectPrefix db projection hproject)
  have hfind :=
    (projectedAssertion_database_fidelity
      db projection assertion hproject hmember).1
  exact (hdatabase.2 assertion.label
    (.assert assertion.formula.toRuntime assertion.frame assertion.label)
    hfind).2

/-! ## Canonical ordered instances -/

private theorem withTypecode_eq_self
    (formula : ConstantHeadedFormula) (typecode : String)
    (htypecode : formula.typecode = typecode) :
    withTypecode typecode formula = formula := by
  cases formula
  simp [withTypecode] at htypecode ⊢
  exact htypecode.symm

private theorem hypothesisInstances_of_pointwise_typecodes :
    ∀ (hypotheses : List HypothesisView)
      (actuals : List ConstantHeadedFormula),
      hypotheses.length = actuals.length →
      (∀ (index : Nat)
          (hhypothesis : index < hypotheses.length)
          (hactual : index < actuals.length),
        match hypotheses.get ⟨index, hhypothesis⟩ with
        | .floating _ typecode _ =>
            (actuals.get ⟨index, hactual⟩).typecode = typecode
        | .essential _ formula =>
            (actuals.get ⟨index, hactual⟩).typecode = formula.typecode) →
      HypothesisInstances hypotheses actuals
        (canonicalSubstitution hypotheses actuals)
  | [], [], _, _ => .nil
  | [], _ :: _, hlength, _ => by simp at hlength
  | _ :: _, [], hlength, _ => by simp at hlength
  | hypothesis :: hypotheses, actual :: actuals, hlength, hpointwise => by
      have htailLength : hypotheses.length = actuals.length := by
        simpa using hlength
      have htailPointwise :
          ∀ (index : Nat) (hhypothesis : index < hypotheses.length)
            (hactual : index < actuals.length),
          match hypotheses.get ⟨index, hhypothesis⟩ with
          | .floating _ typecode _ =>
              (actuals.get ⟨index, hactual⟩).typecode = typecode
          | .essential _ formula =>
              (actuals.get ⟨index, hactual⟩).typecode = formula.typecode := by
        intro index hhypothesis hactual
        simpa using hpointwise (index + 1)
          (by simpa using hhypothesis) (by simpa using hactual)
      have htail := hypothesisInstances_of_pointwise_typecodes
        hypotheses actuals htailLength htailPointwise
      cases hypothesis with
      | floating label typecode variableName =>
          have htypecode : actual.typecode = typecode := by
            simpa using hpointwise 0 (by simp) (by simp)
          have hactual : withTypecode typecode actual = actual :=
            withTypecode_eq_self actual typecode htypecode
          simpa [canonicalSubstitution, hactual] using
            (HypothesisInstances.floating htypecode htail)
      | essential label formula =>
          have htypecode : actual.typecode = formula.typecode := by
            simpa using hpointwise 0 (by simp) (by simp)
          exact HypothesisInstances.essential htypecode htail

private theorem hypothesisInstances_of_checkHypOK
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + frame.hyps.size = stack.size})
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hgraph : Metamath.Kernel.CheckHypOK db frame.hyps stack off 0 ∅
      runtimeSubstitution) :
    HypothesisInstances hypotheses actuals
      (canonicalSubstitution hypotheses actuals) := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hhypothesesLength : hypotheses.length = frame.hyps.size := by
    simpa using hordered.length_eq.symm
  have hactualsLength : actuals.length = frame.hyps.size := by
    have hsize := congrArg Array.size hwindow
    simp at hsize
    omega
  apply hypothesisInstances_of_pointwise_typecodes
  · omega
  · intro index hhypothesis hactual
    have hframe : index < frame.hyps.size := by omega
    cases hview : hypotheses.get ⟨index, hhypothesis⟩ with
    | floating label typecode variableName =>
        have hprojectAt := projected_hypothesis_at
          db frame hypotheses hproject hframe hhypothesis
        rw [hview] at hprojectAt
        have hfindAt := runtime_fidelity_of_projectHypothesis
          db frame.hyps[index]! (.floating label typecode variableName)
          hprojectAt
        have hhead := checkHypOK_head_eq_at db frame.hyps stack off
          0 index ∅ runtimeSubstitution (Nat.zero_le _) hframe hgraph
          false
          (ConstantHeadedFormula.mk typecode [.var variableName]).toRuntime
          frame.hyps[index]! (by simpa [hypothesisEssentialBit,
            HypothesisView.formula] using hfindAt)
        have hstack := stack_get_of_exact_window
          stack off.1 actuals hwindow hactual
        rw [hstack] at hhead
        simpa [ConstantHeadedFormula.toRuntime] using hhead.symm
    | essential label formula =>
        have hprojectAt := projected_hypothesis_at
          db frame hypotheses hproject hframe hhypothesis
        rw [hview] at hprojectAt
        have hfindAt := runtime_fidelity_of_projectHypothesis
          db frame.hyps[index]! (.essential label formula) hprojectAt
        have hhead := checkHypOK_head_eq_at db frame.hyps stack off
          0 index ∅ runtimeSubstitution (Nat.zero_le _) hframe hgraph true
          formula.toRuntime frame.hyps[index]! (by
            simpa [hypothesisEssentialBit, HypothesisView.formula]
              using hfindAt)
        have hstack := stack_get_of_exact_window
          stack off.1 actuals hwindow hactual
        rw [hstack] at hhead
        simpa [ConstantHeadedFormula.toRuntime] using hhead.symm

/-! ## Exact live-map correspondence -/

private def HypothesisInstanceAt (substitution : FiniteSubstitution)
    (hypothesis : HypothesisView) (actual : ConstantHeadedFormula) : Prop :=
  match hypothesis with
  | .floating _ typecode variableName =>
      actual.typecode = typecode ∧
        LookupSemantics substitution variableName actual
  | .essential _ formula => actual.typecode = formula.typecode

private theorem HypothesisInstanceAt.cons_binding
    {substitution : FiniteSubstitution} {hypothesis : HypothesisView}
    {actual : ConstantHeadedFormula} (binding : FormulaBinding)
    (hinstance : HypothesisInstanceAt substitution hypothesis actual) :
    HypothesisInstanceAt (binding :: substitution) hypothesis actual := by
  cases hypothesis with
  | floating label typecode variableName =>
      exact ⟨hinstance.1, List.mem_cons_of_mem binding hinstance.2⟩
  | essential label formula => exact hinstance

private theorem HypothesisInstanceAt.forall₂_cons_binding
    (binding : FormulaBinding) :
    ∀ {hypotheses : List HypothesisView}
      {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution},
      List.Forall₂ (HypothesisInstanceAt substitution)
          hypotheses actuals →
        List.Forall₂ (HypothesisInstanceAt (binding :: substitution))
          hypotheses actuals
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, _, .cons hinstance tail =>
      .cons (hinstance.cons_binding binding)
        (HypothesisInstanceAt.forall₂_cons_binding binding tail)

private theorem hypothesisInstances_forall₂_instanceAt
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution) :
    List.Forall₂ (HypothesisInstanceAt substitution) hypotheses actuals := by
  induction instances with
  | nil => exact .nil
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      apply List.Forall₂.cons
      · exact ⟨typecode_eq, by simp [LookupSemantics]⟩
      · exact HypothesisInstanceAt.forall₂_cons_binding
          ⟨variableName, actual⟩ ih
  | essential typecode_eq tail ih => exact .cons typecode_eq ih

private theorem hypothesisInstances_binding_origin
    {hypotheses : List HypothesisView}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (instances : HypothesisInstances hypotheses actuals substitution)
    {name : String} {replacement : ConstantHeadedFormula}
    (hlookup : LookupSemantics substitution name replacement) :
    ∃ (index : Nat)
        (hhypothesis : index < hypotheses.length)
        (hactual : index < actuals.length)
        (label typecode : String),
      hypotheses.get ⟨index, hhypothesis⟩ =
          .floating label typecode name ∧
        actuals.get ⟨index, hactual⟩ = replacement := by
  induction instances with
  | nil => simp [LookupSemantics] at hlookup
  | @floating label typecode variableName actual hypotheses actuals
      substitution typecode_eq tail ih =>
      change ({ variableName := name, replacement } : FormulaBinding) ∈
        { variableName := variableName, replacement := actual } :: substitution
        at hlookup
      rcases List.mem_cons.mp hlookup with hhead | htail
      · have hname : name = variableName :=
          congrArg FormulaBinding.variableName hhead
        have hreplacement : replacement = actual :=
          congrArg FormulaBinding.replacement hhead
        subst name
        subst replacement
        exact ⟨0, by simp, by simp, label, typecode, rfl, rfl⟩
      · obtain ⟨index, hhypothesis, hactual, sourceLabel,
          sourceTypecode, hview, hvalue⟩ := ih htail
        exact ⟨index + 1, by simp [hhypothesis], by simp [hactual],
          sourceLabel, sourceTypecode, by simpa using hview,
          by simpa using hvalue⟩
  | @essential label formula actual hypotheses actuals substitution
      typecode_eq tail ih =>
      obtain ⟨index, hhypothesis, hactual, sourceLabel,
          sourceTypecode, hview, hvalue⟩ := ih hlookup
      exact ⟨index + 1, by simp [hhypothesis], by simp [hactual],
        sourceLabel, sourceTypecode, by simpa using hview,
        by simpa using hvalue⟩

private theorem runtimeCorrespondence_sigmaFromHypsPrefix
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + frame.hyps.size = stack.size})
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (hinstances : HypothesisInstances hypotheses actuals substitution)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hwellFormed :
      Metamath.WF.WellFormedFrame db
        (Metamath.Verify.Frame.mk #[] frame.hyps)) :
    RuntimeSubstitutionCorrespondence substitution
      (Metamath.Kernel.sigmaFromHypsPrefix
        db frame.hyps stack off frame.hyps.size) := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hhypothesesLength : hypotheses.length = frame.hyps.size := by
    simpa using hordered.length_eq.symm
  have hactualsLength : actuals.length = frame.hyps.size := by
    rw [← hinstances.lengths]
    exact hhypothesesLength
  have hpointInstances := hypothesisInstances_forall₂_instanceAt hinstances
  have hprefix := Metamath.Kernel.sigmaFromHypsPrefix_prefix
    db frame.hyps stack off hwellFormed frame.hyps.size (Nat.le_refl _)
  have hcovers := Metamath.Kernel.sigmaFromHypsPrefix_covers
    db frame.hyps stack off hwellFormed frame.hyps.size (Nat.le_refl _)
  intro name runtimeFormula
  constructor
  · intro hlookup
    obtain ⟨index, hindex, runtimeSource, sourceLabel, hfind,
        _hsize, hkey, hvalue⟩ :=
      hprefix name runtimeFormula hlookup
    have hhypothesis : index < hypotheses.length := by omega
    have hactual : index < actuals.length := by omega
    let hypothesis := hypotheses.get ⟨index, hhypothesis⟩
    have hprojectAt :
        projectHypothesis? db frame.hyps[index]! = some hypothesis :=
      projected_hypothesis_at db frame hypotheses hproject
        hindex hhypothesis
    have hfindAt := runtime_fidelity_of_projectHypothesis
      db frame.hyps[index]! hypothesis hprojectAt
    have hobjects :
        some (Metamath.Verify.Object.hyp false runtimeSource sourceLabel) =
          some (Metamath.Verify.Object.hyp
            (hypothesisEssentialBit hypothesis)
            hypothesis.formula.toRuntime frame.hyps[index]!) := by
      rw [← hfind, ← hfindAt]
    have hinstance := hpointInstances.get hhypothesis hactual
    change HypothesisInstanceAt substitution hypothesis
      (actuals.get ⟨index, hactual⟩) at hinstance
    have hstack := stack_get_of_exact_window
      stack off.1 actuals hwindow hactual
    cases hview : hypothesis with
    | essential label formula =>
        simp [hview, hypothesisEssentialBit] at hobjects
    | floating label typecode variableName =>
        simp only [hview, hypothesisEssentialBit, HypothesisView.formula]
          at hobjects hinstance
        injection hobjects with hobject
        injection hobject with hformula hlabel
        subst runtimeSource
        subst sourceLabel
        have hname : variableName = name := by
          simpa [ConstantHeadedFormula.toRuntime] using hkey
        subst variableName
        refine ⟨actuals.get ⟨index, hactual⟩, hinstance.2, ?_⟩
        exact hvalue.trans hstack
  · rintro ⟨replacement, hlookup, rfl⟩
    obtain ⟨index, hhypothesis, hactual, sourceLabel, typecode,
        hview, hreplacement⟩ :=
      hypothesisInstances_binding_origin hinstances hlookup
    have hindex : index < frame.hyps.size := by omega
    have hprojectAt := projected_hypothesis_at
      db frame hypotheses hproject hindex hhypothesis
    rw [hview] at hprojectAt
    have hfindAt := runtime_fidelity_of_projectHypothesis
      db frame.hyps[index]!
        (.floating sourceLabel typecode name) hprojectAt
    have hfind :
        db.find? frame.hyps[index]! =
          some (.hyp false
            (ConstantHeadedFormula.mk typecode [.var name]).toRuntime
            frame.hyps[index]!) := by
      simpa [hypothesisEssentialBit, HypothesisView.formula] using hfindAt
    have hshape :
        (ConstantHeadedFormula.mk typecode [.var name]).toRuntime.isFloatShape =
          true := by
      simp [ConstantHeadedFormula.toRuntime,
        Metamath.Verify.Formula.isFloatShape]
    have hcovered := hcovers index hindex
      (ConstantHeadedFormula.mk typecode [.var name]).toRuntime
      frame.hyps[index]! hfind hshape
    have hstack := stack_get_of_exact_window
      stack off.1 actuals hwindow hactual
    have hcovered' :
        (Metamath.Kernel.sigmaFromHypsPrefix
          db frame.hyps stack off frame.hyps.size)[name]? =
            some (stack[off.1 + index]!) := by
      simpa [ConstantHeadedFormula.toRuntime,
        Metamath.Verify.Sym.value] using hcovered
    rw [hstack, hreplacement] at hcovered'
    exact hcovered'

/-! ## Essential hypotheses against the completed substitution -/

private theorem essentialMatches_of_pointwise :
    ∀ (substitution : FiniteSubstitution)
      (hypotheses : List HypothesisView)
      (actuals : List ConstantHeadedFormula),
      hypotheses.length = actuals.length →
      (∀ (index : Nat)
          (hhypothesis : index < hypotheses.length)
          (hactual : index < actuals.length)
          (label : String) (formula : ConstantHeadedFormula),
        hypotheses.get ⟨index, hhypothesis⟩ = .essential label formula →
          FormulaSubstitutionSemantics substitution formula
            (actuals.get ⟨index, hactual⟩)) →
      EssentialMatches substitution hypotheses actuals
  | _, [], [], _, _ => trivial
  | _, [], _ :: _, hlength, _ => by simp at hlength
  | _, _ :: _, [], hlength, _ => by simp at hlength
  | substitution, hypothesis :: hypotheses, actual :: actuals,
      hlength, hpointwise => by
      have htailLength : hypotheses.length = actuals.length := by
        simpa using hlength
      have htailPointwise :
          ∀ (index : Nat) (hhypothesis : index < hypotheses.length)
            (hactual : index < actuals.length)
            (label : String) (formula : ConstantHeadedFormula),
          hypotheses.get ⟨index, hhypothesis⟩ = .essential label formula →
            FormulaSubstitutionSemantics substitution formula
              (actuals.get ⟨index, hactual⟩) := by
        intro index hhypothesis hactual label formula hview
        apply hpointwise (index + 1) (by simpa using hhypothesis)
          (by simpa using hactual) label formula
        simpa using hview
      have htail := essentialMatches_of_pointwise substitution hypotheses
        actuals htailLength htailPointwise
      cases hypothesis with
      | floating label typecode variableName =>
          simpa [EssentialMatches] using htail
      | essential label formula =>
          exact ⟨hpointwise 0 (by simp) (by simp) label formula rfl, htail⟩

private theorem essentialMatches_of_checkHyp
    (db : RuntimeDB) (frame : RuntimeFrame)
    (hypotheses : List HypothesisView)
    (actuals : List ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat // offset + frame.hyps.size = stack.size})
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hproject :
      projectHypotheses? db frame.hyps.toList = some hypotheses)
    (hinstances : HypothesisInstances hypotheses actuals substitution)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hwellFormedDB : Metamath.WF.WellFormedDB db)
    (hwellFormed : Metamath.WF.WellFormedFrame db frame)
    (hframeValid : frameProjectionValid frame hypotheses = true)
    (hsuccess :
      db.checkHyp frame.hyps stack off 0 ∅ = .ok runtimeSubstitution)
    (hcorrespondence :
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution) :
    EssentialMatches substitution hypotheses actuals := by
  have hordered :=
    projectHypotheses?_forall₂ db frame.hyps.toList hypotheses hproject
  have hhypothesesLength : hypotheses.length = frame.hyps.size := by
    simpa using hordered.length_eq.symm
  have hactualsLength : actuals.length = frame.hyps.size := by
    rw [← hinstances.lengths]
    exact hhypothesesLength
  have hunique : SubstitutionKeysUnique substitution :=
    hinstances.substitutionKeysUnique
      (floatingVariableNames_nodup_of_frameProjectionValid
        frame hypotheses hframeValid)
  apply essentialMatches_of_pointwise substitution hypotheses actuals
    hinstances.lengths
  intro index hhypothesis hactual label formula hview
  have hframe : index < frame.hyps.size := by omega
  have hprojectAt := projected_hypothesis_at
    db frame hypotheses hproject hframe hhypothesis
  rw [hview] at hprojectAt
  have hfindAt := runtime_fidelity_of_projectHypothesis
    db frame.hyps[index]! (.essential label formula) hprojectAt
  have halignment := Metamath.Kernel.checkHyp_stack_alignment
    db frame.hyps stack off runtimeSubstitution hwellFormedDB hwellFormed.2
    hsuccess index hframe
  have hsubstitution := halignment.2 formula.toRuntime frame.hyps[index]! (by
    simpa [hypothesisEssentialBit, HypothesisView.formula] using hfindAt)
  have hstack := stack_get_of_exact_window
    stack off.1 actuals hwindow hactual
  rw [hstack] at hsubstitution
  exact (formulaSubstitutionSemantics_iff_runtime_subst_of_correspondence
    hunique hcorrespondence formula (actuals.get ⟨index, hactual⟩)).2
      hsubstitution

/-! ## Public reverse bridge -/

/-- The exact successful graph of the live checker determines the independent
ordered instance substitution.  The same substitution validates every
essential hypothesis and corresponds extensionally to the graph's output map. -/
theorem projectedAssertion_instances_of_checkHypOK
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat //
      offset + assertion.frame.hyps.size = stack.size})
    (actuals : List ConstantHeadedFormula)
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hgraph : Metamath.Kernel.CheckHypOK db assertion.frame.hyps stack off
      0 ∅ runtimeSubstitution) :
    let substitution :=
      canonicalSubstitution assertion.hypotheses actuals
    HypothesisInstances assertion.hypotheses actuals substitution ∧
      EssentialMatches substitution assertion.hypotheses actuals ∧
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution := by
  dsimp only
  have hfidelity := projectedAssertion_database_fidelity
    db projection assertion hproject hmember
  have hhypotheses := hfidelity.2.1
  have hinstances := hypothesisInstances_of_checkHypOK
    db assertion.frame assertion.hypotheses actuals stack off
    runtimeSubstitution hhypotheses hwindow hgraph
  have hgraphCanonical :
      Metamath.Kernel.CheckHypOK db assertion.frame.hyps stack off 0
        (Metamath.Kernel.sigmaFromHypsPrefix
          db assertion.frame.hyps stack off 0)
        runtimeSubstitution := by
    simpa [Metamath.Kernel.sigmaFromHypsPrefix] using hgraph
  have houtput := checkHypOK_output_eq_sigmaFromHypsPrefix
    db assertion.frame.hyps stack off 0 runtimeSubstitution
    (Nat.zero_le _) hgraphCanonical
  have hwellFormed := wellFormedAssertionFrame_of_projectPrefix
    db projection assertion hproject hmember
  have hwellFormedHyps := Metamath.Kernel.wellFormedFrame_hyps_only
    db assertion.frame hwellFormed
  have hcorrespondenceCanonical :=
    runtimeCorrespondence_sigmaFromHypsPrefix
      db assertion.frame assertion.hypotheses actuals
      (canonicalSubstitution assertion.hypotheses actuals) stack off
      hhypotheses hinstances hwindow hwellFormedHyps
  have hcorrespondence :
      RuntimeSubstitutionCorrespondence
        (canonicalSubstitution assertion.hypotheses actuals)
        runtimeSubstitution := by
    rw [houtput]
    exact hcorrespondenceCanonical
  have hwellFormedDB := Metamath.WF.wellFormedDB_of_wellFormed?
    (wellFormed_of_projectPrefix db projection hproject)
  have hframeValid := frameProjectionValid_of_projectedAssertion
    db projection assertion hproject hmember
  have hsuccess :=
    (checkHypOK_iff_checkHyp_ok db assertion.frame.hyps stack off 0 ∅
      runtimeSubstitution).1 hgraph
  have hessential := essentialMatches_of_checkHyp
    db assertion.frame assertion.hypotheses actuals
    (canonicalSubstitution assertion.hypotheses actuals) stack off
    runtimeSubstitution hhypotheses hinstances hwindow hwellFormedDB
    hwellFormed hframeValid hsuccess hcorrespondence
  exact ⟨hinstances, hessential, hcorrespondence⟩

/-- Executable success is therefore equivalent data for the reverse bridge;
the graph premise above is not an additional trusted assumption. -/
theorem projectedAssertion_instances_of_checkHyp_ok
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat //
      offset + assertion.frame.hyps.size = stack.size})
    (actuals : List ConstantHeadedFormula)
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hsuccess : db.checkHyp assertion.frame.hyps stack off 0 ∅ =
      .ok runtimeSubstitution) :
    let substitution :=
      canonicalSubstitution assertion.hypotheses actuals
    HypothesisInstances assertion.hypotheses actuals substitution ∧
      EssentialMatches substitution assertion.hypotheses actuals ∧
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution := by
  apply projectedAssertion_instances_of_checkHypOK
    db projection assertion stack off actuals runtimeSubstitution
    hproject hmember hwindow
  exact (checkHypOK_iff_checkHyp_ok db assertion.frame.hyps stack off 0 ∅
    runtimeSubstitution).2 hsuccess

/-! ## Observable boundaries -/

/-- Positive boundary: every decoded stack actual accepted by the live checker
has exactly the authored typecode of its projected mandatory hypothesis. -/
theorem actual_typecode_eq_of_projected_checkHyp_ok
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat //
      offset + assertion.frame.hyps.size = stack.size})
    (actuals : List ConstantHeadedFormula)
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (hsuccess : db.checkHyp assertion.frame.hyps stack off 0 ∅ =
      .ok runtimeSubstitution)
    (index : Nat)
    (hhypothesis : index < assertion.hypotheses.length)
    (hactual : index < actuals.length) :
    (actuals.get ⟨index, hactual⟩).typecode =
      (assertion.hypotheses.get ⟨index, hhypothesis⟩).formula.typecode := by
  have hreverse := projectedAssertion_instances_of_checkHyp_ok
    db projection assertion stack off actuals runtimeSubstitution
    hproject hmember hwindow hsuccess
  have hpoint :=
    (hypothesisInstances_forall₂_instanceAt hreverse.1).get
      hhypothesis hactual
  cases hview : assertion.hypotheses.get ⟨index, hhypothesis⟩ with
  | floating label typecode variableName =>
      rw [hview] at hpoint
      simpa [HypothesisInstanceAt, HypothesisView.formula] using hpoint.1
  | essential label formula =>
      rw [hview] at hpoint
      simpa [HypothesisInstanceAt, HypothesisView.formula] using hpoint

/-- Negative boundary: changing an authored mandatory-hypothesis typecode in
the decoded stack window makes successful live checking impossible. -/
theorem checkHyp_ne_ok_of_actual_typecode_ne
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (stack : Array RuntimeFormula)
    (off : {offset : Nat //
      offset + assertion.frame.hyps.size = stack.size})
    (actuals : List ConstantHeadedFormula)
    (runtimeSubstitution : Std.HashMap String RuntimeFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : assertion ∈ projection.assertions)
    (hwindow :
      stack.extract off.1 stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (index : Nat)
    (hhypothesis : index < assertion.hypotheses.length)
    (hactual : index < actuals.length)
    (hne : (actuals.get ⟨index, hactual⟩).typecode ≠
      (assertion.hypotheses.get ⟨index, hhypothesis⟩).formula.typecode) :
    db.checkHyp assertion.frame.hyps stack off 0 ∅ ≠
      .ok runtimeSubstitution := by
  intro hsuccess
  exact hne (actual_typecode_eq_of_projected_checkHyp_ok
    db projection assertion stack off actuals runtimeSubstitution
    hproject hmember hwindow hsuccess index hhypothesis hactual)

end Mettapedia.Languages.Metamath.InferenceCheckHypReverse
