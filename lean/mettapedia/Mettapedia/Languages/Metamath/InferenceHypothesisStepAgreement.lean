import Mettapedia.Languages.Metamath.InferenceActiveHypothesisLeaf
import Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification

/-!
# Exact live steps for projected active hypotheses

This runtime agreement layer connects a projected active hypothesis to the
live `mm-lean4` hypothesis branch.  The branch pushes exactly the decoded
formula, preserves the caller-frame stack invariant, and supports reverse
classification from an in-scope live hypothesis object.

The static zero-premise rule application and root-pinned typed leaf live in
`InferenceActiveHypothesisLeaf`; this module does not redefine them.
-/

namespace Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification

/-! ## Exact live hypothesis step -/

/-- Both live hypothesis branches push exactly the runtime image retained by
the active view.  The proof uses the exact floating/essential success lemmas
underlying `stepNormal_of_hyp_in_frame`, together with projection fidelity. -/
theorem activeHypothesis_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr : RuntimeProofState)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    db.stepNormal pr hypothesis.label =
      .ok (pr.push hypothesis.formula.toRuntime) := by
  obtain ⟨hscope, hfind⟩ :=
    projectedActiveHypothesis_database_fidelity
      db projection hypothesis hproject hmember
  cases hypothesis with
  | floating label typecode variableName =>
      have hfind' :
          db.find? label =
            some (.hyp false
              (ConstantHeadedFormula.mk typecode [.var variableName]).toRuntime
              label) := by
        simpa [hypothesisEssentialBit, HypothesisView.formula,
          HypothesisView.label] using hfind
      have hshape :
          (ConstantHeadedFormula.mk typecode
            [.var variableName]).toRuntime.isFloatShape = true := by
        simp [ConstantHeadedFormula.toRuntime,
          Metamath.Verify.Formula.isFloatShape]
      exact Metamath.Kernel.stepNormal_floating_success
        db pr label
          (ConstantHeadedFormula.mk typecode [.var variableName]).toRuntime
          label hfind' hscope hshape
  | essential label formula =>
      have hfind' :
          db.find? label =
            some (.hyp true formula.toRuntime label) := by
        simpa [hypothesisEssentialBit, HypothesisView.formula,
          HypothesisView.label] using hfind
      exact Metamath.Kernel.stepNormal_essential_success
        db pr label formula.toRuntime label hfind' hscope
          (ConstantHeadedFormula.hasConstHead_toRuntime formula)

/-- Explicit floating-hypothesis specialization. -/
theorem floatingHypothesis_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (label typecode variableName : String) (pr : RuntimeProofState)
    (hproject : projectPrefix? db = some projection)
    (hmember :
      .floating label typecode variableName ∈ projection.activeHypotheses) :
    db.stepNormal pr label =
      .ok (pr.push
        (ConstantHeadedFormula.mk typecode [.var variableName]).toRuntime) :=
  activeHypothesis_stepNormal db projection
    (.floating label typecode variableName) pr hproject hmember

/-- Explicit essential-hypothesis specialization. -/
theorem essentialHypothesis_stepNormal
    (db : RuntimeDB) (projection : PrefixProjection)
    (label : String) (formula : ConstantHeadedFormula)
    (pr : RuntimeProofState)
    (hproject : projectPrefix? db = some projection)
    (hmember : .essential label formula ∈ projection.activeHypotheses) :
    db.stepNormal pr label = .ok (pr.push formula.toRuntime) :=
  activeHypothesis_stepNormal db projection
    (.essential label formula) pr hproject hmember

/-- Successful execution at an active hypothesis label cannot return a
different proof state. -/
theorem activeHypothesis_stepNormal_result_eq
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr next : RuntimeProofState)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses)
    (hstep : db.stepNormal pr hypothesis.label = .ok next) :
    next = pr.push hypothesis.formula.toRuntime := by
  rw [activeHypothesis_stepNormal db projection hypothesis pr
    hproject hmember] at hstep
  exact Except.ok.inj hstep |>.symm

/-! ## Stack-invariant preservation -/

/-- The formula of an active projected hypothesis passes the live symbol gate
for the exact caller frame. -/
theorem activeHypothesis_formula_respects_callerFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    db.formulaSymsRespectFrame hypothesis.formula.toRuntime db.frame = true := by
  have hfields := projectPrefix?_eq_some_fields db projection hproject
  have hvalid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection hproject
  simp only [prefixProjectionValid, Bool.and_eq_true] at hvalid
  have hframeValid :
      frameProjectionValid projection.callerFrame
        projection.activeHypotheses = true :=
    hvalid.1.1.1.2
  have hcaller :
      projection.callerFrame = proofFacingCallerFrame db :=
    hfields.2.2.1
  rw [hcaller] at hframeValid
  have hactive :
      projectHypotheses? db (proofFacingCallerFrame db).hyps.toList =
        some projection.activeHypotheses := by
    simpa [proofFacingCallerFrame] using hfields.2.2.2.1
  have hgate := projectedHypothesisFormula_runtimeGate_of_frameValid
    db (proofFacingCallerFrame db) projection.activeHypotheses hactive
      hframeValid hypothesis hmember
  simpa [Metamath.Verify.DB.formulaSymsRespectFrame,
    Metamath.Verify.DB.frameFloatVars, proofFacingCallerFrame] using hgate

/-- Executing an active-hypothesis leaf preserves the caller-frame invariant
by pushing the exact projected formula. -/
theorem activeHypothesis_push_stackRespectsFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (stack : Array RuntimeFormula)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses)
    (hstack : Metamath.Kernel.StackRespectsFrame db db.frame stack) :
    Metamath.Kernel.StackRespectsFrame db db.frame
      (stack.push hypothesis.formula.toRuntime) :=
  Metamath.Kernel.stackRespectsFrame_push db db.frame stack
    hypothesis.formula.toRuntime hstack
      (activeHypothesis_formula_respects_callerFrame
        db projection hypothesis hproject hmember)

/-- Proof-state formulation consumed directly by a recursive source-proof
executor. -/
theorem activeHypothesis_step_stackRespectsFrame
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr : RuntimeProofState)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses)
    (hstack : Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    Metamath.Kernel.StackRespectsFrame db db.frame
      (pr.push hypothesis.formula.toRuntime).stack := by
  exact activeHypothesis_push_stackRespectsFrame
    db projection hypothesis pr.stack hproject hmember hstack

/-! ## Reverse active-view reflection -/

private theorem exists_right_of_forall₂_left_member
    {leftType rightType : Type} {relation : leftType → rightType → Prop}
    {left : List leftType} {right : List rightType}
    (hordered : List.Forall₂ relation left right)
    {target : leftType} (hmember : target ∈ left) :
    ∃ result, result ∈ right ∧ relation target result := by
  induction hordered with
  | nil => simp at hmember
  | cons hhead _htail ih =>
      simp only [List.mem_cons] at hmember
      rcases hmember with rfl | htailMember
      · exact ⟨_, by simp, hhead⟩
      · obtain ⟨result, hresultMember, hresult⟩ := ih htailMember
        exact ⟨result, by simp [hresultMember], hresult⟩

/-- A live hypothesis object at an active frame label is represented by an
active projected view with the exact discriminator, formula, and embedded
label.  This is the reverse classification boundary needed by source-fold
reflection. -/
theorem projectedActiveHypothesis_of_runtime_member
    (db : RuntimeDB) (projection : PrefixProjection)
    (label embeddedLabel : String) (essential : Bool)
    (formula : RuntimeFormula)
    (hproject : projectPrefix? db = some projection)
    (hscope : label ∈ db.frame.hyps.toList)
    (hfind : db.find? label =
      some (.hyp essential formula embeddedLabel)) :
    ∃ hypothesis,
      hypothesis ∈ projection.activeHypotheses ∧
      hypothesis.label = label ∧
      essential = hypothesisEssentialBit hypothesis ∧
      formula = hypothesis.formula.toRuntime ∧
      embeddedLabel = label := by
  have hordered :=
    projectedActiveHypotheses_ordered_fidelity db projection hproject
  obtain ⟨hypothesis, hmember, hhypothesisProject⟩ :=
    exists_right_of_forall₂_left_member hordered hscope
  obtain ⟨runtimeFormula, hviewFind, hdecode, hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity
      db label hypothesis hhypothesisProject
  have hruntime : runtimeFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff
      runtimeFormula hypothesis.formula).mp hdecode
  have hobjects :
      Metamath.Verify.Object.hyp essential formula embeddedLabel =
        .hyp (hypothesisEssentialBit hypothesis) runtimeFormula label :=
    Option.some.inj (hfind.symm.trans hviewFind)
  injection hobjects with hessential hformula hembedded
  exact ⟨hypothesis, hmember, hlabel, hessential,
    hformula.trans hruntime, hembedded⟩

/-! ## Negative boundary -/

/-- The live hypothesis branch cannot report a different result. -/
theorem activeHypothesis_stepNormal_ne_wrong_result
    (db : RuntimeDB) (projection : PrefixProjection)
    (hypothesis : HypothesisView) (pr wrong : RuntimeProofState)
    (hproject : projectPrefix? db = some projection)
    (hmember : hypothesis ∈ projection.activeHypotheses)
    (hne : wrong ≠ pr.push hypothesis.formula.toRuntime) :
    db.stepNormal pr hypothesis.label ≠ .ok wrong := by
  rw [activeHypothesis_stepNormal db projection hypothesis pr
    hproject hmember]
  intro heq
  exact hne (Except.ok.inj heq).symm

end Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
