import Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Compressed-lane reflection: shipped acceptance rebuilds the source theorem

Item 4's reflection direction.  The forward lane shows every source
step is executed by the shipped mm-lean4 functions; here the converse
is assembled: shipped **acceptance** reconstructs the source header
build (`headerBuild_runtimeReflected` — each step decided by `preload`
inversion plus reverse lookup fidelity, the successor identified by
determinism against the forward preservation) and, composed with the
sealed `execute_mmLean4Reflected`, the whole compressed occurrence
(`compressedTheoremStep_of_mmLean4`).  `actionsVerified` excludes
`unknown` (`?`) actions by design: incomplete-proof admission is a
distinct source judgment and cannot manufacture a proof tree.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionParserBridge
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
open Metamath.Verify

/-! ## Canonical `preload` outcomes -/

theorem preload_hyp_ok (db : RuntimeDB) (before : RuntimeProofState)
    (label embedded : String) (essential : Bool)
    (runtimeFormula : RuntimeFormula)
    (hfind : db.find? label = some (.hyp essential runtimeFormula embedded))
    (hscope : label ∈ db.frame.hyps.toList) :
    db.preload before label =
      .ok (before.pushHeap (.fmla runtimeFormula)) := by
  simp only [Metamath.Verify.DB.preload, hfind, hscope]
  rfl

theorem preload_hyp_error (db : RuntimeDB) (before : RuntimeProofState)
    (label embedded : String) (essential : Bool)
    (runtimeFormula : RuntimeFormula)
    (hfind : db.find? label = some (.hyp essential runtimeFormula embedded))
    (hscope : label ∉ db.frame.hyps.toList) :
    db.preload before label =
      .error (.proofCheck (.hypothesisNotInDatabaseScope label)) := by
  simp only [Metamath.Verify.DB.preload, hfind, hscope]
  rfl

theorem preload_assert_ok (db : RuntimeDB) (before : RuntimeProofState)
    (label embedded : String)
    (runtimeFormula : RuntimeFormula) (frame : RuntimeFrame)
    (hfind : db.find? label = some (.assert runtimeFormula frame embedded)) :
    db.preload before label =
      .ok (before.pushHeap (.assert runtimeFormula frame)) := by
  simp only [Metamath.Verify.DB.preload, hfind]
  rfl

theorem preload_none_error (db : RuntimeDB) (before : RuntimeProofState)
    (label : String) (hfind : db.find? label = none) :
    db.preload before label =
      .error (.proofCheck (.statementNotFound label)) := by
  simp only [Metamath.Verify.DB.preload, hfind]
  rfl

theorem preload_const_error (db : RuntimeDB) (before : RuntimeProofState)
    (label name : String) (hfind : db.find? label = some (.const name)) :
    db.preload before label =
      .error (.proofCheck (.statementNotFound label)) := by
  simp only [Metamath.Verify.DB.preload, hfind]
  rfl

theorem preload_var_error (db : RuntimeDB) (before : RuntimeProofState)
    (label name : String) (hfind : db.find? label = some (.var name)) :
    db.preload before label =
      .error (.proofCheck (.statementNotFound label)) := by
  simp only [Metamath.Verify.DB.preload, hfind]
  rfl

/-- Inversion of shipped `preload` acceptance: exactly one of the two live
object shapes was found, together with the scope side condition and the exact
successor proof state. -/
theorem preload_ok_inv (db : RuntimeDB) (before after : RuntimeProofState)
    (label : String)
    (accepted : db.preload before label = .ok after) :
    (∃ essential runtimeFormula embedded,
        db.find? label = some (.hyp essential runtimeFormula embedded) ∧
          label ∈ db.frame.hyps.toList ∧
          after = before.pushHeap (.fmla runtimeFormula)) ∨
      (∃ runtimeFormula frame embedded,
        db.find? label = some (.assert runtimeFormula frame embedded) ∧
          after = before.pushHeap (.assert runtimeFormula frame)) := by
  cases hfind : db.find? label with
  | none =>
      exact absurd
        (accepted.symm.trans (preload_none_error db before label hfind))
        (by simp)
  | some object =>
      cases object with
      | const name =>
          exact absurd
            (accepted.symm.trans (preload_const_error db before label name hfind))
            (by simp)
      | var name =>
          exact absurd
            (accepted.symm.trans (preload_var_error db before label name hfind))
            (by simp)
      | hyp essential runtimeFormula embedded =>
          by_cases hscope : label ∈ db.frame.hyps.toList
          · refine Or.inl ⟨essential, runtimeFormula, embedded, rfl, hscope, ?_⟩
            exact Except.ok.inj (accepted.symm.trans
              (preload_hyp_ok db before label embedded essential runtimeFormula
                hfind hscope))
          · exact absurd (accepted.symm.trans
              (preload_hyp_error db before label embedded essential
                runtimeFormula hfind hscope)) (by simp)
      | assert runtimeFormula frame embedded =>
          refine Or.inr ⟨runtimeFormula, frame, embedded, rfl, ?_⟩
          exact Except.ok.inj (accepted.symm.trans
            (preload_assert_ok db before label embedded runtimeFormula frame
              hfind))

/-- The two `preload` acceptance shapes are mutually exclusive, so the
inversion above identifies the live object uniquely. -/
theorem preload_ok_inv_disjoint (db : RuntimeDB) (label : String)
    (essential : Bool) (hypFormula : RuntimeFormula)
    (hypEmbedded : String)
    (assertFormula : RuntimeFormula) (frame : RuntimeFrame)
    (assertEmbedded : String)
    (hhyp : db.find? label = some (.hyp essential hypFormula hypEmbedded))
    (hassert :
      db.find? label = some (.assert assertFormula frame assertEmbedded)) :
    False := by
  rw [hhyp] at hassert
  exact Metamath.Verify.Object.noConfusion (Option.some.inj hassert)

/-! ## Reverse lookup fidelity -/

private theorem exists_right_of_forall₂_left_member
    {leftType rightType : Type} {relation : leftType → rightType → Prop}
    {left : List leftType} {right : List rightType}
    (hordered : List.Forall₂ relation left right)
    {source : leftType} (hmember : source ∈ left) :
    ∃ image, image ∈ right ∧ relation source image := by
  induction hordered with
  | nil => simp at hmember
  | cons hhead _htail ih =>
      simp only [List.mem_cons] at hmember
      rcases hmember with rfl | htailMember
      · exact ⟨_, by simp, hhead⟩
      · obtain ⟨image, himageMember, himage⟩ := ih htailMember
        exact ⟨image, by simp [himageMember], himage⟩

/-- Reverse fidelity for active hypotheses: a live in-scope hypothesis object
is the exact image of an authored source hypothesis. -/
theorem projectedActiveHypothesis_reverse_fidelity
    (db : RuntimeDB) (source : SourcePrefix)
    (hproject : projectPrefix? db = some source.toProjection)
    (label embedded : String) (essential : Bool)
    (runtimeFormula : RuntimeFormula)
    (hfind : db.find? label = some (.hyp essential runtimeFormula embedded))
    (hscope : label ∈ db.frame.hyps.toList) :
    ∃ hypothesis ∈ source.activeHypotheses,
      hypothesis.label = label ∧
        hypothesis.formula.toRuntime = runtimeFormula := by
  have hordered :=
    projectedActiveHypotheses_ordered_fidelity db source.toProjection hproject
  obtain ⟨hypothesis, hmember, hview⟩ :=
    exists_right_of_forall₂_left_member hordered hscope
  obtain ⟨viewFormula, hviewFind, hdecode, hlabel⟩ :=
    projectHypothesis?_eq_some_fidelity db label hypothesis hview
  have hobject :
      Metamath.Verify.Object.hyp (hypothesisEssentialBit hypothesis)
          viewFormula label =
        Metamath.Verify.Object.hyp essential runtimeFormula embedded :=
    Option.some.inj (hviewFind.symm.trans hfind)
  obtain ⟨_hbit, hformula, _hembedded⟩ :=
    Metamath.Verify.Object.hyp.inj hobject
  have hruntime : viewFormula = hypothesis.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff viewFormula
      hypothesis.formula).mp hdecode
  exact ⟨hypothesis, hmember, hlabel, by rw [← hruntime, hformula]⟩

/-- Every live assertion entry is projected, so the projected list contains a
view produced from that exact entry. -/
theorem projectAssertionsFromEntries?_mem
    (db : RuntimeDB) (entries : List (String × Metamath.Verify.Object))
    (assertions : List AssertionView)
    (hproject : projectAssertionsFromEntries? db entries = some assertions)
    (label embedded : String) (runtimeFormula : RuntimeFormula)
    (frame : RuntimeFrame)
    (hmember : (label, .assert runtimeFormula frame embedded) ∈ entries) :
    ∃ assertion ∈ assertions,
      projectAssertion? db label runtimeFormula frame embedded =
        some assertion := by
  induction entries generalizing assertions with
  | nil => simp at hmember
  | cons entry entries ih =>
      rcases entry with ⟨entryLabel, entryObject⟩
      cases entryObject with
      | const name =>
          simp only [projectAssertionsFromEntries?] at hproject
          simp only [List.mem_cons, Prod.mk.injEq] at hmember
          rcases hmember with ⟨_, himpossible⟩ | htailMember
          · exact absurd himpossible (by simp)
          · exact ih assertions hproject htailMember
      | var name =>
          simp only [projectAssertionsFromEntries?] at hproject
          simp only [List.mem_cons, Prod.mk.injEq] at hmember
          rcases hmember with ⟨_, himpossible⟩ | htailMember
          · exact absurd himpossible (by simp)
          · exact ih assertions hproject htailMember
      | hyp entryEssential entryFormula entryEmbedded =>
          simp only [projectAssertionsFromEntries?] at hproject
          simp only [List.mem_cons, Prod.mk.injEq] at hmember
          rcases hmember with ⟨_, himpossible⟩ | htailMember
          · exact absurd himpossible (by simp)
          · exact ih assertions hproject htailMember
      | assert entryFormula entryFrame entryEmbedded =>
          cases hhead :
              projectAssertion? db entryLabel entryFormula entryFrame
                entryEmbedded with
          | none => simp [projectAssertionsFromEntries?, hhead] at hproject
          | some headAssertion =>
              cases htail : projectAssertionsFromEntries? db entries with
              | none =>
                  simp [projectAssertionsFromEntries?, hhead, htail] at hproject
              | some tailAssertions =>
                  simp [projectAssertionsFromEntries?, hhead, htail] at hproject
                  subst assertions
                  simp only [List.mem_cons, Prod.mk.injEq,
                    Metamath.Verify.Object.assert.injEq] at hmember
                  rcases hmember with ⟨hlabel, hformula, hframe, hembedded⟩ |
                    htailMember
                  · subst hlabel
                    subst hformula
                    subst hframe
                    subst hembedded
                    exact ⟨headAssertion, by simp, hhead⟩
                  · obtain ⟨assertion, hassertionMember, hassertionProject⟩ :=
                      ih tailAssertions htail htailMember
                    exact ⟨assertion, by simp [hassertionMember],
                      hassertionProject⟩

/-- Reverse fidelity for assertions: a live assertion object is the exact
image of an authored source assertion. -/
theorem projectedAssertion_reverse_fidelity
    (db : RuntimeDB) (source : SourcePrefix)
    (hproject : projectPrefix? db = some source.toProjection)
    (label embedded : String) (runtimeFormula : RuntimeFormula)
    (frame : RuntimeFrame)
    (hfind : db.find? label = some (.assert runtimeFormula frame embedded)) :
    ∃ assertion ∈ source.assertions,
      assertion.label = label ∧
        assertion.formula.toRuntime = runtimeFormula ∧
        assertion.frame.toRuntime = frame := by
  obtain ⟨_hconstants, _hvariables, _hcaller, _hactive, hassertions⟩ :=
    projectPrefix?_eq_some_fields db source.toProjection hproject
  have hentry :
      (label, Metamath.Verify.Object.assert runtimeFormula frame embedded) ∈
        objectEntries db :=
    (objectEntries_exact db label
      (.assert runtimeFormula frame embedded)).mpr hfind
  obtain ⟨view, hviewMember, hviewProject⟩ :=
    projectAssertionsFromEntries?_mem db (objectEntries db)
      source.toProjection.assertions hassertions label embedded runtimeFormula
      frame hentry
  obtain ⟨_hembedded, hdecode, _hhypotheses, hlabel, hframe⟩ :=
    projectAssertion?_eq_some_fidelity db label embedded runtimeFormula frame
      view hviewProject
  have hmapped :
      view ∈ source.assertions.map SourceAssertion.toProjectionView :=
    hviewMember
  obtain ⟨assertion, hmember, hview⟩ := List.mem_map.mp hmapped
  subst hview
  have hruntime : runtimeFormula = assertion.formula.toRuntime :=
    (ConstantHeadedFormula.ofRuntime?_eq_some_iff runtimeFormula
      assertion.toProjectionView.formula).mp hdecode
  refine ⟨assertion, hmember, ?_, hruntime.symm, ?_⟩
  · simpa [SourceAssertion.toProjectionView] using hlabel
  · simpa [SourceAssertion.toProjectionView] using hframe

/-! ## Header reflection -/

/-- Reflection of one shipped `preload` acceptance into the exact source
header transition.  The successor machine is forced by the `HeaderStep`
constructor, and its agreement is the forward preservation image. -/
noncomputable def headerStep_runtimeReflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    {item : HeaderItem}
    {before : MachineState source target}
    (db : RuntimeDB)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (mandatoryMember : ∀ hypothesis : HypothesisView,
      item = .mandatory hypothesis → hypothesis ∈ source.activeHypotheses)
    (accepted :
      db.preload runtimeBefore (headerRuntimeLabel item) = .ok runtimeAfter) :
    Σ middle : MachineState source target,
      HeaderStep item before middle ×'
      MachineAgrees db source target middle runtimeAfter := by
  cases item with
  | mandatory hypothesis =>
      have member : hypothesis ∈ source.activeHypotheses :=
        mandatoryMember hypothesis rfl
      obtain ⟨runtimeCanonical, canonicalStep, nextAgreement,
          _incomplete⟩ :=
        headerStep_runtimePreserved db hproject runtimeBefore
          (HeaderStep.mandatory before hypothesis member) agreement
      have hruntime : runtimeAfter = runtimeCanonical :=
        Except.ok.inj (accepted.symm.trans canonicalStep)
      subst hruntime
      exact ⟨_, .mandatory before hypothesis member, nextAgreement⟩
  | explicit label =>
      cases hfind : db.find? label with
      | none =>
          exact absurd
            (accepted.symm.trans
              (preload_none_error db runtimeBefore label hfind))
            (by simp)
      | some object =>
          cases object with
          | const name =>
              exact absurd
                (accepted.symm.trans
                  (preload_const_error db runtimeBefore label name hfind))
                (by simp)
          | var name =>
              exact absurd
                (accepted.symm.trans
                  (preload_var_error db runtimeBefore label name hfind))
                (by simp)
          | hyp essential runtimeFormula embedded =>
              by_cases hscope : label ∈ db.frame.hyps.toList
              · have hexists :=
                  projectedActiveHypothesis_reverse_fidelity db source hproject
                    label embedded essential runtimeFormula hfind hscope
                obtain ⟨member, label_eq, _hformula⟩ := hexists.choose_spec
                obtain ⟨runtimeCanonical, canonicalStep, nextAgreement,
                    _incomplete⟩ :=
                  headerStep_runtimePreserved db hproject runtimeBefore
                    (HeaderStep.explicitHypothesis before label hexists.choose
                      member label_eq) agreement
                have hruntime : runtimeAfter = runtimeCanonical :=
                  Except.ok.inj (accepted.symm.trans canonicalStep)
                subst hruntime
                exact ⟨_,
                  .explicitHypothesis before label hexists.choose member
                    label_eq,
                  nextAgreement⟩
              · exact absurd
                  (accepted.symm.trans
                    (preload_hyp_error db runtimeBefore label embedded
                      essential runtimeFormula hfind hscope))
                  (by simp)
          | assert runtimeFormula frame embedded =>
              have hexists :=
                projectedAssertion_reverse_fidelity db source hproject label
                  embedded runtimeFormula frame hfind
              obtain ⟨member, label_eq, _hformula, _hframe⟩ :=
                hexists.choose_spec
              obtain ⟨runtimeCanonical, canonicalStep, nextAgreement,
                  _incomplete⟩ :=
                headerStep_runtimePreserved db hproject runtimeBefore
                  (HeaderStep.explicitAssertion before label hexists.choose
                    member label_eq) agreement
              have hruntime : runtimeAfter = runtimeCanonical :=
                Except.ok.inj (accepted.symm.trans canonicalStep)
              subst hruntime
              exact ⟨_,
                .explicitAssertion before label hexists.choose member label_eq,
                nextAgreement⟩

/-! ## The reflected header build -/

private theorem optionExceptOk_inj {ε α : Type _} {a b : α}
    (h : (Except.ok a : Except ε α) = .ok b) : a = b :=
  Except.ok.inj h

/-- **Header build reflection**: shipped ordered `preload` acceptance
over an item list reconstructs the ordered source header build, with
the shipped successor identified stepwise by determinism. -/
noncomputable def headerBuild_runtimeReflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (hproject : projectPrefix? db = some source.toProjection) :
    ∀ {items : List HeaderItem} {before : MachineState source target}
      {runtimeBefore runtimeAfter : RuntimeProofState},
      MachineAgrees db source target before runtimeBefore →
      ((items.map headerRuntimeLabel).foldlM
          (fun state label => db.preload state label) runtimeBefore =
        .ok runtimeAfter) →
      (∀ hypothesis : HypothesisView,
        HeaderItem.mandatory hypothesis ∈ items →
          hypothesis ∈ source.activeHypotheses) →
      Σ after : MachineState source target,
        HeaderBuild items before after ×'
        MachineAgrees db source target after runtimeAfter
  | [], before, runtimeBefore, runtimeAfter, agreement, hfold, _ => by
      simp only [List.map_nil, List.foldlM_nil] at hfold
      have hid : runtimeBefore = runtimeAfter := optionExceptOk_inj hfold
      subst hid
      exact ⟨before, HeaderBuild.nil before, agreement⟩
  | item :: rest, before, runtimeBefore, runtimeAfter, agreement,
      hfold, hmand => by
      simp only [List.map_cons, List.foldlM_cons] at hfold
      cases hstep : db.preload runtimeBefore
          (headerRuntimeLabel item) with
      | error e =>
          rw [hstep] at hfold
          exact nomatch hfold
      | ok runtimeMiddle =>
          rw [hstep] at hfold
          obtain ⟨middle, step, agreeMiddle⟩ :=
            headerStep_runtimeReflected db hproject runtimeBefore
              runtimeMiddle agreement
              (fun hypothesis hitem =>
                hmand hypothesis (hitem ▸ List.Mem.head _))
              hstep
          obtain ⟨after, build, agreeAfter⟩ :=
            headerBuild_runtimeReflected db hproject agreeMiddle hfold
              (fun hypothesis hmem =>
                hmand hypothesis (List.Mem.tail _ hmem))
          exact ⟨after, HeaderBuild.cons step build, agreeAfter⟩

/-! ## Shipped acceptance reconstructs the theorem step -/

/-- Runtime formula images determine the source formula. -/
theorem ConstantHeadedFormula.toRuntime_injective
    {a b : ConstantHeadedFormula}
    (h : a.toRuntime = b.toRuntime) : a = b := by
  have ha := (ConstantHeadedFormula.ofRuntime?_eq_some_iff
    a.toRuntime a).mpr rfl
  have hb := (ConstantHeadedFormula.ofRuntime?_eq_some_iff
    a.toRuntime b).mpr h
  exact Option.some.inj (ha.symm.trans hb)

/-- Witness extraction from a singleton stack agreement. -/
noncomputable def stackSingletonWitness
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)} {stack : List Nat}
    {f : RuntimeFormula}
    (h : StackEntriesAgree nodes stack [f]) :
    Σ' (nodeId : Nat) (node : ProofNode source target),
      stack = [nodeId] ∧ nodes[nodeId]? = some node ∧
        node.formula.toRuntime = f :=
  match h with
  | .cons node lookup .nil => ⟨_, node, rfl, lookup, rfl⟩

/-- **Compressed execution reflection**: shipped mm-lean4 acceptance —
ordered header preloads from the empty proof context, compressed action
execution, and a singleton result stack holding the target formula —
together with the source-lane facts the fold supplies (validity,
presentation, insertion) and decode success, reconstructs the complete
source compressed theorem occurrence.  `actionsVerified` excludes
`unknown` (`?`) actions by design: incomplete-proof admission is a
distinct source judgment and cannot manufacture a proof tree. -/
noncomputable def compressedTheoremStep_of_mmLean4
    {before next : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (target : ValidatedPresentation)
    (hvalid : sourceStateValid before = true)
    (hpres : presentationOfSourcePrefix? before.toSourcePrefix =
      some target.1)
    (hins : insertAssertion? before label formula = some next)
    {actions : List CompressedAction}
    (hdecode : decodeProgram bodyWords = some actions)
    (hverified : actionsVerified actions)
    (db : RuntimeDB)
    (hproject : projectPrefix? db =
      some before.toSourcePrefix.toProjection)
    (runtimeBase : RuntimeProofState)
    {runtimeInitial runtimeFinal : RuntimeProofState}
    (hheader :
      (((headerItems before formula explicitHeaderLabels).map
          headerRuntimeLabel).foldlM
        (fun state l => db.preload state l)
        { runtimeBase with heap := #[], stack := #[] }) =
        .ok runtimeInitial)
    (hactions :
      ParserState.applyCompressedActions db runtimeInitial
        (actions.map toMMLean4Action) = .ok runtimeFinal)
    (hstack : runtimeFinal.stack = #[formula.toRuntime]) :
    CompressedTheoremStep before next label formula
      explicitHeaderLabels bodyWords := by
  have hmand : ∀ hypothesis : HypothesisView,
      HeaderItem.mandatory hypothesis ∈
        headerItems before formula explicitHeaderLabels →
      hypothesis ∈ before.toSourcePrefix.activeHypotheses := by
    intro hypothesis hmem
    unfold headerItems at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨h₀, hh₀, heq⟩ := List.mem_map.mp hleft
      cases HeaderItem.mandatory.inj heq
      exact List.mem_of_mem_filter hh₀
    · obtain ⟨l₀, hl₀, heq⟩ := List.mem_map.mp hright
      exact nomatch heq
  obtain ⟨initialState, headerBuild, agreementInitial⟩ :=
    headerBuild_runtimeReflected db hproject
      (emptyMachineAgrees db before.toSourcePrefix target runtimeBase)
      hheader hmand
  obtain ⟨finalState, execution, agreementFinal⟩ :=
    execute_mmLean4Reflected actions db hpres hproject runtimeInitial
      runtimeFinal agreementInitial hverified hactions
  -- singleton-stack extraction
  have hformulas : agreementFinal.stackFormulas =
      [formula.toRuntime] := by
    have hs := agreementFinal.stack_eq
    rw [hstack] at hs
    have := congrArg Array.toList hs
    simpa using this.symm
  obtain ⟨rootId, node, hstackEq, lookup, hform⟩ :=
    stackSingletonWitness (hformulas ▸ agreementFinal.stackAgreement)
  exact
    { sourceValid := hvalid
      target := target
      presentation_eq := hpres
      actions := actions
      decoded := hdecode
      initialState := initialState
      finalState := finalState
      header := headerBuild
      execution := execution
      rootId := rootId
      root := node
      finalStack := hstackEq
      rootLookup := lookup
      rootFormula := ConstantHeadedFormula.toRuntime_injective hform
      inserted := hins }

end Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection
