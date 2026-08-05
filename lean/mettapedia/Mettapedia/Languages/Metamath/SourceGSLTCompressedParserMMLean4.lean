import Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
import Mettapedia.Languages.Metamath.InferenceNormalByteLedger
import Metamath.PrefixTraceCompressed

/-!
# Parser-owned compressed Metamath lifecycle

This file moves the occurrence-preserving compressed execution bisimulation
onto the actual `mm-lean4` parser path.  The first seam is mandatory-header
construction: the parser uses the bulk `preloadMandatoryHyps` loop, whereas
the source checker GSLT records proof-relevant header transitions.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Metamath.Verify

/-! ## The complete object namespace

The proof-facing prefix projection intentionally forgets hypotheses that have
left the active frame.  Their labels nevertheless remain occupied in both the
source state and the implementation database.  The following relation records
that persistent namespace separately from the active proof projection. -/

/-- Exact agreement about which global Metamath object names are occupied.
Object payload agreement remains in `projectPrefix?`; this relation retains
the otherwise invisible names of hypotheses retired by scope exit. -/
structure RuntimeObjectNamespaceAgrees
    (db : RuntimeDB) (sourceState : SourceState) : Prop where
  errorFree : db.error? = none
  occupied_iff : ∀ label,
    db.find? label ≠ none ↔ label ∈ sourceState.objectNames

/-- Positive boundary: the empty source and implementation namespaces agree. -/
theorem default_initial_namespaceAgrees :
    RuntimeObjectNamespaceAgrees (default : RuntimeDB) initialState := by
  constructor
  · rfl
  · intro label
    simp [Metamath.Verify.DB.find?, initialState, SourceState.objectNames]

private def retiredLabelRuntimeDB : RuntimeDB :=
  { (default : RuntimeDB) with
    objects :=
      (default : RuntimeDB).objects.insert "retired"
        (.hyp true #[.const "T"] "retired") }

/-- Negative boundary: an implementation-only retired label is invisible to
the empty proof projection but is rejected by global namespace agreement. -/
theorem retiredLabelRuntimeDB_not_initial_namespaceAgrees :
    ¬ RuntimeObjectNamespaceAgrees retiredLabelRuntimeDB initialState := by
  intro agreement
  have occupied : retiredLabelRuntimeDB.find? "retired" ≠ none := by
    simp [retiredLabelRuntimeDB, Metamath.Verify.DB.find?]
  have member := (agreement.occupied_iff "retired").mp occupied
  simp [initialState, SourceState.objectNames] at member

/-- A source-fresh name is absent from an exactly agreeing runtime namespace. -/
theorem RuntimeObjectNamespaceAgrees.find?_eq_none
    {db : RuntimeDB} {sourceState : SourceState}
    (agreement : RuntimeObjectNamespaceAgrees db sourceState)
    {label : String} (fresh : label ∉ sourceState.objectNames) :
    db.find? label = none := by
  by_contra occupied
  exact fresh ((agreement.occupied_iff label).mp occupied)

/-- A successful source theorem insertion makes its label fresh for the
implementation database as well. -/
theorem CompressedTheoremStep.runtimeLabelFresh
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    {db : RuntimeDB}
    (agreement : RuntimeObjectNamespaceAgrees db before) :
    db.find? label = none := by
  exact agreement.find?_eq_none
    (insertAssertion?_label_fresh step.inserted)

/-- The implementation's real assertion insertion succeeds from the same
source freshness fact.  No separately supplied runtime freshness hypothesis is
needed. -/
theorem CompressedTheoremStep.runtimeInsert_errorFree
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    {db : RuntimeDB}
    (agreement : RuntimeObjectNamespaceAgrees db before)
    (pos : Pos) :
    (db.insert pos label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime)).error? = none := by
  have absent : db.find? label = none :=
    CompressedTheoremStep.runtimeLabelFresh step agreement
  simp [Metamath.Verify.DB.insert, Metamath.Verify.DB.error,
    agreement.errorFree, absent]

/-- On the source-fresh branch, implementation insertion is exactly one
hash-map extension; no error or duplicate branch is taken. -/
theorem CompressedTheoremStep.runtimeInsert_eq
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    {db : RuntimeDB}
    (agreement : RuntimeObjectNamespaceAgrees db before)
    (pos : Pos) :
    db.insert pos label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime) =
      { db with objects :=
          (db.objects.insert label
            (.assert formula.toRuntime
              (mandatoryFrame before formula).toRuntime label)) } := by
  have absent : db.find? label = none :=
    CompressedTheoremStep.runtimeLabelFresh step agreement
  simp [Metamath.Verify.DB.insert, Metamath.Verify.DB.error,
    agreement.errorFree, absent]

/-- The real implementation insertion preserves the complete source/runtime
namespace relation, including names of inactive hypotheses. -/
theorem CompressedTheoremStep.runtimeNamespaceAfterInsert
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    {db : RuntimeDB}
    (agreement : RuntimeObjectNamespaceAgrees db before)
    (pos : Pos) :
    RuntimeObjectNamespaceAgrees
      (db.insert pos label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime))
      after := by
  let insertedDB :=
    db.insert pos label
      (.assert formula.toRuntime
        (mandatoryFrame before formula).toRuntime)
  have insertEq : insertedDB =
      { db with objects :=
          (db.objects.insert label
            (.assert formula.toRuntime
              (mandatoryFrame before formula).toRuntime label)) } := by
    exact CompressedTheoremStep.runtimeInsert_eq step agreement pos
  have namesEq : after.objectNames = before.objectNames ++ [label] :=
    insertAssertion?_objectNames step.inserted
  refine
    { errorFree := CompressedTheoremStep.runtimeInsert_errorFree
        step agreement pos
      occupied_iff := ?_ }
  intro candidate
  change insertedDB.find? candidate ≠ none ↔
    candidate ∈ after.objectNames
  rw [insertEq, namesEq]
  by_cases same : candidate = label
  · subst candidate
    simp [Metamath.Verify.DB.find?]
  · change
      (db.objects.insert label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime label))[candidate]? ≠
          none ↔
        candidate ∈ before.objectNames ++ [label]
    have lookupUnchanged :
        (db.objects.insert label
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime label))[candidate]? =
          db.objects[candidate]? := by
      simp [same]
    rw [lookupUnchanged]
    simpa [Metamath.Verify.DB.find?, same] using
      agreement.occupied_iff candidate

/-- One iteration of the implementation's mandatory-hypothesis preload loop,
exposed as an ordinary transition for compositional reasoning. -/
def mandatoryPreloadStep
    (db : RuntimeDB) (state : RuntimeProofState) (label : String) :
    Except ProofCheckFail RuntimeProofState :=
  match db.find? label with
  | some (.hyp _ formula _) =>
      .ok (state.pushHeap (.fmla formula))
  | _ =>
      .error (.proofCheck (.mandatoryHypothesisNotFoundInDatabase label))

/-- The bulk imperative loop is exactly the fold of its exposed transition.
This theorem is implementation-structural and contains no source-language
assumption. -/
theorem preloadMandatoryHyps_eq_mandatoryFold
    (db : RuntimeDB) (state : RuntimeProofState) :
    db.preloadMandatoryHyps state =
      state.frame.hyps.foldlM (mandatoryPreloadStep db) state := by
  let body : String → RuntimeProofState →
      Except ProofCheckFail (ForInStep RuntimeProofState) :=
    fun label current =>
      match db.find? label with
      | some (.hyp _ formula _) =>
          .ok (.yield (current.pushHeap (.fmla formula)))
      | _ =>
          .error (.proofCheck
            (.mandatoryHypothesisNotFoundInDatabase label))
  have listLoop :
      ∀ (labels : List String) (current : RuntimeProofState),
        forIn labels current body =
          labels.foldlM (mandatoryPreloadStep db) current := by
    intro labels
    induction labels with
    | nil =>
        intro current
        rfl
    | cons label labels ih =>
        intro current
        cases hfind : db.find? label with
        | none =>
            simp [List.forIn_cons, List.foldlM, body,
              mandatoryPreloadStep, hfind, Bind.bind, Except.bind]
        | some object =>
            cases object <;>
              simp [List.forIn_cons, List.foldlM, body,
                mandatoryPreloadStep, hfind, Bind.bind, Except.bind, ih]
  calc
    db.preloadMandatoryHyps state =
        forIn state.frame.hyps state body := by
      unfold Metamath.Verify.DB.preloadMandatoryHyps
      simp only [bind_pure]
      rfl
    _ = forIn state.frame.hyps.toList state body := by
      exact (Array.forIn_toList
        (xs := state.frame.hyps) (b := state) (f := body)).symm
    _ = state.frame.hyps.toList.foldlM
        (mandatoryPreloadStep db) state :=
      listLoop state.frame.hyps.toList state
    _ = state.frame.hyps.foldlM
        (mandatoryPreloadStep db) state :=
      Array.foldlM_toList

/-! ## Source-owned mandatory header -/

/-- For an authored mandatory hypothesis, the implementation's special bulk
preload step and its ordinary scoped preload transition are the same state
transition. -/
theorem mandatoryPreloadStep_eq_preload
    (db : RuntimeDB) (sourceState : SourceState)
    (formula : ConstantHeadedFormula) (runtime : RuntimeProofState)
    (hypothesis : HypothesisView)
    (hproject :
      projectPrefix? db =
        some sourceState.toSourcePrefix.toProjection)
    (hmember : hypothesis ∈ mandatoryHypotheses sourceState formula) :
    mandatoryPreloadStep db runtime hypothesis.label =
      db.preload runtime hypothesis.label := by
  have hactive : hypothesis ∈ sourceState.activeHypotheses :=
    (List.mem_filter.mp hmember).1
  obtain ⟨hscope, hfind⟩ :=
    projectedActiveHypothesis_database_fidelity
      db sourceState.toSourcePrefix.toProjection hypothesis hproject hactive
  simp [mandatoryPreloadStep, Metamath.Verify.DB.preload, hfind, hscope,
    Pure.pure, Except.pure]

/-- On the source-derived mandatory header, the implementation's bulk step
fold and its ordinary checked-preload fold coincide exactly. -/
theorem mandatoryPreloadFold_eq_preloadFold
    (db : RuntimeDB) (sourceState : SourceState)
    (formula : ConstantHeadedFormula) (runtime : RuntimeProofState)
    (hproject :
      projectPrefix? db =
        some sourceState.toSourcePrefix.toProjection) :
    ((mandatoryHypotheses sourceState formula).map HypothesisView.label).foldlM
        (mandatoryPreloadStep db) runtime =
      ((mandatoryHypotheses sourceState formula).map
        HypothesisView.label).foldlM (db.preload) runtime := by
  let hypotheses := mandatoryHypotheses sourceState formula
  have go : ∀ (remaining : List HypothesisView),
      (∀ hypothesis ∈ remaining,
        hypothesis ∈ mandatoryHypotheses sourceState formula) →
      ∀ runtime,
        (remaining.map HypothesisView.label).foldlM
            (mandatoryPreloadStep db) runtime =
          (remaining.map HypothesisView.label).foldlM
            (db.preload) runtime := by
    intro remaining
    induction remaining with
    | nil =>
        intro _ runtime
        rfl
    | cons hypothesis remaining ih =>
        intro hsubset runtime
        have hhead :
            hypothesis ∈ mandatoryHypotheses sourceState formula :=
          hsubset hypothesis (.head remaining)
        have htail : ∀ other ∈ remaining,
            other ∈ mandatoryHypotheses sourceState formula := by
          intro other hother
          exact hsubset other (.tail hypothesis hother)
        simp only [List.map_cons, List.foldlM_cons]
        rw [mandatoryPreloadStep_eq_preload db sourceState formula runtime
          hypothesis hproject hhead]
        cases hstep : db.preload runtime hypothesis.label with
        | error error => rfl
        | ok middle =>
            simp only [bind, Except.bind]
            exact ih htail middle
  exact go hypotheses (by
    intro hypothesis hmember
    exact hmember) runtime

/-! ## The actual parser start state -/

/-- Canonical implementation state installed for the source theorem being
checked.  Its frame is derived from the authored source state, not supplied by
an independent runtime ledger. -/
def sourceProofStart
    (db : RuntimeDB) (pos : Pos) (label : String)
    (sourceState : SourceState) (formula : ConstantHeadedFormula) :
    RuntimeProofState :=
  db.mkProofState pos label formula.toRuntime
    (mandatoryFrame sourceState formula).toRuntime

@[simp] theorem sourceProofStart_heap
    (db : RuntimeDB) (pos : Pos) (label : String)
    (sourceState : SourceState) (formula : ConstantHeadedFormula) :
    (sourceProofStart db pos label sourceState formula).heap = #[] := by
  rfl

@[simp] theorem sourceProofStart_stack
    (db : RuntimeDB) (pos : Pos) (label : String)
    (sourceState : SourceState) (formula : ConstantHeadedFormula) :
    (sourceProofStart db pos label sourceState formula).stack = #[] := by
  rfl

@[simp] theorem sourceProofStart_mode
    (db : RuntimeDB) (pos : Pos) (label : String)
    (sourceState : SourceState) (formula : ConstantHeadedFormula) :
    (sourceProofStart db pos label sourceState formula).ptp = .start := by
  rfl

@[simp] theorem sourceProofStart_mandatoryLabels
    (db : RuntimeDB) (pos : Pos) (label : String)
    (sourceState : SourceState) (formula : ConstantHeadedFormula) :
    (sourceProofStart db pos label sourceState formula).frame.hyps.toList =
      (mandatoryHypotheses sourceState formula).map
        HypothesisView.label := by
  simp [sourceProofStart, Metamath.Verify.DB.mkProofState,
    mandatoryFrame, SourceFrame.toRuntime]

/-- Split an ordered source header derivation at a syntactic append boundary.
The intermediate machine is constructed from the derivation rather than
guessed from the two item lists. -/
noncomputable def HeaderBuild.splitAppend
    {source : SourcePrefix} {target : ValidatedPresentation}
    {left right : List HeaderItem}
    {before after : MachineState source target}
    (build : HeaderBuild (left ++ right) before after) :
    Σ middle,
      HeaderBuild left before middle ×'
        HeaderBuild right middle after := by
  induction left generalizing before after with
  | nil =>
      exact ⟨before, .nil before, by simpa using build⟩
  | cons item left ih =>
      cases build with
      | cons head tail =>
          obtain ⟨middle, leftBuild, rightBuild⟩ := ih tail
          exact ⟨middle, .cons head leftBuild, rightBuild⟩

/-- The actual bulk mandatory-preload function executes the mandatory source
header derivation.  This closes the gap between the special parser loop and
the ordinary `DB.preload` transition used by the occurrence semantics. -/
noncomputable def mandatoryHeader_runtimePreserved
    {sourceState : SourceState} {target : ValidatedPresentation}
    {after : MachineState sourceState.toSourcePrefix target}
    (db : RuntimeDB)
    (hproject :
      projectPrefix? db =
        some sourceState.toSourcePrefix.toProjection)
    (pos : Pos) (label : String) (formula : ConstantHeadedFormula)
    (build :
      HeaderBuild
        ((mandatoryHypotheses sourceState formula).map
          HeaderItem.mandatory)
        (emptyMachine sourceState.toSourcePrefix target) after) :
    Σ runtimeAfter,
      (db.preloadMandatoryHyps
          (sourceProofStart db pos label sourceState formula) =
        .ok runtimeAfter) ×'
      MachineAgrees db sourceState.toSourcePrefix target after runtimeAfter := by
  let runtimeStart := sourceProofStart db pos label sourceState formula
  have startAgreement :
      MachineAgrees db sourceState.toSourcePrefix target
        (emptyMachine sourceState.toSourcePrefix target) runtimeStart := by
    simpa [runtimeStart, sourceProofStart, Metamath.Verify.DB.mkProofState] using
      (emptyMachineAgrees db sourceState.toSourcePrefix target runtimeStart)
  obtain ⟨runtimeAfter, hpreload, agreement⟩ :=
    headerBuild_runtimePreserved db hproject runtimeStart build startAgreement
  refine ⟨runtimeAfter, ?_, agreement⟩
  let labels :=
    (mandatoryHypotheses sourceState formula).map HypothesisView.label
  have itemLabels :
      (((mandatoryHypotheses sourceState formula).map
          HeaderItem.mandatory).map headerRuntimeLabel) = labels := by
    simp [labels, headerRuntimeLabel]
  calc
    db.preloadMandatoryHyps runtimeStart =
        runtimeStart.frame.hyps.foldlM
          (mandatoryPreloadStep db) runtimeStart :=
      preloadMandatoryHyps_eq_mandatoryFold db runtimeStart
    _ = runtimeStart.frame.hyps.toList.foldlM
          (mandatoryPreloadStep db) runtimeStart :=
      (Array.foldlM_toList).symm
    _ = labels.foldlM (mandatoryPreloadStep db) runtimeStart := by
      simp [labels, runtimeStart]
    _ = labels.foldlM (db.preload) runtimeStart := by
      exact mandatoryPreloadFold_eq_preloadFold db sourceState formula
        runtimeStart hproject
    _ = .ok runtimeAfter := by
      rw [itemLabels] at hpreload
      exact hpreload

/-! ## Complete parser-core execution -/

@[simp] theorem map_headerRuntimeLabel_explicit (labels : List String) :
    ((labels.map HeaderItem.explicit).map headerRuntimeLabel) = labels := by
  induction labels with
  | nil => rfl
  | cons head tail ih =>
      change head :: ((tail.map HeaderItem.explicit).map
        headerRuntimeLabel) = head :: tail
      rw [ih]

/-- A successful explicit-header preload fold preserves the theorem identity,
claim, and mandatory frame. -/
theorem preloadFold_preserves_identity
    (db : RuntimeDB) (labels : List String)
    (before after : RuntimeProofState)
    (execution : labels.foldlM (db.preload) before = .ok after) :
    after.label = before.label ∧
      after.fmla = before.fmla ∧
      after.frame = before.frame := by
  induction labels generalizing before with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure] at execution
      cases execution
      exact ⟨rfl, rfl, rfl⟩
  | cons label labels ih =>
      simp only [List.foldlM_cons, bind, Except.bind] at execution
      cases first : db.preload before label with
      | error failure => simp [first] at execution
      | ok middle =>
          have rest : labels.foldlM (db.preload) middle = .ok after := by
            simpa [first] using execution
          have tail := ih middle rest
          have labelStep : middle.label = before.label :=
            Metamath.PrefixTraceCompressed.preload_preserves_label
              db before middle label first
          have coreStep :
              middle.fmla = before.fmla ∧
                middle.frame = before.frame :=
            Metamath.ParserOps.preload_ok_preserves_core
              db before middle label first
          exact
            ⟨tail.1.trans labelStep,
              tail.2.1.trans coreStep.1,
              tail.2.2.trans coreStep.2⟩

/-- Finishing a mode-complete singleton proof state executes precisely the
implementation's assertion insertion branch. -/
theorem finishProof_compressed_success
    (parser : ParserState) (proof : RuntimeProofState)
    (mode : proof.ptp = .compressed 0)
    (singleton : proof.stack = #[proof.fmla])
    (inserted :
      (parser.db.insert proof.pos proof.label
        (.assert proof.fmla proof.frame)).error? = none) :
    (parser.finishProof proof).db =
        parser.db.insert proof.pos proof.label
          (.assert proof.fmla proof.frame) ∧
      (parser.finishProof proof).db.error? = none := by
  cases proof with
  | mk pos label formula frame heap stack ptp =>
      simp only at mode singleton inserted ⊢
      subst ptp
      subst stack
      simp [ParserState.finishProof, ParserState.withAt,
        ParserState.withDB, inserted]

/-! ## Concrete explicit-header tokens -/

/-- One lexical token denotes one explicit compressed-header label and cannot
be confused with the header-closing delimiter. -/
structure PreloadTokenRepresents
    (token : ByteSlice) (label : String) : Prop where
  notClose : ¬ token.eqArray ")".toAscii
  decoded : toLabel token = (true, label)

/-- Ordered pointwise representation of the source explicit-header labels. -/
inductive PreloadTokensRepresent :
    List ByteSlice → List String → Prop where
  | nil : PreloadTokensRepresent [] []
  | cons {token : ByteSlice} {label : String}
      {tokens : List ByteSlice} {labels : List String}
      (head : PreloadTokenRepresents token label)
      (tail : PreloadTokensRepresent tokens labels) :
      PreloadTokensRepresent (token :: tokens) (label :: labels)

/-- `DB.preload` is independent of the proof-token phase. -/
theorem preload_withPtp
    (db : RuntimeDB) (before after : RuntimeProofState)
    (label : String) (phase : ProofTokenParser)
    (execution : db.preload before label = .ok after) :
    db.preload { before with ptp := phase } label =
      .ok { after with ptp := phase } := by
  unfold Metamath.Verify.DB.preload at execution ⊢
  cases lookup : db.find? label with
  | none => simp [lookup] at execution
  | some object =>
      simp only [lookup] at execution ⊢
      cases object with
      | const _ => simp at execution
      | var _ => simp at execution
      | hyp _ formula _ =>
          by_cases active : label ∈ db.frame.hyps.toList
          · simp [active, pure, Except.pure] at execution ⊢
            cases execution
            rfl
          · simp [active] at execution
      | assert formula frame _ =>
          simp [pure, Except.pure] at execution ⊢
          cases execution
          rfl

/-- Execute the exact inner parser transition over explicit-header tokens. -/
def runPreloadTokenGo
    (parser : ParserState) (tokens : List ByteSlice)
    (initial : RuntimeProofState) : Except ProofCheckFail RuntimeProofState :=
  tokens.foldlM
    (fun current token => ParserState.feedProof.go parser token current)
    initial

/-! ## The production parser wrapper -/

/-- A successful inner proof transition lifts through the implementation's
`withAt` wrapper without changing the database.  The explicit error-free
premise is essential: `withAt` rewrites only an already-present textual error,
and the source/runtime lifecycle must prove that no such error is present. -/
theorem feedProof_eq_of_go_ok
    (parser : ParserState) (token : ByteSlice)
    (before after : RuntimeProofState)
    (errorFree : parser.db.error? = none)
    (execution :
      ParserState.feedProof.go parser token before = .ok after) :
    parser.feedProof token before =
      { parser with tokp := .proof after } := by
  unfold ParserState.feedProof
  rw [execution]
  simp [ParserState.withAt, errorFree]

/-- A non-terminating proof token lifts through the complete production
`feedToken` dispatch.  The three discriminator premises are exactly the
lexical facts that keep a proof token from being stolen by the global comment,
include, or theorem-terminator branches. -/
theorem feedToken_proof_eq_of_go_ok
    (live : ParserState) (offset : Nat) (token : ByteSlice)
    (before after : RuntimeProofState)
    (parserMode : live.tokp = .proof before)
    (notComment : token.eqArray "$(".toAscii = false)
    (notInclude : token.eqArray "$[".toAscii = false)
    (notFinish : token.eqArray "$.".toAscii = false)
    (errorFree : live.db.error? = none)
    (execution :
      ParserState.feedProof.go { live with tokp := default }
        token before = .ok after) :
    live.feedToken offset token =
      { live with tokp := .proof after } := by
  rw [Mettapedia.Languages.Metamath.InferenceNormalByteLedger.feedToken_proof_step_exact
    live offset token before parserMode notComment notInclude notFinish]
  have lifted := feedProof_eq_of_go_ok
    { live with tokp := default } token before after
      (by simpa using errorFree) execution
  simpa using lifted

/-- Lexical evidence that a token occurring inside a proof is dispatched to
`feedProof`, rather than to one of `feedToken`'s three outer control branches. -/
structure ProofTokenDispatchesToFeedProof (token : ByteSlice) : Prop where
  notComment : token.eqArray "$(".toAscii = false
  notInclude : token.eqArray "$[".toAscii = false
  notFinish : token.eqArray "$.".toAscii = false

/-- Negative calibration: a theorem terminator cannot simultaneously be an
interior proof token. -/
theorem ProofTokenDispatchesToFeedProof.not_of_finish
    {token : ByteSlice}
    (dispatch : ProofTokenDispatchesToFeedProof token)
    (isFinish : token.eqArray "$.".toAscii = true) : False := by
  rw [dispatch.notFinish] at isFinish
  contradiction

/-- Execute located proof tokens through the production `feedToken` entry
point.  Offsets are retained because the outer parser accepts absolute source
positions even though successful interior proof steps do not inspect them. -/
def runProofFeedTokens
    (live : ParserState) (tokens : List (Nat × ByteSlice)) : ParserState :=
  tokens.foldl
    (fun current located =>
      current.feedToken located.1 located.2)
    live

/-! ## Comment-transparent proof token programmes -/

/-- A token strictly inside a Metamath comment.  The scannerless source GSLT
proves the stronger character-level fact that neither delimiter occurs as a
substring; these two token-level consequences are exactly what the production
`feedToken` comment branch consumes. -/
structure CommentInteriorToken (token : ByteSlice) : Prop where
  notClose : token.eqArray "$)".toAscii = false
  notOpen : token.eqArray "$(".toAscii = false

/-- One located comment block as observed by the production byte loop.  The
opening and closing calls are retained rather than erased because the
mm-lean4 implementation sends them through `feedToken`. -/
structure LocatedCommentBlock : Type where
  openLocated : Nat × ByteSlice
  openToken : openLocated.2.eqArray "$(".toAscii = true
  bodyLocated : List (Nat × ByteSlice)
  bodyTokens : ∀ located ∈ bodyLocated,
    CommentInteriorToken located.2
  closeLocated : Nat × ByteSlice
  closeToken : closeLocated.2.eqArray "$)".toAscii = true

/-- Execute every concrete token call belonging to one comment block. -/
def runLocatedCommentBlock
    (live : ParserState) (comment : LocatedCommentBlock) : ParserState :=
  let entered :=
    live.feedToken comment.openLocated.1 comment.openLocated.2
  let afterBody := runProofFeedTokens entered comment.bodyLocated
  afterBody.feedToken comment.closeLocated.1 comment.closeLocated.2

/-- Interior comment tokens leave the complete parser state unchanged. -/
theorem runCommentInteriorTokens_eq
    (live : ParserState) (inner : TokenParser)
    (tokens : List (Nat × ByteSlice))
    (commentMode : live.tokp = .comment inner)
    (interior : ∀ located ∈ tokens,
      CommentInteriorToken located.2) :
    runProofFeedTokens live tokens = live := by
  induction tokens generalizing live with
  | nil =>
      rfl
  | cons located tokens inductionHypothesis =>
      have headInterior := interior located (by simp)
      have headStep :
          live.feedToken located.1 located.2 = live := by
        simp [ParserState.feedToken, commentMode,
          headInterior.notClose, headInterior.notOpen]
      have tailInterior : ∀ item ∈ tokens,
          CommentInteriorToken item.2 := by
        intro item member
        exact interior item (by simp [member])
      simp only [runProofFeedTokens, List.foldl_cons, headStep]
      exact inductionHypothesis live commentMode tailInterior

/-- Positive comment boundary: from a live proof mode, a complete legal
comment performs its actual production calls and restores the exact parser
state.  In particular, comments do not merely preserve the database; they
preserve the suspended proof state and all sharing identities. -/
theorem runLocatedCommentBlock_eq_of_proofMode
    (live : ParserState) (proof : RuntimeProofState)
    (comment : LocatedCommentBlock)
    (proofMode : live.tokp = .proof proof) :
    runLocatedCommentBlock live comment = live := by
  let entered : ParserState :=
    { live with tokp := .comment (.proof proof) }
  have openStep :
      live.feedToken comment.openLocated.1 comment.openLocated.2 =
        entered := by
    simp [ParserState.feedToken, proofMode, comment.openToken, entered]
  have bodyStep :
      runProofFeedTokens entered comment.bodyLocated = entered :=
    runCommentInteriorTokens_eq entered (.proof proof)
      comment.bodyLocated rfl comment.bodyTokens
  have closeStep :
      entered.feedToken comment.closeLocated.1 comment.closeLocated.2 =
        live := by
    have restored : { live with tokp := .proof proof } = live := by
      cases live
      simp_all
    simpa [ParserState.feedToken, entered, comment.closeToken] using restored
  simp [runLocatedCommentBlock, openStep, bodyStep, closeStep]

/-- Negative comment boundary: a nested opening delimiter is rejected by the
actual production parser, so it cannot be treated as transparent trivia. -/
theorem nestedCommentOpening_rejected
    (live : ParserState) (inner : TokenParser)
    (offset : Nat) (token : ByteSlice)
    (commentMode : live.tokp = .comment inner)
    (notClose : token.eqArray "$)".toAscii = false)
    (nestedOpen : token.eqArray "$(".toAscii = true) :
    (live.feedToken offset token).db.error? ≠ none := by
  simp [ParserState.feedToken, commentMode, notClose, nestedOpen,
    ParserState.mkErrorFromEvidence, ParserState.withDB]

/-- If the source-derived inner transition fold succeeds, and the lexical
layer proves that every located token reaches the proof branch, then the same
tokens produce the exact corresponding state through the complete production
`feedToken` wrapper. -/
theorem runProofFeedTokens_eq_of_goFold
    (live : ParserState) (tokens : List (Nat × ByteSlice))
    (before after : RuntimeProofState)
    (parserMode : live.tokp = .proof before)
    (dispatch : ∀ located ∈ tokens,
      ProofTokenDispatchesToFeedProof located.2)
    (errorFree : live.db.error? = none)
    (execution :
      (tokens.map Prod.snd).foldlM
          (fun current token =>
            ParserState.feedProof.go { live with tokp := default }
              token current)
          before =
        .ok after) :
    runProofFeedTokens live tokens =
      { live with tokp := .proof after } := by
  induction tokens generalizing live before after with
  | nil =>
      simp [runProofFeedTokens] at execution ⊢
      cases execution
      cases live
      simp_all
  | cons located tokens ih =>
      simp only [List.map_cons, List.foldlM_cons, bind,
        Except.bind] at execution
      cases first :
          ParserState.feedProof.go { live with tokp := default }
            located.2 before with
      | error error =>
          rw [first] at execution
          cases execution
      | ok middle =>
          rw [first] at execution
          have headDispatch := dispatch located (by simp)
          have headStep :
              live.feedToken located.1 located.2 =
                { live with tokp := .proof middle } :=
            feedToken_proof_eq_of_go_ok live located.1 located.2
              before middle parserMode headDispatch.notComment
              headDispatch.notInclude headDispatch.notFinish errorFree first
          have tailDispatch : ∀ item ∈ tokens,
              ProofTokenDispatchesToFeedProof item.2 := by
            intro item member
            exact dispatch item (by simp [member])
          have tail := ih
            { live with tokp := .proof middle } middle after rfl
            tailDispatch (by simpa using errorFree) (by simpa using execution)
          simpa [runProofFeedTokens, headStep] using tail

/-- A represented explicit-header token sequence executes exactly the same
ordered preload fold as the source header, in the implementation's preload
phase. -/
theorem runPreloadTokenGo_eq_of_representation
    (parser : ParserState)
    {tokens : List ByteSlice} {labels : List String}
    (representation : PreloadTokensRepresent tokens labels)
    (initial result : RuntimeProofState)
    (execution : labels.foldlM (parser.db.preload) initial = .ok result) :
    runPreloadTokenGo parser tokens
        { initial with ptp := .preload } =
      .ok { result with ptp := .preload } := by
  induction representation generalizing initial result with
  | nil =>
      simp [runPreloadTokenGo] at execution ⊢
      cases execution
      rfl
  | @cons token label tokens labels head tail ih =>
      simp only [List.foldlM_cons, bind, Except.bind] at execution
      cases first : parser.db.preload initial label with
      | error error =>
          rw [first] at execution
          cases execution
      | ok middle =>
          rw [first] at execution
          have phaseExecution :=
            preload_withPtp parser.db initial middle label .preload first
          have firstToken :
              ParserState.feedProof.go parser token
                  { initial with ptp := .preload } =
                .ok { middle with ptp := .preload } := by
            unfold ParserState.feedProof.go
            rw [head.decoded]
            simp [head.notClose, phaseExecution]
          simp only [runPreloadTokenGo, List.foldlM_cons,
            bind, Except.bind]
          rw [firstToken]
          exact ih middle result execution

/-- Proof-relevant implementation witness for one complete source compressed
theorem through the parser's actual mandatory-header function, its ordinary
explicit-header preloads, and its shipped compressed-action executor. -/
structure CompressedParserExecutionPreservation
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (db : RuntimeDB) (pos : Pos)
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) : Type where
  runtimeMandatory : RuntimeProofState
  runtimeInitial : RuntimeProofState
  runtimeFinal : RuntimeProofState
  mandatoryExecution :
    db.preloadMandatoryHyps
        (sourceProofStart db pos label before formula) =
      .ok runtimeMandatory
  explicitHeaderExecution :
    explicitHeaderLabels.foldlM (db.preload) runtimeMandatory =
      .ok runtimeInitial
  actionExecution :
    ParserState.applyCompressedActions db runtimeInitial
        (step.actions.map toMMLean4Action) =
      .ok runtimeFinal
  finalAgreement :
    MachineAgrees db before.toSourcePrefix step.target
      step.finalState runtimeFinal
  finalStack : runtimeFinal.stack = #[formula.toRuntime]

/-- The three implementation phases preserve the source-authored theorem
identity, claimed formula, and mandatory frame all the way to the final proof
state. -/
theorem CompressedParserExecutionPreservation.finalIdentity
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {db : RuntimeDB} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation : CompressedParserExecutionPreservation db pos step) :
    preservation.runtimeFinal.label = label ∧
      preservation.runtimeFinal.fmla = formula.toRuntime ∧
      preservation.runtimeFinal.frame =
        (mandatoryFrame before formula).toRuntime := by
  have mandatoryLabel :
      preservation.runtimeMandatory.label =
        (sourceProofStart db pos label before formula).label :=
    Metamath.PrefixTraceCompressed.preloadMandatoryHyps_preserves_label
      db (sourceProofStart db pos label before formula)
        preservation.runtimeMandatory preservation.mandatoryExecution
  have mandatoryCore :
      preservation.runtimeMandatory.fmla =
          (sourceProofStart db pos label before formula).fmla ∧
        preservation.runtimeMandatory.frame =
          (sourceProofStart db pos label before formula).frame :=
    Metamath.ParserOps.preloadMandatoryHyps_ok_preserves_core
      db (sourceProofStart db pos label before formula)
        preservation.runtimeMandatory preservation.mandatoryExecution
  have explicitIdentity :=
    preloadFold_preserves_identity db explicitHeaderLabels
      preservation.runtimeMandatory preservation.runtimeInitial
      preservation.explicitHeaderExecution
  have actionLabel :
      preservation.runtimeFinal.label =
        preservation.runtimeInitial.label :=
    Metamath.PrefixTraceCompressed.applyCA_preserves_label
      db preservation.runtimeInitial
        (step.actions.map toMMLean4Action)
        preservation.runtimeFinal preservation.actionExecution
  have actionCore :
      preservation.runtimeFinal.fmla =
          preservation.runtimeInitial.fmla ∧
        preservation.runtimeFinal.frame =
          preservation.runtimeInitial.frame :=
    Metamath.ParserOps.applyCompressedActions_ok_preserves_core
      db preservation.runtimeInitial preservation.runtimeFinal
        (step.actions.map toMMLean4Action) preservation.actionExecution
  constructor
  · simpa [sourceProofStart, Metamath.Verify.DB.mkProofState] using
      actionLabel.trans (explicitIdentity.1.trans mandatoryLabel)
  constructor
  · simpa [sourceProofStart, Metamath.Verify.DB.mkProofState] using
      actionCore.1.trans
        (explicitIdentity.2.1.trans mandatoryCore.1)
  · simpa [sourceProofStart, Metamath.Verify.DB.mkProofState] using
      actionCore.2.trans
        (explicitIdentity.2.2.trans mandatoryCore.2)

/-- Concrete compressed proof tokens execute through the implementation's
actual inner `feedProof.go` transition to the same final state as the source
occurrence semantics.  The byte-image equation is the local lexical seam that
the raw-byte composition theorem must later supply. -/
theorem CompressedParserExecutionPreservation.bodyTokenGo
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {parser : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation parser.db pos step)
    (bodyTokens : List ByteSlice)
    (bytes : bodyTokens.map sliceBytes = bodyWords) :
    runCompressedTokenGo parser bodyTokens
        { preservation.runtimeInitial with ptp := .compressed 0 } =
      .ok { preservation.runtimeFinal with ptp := .compressed 0 } := by
  have decoded :
      decodeCompressedProgram bodyTokens =
        .ok (step.actions.map toMMLean4Action) :=
    decodeCompressedProgram_eq_ok_of_sliceBytes bodyTokens bodyWords
      step.actions bytes step.decoded
  exact runCompressedTokenGo_eq_of_program_ok parser bodyTokens
    preservation.runtimeInitial preservation.runtimeFinal
      (step.actions.map toMMLean4Action) decoded
      preservation.actionExecution

/-- Concrete explicit-header tokens execute through the implementation's
actual inner preload transition to the same source-derived initial action
state. -/
theorem CompressedParserExecutionPreservation.explicitHeaderTokenGo
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {parser : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation parser.db pos step)
    {headerTokens : List ByteSlice}
    (representation :
      PreloadTokensRepresent headerTokens explicitHeaderLabels) :
    runPreloadTokenGo parser headerTokens
        { preservation.runtimeMandatory with ptp := .preload } =
      .ok { preservation.runtimeInitial with ptp := .preload } := by
  exact runPreloadTokenGo_eq_of_representation parser representation
    preservation.runtimeMandatory preservation.runtimeInitial
      preservation.explicitHeaderExecution

/-- The opening delimiter executes the implementation's bulk mandatory
preload and enters the preload phase. -/
theorem CompressedParserExecutionPreservation.openTokenGo
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {parser : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation parser.db pos step)
    (openToken : ByteSlice)
    (isOpen : openToken.eqArray "(".toAscii = true) :
    ParserState.feedProof.go parser openToken
        (sourceProofStart parser.db pos label before formula) =
      .ok { preservation.runtimeMandatory with ptp := .preload } := by
  unfold ParserState.feedProof.go
  simp [sourceProofStart_mode, isOpen, preservation.mandatoryExecution]

/-- The closing delimiter leaves the explicit-header preload phase and enters
compressed decoding with a zero accumulator. -/
theorem CompressedParserExecutionPreservation.closeTokenGo
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {parser : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation parser.db pos step)
    (closeToken : ByteSlice)
    (isClose : closeToken.eqArray ")".toAscii = true) :
    ParserState.feedProof.go parser closeToken
        { preservation.runtimeInitial with ptp := .preload } =
      .ok { preservation.runtimeInitial with ptp := .compressed 0 } := by
  unfold ParserState.feedProof.go
  simp [isClose, pure, Except.pure]

/-! ## Complete `feedToken` routing for compressed proof phases -/

/-- The opening parenthesis reaches the proof parser through the production
outer dispatch, runs bulk mandatory preload, and installs the exact resulting
proof state in the live parser. -/
theorem CompressedParserExecutionPreservation.openFeedToken
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {live : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation live.db pos step)
    (offset : Nat) (openToken : ByteSlice)
    (parserMode : live.tokp =
      .proof (sourceProofStart live.db pos label before formula))
    (dispatch : ProofTokenDispatchesToFeedProof openToken)
    (isOpen : openToken.eqArray "(".toAscii = true)
    (errorFree : live.db.error? = none) :
    live.feedToken offset openToken =
      { live with tokp :=
          TokenParser.proof ({ preservation.runtimeMandatory with ptp := .preload }) } := by
  exact feedToken_proof_eq_of_go_ok live offset openToken
    (sourceProofStart live.db pos label before formula)
    { preservation.runtimeMandatory with ptp := .preload }
    parserMode dispatch.notComment dispatch.notInclude dispatch.notFinish
    errorFree (preservation.openTokenGo
      (parser := { live with tokp := default }) openToken isOpen)

/-- Located explicit-header labels pass through the complete outer parser and
produce the exact source-derived pre-compressed state. -/
theorem CompressedParserExecutionPreservation.explicitHeaderFeedTokens
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {live : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation live.db pos step)
    (tokens : List (Nat × ByteSlice))
    (parserMode : live.tokp =
      .proof ({ preservation.runtimeMandatory with ptp := .preload }))
    (representation :
      PreloadTokensRepresent (tokens.map Prod.snd) explicitHeaderLabels)
    (dispatch : ∀ located ∈ tokens,
      ProofTokenDispatchesToFeedProof located.2)
    (errorFree : live.db.error? = none) :
    runProofFeedTokens live tokens =
      { live with tokp :=
          TokenParser.proof ({ preservation.runtimeInitial with ptp := .preload }) } := by
  apply runProofFeedTokens_eq_of_goFold live tokens
    { preservation.runtimeMandatory with ptp := .preload }
    { preservation.runtimeInitial with ptp := .preload }
    parserMode dispatch errorFree
  have inner := preservation.explicitHeaderTokenGo
    (parser := { live with tokp := default }) representation
  simpa [runPreloadTokenGo] using inner

/-- The closing parenthesis passes through the complete outer parser and
enters compressed mode with a zero decoder accumulator. -/
theorem CompressedParserExecutionPreservation.closeFeedToken
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {live : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation live.db pos step)
    (offset : Nat) (closeToken : ByteSlice)
    (parserMode : live.tokp =
      .proof ({ preservation.runtimeInitial with ptp := .preload }))
    (dispatch : ProofTokenDispatchesToFeedProof closeToken)
    (isClose : closeToken.eqArray ")".toAscii = true)
    (errorFree : live.db.error? = none) :
    live.feedToken offset closeToken =
      { live with tokp :=
          TokenParser.proof ({ preservation.runtimeInitial with ptp := .compressed 0 }) } := by
  exact feedToken_proof_eq_of_go_ok live offset closeToken
    { preservation.runtimeInitial with ptp := .preload }
    { preservation.runtimeInitial with ptp := .compressed 0 }
    parserMode dispatch.notComment dispatch.notInclude dispatch.notFinish
    errorFree (preservation.closeTokenGo
      (parser := { live with tokp := default }) closeToken isClose)

/-- Located compressed-body tokens pass through the complete outer parser and
produce the exact occurrence-preserving final proof state.  The byte-image
equation and dispatch evidence are precisely the obligations exported to the
raw-byte lexical GSLT. -/
theorem CompressedParserExecutionPreservation.bodyFeedTokens
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    {live : ParserState} {pos : Pos}
    {step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords}
    (preservation :
      CompressedParserExecutionPreservation live.db pos step)
    (tokens : List (Nat × ByteSlice))
    (parserMode : live.tokp =
      .proof ({ preservation.runtimeInitial with ptp := .compressed 0 }))
    (bytes : (tokens.map Prod.snd).map sliceBytes = bodyWords)
    (dispatch : ∀ located ∈ tokens,
      ProofTokenDispatchesToFeedProof located.2)
    (errorFree : live.db.error? = none) :
    runProofFeedTokens live tokens =
      { live with tokp :=
          TokenParser.proof ({ preservation.runtimeFinal with ptp := .compressed 0 }) } := by
  apply runProofFeedTokens_eq_of_goFold live tokens
    { preservation.runtimeInitial with ptp := .compressed 0 }
    { preservation.runtimeFinal with ptp := .compressed 0 }
    parserMode dispatch errorFree
  have inner := preservation.bodyTokenGo
    (parser := { live with tokp := default })
    (bodyTokens := tokens.map Prod.snd) bytes
  simpa [runCompressedTokenGo] using inner

/-- Lexical evidence for the theorem-closing `$.` token. -/
structure ProofFinishToken (token : ByteSlice) : Prop where
  notComment : token.eqArray "$(".toAscii = false
  notInclude : token.eqArray "$[".toAscii = false
  isFinish : token.eqArray "$.".toAscii = true

/-- Negative calibration: the same token cannot be both an interior proof
token and the theorem terminator. -/
theorem ProofFinishToken.not_interior
    {token : ByteSlice} (finish : ProofFinishToken token)
    (interior : ProofTokenDispatchesToFeedProof token) : False := by
  exact interior.not_of_finish finish.isFinish

/-- The ordered located-token interface exported by the future raw-byte
lexical GSLT for one compressed theorem proof.  This record does not assert
raw-byte origin by itself: the raw-byte composition theorem must construct it
from a scanner derivation, including the actual `ByteSlice` values and source
offsets. -/
structure CompressedProofLocatedTokens
    (explicitHeaderLabels : List String)
    (bodyWords : List (List UInt8)) : Type where
  openLocated : Nat × ByteSlice
  openDispatch : ProofTokenDispatchesToFeedProof openLocated.2
  openDelimiter : openLocated.2.eqArray "(".toAscii = true
  headerLocated : List (Nat × ByteSlice)
  headerRepresentation :
    PreloadTokensRepresent (headerLocated.map Prod.snd) explicitHeaderLabels
  headerDispatch : ∀ located ∈ headerLocated,
    ProofTokenDispatchesToFeedProof located.2
  closeLocated : Nat × ByteSlice
  closeDispatch : ProofTokenDispatchesToFeedProof closeLocated.2
  closeDelimiter : closeLocated.2.eqArray ")".toAscii = true
  bodyLocated : List (Nat × ByteSlice)
  bodyBytes : (bodyLocated.map Prod.snd).map sliceBytes = bodyWords
  bodyDispatch : ∀ located ∈ bodyLocated,
    ProofTokenDispatchesToFeedProof located.2
  finishLocated : Nat × ByteSlice
  finishToken : ProofFinishToken finishLocated.2

/-- Execute one complete located compressed-proof token programme through the
production `feedToken` entry point, including the final theorem terminator. -/
def runCompressedProofLocatedTokens
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (live : ParserState)
    (tokens : CompressedProofLocatedTokens explicitHeaderLabels bodyWords) :
    ParserState :=
  let afterOpen :=
    live.feedToken tokens.openLocated.1 tokens.openLocated.2
  let afterHeader :=
    runProofFeedTokens afterOpen tokens.headerLocated
  let afterClose :=
    afterHeader.feedToken tokens.closeLocated.1 tokens.closeLocated.2
  let afterBody :=
    runProofFeedTokens afterClose tokens.bodyLocated
  afterBody.feedToken tokens.finishLocated.1 tokens.finishLocated.2

/-- Source compressed theorem execution is preserved by the exact parser-core
functions.  Unlike the earlier uniform-header theorem, this result uses the
implementation's special `preloadMandatoryHyps` entry point for the mandatory
prefix and therefore matches the production lifecycle division. -/
noncomputable def CompressedTheoremStep.mmLean4ParserCorePreserved
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (db : RuntimeDB)
    (hproject :
      projectPrefix? db = some before.toSourcePrefix.toProjection)
    (pos : Pos) :
    CompressedParserExecutionPreservation db pos step := by
  have fullHeader :
      HeaderBuild
        (((mandatoryHypotheses before formula).map HeaderItem.mandatory) ++
          explicitHeaderLabels.map HeaderItem.explicit)
        (emptyMachine before.toSourcePrefix step.target)
        step.initialState := by
    simpa [headerItems] using step.header
  obtain ⟨sourceMandatory, mandatoryBuild, explicitBuild⟩ :=
    Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4.HeaderBuild.splitAppend
      fullHeader
  obtain ⟨runtimeMandatory, mandatoryExecution, mandatoryAgreement⟩ :=
    mandatoryHeader_runtimePreserved db hproject pos label formula
      mandatoryBuild
  obtain ⟨runtimeInitial, explicitHeaderExecution,
      initialAgreement⟩ :=
    headerBuild_runtimePreserved db hproject runtimeMandatory explicitBuild
      mandatoryAgreement
  obtain ⟨runtimeFinal, actionExecution, finalAgreement⟩ :=
    execute_mmLean4Preserved db step.presentation_eq hproject runtimeInitial
      step.execution initialAgreement
  have rootStack :
      runtimeFinal.stack = #[step.root.formula.toRuntime] :=
    finalAgreement.singletonStack_eq step.rootId step.root step.finalStack
      step.rootLookup
  have finalStack : runtimeFinal.stack = #[formula.toRuntime] := by
    rw [rootStack, step.rootFormula]
  have explicitLabels :
      ((explicitHeaderLabels.map HeaderItem.explicit).map
        headerRuntimeLabel) = explicitHeaderLabels := by
    exact map_headerRuntimeLabel_explicit explicitHeaderLabels
  rw [explicitLabels] at explicitHeaderExecution
  exact
    { runtimeMandatory
      runtimeInitial
      runtimeFinal
      mandatoryExecution := mandatoryExecution
      explicitHeaderExecution := explicitHeaderExecution
      actionExecution := actionExecution
      finalAgreement := finalAgreement
      finalStack := finalStack }

/-! ## Source-owned theorem insertion -/

/-- Proof-relevant preservation of the implementation's final theorem
insertion.  `finalProof` is the parser-core result placed in the completed
compressed phase; raw proof-token routing into that phase remains a separate
composition theorem. -/
structure CompressedParserFinishPreservation
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (parser : ParserState) (pos : Pos)
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) : Type where
  core : CompressedParserExecutionPreservation parser.db pos step
  finalProof : RuntimeProofState
  finalProof_eq :
    finalProof = { core.runtimeFinal with ptp := .compressed 0 }
  finalIdentity :
    finalProof.label = label ∧
      finalProof.fmla = formula.toRuntime ∧
      finalProof.frame = (mandatoryFrame before formula).toRuntime
  finalMode : finalProof.ptp = .compressed 0
  finalStack : finalProof.stack = #[formula.toRuntime]
  finishDB :
    (parser.finishProof finalProof).db =
      parser.db.insert finalProof.pos label
        (.assert formula.toRuntime
          (mandatoryFrame before formula).toRuntime)
  finishErrorFree : (parser.finishProof finalProof).db.error? = none
  namespaceAfter :
    RuntimeObjectNamespaceAgrees
      (parser.finishProof finalProof).db after

/-- The complete source compressed occurrence is preserved through the
implementation parser core and its real `finishProof`/`DB.insert` branch.
Global namespace agreement supplies duplicate-label safety, including labels
of hypotheses that are no longer active. -/
noncomputable def CompressedTheoremStep.mmLean4FinishPreserved
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (parser : ParserState)
    (hproject :
      projectPrefix? parser.db =
        some before.toSourcePrefix.toProjection)
    (namespaceAgreement : RuntimeObjectNamespaceAgrees parser.db before)
    (pos : Pos) :
    CompressedParserFinishPreservation parser pos step := by
  let core :=
    CompressedTheoremStep.mmLean4ParserCorePreserved
      step parser.db hproject pos
  let finalProof : RuntimeProofState :=
    { core.runtimeFinal with ptp := .compressed 0 }
  have coreIdentity := core.finalIdentity
  have finalIdentity :
      finalProof.label = label ∧
        finalProof.fmla = formula.toRuntime ∧
        finalProof.frame =
          (mandatoryFrame before formula).toRuntime := by
    simpa [finalProof] using coreIdentity
  have finalStack : finalProof.stack = #[formula.toRuntime] := by
    simpa [finalProof] using core.finalStack
  have singleton : finalProof.stack = #[finalProof.fmla] := by
    rw [finalStack, finalIdentity.2.1]
  have insertError :
      (parser.db.insert finalProof.pos finalProof.label
        (.assert finalProof.fmla finalProof.frame)).error? = none := by
    simpa [finalIdentity.1, finalIdentity.2.1, finalIdentity.2.2] using
      CompressedTheoremStep.runtimeInsert_errorFree
        step namespaceAgreement finalProof.pos
  have finished :=
    finishProof_compressed_success parser finalProof rfl singleton insertError
  have finishDB :
      (parser.finishProof finalProof).db =
        parser.db.insert finalProof.pos label
          (.assert formula.toRuntime
            (mandatoryFrame before formula).toRuntime) := by
    simpa [finalIdentity.1, finalIdentity.2.1, finalIdentity.2.2] using
      finished.1
  have namespaceAfter :
      RuntimeObjectNamespaceAgrees
        (parser.finishProof finalProof).db after := by
    rw [finishDB]
    exact CompressedTheoremStep.runtimeNamespaceAfterInsert
      step namespaceAgreement finalProof.pos
  exact
    { core
      finalProof
      finalProof_eq := rfl
      finalIdentity
      finalMode := rfl
      finalStack
      finishDB
      finishErrorFree := finished.2
      namespaceAfter }

/-! ## One complete production token lifecycle -/

/-- Proof-relevant preservation of one complete located compressed-proof token
programme through `feedToken`, including the real `$.` finalization event. -/
structure CompressedFeedTokenPreservation
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (live : ParserState) (pos : Pos)
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (tokens :
      CompressedProofLocatedTokens explicitHeaderLabels bodyWords) : Type where
  finish :
    CompressedParserFinishPreservation
      { live with tokp := default } pos step
  execution :
    runCompressedProofLocatedTokens live tokens =
      ({ live with tokp := default }).finishProof finish.finalProof
  resultErrorFree :
    (runCompressedProofLocatedTokens live tokens).db.error? = none
  namespaceAfter :
    RuntimeObjectNamespaceAgrees
      (runCompressedProofLocatedTokens live tokens).db after

/-- A source compressed theorem occurrence, an agreeing runtime prefix, and a
located lexical token programme determine the exact successful production
`feedToken` execution through final database insertion.  Token origin is still
an explicit upstream obligation: this theorem consumes, but does not invent,
the located-token programme. -/
noncomputable def CompressedTheoremStep.mmLean4FeedTokensPreserved
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (live : ParserState) (pos : Pos)
    (parserMode : live.tokp =
      .proof (sourceProofStart live.db pos label before formula))
    (hproject :
      projectPrefix? live.db =
        some before.toSourcePrefix.toProjection)
    (namespaceAgreement : RuntimeObjectNamespaceAgrees live.db before)
    (tokens :
      CompressedProofLocatedTokens explicitHeaderLabels bodyWords) :
    CompressedFeedTokenPreservation live pos step tokens := by
  let base : ParserState := { live with tokp := default }
  let finish :=
    CompressedTheoremStep.mmLean4FinishPreserved
      step base (by simpa [base] using hproject)
        (by simpa [base] using namespaceAgreement) pos
  let openState : ParserState :=
    { live with tokp := TokenParser.proof ({ finish.core.runtimeMandatory with ptp := .preload }) }
  let headerState : ParserState :=
    { live with tokp := TokenParser.proof ({ finish.core.runtimeInitial with ptp := .preload }) }
  let closeState : ParserState :=
    { live with tokp := TokenParser.proof ({ finish.core.runtimeInitial with ptp := .compressed 0 }) }
  let bodyState : ParserState :=
    { live with tokp := TokenParser.proof finish.finalProof }
  have openExecution :
      live.feedToken tokens.openLocated.1 tokens.openLocated.2 =
        openState := by
    simpa [openState] using finish.core.openFeedToken
      (live := live) tokens.openLocated.1 tokens.openLocated.2 parserMode
      tokens.openDispatch tokens.openDelimiter namespaceAgreement.errorFree
  have headerExecution :
      runProofFeedTokens openState tokens.headerLocated =
        headerState := by
    simpa [openState, headerState] using
      finish.core.explicitHeaderFeedTokens
        (live := openState) tokens.headerLocated rfl
        tokens.headerRepresentation tokens.headerDispatch
        (by simpa [openState] using namespaceAgreement.errorFree)
  have closeExecution :
      headerState.feedToken tokens.closeLocated.1 tokens.closeLocated.2 =
        closeState := by
    simpa [headerState, closeState] using finish.core.closeFeedToken
      (live := headerState) tokens.closeLocated.1 tokens.closeLocated.2 rfl
      tokens.closeDispatch tokens.closeDelimiter
      (by simpa [headerState] using namespaceAgreement.errorFree)
  have bodyExecution :
      runProofFeedTokens closeState tokens.bodyLocated =
        bodyState := by
    have raw := finish.core.bodyFeedTokens
      (live := closeState) tokens.bodyLocated rfl tokens.bodyBytes
      tokens.bodyDispatch
      (by simpa [closeState] using namespaceAgreement.errorFree)
    simpa [closeState, bodyState, finish.finalProof_eq] using raw
  have finishExecution :
      bodyState.feedToken tokens.finishLocated.1 tokens.finishLocated.2 =
        base.finishProof finish.finalProof := by
    have raw :=
      Mettapedia.Languages.Metamath.InferenceNormalByteLedger.feedToken_proof_finish_exact
        bodyState tokens.finishLocated.1 tokens.finishLocated.2
        finish.finalProof rfl tokens.finishToken.notComment
        tokens.finishToken.notInclude tokens.finishToken.isFinish
    simpa [bodyState, base] using raw
  have execution :
      runCompressedProofLocatedTokens live tokens =
        base.finishProof finish.finalProof := by
    simp only [runCompressedProofLocatedTokens]
    rw [openExecution, headerExecution, closeExecution, bodyExecution]
    exact finishExecution
  refine
    { finish
      execution := by simpa [base] using execution
      resultErrorFree := ?_
      namespaceAfter := ?_ }
  · rw [execution]
    exact finish.finishErrorFree
  · rw [execution]
    exact finish.namespaceAfter

end Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
