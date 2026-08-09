import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
import Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition

/-!
# Source/runtime database agreement

`SourceState` owns the chronological source history.  The shipped
`mm-lean4` database stores global objects in a hash map, so its inspectable
projection has a deterministic label order rather than source order.  This
module makes that representation boundary explicit:

* `SourceState.runtimePrefix` is the canonical, label-sorted checker view;
* `RuntimeObjectNamespaceAgrees` retains every occupied global name,
  including hypothesis labels retired by scope exit;
* `runtimeScopeSizes` relates the source's newest-first boundary stack to
  the implementation's oldest-first array.

The chronological state is not replaced or reconstructed from the hash map.
Only the extensional checker view is canonicalized.  Later native backends
must refine this same source semantics independently; agreement with `mm-lean4`
does not authorize a native state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
open Metamath.Verify

/-! ## Canonical checker view -/

/-- Deterministic label order for the source-owned assertion set. -/
def sortSourceAssertions (assertions : List SourceAssertion) :
    List SourceAssertion :=
  assertions.mergeSort fun left right => left.label ≤ right.label

theorem mem_sortSourceAssertions_iff (assertion : SourceAssertion)
    (assertions : List SourceAssertion) :
    assertion ∈ sortSourceAssertions assertions ↔ assertion ∈ assertions := by
  exact (List.mergeSort_perm assertions _).mem_iff

/-- Extensional checker prefix corresponding to the runtime hash-map
projection.  Active hypotheses remain in frame order; only global sets whose
runtime carrier forgets insertion order are canonicalized. -/
def runtimePrefix (state : SourceState) : SourcePrefix :=
  { declaredConstants := sortStrings state.declaredConstants
    declaredVariables := sortStrings state.declaredVariables
    callerFrame := state.callerFrame
    activeHypotheses := state.activeHypotheses
    assertions := sortSourceAssertions state.assertions }

@[simp] theorem initialState_runtimePrefix :
    runtimePrefix initialState = initialState.toSourcePrefix := by
  simp [runtimePrefix, sortStrings, sortSourceAssertions, initialState,
    SourceState.toSourcePrefix, SourceState.callerFrame,
    SourceState.proofDistinctVariables,
    SourceState.activeFloatingVariables]

theorem runtimePrefix_assertion_mem_iff (state : SourceState)
    (assertion : SourceAssertion) :
    assertion ∈ (runtimePrefix state).assertions ↔
      assertion ∈ state.assertions := by
  exact mem_sortSourceAssertions_iff assertion state.assertions

theorem runtimePrefix_constant_mem_iff (state : SourceState)
    (constantName : String) :
    constantName ∈ (runtimePrefix state).declaredConstants ↔
      constantName ∈ state.declaredConstants := by
  exact mem_sortStrings_iff constantName state.declaredConstants

theorem runtimePrefix_variable_mem_iff (state : SourceState)
    (variableName : String) :
    variableName ∈ (runtimePrefix state).declaredVariables ↔
      variableName ∈ state.declaredVariables := by
  exact mem_sortStrings_iff variableName state.declaredVariables

/-! ## Scope-stack representation -/

/-- Runtime `Frame.size` order for one source scope boundary. -/
def ScopeBoundary.runtimeSize (boundary : ScopeBoundary) : Nat × Nat :=
  (boundary.activeDistinctLength, boundary.activeHypothesisLength)

/-- The source stack is newest-first; the runtime array is oldest-first. -/
def runtimeScopeSizes (state : SourceState) : List (Nat × Nat) :=
  state.scopes.reverse.map ScopeBoundary.runtimeSize

/-! ## Complete agreement -/

/-- Erase administrative carriers before projection.  Projection observes
the current frame and global object map; scope history is related separately
by `RuntimeDBAgrees.scopeStack`, while incomplete-proof labels are a warning
ledger with no source-prefix meaning. -/
def projectionDB (db : RuntimeDB) : RuntimeDB :=
  { db with scopes := #[], incompleteProofs := #[] }

@[simp] theorem projectionDB_default :
    projectionDB (default : RuntimeDB) = default := by
  rfl

@[simp] theorem projectHypothesis?_projectionDB
    (db : RuntimeDB) (label : String) :
    projectHypothesis? (projectionDB db) label =
      projectHypothesis? db label := by
  simp [projectHypothesis?, projectionDB, Metamath.Verify.DB.find?]

@[simp] theorem projectHypotheses?_projectionDB
    (db : RuntimeDB) (labels : List String) :
    projectHypotheses? (projectionDB db) labels =
      projectHypotheses? db labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      unfold projectHypotheses? at ih ⊢
      simp only [List.mapM_cons]
      rw [projectHypothesis?_projectionDB, ih]

@[simp] theorem projectAssertion?_projectionDB
    (db : RuntimeDB) (label : String)
    (formula : RuntimeFormula) (frame : RuntimeFrame)
    (embeddedLabel : String) :
    projectAssertion? (projectionDB db) label formula frame embeddedLabel =
      projectAssertion? db label formula frame embeddedLabel := by
  simp [projectAssertion?]

@[simp] theorem projectAssertionsFromEntries?_projectionDB
    (db : RuntimeDB)
    (entries : List (String × Metamath.Verify.Object)) :
    projectAssertionsFromEntries? (projectionDB db) entries =
      projectAssertionsFromEntries? db entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨label, object⟩
      cases object <;>
        simp [projectAssertionsFromEntries?, ih]

@[simp] theorem projectionDB_frame (db : RuntimeDB) :
    (projectionDB db).frame = db.frame := by
  rfl

@[simp] theorem projectionDB_objects (db : RuntimeDB) :
    (projectionDB db).objects = db.objects := by
  rfl

@[simp] theorem projectionDB_error? (db : RuntimeDB) :
    (projectionDB db).error? = db.error? := by
  rfl

@[simp] theorem wellFormed?_projectionDB (db : RuntimeDB) :
    (projectionDB db).wellFormed? = db.wellFormed? := by
  simp [Metamath.Verify.DB.wellFormed?,
    Metamath.Verify.DB.wellFormedFrame?,
    Metamath.Verify.DB.wellFormedObjects?,
    Metamath.Verify.DB.frameHypsOk?,
    Metamath.Verify.DB.frameFloatVarsUnique?,
    Metamath.Verify.DB.wellFormedObj?,
    Metamath.Verify.DB.hypOK?, Metamath.Verify.DB.find?]

@[simp] theorem assertDvVarsInFrame?_projectionDB (db : RuntimeDB) :
    (projectionDB db).assertDvVarsInFrame? =
      db.assertDvVarsInFrame? := by
  simp [Metamath.Verify.DB.assertDvVarsInFrame?,
    Metamath.Verify.DB.frameDvVarsInFrame?,
    Metamath.Verify.DB.frameFloatVars,
    Metamath.Verify.DB.find?]

@[simp] theorem rawCallerDVStrict_projectionDB (db : RuntimeDB) :
    rawCallerDVStrict (projectionDB db) = rawCallerDVStrict db := by
  rfl

@[simp] theorem objectEntries_projectionDB (db : RuntimeDB) :
    objectEntries (projectionDB db) = objectEntries db := by
  rfl

@[simp] theorem proofFacingCallerFrame_projectionDB (db : RuntimeDB) :
    proofFacingCallerFrame (projectionDB db) =
      proofFacingCallerFrame db := by
  unfold proofFacingCallerFrame projectionDB Metamath.Verify.DB.frameFloatVars
  rfl

/-- The shared prefix projector is insensitive to the independently tracked
scope-history stack. -/
@[simp] theorem projectPrefix?_projectionDB (db : RuntimeDB) :
    projectPrefix? (projectionDB db) = projectPrefix? db := by
  simp only [projectPrefix?, projectionDB_error?,
    wellFormed?_projectionDB, assertDvVarsInFrame?_projectionDB,
    rawCallerDVStrict_projectionDB, objectEntries_projectionDB,
    projectionDB_frame, projectHypotheses?_projectionDB,
    proofFacingCallerFrame_projectionDB,
    projectAssertionsFromEntries?_projectionDB]

/-- Scope-insensitive use of the single shared prefix projector.  This wrapper
does not implement projection logic; it only erases the independently related
scope-history carrier before calling `projectPrefix?`. -/
def projectSourcePrefix? (live : RuntimeDB) : Option PrefixProjection :=
  projectPrefix? (projectionDB live)

/-- Hypothesis projection reads the global object map, not variable activity. -/
@[simp] theorem projectHypothesis?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat))
    (label : String) :
    projectHypothesis? { db with activeVars := activeVars } label =
      projectHypothesis? db label := by
  unfold projectHypothesis? Metamath.Verify.DB.find?
  rfl

@[simp] theorem projectHypotheses?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat))
    (labels : List String) :
    projectHypotheses? { db with activeVars := activeVars } labels =
      projectHypotheses? db labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih =>
      unfold projectHypotheses? at ih ⊢
      simp only [List.mapM_cons]
      rw [projectHypothesis?_with_activeVars, ih]

@[simp] theorem projectAssertion?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat))
    (label : String) (formula : RuntimeFormula) (frame : RuntimeFrame)
    (embeddedLabel : String) :
    projectAssertion? { db with activeVars := activeVars }
        label formula frame embeddedLabel =
      projectAssertion? db label formula frame embeddedLabel := by
  simp [projectAssertion?]

@[simp] theorem projectAssertionsFromEntries?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat))
    (entries : List (String × Metamath.Verify.Object)) :
    projectAssertionsFromEntries? { db with activeVars := activeVars }
        entries =
      projectAssertionsFromEntries? db entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨label, object⟩
      cases object <;> simp [projectAssertionsFromEntries?, ih]

@[simp] theorem wellFormed?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    ({ db with activeVars := activeVars } : RuntimeDB).wellFormed? =
      db.wellFormed? := by
  simp [Metamath.Verify.DB.wellFormed?,
    Metamath.Verify.DB.wellFormedFrame?,
    Metamath.Verify.DB.wellFormedObjects?,
    Metamath.Verify.DB.frameHypsOk?,
    Metamath.Verify.DB.frameFloatVarsUnique?,
    Metamath.Verify.DB.wellFormedObj?,
    Metamath.Verify.DB.hypOK?, Metamath.Verify.DB.find?]

@[simp] theorem assertDvVarsInFrame?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    ({ db with activeVars := activeVars } : RuntimeDB).assertDvVarsInFrame? =
      db.assertDvVarsInFrame? := by
  simp [Metamath.Verify.DB.assertDvVarsInFrame?,
    Metamath.Verify.DB.frameDvVarsInFrame?,
    Metamath.Verify.DB.frameFloatVars,
    Metamath.Verify.DB.find?]

@[simp] theorem proofFacingCallerFrame_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    proofFacingCallerFrame { db with activeVars := activeVars } =
      proofFacingCallerFrame db := by
  unfold proofFacingCallerFrame Metamath.Verify.DB.frameFloatVars
  rfl

@[simp] theorem rawCallerDVStrict_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    rawCallerDVStrict { db with activeVars := activeVars } =
      rawCallerDVStrict db := rfl

@[simp] theorem objectEntries_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    objectEntries { db with activeVars := activeVars } =
      objectEntries db := rfl

/-- Prefix projection is insensitive to the separately tracked active-variable
stack. -/
@[simp] theorem projectPrefix?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    projectPrefix? { db with activeVars := activeVars } =
      projectPrefix? db := by
  unfold projectPrefix?
  simp only [wellFormed?_with_activeVars,
    assertDvVarsInFrame?_with_activeVars,
    rawCallerDVStrict_with_activeVars,
    objectEntries_with_activeVars,
    projectHypotheses?_with_activeVars,
    proofFacingCallerFrame_with_activeVars,
    projectAssertionsFromEntries?_with_activeVars]
  rfl

/-- The proof-facing projection deliberately ignores the separate
scope-sensitive active-variable stack. -/
@[simp] theorem projectSourcePrefix?_with_activeVars
    (db : RuntimeDB) (activeVars : Array (String × Nat)) :
    projectSourcePrefix? { db with activeVars := activeVars } =
      projectSourcePrefix? db := by
  change projectPrefix?
      { projectionDB db with activeVars := activeVars } =
    projectPrefix? (projectionDB db)
  exact projectPrefix?_with_activeVars _ _

/-- A successful source-facing projection exposes exactly the values read
from the live implementation state. -/
theorem projectSourcePrefix?_eq_some_fields
    (db : RuntimeDB) (projection : PrefixProjection)
    (hproject : projectSourcePrefix? db = some projection) :
    projection.declaredConstants =
        declaredConstantNames (objectEntries (projectionDB db)) ∧
      projection.declaredVariables =
        declaredVariableNames (objectEntries (projectionDB db)) ∧
      projection.callerFrame = proofFacingCallerFrame (projectionDB db) ∧
      projectHypotheses? (projectionDB db)
          (projectionDB db).frame.hyps.toList =
        some projection.activeHypotheses ∧
      projectAssertionsFromEntries? (projectionDB db)
          (objectEntries (projectionDB db)) =
        some projection.assertions := by
  exact projectPrefix?_eq_some_fields (projectionDB db) projection hproject

/-! ## Active-variable stack representation -/

/-- Exact agreement between the shipped depth-tagged active-variable stack
and the source state's scope-sensitive active-variable list.  At global
scope every entry has depth zero.  Inside a block, the saved source prefix
agrees recursively with the outer scopes and every entry after that prefix
has the current runtime depth. -/
inductive RuntimeActiveVariablesAgree :
    List (String × Nat) → List String → List ScopeBoundary → Prop
  | global {entries names}
      (names_eq : entries.map Prod.fst = names)
      (depth_zero : ∀ entry ∈ entries, entry.2 = 0) :
      RuntimeActiveVariablesAgree entries names []
  | block {entries names boundary rest}
      (names_eq : entries.map Prod.fst = names)
      (boundary_le : boundary.activeVariableLength ≤ entries.length)
      (outer : RuntimeActiveVariablesAgree
        (entries.take boundary.activeVariableLength)
        (names.take boundary.activeVariableLength) rest)
      (current_depth :
        ∀ entry ∈ entries.drop boundary.activeVariableLength,
          entry.2 = (boundary :: rest).length) :
      RuntimeActiveVariablesAgree entries names (boundary :: rest)

theorem RuntimeActiveVariablesAgree.names_eq
    {entries : List (String × Nat)} {names : List String}
    {scopes : List ScopeBoundary}
    (agreement : RuntimeActiveVariablesAgree entries names scopes) :
    entries.map Prod.fst = names := by
  cases agreement with
  | global names_eq _ => exact names_eq
  | block names_eq _ _ _ => exact names_eq

theorem RuntimeActiveVariablesAgree.depth_bounded
    {entries : List (String × Nat)} {names : List String}
    {scopes : List ScopeBoundary}
    (agreement : RuntimeActiveVariablesAgree entries names scopes) :
    ∀ entry ∈ entries, entry.2 ≤ scopes.length := by
  induction agreement with
  | global names_eq depth_zero =>
      intro entry hentry
      simp [depth_zero entry hentry]
  | @block entries names boundary rest names_eq boundary_le outer
      current_depth ih =>
      intro entry hentry
      rw [← List.take_append_drop boundary.activeVariableLength entries]
        at hentry
      rcases List.mem_append.mp hentry with houter | hcurrent
      · exact Nat.le_trans (ih entry houter) (by simp)
      · simp [current_depth entry hcurrent]

/-- Opening a source scope and pushing the shipped runtime scope preserve the
active-variable representation. -/
theorem RuntimeActiveVariablesAgree.pushScope
    {entries : List (String × Nat)} {names : List String}
    {scopes : List ScopeBoundary}
    (agreement : RuntimeActiveVariablesAgree entries names scopes)
    (boundary : ScopeBoundary)
    (hboundary : boundary.activeVariableLength = names.length) :
    RuntimeActiveVariablesAgree entries names (boundary :: scopes) := by
  have hlength : entries.length = names.length := by
    simpa using congrArg List.length agreement.names_eq
  refine .block agreement.names_eq ?_ ?_ ?_
  · simp [hboundary, hlength]
  · have entriesTake :
        entries.take boundary.activeVariableLength = entries := by
      rw [hboundary, ← hlength, List.take_length]
    have namesTake : names.take boundary.activeVariableLength = names := by
      rw [hboundary, List.take_length]
    rw [entriesTake, namesTake]
    exact agreement
  · intro entry hentry
    simp [hboundary, ← hlength] at hentry

/-- Activating one variable appends the source name and the shipped entry at
the current scope depth. -/
theorem RuntimeActiveVariablesAgree.activate
    {entries : List (String × Nat)} {names : List String}
    {scopes : List ScopeBoundary}
    (agreement : RuntimeActiveVariablesAgree entries names scopes)
    (name : String) :
    RuntimeActiveVariablesAgree
      (entries ++ [(name, scopes.length)]) (names ++ [name]) scopes := by
  cases agreement with
  | global names_eq depth_zero =>
      refine .global (by simp [names_eq]) ?_
      intro entry hentry
      rcases List.mem_append.mp hentry with hold | hnew
      · exact depth_zero entry hold
      · simpa using congrArg Prod.snd (List.mem_singleton.mp hnew)
  | @block entries names boundary rest names_eq boundary_le outer
      current_depth =>
      have hlength : entries.length = names.length := by
        simpa using congrArg List.length names_eq
      have hnamesLength : boundary.activeVariableLength ≤ names.length := by
        simpa [← hlength] using boundary_le
      refine .block (by simp [names_eq]) ?_ ?_ ?_
      · simpa using Nat.le_trans boundary_le (Nat.le_succ entries.length)
      · simpa [List.take_append_of_le_length boundary_le,
          List.take_append_of_le_length hnamesLength] using outer
      · intro entry hentry
        rw [List.drop_append_of_le_length boundary_le] at hentry
        rcases List.mem_append.mp hentry with hold | hnew
        · exact current_depth entry hold
        · simpa using congrArg Prod.snd (List.mem_singleton.mp hnew)

/-- Closing the newest scope filters out exactly its active-variable suffix
and exposes the recursively related outer prefix. -/
theorem RuntimeActiveVariablesAgree.popScope
    {entries : List (String × Nat)} {names : List String}
    {boundary : ScopeBoundary} {rest : List ScopeBoundary}
    (agreement : RuntimeActiveVariablesAgree entries names
      (boundary :: rest)) :
    RuntimeActiveVariablesAgree
      (entries.filter fun entry => entry.2 ≤ rest.length)
      (names.take boundary.activeVariableLength) rest := by
  cases agreement with
  | block names_eq boundary_le outer current_depth =>
      have hprefix :
          (entries.take boundary.activeVariableLength).filter
              (fun entry => entry.2 ≤ rest.length) =
            entries.take boundary.activeVariableLength := by
        apply List.filter_eq_self.mpr
        intro entry hentry
        exact decide_eq_true (outer.depth_bounded entry hentry)
      have hsuffix :
          (entries.drop boundary.activeVariableLength).filter
              (fun entry => entry.2 ≤ rest.length) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro entry hentry
        rw [decide_eq_true_eq]
        simp [current_depth entry hentry]
      rw [← List.take_append_drop boundary.activeVariableLength entries,
        List.filter_append, hprefix, hsuffix, List.append_nil]
      exact outer

/-- Source/runtime agreement at a parser-prefix boundary.  Projection,
permanent namespace, and scoped stack are separate fields because they obey
different structural laws. -/
structure RuntimeDBAgrees (db : RuntimeDB) (state : SourceState) : Prop where
  projection :
    projectSourcePrefix? db = some (runtimePrefix state).toProjection
  objectNamespace : RuntimeObjectNamespaceAgrees db state
  rawFrame :
    db.frame.dj.toList = state.activeDistinctVariables ∧
      db.frame.hyps.toList =
        state.activeHypotheses.map HypothesisView.label
  activeVariables : RuntimeActiveVariablesAgree db.activeVars.toList
    state.activeVariables state.scopes
  scopeStack : db.scopes.toList = runtimeScopeSizes state

theorem RuntimeDBAgrees.errorFree {db : RuntimeDB} {state : SourceState}
    (agreement : RuntimeDBAgrees db state) : db.error? = none :=
  agreement.objectNamespace.errorFree

/-- The source-facing projection does not observe the incomplete-proof
warning ledger. -/
@[simp] theorem projectSourcePrefix?_recordIncomplete
    (db : RuntimeDB) (incomplete : Bool) (label : String) :
    projectSourcePrefix? (db.recordIncomplete incomplete label) =
      projectSourcePrefix? db := by
  cases incomplete with
  | false => rfl
  | true =>
      unfold Metamath.Verify.DB.recordIncomplete
      simp only [if_true]
      unfold projectSourcePrefix? projectionDB
      rfl

/-- Recording the warning label of an accepted incomplete proof is
administrative: it changes none of the source-facing database observations. -/
theorem RuntimeDBAgrees.recordIncomplete
    {db : RuntimeDB} {state : SourceState}
    (agreement : RuntimeDBAgrees db state)
    (incomplete : Bool) (label : String) :
    RuntimeDBAgrees (db.recordIncomplete incomplete label) state := by
  refine
    { projection := by simpa using agreement.projection
      objectNamespace :=
        { errorFree := by
            simpa using agreement.objectNamespace.errorFree
          occupied_iff := by
            intro candidate
            simpa using agreement.objectNamespace.occupied_iff candidate }
      rawFrame := by simpa using agreement.rawFrame
      activeVariables := by simpa using agreement.activeVariables
      scopeStack := by simpa using agreement.scopeStack }

/-- Complete agreement exposes the direct shared projector as well as the
source-facing wrapper used in the relation. -/
theorem RuntimeDBAgrees.projectPrefix_eq
    {db : RuntimeDB} {state : SourceState}
    (agreement : RuntimeDBAgrees db state) :
    projectPrefix? db = some (runtimePrefix state).toProjection := by
  simpa [projectSourcePrefix?] using agreement.projection

theorem RuntimeDBAgrees.proofFacingFrame_eq
    {db : RuntimeDB} {state : SourceState}
    (agreement : RuntimeDBAgrees db state) :
    proofFacingCallerFrame db = state.callerFrame.toRuntime := by
  have fields := projectSourcePrefix?_eq_some_fields
    _ _ agreement.projection
  have hframe := fields.2.2.1
  rw [proofFacingCallerFrame_projectionDB] at hframe
  simpa [runtimePrefix, SourcePrefix.toProjection] using hframe.symm

@[simp] theorem projectSourcePrefix?_pushScope (db : RuntimeDB) :
    projectSourcePrefix? db.pushScope = projectSourcePrefix? db := by
  unfold projectSourcePrefix? projectionDB Metamath.Verify.DB.pushScope
  rfl

/-! ## Boundary calibration -/

private theorem default_projectPrefix :
    projectSourcePrefix? (default : RuntimeDB) =
      some (runtimePrefix initialState).toProjection := by
  have hwf : (default : RuntimeDB).wellFormed? = true := by
    simp [DB.wellFormed?, DB.wellFormedFrame?, DB.frameHypsOk?,
      DB.frameFloatVarsUnique?, DB.wellFormedObjects?]
  have hdv : (default : RuntimeDB).assertDvVarsInFrame? = true := by
    simp [DB.assertDvVarsInFrame?]
  have hrawDV : rawCallerDVStrict (default : RuntimeDB) = true := by
    rfl
  have hentries : objectEntries (default : RuntimeDB) = [] := by
    simp [objectEntries, sortObjectEntries]
  rw [initialState_runtimePrefix]
  simp only [projectSourcePrefix?, projectionDB_default, projectPrefix?, hwf,
    hdv, hrawDV, hentries]
  rfl

/-- Positive boundary: the empty source and shipped runtime agree in all
three dimensions. -/
theorem default_initial_runtimeDBAgrees :
    RuntimeDBAgrees (default : RuntimeDB) initialState := by
  exact
    { projection := default_projectPrefix
      objectNamespace := default_initial_namespaceAgrees
      rawFrame := ⟨rfl, rfl⟩
      activeVariables := .global rfl (by
        intro entry hentry
        change entry ∈ ([] : List (String × Nat)) at hentry
        simp at hentry)
      scopeStack := rfl }

/-- Negative boundary: a runtime-only pushed scope is visible even though it
does not change the proof-facing projection or global namespace. -/
theorem pushedDefault_not_initial_runtimeDBAgrees :
    ¬ RuntimeDBAgrees (default : RuntimeDB).pushScope initialState := by
  intro agreement
  have hscopes := agreement.scopeStack
  simp [DB.pushScope, runtimeScopeSizes, initialState] at hscopes

/-! ## Assertion insertion -/

/-- Source insertion freshness is sufficient for the shipped database's
global object namespace, including labels of hypotheses retired by a scope. -/
theorem runtimeLabelFresh_of_sourceInsert {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after) :
    db.find? label = none :=
  agreement.objectNamespace.find?_eq_none
    (insertAssertion?_label_fresh inserted)

/-- On that source-fresh branch, the shipped insertion is exactly one object
map extension. -/
theorem runtimeInsert_eq_of_sourceInsert {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after)
    (pos : Pos) :
    db.insert pos label
        (.assert formula.toRuntime (mandatoryFrame before formula).toRuntime) =
      { db with objects :=
          (db.objects.insert label
            (.assert formula.toRuntime
              (mandatoryFrame before formula).toRuntime label)) } := by
  have absent := runtimeLabelFresh_of_sourceInsert agreement inserted
  simp [DB.insert, DB.error, agreement.errorFree, absent]

/-- The real implementation insertion extends the permanent object namespace
by exactly the label added by the source transition. -/
theorem runtimeNamespaceAfterInsert {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after)
    (pos : Pos) :
    RuntimeObjectNamespaceAgrees
      (db.insert pos label
        (.assert formula.toRuntime (mandatoryFrame before formula).toRuntime))
      after := by
  let insertedDB :=
    db.insert pos label
      (.assert formula.toRuntime (mandatoryFrame before formula).toRuntime)
  have insertEq : insertedDB =
      { db with objects :=
          (db.objects.insert label
            (.assert formula.toRuntime
              (mandatoryFrame before formula).toRuntime label)) } :=
    runtimeInsert_eq_of_sourceInsert agreement inserted pos
  have namesEq := insertAssertion?_objectNames inserted
  refine
    { errorFree := ?_
      occupied_iff := ?_ }
  · change insertedDB.error? = none
    rw [insertEq]
    exact agreement.errorFree
  · intro candidate
    change insertedDB.find? candidate ≠ none ↔
      candidate ∈ after.objectNames
    rw [insertEq, namesEq]
    by_cases same : candidate = label
    · subst candidate
      simp [DB.find?]
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
      simpa [DB.find?, same] using
        agreement.objectNamespace.occupied_iff candidate

/-- All non-projection dimensions of source/runtime agreement are preserved
by assertion insertion.  The remaining premise is deliberately the exact
post-insertion call to the shared projector; it is the isolated hash-map /
canonical-order representation theorem, not a semantic assumption hidden in
the relation. -/
theorem RuntimeDBAgrees.insertAssertion_of_projection {db : RuntimeDB}
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (agreement : RuntimeDBAgrees db before)
    (inserted : insertAssertion? before label formula = some after)
    (pos : Pos)
    (postProjection :
      projectSourcePrefix?
          (db.insert pos label
            (.assert formula.toRuntime
              (mandatoryFrame before formula).toRuntime)) =
        some (runtimePrefix after).toProjection) :
    RuntimeDBAgrees
      (db.insert pos label
        (.assert formula.toRuntime (mandatoryFrame before formula).toRuntime))
      after := by
  have insertEq := runtimeInsert_eq_of_sourceInsert agreement inserted pos
  have afterEq := insertAssertion?_eq_some_state inserted
  subst after
  refine
    { projection := postProjection
      objectNamespace := runtimeNamespaceAfterInsert agreement inserted pos
      rawFrame := ?_
      activeVariables := ?_
      scopeStack := ?_ }
  · rw [insertEq]
    exact agreement.rawFrame
  · rw [insertEq]
    exact agreement.activeVariables
  · rw [insertEq]
    exact agreement.scopeStack

/-! ## Scope evolution -/

/-- The source `$\{` transition and the shipped `DB.pushScope` transition
preserve the complete agreement.  The saved runtime size is obtained from the
raw-frame field, not from the filtered proof-facing caller frame. -/
theorem RuntimeDBAgrees.pushScope {db : RuntimeDB}
    {before after : SourceState}
    (agreement : RuntimeDBAgrees db before)
    (opened : openScope? before = some after) :
    RuntimeDBAgrees db.pushScope after := by
  have shape := openScope?_eq_some_shape opened
  subst after
  have hdj : db.frame.dj.size = before.activeDistinctVariables.length := by
    calc
      db.frame.dj.size = db.frame.dj.toList.length := by simp
      _ = before.activeDistinctVariables.length :=
        congrArg List.length agreement.rawFrame.1
  have hhyps : db.frame.hyps.size = before.activeHypotheses.length := by
    calc
      db.frame.hyps.size = db.frame.hyps.toList.length := by simp
      _ = (before.activeHypotheses.map HypothesisView.label).length :=
        congrArg List.length agreement.rawFrame.2
      _ = before.activeHypotheses.length := by simp
  refine
    { projection := ?_
      objectNamespace := ?_
      rawFrame := agreement.rawFrame
      activeVariables := ?_
      scopeStack := ?_ }
  · rw [projectSourcePrefix?_pushScope]
    simpa [runtimePrefix, SourceState.callerFrame,
      SourceState.proofDistinctVariables,
      SourceState.activeFloatingVariables] using agreement.projection
  · refine
      { errorFree := ?_
        occupied_iff := ?_ }
    · exact agreement.objectNamespace.errorFree
    · intro label
      simpa [DB.pushScope, Metamath.Verify.DB.find?,
        SourceState.objectNames] using
        agreement.objectNamespace.occupied_iff label
  · simpa [DB.pushScope] using agreement.activeVariables.pushScope
      { activeVariableLength := before.activeVariables.length
        activeHypothesisLength := before.activeHypotheses.length
        activeDistinctLength := before.activeDistinctVariables.length } rfl
  · simp [DB.pushScope, runtimeScopeSizes, ScopeBoundary.runtimeSize,
      agreement.scopeStack]
    simp [Metamath.Verify.Frame.size, hdj, hhyps]

/-- The newest runtime scope boundary is exactly the newest source boundary.
This is the structural hinge for scope-pop refinement. -/
theorem RuntimeDBAgrees.backScope_eq {db : RuntimeDB}
    {state : SourceState} (agreement : RuntimeDBAgrees db state)
    {boundary : ScopeBoundary} {rest : List ScopeBoundary}
    (hscopes : state.scopes = boundary :: rest) :
    db.scopes.back? = some (ScopeBoundary.runtimeSize boundary) := by
  have scopesList : db.scopes.toList =
      rest.reverse.map ScopeBoundary.runtimeSize ++
        [ScopeBoundary.runtimeSize boundary] := by
    rw [agreement.scopeStack]
    unfold runtimeScopeSizes
    rw [hscopes]
    simp
  have scopesArray : db.scopes =
      (rest.reverse.map ScopeBoundary.runtimeSize ++
        [ScopeBoundary.runtimeSize boundary]).toArray := by
    simpa using congrArg List.toArray scopesList
  rw [scopesArray]
  simp

/-- Scope-pop refinement with the proof-facing post-projection exposed as
the single semantic premise.  Raw-frame restoration, permanent namespace,
and stack evolution are derived here from the source/runtime agreement. -/
theorem RuntimeDBAgrees.popScope_of_projection {db : RuntimeDB}
    {before after : SourceState} (agreement : RuntimeDBAgrees db before)
    (pos : Pos) (closed : closeScope? before = some after)
    (postProjection :
      projectSourcePrefix? (db.popScope pos) =
        some (runtimePrefix after).toProjection) :
    RuntimeDBAgrees (db.popScope pos) after := by
  obtain ⟨boundary, rest, hscopes, shape⟩ :=
    closeScope?_eq_some_shape closed
  subst after
  have hback : db.scopes.back? =
      some (ScopeBoundary.runtimeSize boundary) :=
    agreement.backScope_eq hscopes
  have popEq : db.popScope pos =
      { db with
        frame := db.frame.shrink (ScopeBoundary.runtimeSize boundary)
        scopes := db.scopes.pop
        activeVars := db.activeVars.filter
          (fun entry => entry.2 ≤ db.scopes.size - 1) } := by
    simp [Metamath.Verify.DB.popScope, hback]
  have scopesList : db.scopes.toList =
      rest.reverse.map ScopeBoundary.runtimeSize ++
        [ScopeBoundary.runtimeSize boundary] := by
    rw [agreement.scopeStack]
    unfold runtimeScopeSizes
    rw [hscopes]
    simp
  have scopesArray : db.scopes =
      (rest.reverse.map ScopeBoundary.runtimeSize ++
        [ScopeBoundary.runtimeSize boundary]).toArray := by
    simpa using congrArg List.toArray scopesList
  have poppedScopes : db.scopes.pop.toList =
      rest.reverse.map ScopeBoundary.runtimeSize := by
    rw [scopesArray]
    simp
  have scopeSize : db.scopes.size = (boundary :: rest).length := by
    calc
      db.scopes.size = db.scopes.toList.length := by simp
      _ = (runtimeScopeSizes before).length :=
        congrArg List.length agreement.scopeStack
      _ = (boundary :: rest).length := by
        simp [runtimeScopeSizes, hscopes]
  refine
    { projection := postProjection
      objectNamespace := ?_
      rawFrame := ?_
      activeVariables := ?_
      scopeStack := ?_ }
  · refine
      { errorFree := ?_
        occupied_iff := ?_ }
    · rw [popEq]
      exact agreement.objectNamespace.errorFree
    · intro label
      rw [popEq]
      simpa [Metamath.Verify.DB.find?, SourceState.objectNames] using
        agreement.objectNamespace.occupied_iff label
  · constructor
    · rw [popEq]
      simp [Metamath.Verify.Frame.shrink, ScopeBoundary.runtimeSize,
        agreement.rawFrame.1]
      rfl
    · rw [popEq]
      simp [Metamath.Verify.Frame.shrink, ScopeBoundary.runtimeSize,
        agreement.rawFrame.2]
  · rw [popEq]
    have activeAgreement := agreement.activeVariables
    rw [hscopes] at activeAgreement
    simpa [scopeSize] using activeAgreement.popScope
  · rw [popEq]
    simpa [runtimeScopeSizes] using poppedScopes

/-- The source-only completion marker after `$\}` leaves the shipped database
unchanged and therefore preserves all agreement dimensions. -/
theorem RuntimeDBAgrees.completeBlock {db : RuntimeDB}
    {before after : SourceState} (agreement : RuntimeDBAgrees db before)
    (completed : completeBlock? before = some after) :
    RuntimeDBAgrees db after := by
  have shape := completeBlock?_eq_some_shape completed
  subst after
  refine
    { projection := ?_
      objectNamespace := ?_
      rawFrame := agreement.rawFrame
      activeVariables := agreement.activeVariables
      scopeStack := ?_ }
  · simpa [runtimePrefix, SourceState.callerFrame,
      SourceState.proofDistinctVariables,
      SourceState.activeFloatingVariables] using agreement.projection
  · refine
      { errorFree := agreement.objectNamespace.errorFree
        occupied_iff := ?_ }
    intro label
    simpa [SourceState.objectNames] using
      agreement.objectNamespace.occupied_iff label
  · simpa [runtimeScopeSizes] using agreement.scopeStack

end Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
