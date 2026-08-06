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

/-- Erase the scope-history carrier before projection.  Projection observes
the current frame and global object map; scope history is related separately
by `RuntimeDBAgrees.scopeStack`. -/
def projectionDB (db : RuntimeDB) : RuntimeDB :=
  { db with scopes := #[] }

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
  scopeStack : db.scopes.toList = runtimeScopeSizes state

theorem RuntimeDBAgrees.errorFree {db : RuntimeDB} {state : SourceState}
    (agreement : RuntimeDBAgrees db state) : db.error? = none :=
  agreement.objectNamespace.errorFree

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
      scopeStack := ?_ }
  · rw [insertEq]
    exact agreement.rawFrame
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
        scopes := db.scopes.pop } := by
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
  refine
    { projection := postProjection
      objectNamespace := ?_
      rawFrame := ?_
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
