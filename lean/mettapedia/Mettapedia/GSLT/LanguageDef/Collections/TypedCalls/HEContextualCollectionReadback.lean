import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceAudit

/-!
# Collection replay under a retained contextual caller

Captured child frames may already contain all caller constraints. Their
actual snapshot restore can then retain the exact captured frame. A separate
annotated read condition governs the packed values that the chain passes
through its caller; erased constraint equivalence alone cannot justify it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualCollectionReadback

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation

/-- An already retained caller adds no constraint or support. The snapshot
unifier keeps the captured annotated environment itself, not an erased copy. -/
theorem snapshot_absorbs (policy : Policy) (caller captured : Frame)
    (support : ∀ name ∈ specBindingVars caller.bindings, name ∈ specBindingVars captured.bindings)
    (entails : ∀ valuation, TypeBindingSatisfied valuation captured.bindings →
      TypeBindingSatisfied valuation caller.bindings) :
    Frame.SnapshotMergeRel policy captured caller captured := by
  have agreement : BindingSourceAgreement captured.bindings
      ⟨captured.bindings.assignments ++ caller.bindings.assignments,
        captured.bindings.equalities ++ caller.bindings.equalities⟩ := by
    constructor
    · intro valuation
      rw [bindingSatisfied_append_iff]
      exact ⟨fun model => ⟨model, entails valuation model⟩, And.left⟩
    · intro name
      rw [mem_specBindingVars_append]
      exact ⟨Or.inl, fun member => member.elim id (support name)⟩
  have model := (captured.certified.theory (Theory.presentedValuation _)).mp
    (Theory.normal_presentedValuation_satisfied captured.certified.normal)
  have packets := (caller.packet_theory (Theory.presentedValuation _)).mpr (entails _ model)
  refine .merged ⟨agreement, captured.certified.satisfiable⟩ (.ordinary (.identical ?_))
  simpa only [Entry.Value.erase_substitute_environment,
    Theory.applyTypeValuation_presented_eq_apply] using packets

/-- The actual contextual unifier only adds assigned keys; old keys are
not removed when their values are updated by a later private constraint. -/
theorem unifier_keys_mono {rebuilding : Entry.RebuildPolicy}
    {before after : Entry.Value.Environment} {left right : Entry.Value}
    (source : Entry.Value.UnifyRel rebuilding before left right after) :
    ∀ name ∈ (Entry.Value.eraseEnvironment before).keys,
      name ∈ (Entry.Value.eraseEnvironment after).keys := by
  let property := fun first last : Entry.Value.Environment =>
    ∀ name ∈ (Entry.Value.eraseEnvironment first).keys, name ∈ (Entry.Value.eraseEnvironment last).keys
  let applied := fun first a b last (_ : Entry.Value.AppliedUnifyRel rebuilding first a b last) => property first last
  let ordinary := fun first a b last (_ : Entry.Value.UnifyRel rebuilding first a b last) => property first last
  let many := fun first as_ bs last (_ : Entry.Value.UnifyListRel rebuilding first as_ bs last) => property first last
  have bound (first : Entry.Value.Environment) (key : String) (value : Entry.Value) :
      property first (Entry.Value.bind rebuilding first key value) := by
    intro name member
    rw [Entry.Value.erase_bind, TypeSubst.keys_bind]
    by_cases same : name = key
    · simp [same]
    · simp [member, same]
  have identical {first a b} (same : a.erase = b.erase) :
      applied first a b first (.identical same) := fun _ => id
  have bindLeft {first name value} (absent : name ∉ TypeSubst.typeVars value.erase) :
      applied first (.var name) value (Entry.Value.bind rebuilding first name value) (.bindLeft absent) :=
    bound first name value
  have bindRight {first value name} (notVar : ∀ key, value.erase ≠ .var key)
      (absent : name ∉ TypeSubst.typeVars value.erase) :
      applied first value (.var name) (Entry.Value.bind rebuilding first name value) (.bindRight notVar absent) :=
    bound first name value
  have expression {first last as_ bs previous next}
      (children : Entry.Value.UnifyListRel rebuilding first as_ bs last) (ih : many first as_ bs last children) :
      applied first (.expression previous as_) (.expression next bs) last (.expression children) := ih
  have materialized {first last a b}
      (derived : Entry.Value.AppliedUnifyRel rebuilding first
        (Entry.Value.substitute rebuilding (Entry.Value.resolve first) a)
        (Entry.Value.substitute rebuilding (Entry.Value.resolve first) b) last)
      (ih : applied first _ _ last derived) : ordinary first a b last (.ordinary derived) := ih
  have nil (first) : many first [] [] first (.nil first) := fun _ => id
  have cons {first next last a b as_ bs}
      (head : Entry.Value.UnifyRel rebuilding first a b next)
      (tail : Entry.Value.UnifyListRel rebuilding next as_ bs last)
      (ih : ordinary first a b next head) (it : many next as_ bs last tail) :
      many first (a :: as_) (b :: bs) last (.cons head tail) :=
    fun name present => it name (ih name present)
  exact Entry.Value.UnifyRel.rec (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
    identical bindLeft bindRight @expression materialized nil cons source

/-- A normalized child value mentions no assigned child key. If the child
keeps the caller keys, caller readback cannot change any nested readiness mark. -/
theorem caller_read_of_child_normalized (policy : Policy) (caller captured : Frame)
    (keys : ∀ name ∈ (Entry.Value.eraseEnvironment caller.environment).keys,
      name ∈ (Entry.Value.eraseEnvironment captured.environment).keys)
    (value : Entry.Value) :
    caller.read policy (captured.read policy value) = captured.read policy value := by
  apply FrameUnassignedOn.read_eq
  intro name used oldKey
  exact FrameUnassignedOn.after_read policy captured value name used (keys name oldKey)

theorem caller_read_of_actual_unification (policy : Policy) (caller captured : Frame)
    (left right value : Entry.Value)
    (source : Entry.Value.UnifyRel policy.rebuilding caller.environment left right captured.environment) :
    caller.read policy (captured.read policy value) = captured.read policy value :=
  caller_read_of_child_normalized policy caller captured (unifier_keys_mono source) value

/-- Actual source conjunction, rather than an annotation or desired result,
discharges the retained-caller restoration condition. -/
theorem snapshot_absorbs_source_merge (policy : Policy) (caller captured : Frame) (added : Bindings)
    (merged : LogicalMergeRel added caller.bindings captured.bindings) :
    Frame.SnapshotMergeRel policy captured caller captured :=
  snapshot_absorbs policy caller captured
    (fun name present => (merged.support name).mpr (Or.inr present))
    (fun valuation model => ((merged.solutions valuation).mp model).2)

/-- Logical entailment gives ordinary erased substitution absorption. It
does not by itself supply the stronger annotated readback law above. -/
theorem erased_read_absorbs (policy : Policy) (caller captured : Frame)
    (entails : ∀ valuation, TypeBindingSatisfied valuation captured.bindings →
      TypeBindingSatisfied valuation caller.bindings) (value : Entry.Value) :
    (captured.read policy (caller.read policy value)).erase = (captured.read policy value).erase := by
  simp only [Frame.read, Entry.Value.erase_substitute_environment]
  exact caller.certified.absorbs captured.certified entails value.erase

theorem restore_stored_caller {Context World : Type} {services : SnapshotServices Context World}
    {label world policy caller rows pairs saved}
    (paired : List.Forall₂ (StoredPairRel services label world) rows pairs)
    (retained : ∀ row ∈ rows,
      Frame.SnapshotMergeRel policy row.2 caller row.2) :
    RestoreRowsRel services label world policy caller pairs saved (saved.reverse ++ rows) := by
  induction paired generalizing saved with
  | nil => simpa only [List.append_nil] using (RestoreRowsRel.nil (saved := saved))
  | @cons row pair rows pairs related paired ih =>
      obtain ⟨payload, rfl, loaded⟩ := related
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        RestoreRowsRel.cons loaded (retained row (by simp))
          (ih (fun item member => retained item (List.mem_cons_of_mem _ member)) (saved := (row.1, row.2) :: saved))

theorem stored_pair_read {Context World : Type} {services : SnapshotServices Context World}
    {label world row pair} (policy : Policy) (caller : Frame)
    (stored : StoredPairRel services label world row pair)
    (stable : caller.read policy row.1 = row.1) : caller.read policy pair = pair := by
  obtain ⟨payload, rfl, _⟩ := stored
  simpa only [Frame.read, Entry.Value.substitute,
    HEFreshEquationFrames.Range.active_rebuild, List.map_cons, List.map_nil] using
    congrArg (fun value => Entry.Value.expression .active [value, .grounded payload]) stable

theorem captured_read {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows packed afterWorld}
    (source : CaptureRowsRel services label world rows [] packed afterWorld)
    (policy : Policy) (caller : Frame)
    (stable : ∀ row ∈ survivingRows rows, caller.read policy row.1 = row.1) :
    caller.read policy packed = packed := by
  obtain ⟨pairs, shape, paired⟩ := source.encoded laws
  have shape' : packed = .expression .active pairs := by simpa using shape
  rw [shape']
  have mapStable : ∀ {rs ps}, List.Forall₂ (StoredPairRel services label afterWorld) rs ps →
      (∀ row ∈ rs, caller.read policy row.1 = row.1) → ps.map (caller.read policy) = ps := by
    intro rs ps related
    induction related with
    | nil => intro _; rfl
    | @cons row pair rs ps head tail ih =>
        intro fixed
        rw [List.map_cons, stored_pair_read policy caller head (fixed row (by simp)),
          ih (fun item present => fixed item (List.mem_cons_of_mem _ present))]
  have mapped := mapStable paired stable
  change pairs.map (Entry.Value.substitute policy.rebuilding (Entry.Value.resolve caller.environment)) = pairs at mapped
  simpa only [Frame.read, Entry.Value.substitute, HEFreshEquationFrames.Range.active_rebuild] using
    congrArg (Entry.Value.expression .active) mapped

/-- Capture and restore traverse the actual token-bearing pair list.
The caller read in between retains the entire annotated packet. -/
theorem capture_roundtrip {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows packed afterWorld}
    (source : CaptureRowsRel services label world rows [] packed afterWorld)
    (policy : Policy) (caller : Frame)
    (stable : ∀ row ∈ survivingRows rows, caller.read policy row.1 = row.1)
    (retained : ∀ row ∈ survivingRows rows, Frame.SnapshotMergeRel policy row.2 caller row.2) :
    ∃ pairs, packed = .expression .active pairs ∧ caller.read policy packed = packed ∧
      RestoreRowsRel services label afterWorld policy caller pairs [] (survivingRows rows) := by
  obtain ⟨pairs, shape, paired⟩ := source.encoded laws
  exact ⟨pairs, by simpa using shape, captured_read laws source policy caller stable,
    by simpa only [List.reverse_nil, List.nil_append] using restore_stored_caller (saved := []) paired retained⟩

theorem collection_roundtrip {Context World : Type} {environment : WorldEnvironment Context World}
    {snapshots : SnapshotServices Context World} (provided : environment.services.snapshots = some snapshots)
    (laws : snapshots.Laws) {label world childWorld afterWorld live scope caller operand rows packed policy}
    (frame : Frame)
    (child : Stateful.MinimalRel environment label world ((collectionReplay operand).erase :: live) scope
      (some (collectionReplay operand).erase) operand frame rows childWorld (policy := policy))
    (captured : CaptureRowsRel snapshots label childWorld rows [] packed afterWorld)
    (stable : ∀ row ∈ survivingRows rows, frame.read policy row.1 = row.1)
    (retained : ∀ row ∈ survivingRows rows, Frame.SnapshotMergeRel policy row.2 frame row.2) :
    Stateful.MinimalRel environment label world live scope caller (collectionReplay operand) frame
      (survivingRows rows) afterWorld (policy := policy) := by
  obtain ⟨pairs, rfl, read, restored⟩ := capture_roundtrip laws captured policy frame stable retained
  refine .chain (world1 := afterWorld) (selected := [(.expression .active pairs, frame)])
    (.collapseBind provided (by simpa [collectionReplay, Entry.Value.erase] using child) captured) ?_
  apply Stateful.BoundaryBatchRel.single_iff.mpr
  apply Stateful.BoundaryRel.chain
  simpa only [read, substituteBinder_superpose] using
    (Stateful.MinimalRel.superposeBind (environment := environment) (policy := policy)
      (readiness := .active) provided restored)

def heldOperand {Context World : Type} (environment : WorldEnvironment Context World)
    (label : Context) (value : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "metta", value, .symbol "Atom", .grounded (environment.services.contextPayload label)]

/-- A complete source instance with arbitrary open values and caller frames.
The child is the actual metta/Atom instruction, whose result is earned by
source entry. Idempotence of its annotated read discharges capture stability. -/
theorem held_source_roundtrip {Context World : Type} (environment : WorldEnvironment Context World)
    {snapshots : SnapshotServices Context World} (provided : environment.services.snapshots = some snapshots)
    (laws : snapshots.Laws)
    (available : ∀ label world frame, ∃ payload after, snapshots.capture label world frame payload after)
    (policy : Policy) (label : Context) (world : World) (frame : Frame) (value : Entry.Value)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    ∃ afterWorld,
      Stateful.MinimalRel environment label world live scope caller
        (collectionReplay (heldOperand environment label value)) frame
        (survivingRows [(frame.read policy value, frame)]) afterWorld (policy := policy) := by
  have child : Stateful.MinimalRel environment label world
      ((collectionReplay (heldOperand environment label value)).erase :: live) scope
      (some (collectionReplay (heldOperand environment label value)).erase)
      (heldOperand environment label value) frame [(frame.read policy value, frame)] world (policy := policy) := by
    apply Stateful.MinimalRel.metta
    simpa only [Entry.Value.erase, Atom.atomType] using
      HEHeldSourceArguments.held environment policy label world _ scope value frame
  obtain ⟨packed, afterWorld, captured⟩ := CaptureRowsRel.total snapshots available label world
    [(frame.read policy value, frame)] []
  refine ⟨afterWorld, collection_roundtrip (environment := environment) (live := live) (caller := caller)
    provided laws frame child captured ?_ ?_⟩
  · intro row member
    have same := List.mem_singleton.mp (List.mem_of_mem_filter member)
    subst row
    exact frame.read_idempotent policy value
  · intro row member
    have same := List.mem_singleton.mp (List.mem_of_mem_filter member)
    subst row
    exact snapshot_absorbs policy frame frame (fun _ => id) (fun _ => id)

theorem held_source_retained_run {Context World : Type} (environment : WorldEnvironment Context World)
    {snapshots : SnapshotServices Context World} (provided : environment.services.snapshots = some snapshots)
    (laws : snapshots.Laws)
    (available : ∀ label world frame, ∃ payload after, snapshots.capture label world frame payload after)
    (policy : Policy) (label : Context) (world : World) (frame : Frame) (value : Entry.Value)
    (live : List Atom) (scope : List String) (caller : Option Atom)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ afterWorld,
      RecursiveMachine.Contextual.WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        ⟨world, label, .work (.minimal live scope caller (collectionReplay (heldOperand environment label value)) frame),
          stack, emitted⟩
        ⟨afterWorld, label, .returning (survivingRows [(frame.read policy value, frame)]), stack, emitted⟩ := by
  obtain ⟨afterWorld, source⟩ := held_source_roundtrip environment provided laws available policy label world frame value live scope caller
  exact ⟨afterWorld, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.task_complete
      (task := .minimal live scope caller (collectionReplay (heldOperand environment label value)) frame) source stack) emitted⟩

namespace Controls

def snapshots : SnapshotServices Unit (Unit × List Frame) := SnapshotServices.appendModel Unit Unit

def services : WorldServices Unit (Unit × List Frame) where
  contextPayload _ := .int 0
  nativeCall _ _ _ _ _ _ _ _ := False
  snapshots := some snapshots

def dispatch : Spec.Eval.GroundedDispatch where
  executable _ := False
  outcome _ _ _ := False

def environment : WorldEnvironment Unit (Unit × List Frame) where
  view _ _ := Space.empty
  services := services
  dispatch := dispatch
  lookup := scopedLookup

def value : Entry.Value := Entry.Value.Controls.heldNested
def callerFrame : Frame := Completed.Controls.argumentAliasFrame

def operand : Entry.Value := .expression .active
  [.symbol "metta", value, .symbol "Atom", .grounded (.int 0)]

def packed : Entry.Value := .expression .active
  [.expression .active [value, .grounded (.int 0)]]

theorem value_fixed (policy : Policy) (frame : Frame) : frame.read policy value = value := by
  apply Frame.read_variable_free
  intro name occurs
  have member := Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
  simp [value, Entry.Value.Controls.heldNested, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList] at member

theorem actual_child (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.MinimalRel environment () ((), []) live scope caller operand callerFrame
      [(value, callerFrame)] ((), []) (policy := policy) := by
  apply Stateful.MinimalRel.metta
  simpa only [value_fixed, Entry.Value.erase, Atom.atomType] using
    HEHeldSourceArguments.held environment policy () ((), []) live scope value callerFrame

theorem actual_capture :
    CaptureRowsRel snapshots () ((), []) [(value, callerFrame)] [] packed ((), [callerFrame]) := by
  apply CaptureRowsRel.cons (payload := .int 0) (nextWorld := ((), [callerFrame]))
  · simp [value, Entry.Value.Controls.heldNested, Entry.Value.erase, Atom.empty]
  · exact ⟨rfl, rfl⟩
  · exact .nil

/-- The source operand itself earns the captured result. Its nonempty
caller aliases and nested held marks survive the whole collection replay. -/
theorem aliased_caller_replay (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.MinimalRel environment () ((), []) live scope caller (collectionReplay operand) callerFrame
      [(value, callerFrame)] ((), [callerFrame]) (policy := policy) := by
  have source := collection_roundtrip (environment := environment) (snapshots := snapshots)
    (live := live) (caller := caller) rfl
    (SnapshotServices.appendModel_laws Unit Unit) callerFrame
    (actual_child policy _ scope _) actual_capture
    (by
      intro row member
      have same : row = (value, callerFrame) := by
        simpa [survivingRows, value, Entry.Value.Controls.heldNested, Entry.Value.erase, Atom.empty] using member
      subst row
      exact value_fixed policy callerFrame)
    (by
      intro row member
      have same : row = (value, callerFrame) := by
        simpa [survivingRows, value, Entry.Value.Controls.heldNested, Entry.Value.erase, Atom.empty] using member
      subst row
      exact snapshot_absorbs policy callerFrame callerFrame (fun _ => id) (fun _ => id))
  simpa [survivingRows, value, Entry.Value.Controls.heldNested, Entry.Value.erase, Atom.empty] using source

def literalPairs (values : List Entry.Value) : List Entry.Value :=
  values.map fun item => .expression .active [item, .grounded (.int 0)]

def literalRows (values : List Entry.Value) : List Result :=
  values.map fun item => (item, callerFrame)

def literalProducer (values : List Entry.Value) : Entry.Value :=
  .expression .active [.symbol "superpose-bind", .expression .active (literalPairs values)]

theorem stored_literals (values : List Entry.Value) :
    List.Forall₂ (StoredPairRel snapshots () ((), [callerFrame])) (literalRows values) (literalPairs values) := by
  induction values with
  | nil => exact .nil
  | cons item items ih =>
      exact .cons ⟨.int 0, rfl, 0, rfl, rfl⟩ ih

/-- A literal superpose-bind source instruction decodes each actual stored
frame. The input list is source data, not an evaluator-result oracle. -/
theorem literal_child (policy : Policy) (values : List Entry.Value)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.MinimalRel environment () ((), [callerFrame]) live scope caller (literalProducer values) callerFrame
      (literalRows values) ((), [callerFrame]) (policy := policy) := by
  apply Stateful.MinimalRel.superposeBind (snapshots := snapshots) rfl
  have restored := restore_stored_caller (policy := policy) (caller := callerFrame) (saved := [])
    (stored_literals values) (by
      intro row present
      obtain ⟨item, _, rfl⟩ := List.mem_map.mp present
      exact snapshot_absorbs policy callerFrame callerFrame (fun _ => id) (fun _ => id))
  simpa only [List.reverse_nil, List.nil_append] using restored

theorem finite_source_replay (policy : Policy) (values : List Entry.Value)
    (closed : ∀ item ∈ values, TypeSubst.typeVars item.erase = [])
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    ∃ afterWorld,
      Stateful.MinimalRel environment () ((), [callerFrame]) live scope caller
        (collectionReplay (literalProducer values)) callerFrame
        (survivingRows (literalRows values)) afterWorld (policy := policy) := by
  obtain ⟨packed, afterWorld, captured⟩ := CaptureRowsRel.total snapshots
    (SnapshotServices.appendModel_total Unit Unit) () ((), [callerFrame]) (literalRows values) []
  refine ⟨afterWorld, collection_roundtrip (environment := environment) (snapshots := snapshots)
    (live := live) (caller := caller) rfl (SnapshotServices.appendModel_laws Unit Unit) callerFrame
      (literal_child policy values _ scope _) captured ?_ ?_⟩
  · intro row member
    have original := List.mem_of_mem_filter member
    obtain ⟨item, present, rfl⟩ := List.mem_map.mp original
    apply Frame.read_variable_free
    intro name occurs
    have used := Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
    simp only [closed item present, List.not_mem_nil] at used
  · intro row member
    have original := List.mem_of_mem_filter member
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp original
    exact snapshot_absorbs policy callerFrame callerFrame (fun _ => id) (fun _ => id)

def errorValue : Entry.Value := .expression .held [.symbol "Error", .symbol "input", .symbol "BadType"]

/-- Final Empty is removed, while the intervening error and both equal
marked values survive in source order. The caller frame is not empty. -/
theorem duplicate_error_empty_control (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom) :
    ∃ afterWorld,
      Stateful.MinimalRel environment () ((), [callerFrame]) live scope caller
        (collectionReplay (literalProducer [value, .symbol "Empty", errorValue, value])) callerFrame
        [(value, callerFrame), (errorValue, callerFrame), (value, callerFrame)] afterWorld (policy := policy) := by
  have complete := finite_source_replay policy [value, .symbol "Empty", errorValue, value]
    (by
      intro item present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl | rfl <;>
        simp [value, errorValue, Entry.Value.Controls.heldNested, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])
    live scope caller
  simpa [survivingRows, literalRows, value, errorValue, Entry.Value.Controls.heldNested, Entry.Value.erase, Atom.empty] using complete

/-- Equal erased binding theories can disagree on nested occurrence marks.
Thus erased absorption cannot be promoted to an annotated equality. -/
theorem erased_theory_does_not_supply_annotated_absorption (policy : Policy) :
    ∃ captured : Frame,
      BindingSourceAgreement Completed.Controls.heldFrame.bindings captured.bindings ∧
      captured.read policy (Completed.Controls.heldFrame.read policy (.var "x")) ≠
        captured.read policy (.var "x") := by
  obtain ⟨captured, agreement, _, different⟩ :=
    Completed.Controls.constraint_agreement_alone_does_not_preserve_readiness policy
  have held : Completed.Controls.heldFrame.read policy (.var "x") = value :=
    Entry.Value.Controls.nested_statuses_retained policy.rebuilding
  refine ⟨captured, agreement, ?_⟩
  rw [held, value_fixed]
  intro same
  exact different (by simpa only [held] using congrArg Entry.Value.status same)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEContextualCollectionReadback
