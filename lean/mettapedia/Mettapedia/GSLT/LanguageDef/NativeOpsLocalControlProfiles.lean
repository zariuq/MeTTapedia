import Mettapedia.GSLT.LanguageDef.NativeOpsStatementPrimitives

/-!
# Local types through declarations, writes and lexical cleanup

Coherence constrains bindings which share one local cell. It supplies neither
cell existence nor pointee typing. The profile is derived through the actual
parameter/declaration operations; successful local stores and scope cleanup
retain the corresponding tags.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

/-- Aliased local declarations must agree on the declared cell type. -/
def LocalTypesCoherent (bindings : List LocalBinding) : Prop :=
  ∀ first ∈ bindings, ∀ second ∈ bindings, first.position = second.position → first.type = second.type

structure SourceFrameExtends (marker current : SourceFrame) : Prop where
  storage : current.storage = marker.storage
  counter : marker.nextLocal ≤ current.nextLocal
  visible : ∀ binding ∈ marker.bindings, binding ∈ current.bindings

theorem local_types_empty : LocalTypesCoherent [] := by
  intro binding member
  cases member

theorem local_types_cons_fresh {bindings : List LocalBinding}
    (coherent : LocalTypesCoherent bindings) (position : Nat)
    (below : ∀ binding ∈ bindings, binding.position < position) (name : String) (type : NativeType) :
    LocalTypesCoherent (⟨name, type, position⟩ :: bindings) := by
  intro first firstMember second secondMember samePosition
  rcases List.mem_cons.mp firstMember with firstNew | firstOld
  · cases firstNew
    rcases List.mem_cons.mp secondMember with secondNew | secondOld
    · cases secondNew
      rfl
    · exact False.elim ((Nat.ne_of_lt (below second secondOld)) samePosition.symm)
  · rcases List.mem_cons.mp secondMember with secondNew | secondOld
    · cases secondNew
      exact False.elim ((Nat.ne_of_lt (below first firstOld)) samePosition)
    · exact coherent first firstOld second secondOld samePosition

theorem source_declare_local_coherent {World : Type} {frame : SourceFrame} {state : SourceState World}
    (coherent : LocalTypesCoherent frame.bindings) (below : SourceLocalsBelow frame)
    (name : String) (type : NativeType) (value : SourceValue) :
    LocalTypesCoherent (sourceDeclareLocal frame state name type value).1.bindings :=
  local_types_cons_fresh coherent frame.nextLocal below name type

theorem target_declare_local_coherent {World : Type} {frame : TargetFrame} {state : TargetState World}
    (coherent : LocalTypesCoherent frame.bindings) (below : TargetLocalsBelow frame)
    (name : String) (type : NativeType) (value : TargetValue) :
    LocalTypesCoherent (targetDeclareLocal frame state name type value).1.bindings :=
  local_types_cons_fresh coherent frame.nextLocal below name type

theorem related_local_types {source : SourceFrame} {target : TargetFrame}
    (frames : FrameRelated source target) :
    LocalTypesCoherent source.bindings ↔ LocalTypesCoherent target.bindings := by
  rw [frames.bindings]

theorem source_bind_parameters_coherent {World : Type} (parameters : List Parameter)
    {arguments : List SourceValue} {frame outFrame : SourceFrame} {state outState : SourceState World}
    (coherent : LocalTypesCoherent frame.bindings) (below : SourceLocalsBelow frame)
    (bound : sourceBindParameters parameters arguments frame state = some (outFrame, outState)) :
    LocalTypesCoherent outFrame.bindings ∧ SourceLocalsBelow outFrame := by
  induction parameters generalizing arguments frame state with
  | nil =>
      cases arguments with
      | nil =>
          cases Option.some.inj bound
          exact ⟨coherent, below⟩
      | cons value rest => cases bound
  | cons parameter parameters ih =>
      cases arguments with
      | nil => cases bound
      | cons value values =>
          exact ih (source_declare_local_coherent coherent below parameter.name parameter.type value)
            (source_declare_local_below below parameter.name parameter.type value) bound

theorem target_bind_parameters_coherent {World : Type} (parameters : List Parameter)
    {arguments : List TargetValue} {frame outFrame : TargetFrame} {state outState : TargetState World}
    (coherent : LocalTypesCoherent frame.bindings) (below : TargetLocalsBelow frame)
    (bound : targetBindParameters parameters arguments frame state = some (outFrame, outState)) :
    LocalTypesCoherent outFrame.bindings ∧ TargetLocalsBelow outFrame := by
  induction parameters generalizing arguments frame state with
  | nil =>
      cases arguments with
      | nil =>
          cases Option.some.inj bound
          exact ⟨coherent, below⟩
      | cons value rest => cases bound
  | cons parameter parameters ih =>
      cases arguments with
      | nil => cases bound
      | cons value values =>
          exact ih (target_declare_local_coherent coherent below parameter.name parameter.type value)
            (target_declare_local_below below parameter.name parameter.type value) bound

theorem source_local_binding_selected {frame : SourceFrame} {name : String} {type : NativeType}
    {address : Address} (typed : lookupVariable (sourceFrameScope frame) name = some type)
    (located : sourceLocalAddress frame name = some address) :
    ∃ binding ∈ frame.bindings, binding.type = type ∧
      address = ⟨frame.storage, binding.position, []⟩ := by
  have lookup : lookupVariable (sourceFrameScope frame) name =
      (frame.bindings.find? (fun binding => binding.name == name)).map LocalBinding.type := by
    simp only [lookupVariable, sourceFrameScope, List.find?_map, Option.map_map]
    rfl
  rw [lookup] at typed
  cases selected : frame.bindings.find? (fun binding => binding.name == name) with
  | none =>
      simp only [sourceLocalAddress, selected, bind, Option.bind_none] at located
      cases located
  | some binding =>
      have typeSame : binding.type = type := by
        simpa only [selected, Option.map_some, Option.some.injEq] using typed
      have addressSame : ⟨frame.storage, binding.position, []⟩ = address := by
        simpa only [sourceLocalAddress, selected, bind, pure, Option.bind_some, Option.some.injEq] using located
      exact ⟨binding, List.mem_of_find?_eq_some selected, typeSame, addressSame.symm⟩

theorem source_typed_local_has_address {frame : SourceFrame} {name : String} {type : NativeType}
    (typed : lookupVariable (sourceFrameScope frame) name = some type) :
    ∃ address, sourceLocalAddress frame name = some address := by
  have lookup : lookupVariable (sourceFrameScope frame) name =
      (frame.bindings.find? (fun binding => binding.name == name)).map LocalBinding.type := by
    simp only [lookupVariable, sourceFrameScope, List.find?_map, Option.map_map]
    rfl
  rw [lookup] at typed
  cases selected : frame.bindings.find? (fun binding => binding.name == name) with
  | none => simp only [selected, Option.map_none] at typed; cases typed
  | some binding =>
      exact ⟨⟨frame.storage, binding.position, []⟩,
        by simp only [sourceLocalAddress, selected, bind, pure, Option.bind_some]⟩

theorem source_local_write_tagged {frame : SourceFrame} {memory after : SourceMemory}
    (tagged : SourceLocalsTagged frame memory) (coherent : LocalTypesCoherent frame.bindings)
    {name : String} {type : NativeType} {address : Address} {value : SourceValue}
    (typed : lookupVariable (sourceFrameScope frame) name = some type)
    (located : sourceLocalAddress frame name = some address) (valueTag : SourceOuterTag type value)
    (written : sourceWrite memory address value = some after) : SourceLocalsTagged frame after := by
  obtain ⟨selected, selectedMember, selectedType, addressSame⟩ := source_local_binding_selected typed located
  subst address
  cases previous : memory.cells frame.storage selected.position with
  | none =>
      simp only [sourceWrite, previous, bind, Option.bind_none] at written
      cases written
  | some old =>
      have stored : sourceStoreCell memory frame.storage selected.position value = after := by
        simpa only [sourceWrite, previous, sourceWritePath, bind, Option.bind_some,
          Option.some.injEq] using written
      cases stored
      apply source_store_cell_tagged tagged frame.storage selected.position value
      intro binding member _ samePosition
      have typeSame := coherent binding member selected selectedMember samePosition.symm
      exact (typeSame.trans selectedType).symm ▸ valueTag

theorem source_frame_extends_refl (frame : SourceFrame) : SourceFrameExtends frame frame :=
  ⟨rfl, Nat.le_refl _, fun _ member => member⟩

theorem source_frame_extends_trans {first middle last : SourceFrame}
    (left : SourceFrameExtends first middle) (right : SourceFrameExtends middle last) :
    SourceFrameExtends first last :=
  ⟨right.storage.trans left.storage, left.counter.trans right.counter,
    fun binding member => right.visible binding (left.visible binding member)⟩

theorem source_declaration_extends {World : Type} (frame : SourceFrame) (state : SourceState World)
    (name : String) (type : NativeType) (value : SourceValue) :
    SourceFrameExtends frame (sourceDeclareLocal frame state name type value).1 :=
  ⟨rfl, Nat.le_succ _, fun _ member => List.mem_cons_of_mem _ member⟩

theorem source_scope_frame_extends {World : Type} {marker current : SourceFrame}
    (extended : SourceFrameExtends marker current) (state : SourceState World) :
    SourceFrameExtends marker (sourceLeaveScope marker current state).1 :=
  ⟨extended.storage, extended.counter, fun _ member => member⟩

theorem source_scope_local_coherent {World : Type} (marker current : SourceFrame) (state : SourceState World)
    (coherent : LocalTypesCoherent marker.bindings) :
    LocalTypesCoherent (sourceLeaveScope marker current state).1.bindings := coherent

theorem source_scope_local_below {World : Type} {marker current : SourceFrame}
    (extended : SourceFrameExtends marker current) (below : SourceLocalsBelow marker)
    (state : SourceState World) : SourceLocalsBelow (sourceLeaveScope marker current state).1 := by
  intro binding member
  exact (below binding member).trans_le extended.counter

theorem source_scope_local_tagged {World : Type} {marker current : SourceFrame}
    (extended : SourceFrameExtends marker current) (below : SourceLocalsBelow marker)
    (state : SourceState World) (tagged : SourceLocalsTagged current state.memory) :
    SourceLocalsTagged (sourceLeaveScope marker current state).1
      (sourceLeaveScope marker current state).2.memory := by
  intro binding member value read
  have earlier := below binding member
  have notInside : ¬ marker.nextLocal ≤ binding.position := Nat.not_le_of_gt earlier
  simp only [sourceLeaveScope, sourceDropLocals, notInside, and_false, false_and, if_false] at read
  exact tagged binding (extended.visible binding member) value read

theorem short_circuit_source_state {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame} {expression : Expr}
    (supported : SourceShortCircuitExpression expression) (before : SourceState World)
    (clear : before.fault = none) {out : SourceOutcome World}
    (ran : SourceExprEval interface heap calls frame expression before out) :
    SourceScalarResultState before out.result out.state := by
  induction supported generalizing before out with
  | guarded child => exact source_guarded_run_state child before clear ran
  | connect continueValue first second firstIH secondIH =>
      rcases (source_short_circuit_exact continueValue _ _ before out).mp ran with
        ⟨after, evaluated, same⟩ | ⟨middle, evaluated, continued⟩ | ⟨fault, after, evaluated, same⟩
      · have unchanged := firstIH before clear evaluated
        change after = before at unchanged
        subst after
        subst out
        rfl
      · have unchanged := firstIH before clear evaluated
        change middle = before at unchanged
        subst middle
        exact secondIH before clear continued
      · have poisoned := firstIH before clear evaluated
        change after = sourcePoison before fault at poisoned
        subst after
        subst out
        rfl

theorem short_circuit_source_success_tag {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame} {expression : Expr}
    (supported : SourceShortCircuitExpression expression) {before : SourceState World}
    (clear : before.fault = none) (tagged : SourceLocalsTagged frame before.memory)
    {type : NativeType} {value : SourceValue}
    (typing : inferExpr interface (sourceFrameScope frame) expression = some type)
    (ran : SourceExprEval interface heap calls frame expression before ⟨.ok value, before⟩) :
    SourceOuterTag type value := by
  induction supported generalizing type value with
  | guarded child => exact source_guarded_success_tag child before clear tagged typing ran
  | connect continueValue first second firstIH secondIH =>
      obtain ⟨sameType, _, rightType⟩ := short_circuit_inferred continueValue typing
      subst type
      rcases (source_short_circuit_exact continueValue _ _ before _).mp ran with
        ⟨after, _, same⟩ | ⟨middle, evaluated, continued⟩ | ⟨fault, after, _, impossible⟩
      · have sameValue := congrArg SourceOutcome.result same
        cases sameValue
        constructor
      · have unchanged := short_circuit_source_state first before clear evaluated
        change middle = before at unchanged
        subst middle
        exact secondIH rightType continued
      · cases impossible

/-- The local execution invariant retains the allocated-cell counter, binding
types and actual context fault, including abrupt exits. The checked scope is
required only when execution reaches the next statement normally. -/
structure SourceLocalOutcomeProfile {World : Type} (marker : SourceFrame)
    (nextScope : Scope) (out : SourceBlockOutcome World) : Prop where
  extended : SourceFrameExtends marker out.frame
  below : SourceLocalsBelow out.frame
  coherent : LocalTypesCoherent out.frame.bindings
  tagged : SourceLocalsTagged out.frame out.state.memory
  fault : match out.flow with
    | .fault error => out.state.fault = some error
    | _ => out.state.fault = none
  scope : out.flow = .normal → sourceFrameScope out.frame = nextScope

theorem source_local_profile_close {World : Type} {marker : SourceFrame}
    {nextScope : Scope} {out : SourceBlockOutcome World}
    (below : SourceLocalsBelow marker) (coherent : LocalTypesCoherent marker.bindings)
    (profile : SourceLocalOutcomeProfile marker nextScope out) :
    SourceLocalOutcomeProfile marker (sourceFrameScope marker) (sourceCloseBlock marker out) :=
  ⟨source_scope_frame_extends profile.extended out.state,
    source_scope_local_below profile.extended below out.state,
    source_scope_local_coherent marker out.frame out.state coherent,
    source_scope_local_tagged profile.extended below out.state profile.tagged,
    profile.fault, fun _ => rfl⟩

theorem source_local_profile_trans {World : Type} {first middle : SourceFrame}
    {nextScope : Scope} {out : SourceBlockOutcome World}
    (extended : SourceFrameExtends first middle)
    (profile : SourceLocalOutcomeProfile middle nextScope out) :
    SourceLocalOutcomeProfile first nextScope out :=
  ⟨source_frame_extends_trans extended profile.extended, profile.below,
    profile.coherent, profile.tagged, profile.fault, profile.scope⟩

theorem source_close_retains_caller_cell {World : Type} {marker : SourceFrame}
    {out : SourceBlockOutcome World} (extended : SourceFrameExtends marker out.frame)
    (position : Nat) (caller : position < marker.nextLocal) :
    (sourceCloseBlock marker out).state.memory.cells marker.storage position =
      out.state.memory.cells marker.storage position := by
  have outside : ¬ marker.nextLocal ≤ position := Nat.not_le_of_gt caller
  simp only [sourceCloseBlock, sourceLeaveScope, sourceDropLocals,
    extended.storage, outside, false_and, and_false, if_false]

end Mettapedia.GSLT.LanguageDef.NativeOps
