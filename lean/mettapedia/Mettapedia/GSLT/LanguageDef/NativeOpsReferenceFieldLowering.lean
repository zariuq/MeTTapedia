import Mettapedia.GSLT.LanguageDef.NativeOpsReadExpressionLowering

/-!
# Checked reference-field addresses and reads

The source looks up the declared field. The target checks the base reference,
forms its positional field address, then reads memory. A missing cell remains
undefined; nominal reference types do not establish the loaded value's tag.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)

theorem source_reference_field_location_primitive_exact {World : Type} {interface : Interface}
    (heap : SourceHeapSemantics World) (frame : SourceFrame) (base : Expr)
    (record member : String) (index : Nat) (pointer : Option Address)
    (type : inferExpr interface (sourceFrameScope frame) base = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (state : SourceState World) (out : SourceLocationOutcome World) :
    sourcePrimitiveLocation interface heap frame (.field base member) [.reference pointer] state out ↔
      match (sourceReferenceCall state pointer).state.fault with
      | some fault => out = ⟨.error fault, (sourceReferenceCall state pointer).state⟩
      | none => ∃ address, pointer = some address ∧
          out = ⟨.ok (sourceFieldAddress address index), (sourceReferenceCall state pointer).state⟩ := by
  have selected := (field_layout_correspondence interface record member).symm.trans position
  cases failed : (sourceReferenceCall state pointer).state.fault <;>
    simp [sourcePrimitiveLocation, type, selected, failed]

theorem source_reference_field_primitive_exact {World : Type} {interface : Interface}
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (base : Expr) (record member : String) (index : Nat) (pointer : Option Address)
    (type : inferExpr interface (sourceFrameScope frame) base = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (state : SourceState World) (out : SourceOutcome World) :
    sourcePrimitive interface heap calls frame (.field base member) [.reference pointer] state out ↔
      match (sourceReferenceCall state pointer).state.fault with
      | some fault => out = ⟨.error fault, (sourceReferenceCall state pointer).state⟩
      | none => ∃ address value, pointer = some address ∧
          sourceRead (sourceReferenceCall state pointer).state.memory (sourceFieldAddress address index) = some value ∧
          out = ⟨.ok value, (sourceReferenceCall state pointer).state⟩ := by
  change (∃ location,
    sourcePrimitiveLocation interface heap frame (.field base member) [.reference pointer] state location ∧
      sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ out = ⟨.ok value, post⟩) out) ↔ _
  simp only [source_reference_field_location_primitive_exact heap frame base record member index pointer type position]
  cases failed : (sourceReferenceCall state pointer).state.fault with
  | some fault => simp [sourceLocationNext]
  | none =>
      constructor
      · rintro ⟨location, ⟨address, pointed, same⟩, next⟩
        subst location
        obtain ⟨value, loaded, same⟩ := next
        exact ⟨address, value, pointed, loaded, same⟩
      · rintro ⟨address, value, pointed, loaded, same⟩
        exact ⟨⟨.ok (sourceFieldAddress address index), (sourceReferenceCall state pointer).state⟩,
          ⟨address, pointed, rfl⟩, value, loaded, same⟩

theorem target_field_address_exact {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {address : Address}
    (read : TargetAtomEval interface frame state atom (.reference (some address)))
    (record : String) (index : Nat) (value : TargetValue) :
    TargetPureEval interface frame state (.fieldAddress atom record index) value ↔
      value = .reference (some (sourceFieldAddress address index)) := by
  constructor
  · intro evaluated
    cases evaluated with
    | fieldAddress otherRead => cases target_atom_unique read otherRead; rfl
  · intro same
    subst value
    exact .fieldAddress read

theorem target_field_address_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {address : Address}
    (read : TargetAtomEval interface frame state atom (.reference (some address)))
    (record : String) (index identity : Nat) (type : NativeType)
    (unused : frame.temporaryNames.contains identity = false) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.temporary identity (.ref type) (.fieldAddress atom record index)) frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity
        (.reference (some (sourceFieldAddress address index))), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | temporary _ computed =>
        cases (target_field_address_exact read record index _).mp computed
        rfl
  · intro same
    subst out
    exact .temporary unused (.fieldAddress read)

/-- An authored, unguarded field load has a run exactly when its actual
positional cell has contents. No null check or default value is invented.
The complete external state is retained; only two fresh private cells change. -/
theorem target_field_read_partial_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {address : Address}
    (read : TargetAtomEval interface frame state atom (.reference (some address)))
    (record : String) (index locationId valueId : Nat) (type : NativeType)
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.temporary locationId (.ref type) (.fieldAddress atom record index),
       .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))] frame state out ↔
      ∃ value, targetRead state.memory (sourceFieldAddress address index) = some value ∧
        out = ⟨.normal, targetDeclareTemporary
          (targetDeclareTemporary frame locationId (.reference (some (sourceFieldAddress address index))))
          valueId value, state⟩ := by
  rw [target_normal_then_exact
    (target_field_address_instruction_exact read record index locationId type locationUnused)]
  let middle := targetDeclareTemporary frame locationId
    (.reference (some (sourceFieldAddress address index)))
  have nextUnused : middle.temporaryNames.contains valueId = false := by
    simp only [middle, targetDeclareTemporary, List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨by simp [distinct], valueUnused⟩
  rw [target_pure_temporary_any_exact interface heap calls result root middle state valueId type
    (.indirectRead (.temporary locationId (.ref type))) nextUnused]
  have pointed := declared_temporary_atom interface frame state locationId (.ref type)
    (.reference (some (sourceFieldAddress address index)))
  constructor
  · rintro ⟨value, computed, same⟩
    cases computed with
    | indirect pointer loaded =>
        cases target_atom_unique pointed pointer
        exact ⟨value, loaded, same⟩
  · rintro ⟨value, loaded, same⟩
    exact ⟨value, .indirect pointed loaded, same⟩

theorem target_field_read_defined_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {address : Address}
    (read : TargetAtomEval interface frame state atom (.reference (some address)))
    (record : String) (index locationId valueId : Nat) (type : NativeType)
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    {value : TargetValue}
    (loaded : targetRead state.memory (sourceFieldAddress address index) = some value)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.temporary locationId (.ref type) (.fieldAddress atom record index),
       .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))] frame state out ↔
      out = ⟨.normal, targetDeclareTemporary
        (targetDeclareTemporary frame locationId (.reference (some (sourceFieldAddress address index))))
        valueId value, state⟩ := by
  rw [target_field_read_partial_exact read record index locationId valueId type
    locationUnused valueUnused distinct root out, loaded]
  constructor
  · rintro ⟨other, same, resultEq⟩
    cases Option.some.inj same
    exact resultEq
  · intro resultEq
    exact ⟨value, rfl, resultEq⟩

/-- A declared pointer and field type do not turn missing storage into zero. -/
theorem missing_field_read_has_no_run {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {address : Address}
    (read : TargetAtomEval interface frame state atom (.reference (some address)))
    (record : String) (index locationId valueId : Nat) (type : NativeType)
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    (missing : targetRead state.memory (sourceFieldAddress address index) = none)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    ¬ TargetRun interface heap calls result root
      [.temporary locationId (.ref type) (.fieldAddress atom record index),
       .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))] frame state out := by
  rw [target_field_read_partial_exact read record index locationId valueId type
    locationUnused valueUnused distinct root out, missing]
  simp only [reduceCtorEq, false_and, exists_false, not_false_eq_true]

theorem target_field_read_clear_exact {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    (frame : TargetFrame) (atom : Atom) (address : Address) (record : String)
    (index locationId valueId : Nat) (type : NativeType)
    (read : TargetAtomEval interface frame target atom (.reference (some address)))
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    (clear : (sourceReferenceCall source (some address)).state.fault = none)
    (root : List Instruction) (out : TargetBlockOutcome TargetWorld) :
    TargetRun interface heap calls result root
      (NativeLowering.checkReference atom ++
        [.temporary locationId (.ref type) (.fieldAddress atom record index),
         .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))]) frame target out ↔
      ∃ original,
        sourceRead (sourceReferenceCall source (some address)).state.memory
          (sourceFieldAddress address index) = some original ∧
        out = ⟨.normal, targetDeclareTemporary
          (targetDeclareTemporary frame locationId (.reference (some (sourceFieldAddress address index))))
          valueId (encodeValue original), (targetReferenceCall target (some address)).state⟩ := by
  have related := reference_call_correspondence states (some address)
  rw [target_reference_clear_then_exact read (related.state.fault.trans clear)]
  have readAfter := target_atom_state_irrelevant read (targetReferenceCall target (some address)).state
  rw [target_normal_then_exact
    (target_field_address_instruction_exact readAfter record index locationId type locationUnused)]
  have nextUnused : (targetDeclareTemporary frame locationId
      (.reference (some (sourceFieldAddress address index)))).temporaryNames.contains valueId = false := by
    simp only [targetDeclareTemporary, List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨by simp [distinct], valueUnused⟩
  exact target_indirect_temporary_exact related.state _ _ _ valueId type
    (declared_temporary_atom interface frame _ locationId (.ref type) _) nextUnused root out

theorem target_field_read_fault_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {pointer : Option Address}
    (read : TargetAtomEval interface frame state atom (.reference pointer))
    (record : String) (index locationId valueId : Nat) (type : NativeType)
    {fault : NativeWord64.Fault} {default : TargetValue}
    (failed : (targetReferenceCall state pointer).state.fault = some fault)
    (zero : TargetZero interface result default) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (NativeLowering.checkReference atom ++
        [.temporary locationId (.ref type) (.fieldAddress atom record index),
         .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))]) frame state out ↔
      out = ⟨.returned default, frame, (targetReferenceCall state pointer).state⟩ :=
  target_reference_fault_then_exact read failed zero root _ out

theorem reference_field_location_type {interface : Interface} {scope : Scope}
    {base : Expr} {record member : String}
    (baseType : inferExpr interface scope base = some (.ref (.named record))) :
    inferLocation interface scope (.field base member) = inferExpr interface scope (.field base member) := by
  rw [inferLocation, inferExpr, baseType]
  rfl

theorem reference_field_combined_lowering_exact {interface : Interface} {scope : Scope}
    {base : Expr} {member record : String} {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (baseType : inferExpr interface scope base = some (.ref (.named record)))
    (compiled : NativeLowering.expression? interface scope (.field base member) supply = some output) :
    ∃ type child index,
      inferExpr interface scope (.field base member) = some type ∧
      NativeLowering.expression? interface scope base supply = some child ∧
      NativeLowering.fieldLayout? interface record member = some index ∧
      output = NativeLowering.prependCode
        (child.code ++ NativeLowering.checkReference child.result ++
          [.temporary (NativeIR.fresh child.supply).1 (.ref type) (.fieldAddress child.result record index)])
        (NativeLowering.pureTemporary (NativeIR.fresh child.supply).2 type
          (.indirectRead (.temporary (NativeIR.fresh child.supply).1 (.ref type)))) := by
  obtain ⟨type, location, typing, located, same⟩ := read_reference_field_lowering_exact baseType compiled
  obtain ⟨locationType, child, index, locationTyping, childCompiled, selected, exactLocation⟩ :=
    read_reference_field_location_lowering_exact baseType located
  rw [reference_field_location_type baseType, typing] at locationTyping
  cases Option.some.inj locationTyping
  subst location
  exact ⟨type, child, index, typing, childCompiled, selected, same⟩

theorem checked_reference_field_preservation {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (frame : TargetFrame) (base : Expr) (pointer : Option Address)
    (record member : String) (index locationId valueId : Nat) (type result : NativeType)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (atom : Atom) (read : TargetAtomEval interface frame target atom (.reference pointer))
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {sourceOut : SourceOutcome SourceWorld}
    (ran : sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.field base member)
      [.reference pointer] source sourceOut) :
    ∃ out observed, TargetRun interface targetHeap targetCalls result root
        (NativeLowering.checkReference atom ++
          [.temporary locationId (.ref type) (.fieldAddress atom record index),
           .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))]) frame target out ∧
      targetExpressionObservation interface (.temporary valueId type) out observed ∧
      OutcomeRelated worldRelated sourceOut observed := by
  have related := reference_call_correspondence states pointer
  have exactSource := (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame
    base record member index pointer baseType position source sourceOut).mp ran
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      rw [failed] at exactSource
      subst sourceOut
      have targetFailed := related.state.fault.trans failed
      refine ⟨⟨.returned default, frame, (targetReferenceCall target pointer).state⟩,
        targetObserve (targetReferenceCall target pointer).state default, ?_, rfl, ?_, ?_⟩
      · exact (target_field_read_fault_exact read record index locationId valueId type targetFailed zero root _).mpr rfl
      · simpa only [targetObserve_state] using related.state
      · simp [targetObserve, targetFailed, Except.map]
  | none =>
      rw [failed] at exactSource
      obtain ⟨address, value, pointed, loaded, same⟩ := exactSource
      subst pointer
      subst sourceOut
      let middle := targetDeclareTemporary frame locationId (.reference (some (sourceFieldAddress address index)))
      let after := targetDeclareTemporary middle valueId (encodeValue value)
      have targetClear := related.state.fault.trans failed
      refine ⟨⟨.normal, after, (targetReferenceCall target (some address)).state⟩,
        targetObserve (targetReferenceCall target (some address)).state (encodeValue value), ?_, ?_, ?_, ?_⟩
      · exact (target_field_read_clear_exact states frame atom address record index locationId valueId
          type read locationUnused valueUnused distinct failed root _).mpr ⟨value, loaded, rfl⟩
      · exact ⟨encodeValue value, declared_temporary_atom interface middle _ valueId type _, rfl⟩
      · simpa only [targetObserve_state] using related.state
      · simp [targetObserve, targetClear, Except.map]

theorem checked_reference_field_reflection {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (frame : TargetFrame) (base : Expr) (pointer : Option Address)
    (record member : String) (index locationId valueId : Nat) (type result : NativeType)
    (baseType : inferExpr interface (sourceFrameScope sourceFrame) base = some (.ref (.named record)))
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (atom : Atom) (read : TargetAtomEval interface frame target atom (.reference pointer))
    (locationUnused : frame.temporaryNames.contains locationId = false)
    (valueUnused : frame.temporaryNames.contains valueId = false) (distinct : valueId ≠ locationId)
    {default : TargetValue} (zero : TargetZero interface result default)
    (root : List Instruction) {out : TargetBlockOutcome TargetWorld} {observed : TargetOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root
      (NativeLowering.checkReference atom ++
        [.temporary locationId (.ref type) (.fieldAddress atom record index),
         .temporary valueId type (.indirectRead (.temporary locationId (.ref type)))]) frame target out)
    (observation : targetExpressionObservation interface (.temporary valueId type) out observed) :
    ∃ sourceOut, sourcePrimitive interface sourceHeap sourceCalls sourceFrame (.field base member)
      [.reference pointer] source sourceOut ∧ OutcomeRelated worldRelated sourceOut observed := by
  have related := reference_call_correspondence states pointer
  cases failed : (sourceReferenceCall source pointer).state.fault with
  | some fault =>
      have targetFailed := related.state.fault.trans failed
      cases (target_field_read_fault_exact read record index locationId valueId type targetFailed zero root out).mp ran
      change observed = targetObserve (targetReferenceCall target pointer).state default at observation
      subst observed
      refine ⟨⟨.error fault, (sourceReferenceCall source pointer).state⟩, ?_, ?_, ?_⟩
      · apply (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame base record member
          index pointer baseType position source _).mpr
        simp only [failed]
      · simpa only [targetObserve_state] using related.state
      · simp [targetObserve, targetFailed, Except.map]
  | none =>
      obtain ⟨address, pointed⟩ := source_reference_clear_nonnull source pointer failed
      subst pointer
      obtain ⟨value, loaded, same⟩ := (target_field_read_clear_exact states frame atom address record index
        locationId valueId type read locationUnused valueUnused distinct failed root out).mp ran
      subst out
      obtain ⟨native, nativeRead, exactObserved⟩ := observation
      cases target_atom_unique (declared_temporary_atom interface _ _ valueId type (encodeValue value)) nativeRead
      subst observed
      refine ⟨⟨.ok value, (sourceReferenceCall source (some address)).state⟩, ?_, ?_, ?_⟩
      · apply (source_reference_field_primitive_exact sourceHeap sourceCalls sourceFrame base record member
          index (some address) baseType position source _).mpr
        simpa only [failed] using ⟨address, value, rfl, loaded, rfl⟩
      · simpa only [targetObserve_state] using related.state
      · simp [targetObserve, related.state.fault.trans failed, Except.map]

/-- Consecutive private cells used by an authored field address and read. -/
def fieldReadCode (base : Atom) (record : String) (index first : Nat) (type : NativeType) :
    List Instruction :=
  [.temporary first (.ref type) (.fieldAddress base record index),
   .temporary (first + 1) type (.indirectRead (.temporary first (.ref type)))]

def fieldReadFrame (frame : TargetFrame) (address : Address) (index first : Nat)
    (value : TargetValue) : TargetFrame :=
  targetDeclareTemporary
    (targetDeclareTemporary frame first (.reference (some (sourceFieldAddress address index))))
    (first + 1) value

theorem field_read_frame_bound {frame : TargetFrame} {lower first : Nat}
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (address : Address) (index : Nat) (value : TargetValue) :
    TemporaryNamesBound (fieldReadFrame frame address index first value) (first + 1) := by
  exact declared_temporary_bound
    (declared_temporary_bound bounded (by omega) (Nat.le_refl first) _) (by omega) (Nat.le_refl _) _

theorem field_read_frame_protects {lower first : Nat} (frame : TargetFrame)
    (fresh : lower < first) (address : Address) (index : Nat) (value : TargetValue) :
    TemporaryProtection lower frame (fieldReadFrame frame address index first value) :=
  temporary_protection_trans (declare_temporary_protects frame _ fresh)
    (declare_temporary_protects _ _ (by omega))

theorem field_read_frame_scoped {frame : TargetFrame} (hscope : TemporariesScoped frame)
    (address : Address) (index first : Nat) (value : TargetValue) :
    TemporariesScoped (fieldReadFrame frame address index first value) :=
  declared_temporaries_completeNames (declared_temporaries_completeNames hscope _ _) _ _

theorem field_read_code_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {base : Atom}
    {address : Address} {lower first index : Nat} {type : NativeType} {value : TargetValue}
    (read : TargetAtomEval interface frame state base (.reference (some address)))
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (loaded : targetRead state.memory (sourceFieldAddress address index) = some value)
    (record : String) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (fieldReadCode base record index first type) frame state out ↔
      out = ⟨.normal, fieldReadFrame frame address index first value, state⟩ :=
  target_field_read_defined_exact read record index first (first + 1) type
    (temporary_bound_fresh bounded fresh) (temporary_bound_fresh bounded (by omega))
    (by omega) loaded root out

/-- One declared field transport, from the source record's positional field
to the destination record's positional field. -/
structure FieldCopy where
  sourceIndex : Nat
  destinationIndex : Nat
  type : NativeType
  deriving DecidableEq, Repr

def fieldCopyCode (source destination : Atom) (sourceRecord destinationRecord : String)
    (field : FieldCopy) (first : Nat) : List Instruction :=
  [.temporary first (.ref field.type)
     (.fieldAddress destination destinationRecord field.destinationIndex),
   .temporary (first + 1) (.ref field.type)
     (.fieldAddress source sourceRecord field.sourceIndex),
   .temporary (first + 2) field.type (.indirectRead (.temporary (first + 1) (.ref field.type))),
   .write (.temporary first (.ref field.type)) (.temporary (first + 2) field.type)]

def fieldCopyFrame (frame : TargetFrame) (source destination : Address)
    (field : FieldCopy) (first : Nat) (value : TargetValue) : TargetFrame :=
  fieldReadFrame (targetDeclareTemporary frame first
    (.reference (some (sourceFieldAddress destination field.destinationIndex))))
    source field.sourceIndex (first + 1) value

theorem field_copy_frame_bound {frame : TargetFrame} {lower first : Nat}
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (source destination : Address) (field : FieldCopy) (value : TargetValue) :
    TemporaryNamesBound (fieldCopyFrame frame source destination field first value) (first + 2) := by
  exact field_read_frame_bound
    (declared_temporary_bound bounded (by omega) (Nat.le_refl first) _) (by omega) _ _ _

theorem field_copy_frame_protects {lower first : Nat} (frame : TargetFrame)
    (fresh : lower < first) (source destination : Address) (field : FieldCopy) (value : TargetValue) :
    TemporaryProtection lower frame (fieldCopyFrame frame source destination field first value) :=
  temporary_protection_trans (declare_temporary_protects frame _ fresh)
    (field_read_frame_protects _ (by omega) _ _ _)

/-- The actual four-instruction field store has exactly the defined read and
write behaviors of its live storage. Aliasing is retained, and neither a null
guard nor a default value is added to the original C operation. -/
theorem field_copy_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {source destination : Atom}
    {sourceAddress destinationAddress : Address} {lower first : Nat}
    (sourceRead : TargetAtomEval interface frame state source (.reference (some sourceAddress)))
    (destinationRead : TargetAtomEval interface frame state destination (.reference (some destinationAddress)))
    (sourceWithin : atomWithin lower source) (bounded : TemporaryNamesBound frame lower)
    (fresh : lower < first) (sourceRecord destinationRecord : String) (field : FieldCopy)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (fieldCopyCode source destination sourceRecord destinationRecord field first ++ rest) frame state out ↔
      ∃ value memory,
        targetRead state.memory (sourceFieldAddress sourceAddress field.sourceIndex) = some value ∧
        targetWrite state.memory (sourceFieldAddress destinationAddress field.destinationIndex) value = some memory ∧
        TargetRun interface heap calls result root rest
          (fieldCopyFrame frame sourceAddress destinationAddress field first value)
          { state with memory := memory } out := by
  let destinationFrame := targetDeclareTemporary frame first
    (.reference (some (sourceFieldAddress destinationAddress field.destinationIndex)))
  have destinationBound : TemporaryNamesBound destinationFrame first :=
    declared_temporary_bound bounded (by omega) (Nat.le_refl _) _
  have sourceAfter : TargetAtomEval interface destinationFrame state source
      (.reference (some sourceAddress)) := (protection_atom_evaluation
    (declare_temporary_protects frame
      (.reference (some (sourceFieldAddress destinationAddress field.destinationIndex))) fresh)
      source sourceWithin state state _).mp sourceRead
  have sourceUnused := temporary_bound_fresh destinationBound (show first < first + 1 by omega)
  have loadUnused := temporary_bound_fresh
    (declared_temporary_bound destinationBound (show first ≤ first + 1 by omega)
      (Nat.le_refl (first + 1))
      (.reference (some (sourceFieldAddress sourceAddress field.sourceIndex))))
    (show first + 1 < first + 2 by omega)
  unfold fieldCopyCode
  simp only [List.cons_append, List.nil_append]
  rw [target_normal_then_exact (target_field_address_instruction_exact destinationRead
    destinationRecord field.destinationIndex first field.type (temporary_bound_fresh bounded fresh))]
  rw [target_normal_then_exact (target_field_address_instruction_exact sourceAfter
    sourceRecord field.sourceIndex (first + 1) field.type sourceUnused)]
  rw [target_pure_temporary_then_iff loadUnused]
  let addressFrame := targetDeclareTemporary destinationFrame (first + 1)
    (.reference (some (sourceFieldAddress sourceAddress field.sourceIndex)))
  have sourcePointer := declared_temporary_atom interface destinationFrame state (first + 1)
    (.ref field.type) (.reference (some (sourceFieldAddress sourceAddress field.sourceIndex)))
  have destinationPointer (value : TargetValue) :
      TargetAtomEval interface (fieldCopyFrame frame sourceAddress destinationAddress field first value)
        state (.temporary first (.ref field.type))
        (.reference (some (sourceFieldAddress destinationAddress field.destinationIndex))) := by
    exact (protection_atom_evaluation
      (field_read_frame_protects destinationFrame (show first < first + 1 by omega) _ _ value)
      (.temporary first (.ref field.type)) (Nat.le_refl first) state state _).mp
      (declared_temporary_atom interface frame state first (.ref field.type) _)
  constructor
  · rintro ⟨value, computed, remaining⟩
    have loaded : targetRead state.memory (sourceFieldAddress sourceAddress field.sourceIndex) = some value := by
      cases computed with
      | indirect pointer loaded =>
          cases target_atom_unique sourcePointer pointer
          exact loaded
    obtain ⟨memory, written, suffix⟩ := (target_write_then_iff (destinationPointer value)
      (declared_temporary_atom interface addressFrame state (first + 2) field.type value) root rest out).mp remaining
    exact ⟨value, memory, loaded, written, suffix⟩
  · rintro ⟨value, memory, loaded, written, suffix⟩
    refine ⟨value, .indirect sourcePointer loaded, ?_⟩
    exact (target_write_then_iff (destinationPointer value)
      (declared_temporary_atom interface addressFrame state (first + 2) field.type value) root rest out).mpr
      ⟨memory, written, suffix⟩

def fieldCopiesCode (source destination : Atom) (sourceRecord destinationRecord : String) :
    List FieldCopy → Nat → List Instruction
  | [], _ => []
  | field :: rest, first =>
      fieldCopyCode source destination sourceRecord destinationRecord field first ++
        fieldCopiesCode source destination sourceRecord destinationRecord rest (first + 3)

/-- A finite ordered storage account, independent of target instructions.
Each step contains its actual read, actual write and private observation.
An omitted or reordered field changes the account. -/
inductive FieldCopiesExecution (source destination : Address) :
    List FieldCopy → Nat → TargetFrame → TargetMemory → TargetFrame → TargetMemory → Prop where
  | nil (first : Nat) (frame : TargetFrame) (memory : TargetMemory) :
      FieldCopiesExecution source destination [] first frame memory frame memory
  | cons {field : FieldCopy} {rest : List FieldCopy} {first : Nat}
      {frame final : TargetFrame} {memory middle after : TargetMemory} {value : TargetValue}
      (loaded : targetRead memory (sourceFieldAddress source field.sourceIndex) = some value)
      (written : targetWrite memory (sourceFieldAddress destination field.destinationIndex) value = some middle)
      (remaining : FieldCopiesExecution source destination rest (first + 3)
        (fieldCopyFrame frame source destination field first value) middle final after) :
      FieldCopiesExecution source destination (field :: rest) first frame memory final after

theorem field_copies_execution_memory {source destination : Address} {fields : List FieldCopy}
    {first : Nat} {before after : TargetFrame} {memory final : TargetMemory}
    (executed : FieldCopiesExecution source destination fields first before memory after final) :
    targetCopyFields source destination
      (fields.map (fun field => (field.sourceIndex, field.destinationIndex))) memory = some final := by
  induction executed with
  | nil => rfl
  | cons loaded written _ ih =>
      simp only [sourceFieldAddress] at loaded written
      simpa [targetCopyFields, loaded, written] using ih

theorem field_copies_execution_frame_extent {source destination : Address} {fields : List FieldCopy}
    {first : Nat} {before after : TargetFrame} {memory final : TargetMemory}
    (executed : FieldCopiesExecution source destination fields first before memory after final) :
    after.storage = before.storage ∧ after.nextLocal = before.nextLocal := by
  induction executed with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ ih => exact ih

theorem field_copies_execution_protects {source destination : Address} {fields : List FieldCopy}
    {first lower : Nat} {before after : TargetFrame} {memory final : TargetMemory}
    (executed : FieldCopiesExecution source destination fields first before memory after final)
    (fresh : lower < first) : TemporaryProtection lower before after := by
  induction executed generalizing lower with
  | nil => exact temporary_protection_refl _ _
  | @cons field rest first frame _ _ _ _ value _ _ _ ih =>
      exact temporary_protection_trans
        (field_copy_frame_protects frame fresh source destination field value) (ih (by omega))

theorem field_copies_execution_of_memory (source destination : Address)
    (fields : List FieldCopy) (first : Nat) (frame : TargetFrame)
    {memory final : TargetMemory}
    (copied : targetCopyFields source destination
      (fields.map (fun field => (field.sourceIndex, field.destinationIndex))) memory = some final) :
    ∃ after, FieldCopiesExecution source destination fields first frame memory after final := by
  induction fields generalizing memory first frame with
  | nil => cases Option.some.inj copied; exact ⟨frame, .nil _ _ _⟩
  | cons field rest ih =>
      cases loaded : targetRead memory { source with fields := source.fields ++ [field.sourceIndex] } with
      | none => simp [targetCopyFields, loaded] at copied
      | some value =>
          cases written : targetWrite memory
              { destination with fields := destination.fields ++ [field.destinationIndex] } value with
          | none => simp [targetCopyFields, loaded, written] at copied
          | some middle =>
              have tail : targetCopyFields source destination
                  (rest.map (fun field => (field.sourceIndex, field.destinationIndex))) middle = some final := by
                simpa [targetCopyFields, loaded, written] using copied
              obtain ⟨after, remaining⟩ := ih (first + 3)
                (fieldCopyFrame frame source destination field first value) tail
              exact ⟨after, .cons loaded written remaining⟩

private theorem atom_within_enlarged {lower upper : Nat} (atom : Atom)
    (inside : atomWithin lower atom) (extended : lower ≤ upper) : atomWithin upper atom := by
  cases atom <;> first | exact inside.trans extended | trivial

/-- Preservation and reflection for an arbitrary finite list of field
assignments and an arbitrary continuation. All public state survives except
for the actual defined writes; private temporaries are recorded separately. -/
theorem field_copies_code_then_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {source destination : Atom} {sourceAddress destinationAddress : Address}
    (sourceRecord destinationRecord : String) (fields : List FieldCopy)
    {frame : TargetFrame} {state : TargetState World} {lower first : Nat}
    (sourceRead : TargetAtomEval interface frame state source (.reference (some sourceAddress)))
    (destinationRead : TargetAtomEval interface frame state destination (.reference (some destinationAddress)))
    (sourceWithin : atomWithin lower source) (destinationWithin : atomWithin lower destination)
    (bounded : TemporaryNamesBound frame lower) (fresh : lower < first)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      (fieldCopiesCode source destination sourceRecord destinationRecord fields first ++ rest) frame state out ↔
      ∃ after memory,
        FieldCopiesExecution sourceAddress destinationAddress fields first frame state.memory after memory ∧
        TargetRun interface heap calls result root rest after { state with memory := memory } out := by
  induction fields generalizing frame state lower first with
  | nil =>
      simp only [fieldCopiesCode, List.nil_append]
      constructor
      · intro ran; exact ⟨frame, state.memory, .nil _ _ _, ran⟩
      · rintro ⟨after, memory, executed, ran⟩
        cases executed
        exact ran
  | cons field fields ih =>
      simp only [fieldCopiesCode, List.append_assoc]
      rw [field_copy_then_iff sourceRead destinationRead sourceWithin bounded fresh]
      constructor
      · rintro ⟨value, middle, loaded, written, ran⟩
        let next := fieldCopyFrame frame sourceAddress destinationAddress field first value
        have protection := field_copy_frame_protects frame fresh sourceAddress destinationAddress field value
        have nextSource := (protection_atom_evaluation protection source sourceWithin
          state { state with memory := middle } _).mp sourceRead
        have nextDestination := (protection_atom_evaluation protection destination destinationWithin
          state { state with memory := middle } _).mp destinationRead
        obtain ⟨after, memory, executed, suffix⟩ := (ih nextSource nextDestination
          (atom_within_enlarged source sourceWithin (show lower ≤ first + 2 by omega))
          (atom_within_enlarged destination destinationWithin (show lower ≤ first + 2 by omega))
          (field_copy_frame_bound bounded fresh _ _ _ _) (show first + 2 < first + 3 by omega)).mp ran
        exact ⟨after, memory, .cons loaded written executed, suffix⟩
      · rintro ⟨after, memory, executed, suffix⟩
        cases executed with
        | cons loaded written remaining =>
          rename_i middle value
          have protection := field_copy_frame_protects frame fresh sourceAddress destinationAddress field value
          have nextSource := (protection_atom_evaluation protection source sourceWithin
            state { state with memory := middle } _).mp sourceRead
          have nextDestination := (protection_atom_evaluation protection destination destinationWithin
            state { state with memory := middle } _).mp destinationRead
          refine ⟨_, _, loaded, written, ?_⟩
          exact (ih nextSource nextDestination
            (atom_within_enlarged source sourceWithin (show lower ≤ first + 2 by omega))
            (atom_within_enlarged destination destinationWithin (show lower ≤ first + 2 by omega))
            (field_copy_frame_bound bounded fresh _ _ _ _) (show first + 2 < first + 3 by omega)).mpr
            ⟨after, memory, remaining, suffix⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
