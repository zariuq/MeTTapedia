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

end Mettapedia.GSLT.LanguageDef.NativeOps
