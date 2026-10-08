import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetSwitchReturns
import Mettapedia.GSLT.LanguageDef.NativeOpsFieldLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsTemporaryFrames

/-!
# Exact checked read fragments

Reference and index helpers retain their raw result and complete post-state.
The emitted context check follows the helper, and an index result is stored
before that check. A non-null reference does not establish a live read.
Undefined storage reads have no execution, independently of context faults.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom Instruction)

theorem source_reference_location_read_exact {World : Type}
    (raw : SourceRawResult World) (out : SourceOutcome World) :
    (∃ location, sourceReferenceLocation raw location ∧
      sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ out = ⟨.ok value, post⟩) out) ↔
      match raw.state.fault with
      | some fault => out = ⟨.error fault, raw.state⟩
      | none => ∃ address value, raw.value = .reference (some address) ∧
          sourceRead raw.state.memory address = some value ∧ out = ⟨.ok value, raw.state⟩ := by
  cases failed : raw.state.fault with
  | some fault =>
      constructor
      · rintro ⟨location, located, remaining⟩
        have same : location = ⟨.error fault, raw.state⟩ := by
          simpa only [sourceReferenceLocation, failed] using located
        subst location
        exact remaining
      · intro same
        exact ⟨⟨.error fault, raw.state⟩, by simp [sourceReferenceLocation, failed], same⟩
  | none =>
      constructor
      · rintro ⟨location, located, remaining⟩
        obtain ⟨address, pointer, same⟩ := (show ∃ address,
          raw.value = .reference (some address) ∧ location = ⟨.ok address, raw.state⟩ from by
          simpa only [sourceReferenceLocation, failed] using located)
        subst location
        obtain ⟨value, read, same⟩ := remaining
        exact ⟨address, value, pointer, read, same⟩
      · rintro ⟨address, value, pointer, read, same⟩
        exact ⟨⟨.ok address, raw.state⟩,
          by simpa only [sourceReferenceLocation, failed] using ⟨address, pointer, rfl⟩,
          value, read, same⟩

theorem source_reference_location_read_unique {World : Type}
    {raw : SourceRawResult World} {left right : SourceOutcome World}
    (one : ∃ location, sourceReferenceLocation raw location ∧
      sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ left = ⟨.ok value, post⟩) left)
    (two : ∃ location, sourceReferenceLocation raw location ∧
      sourceLocationNext location (fun address post => ∃ value,
        sourceRead post.memory address = some value ∧ right = ⟨.ok value, post⟩) right) :
    left = right := by
  have first := (source_reference_location_read_exact raw left).mp one
  have second := (source_reference_location_read_exact raw right).mp two
  cases failed : raw.state.fault with
  | some fault =>
      simp only [failed] at first second
      exact first.trans second.symm
  | none =>
      simp only [failed] at first second
      obtain ⟨a, v, pointer, read, out⟩ := first
      obtain ⟨b, w, otherPointer, otherRead, otherOut⟩ := second
      cases Option.some.inj (SourceValue.reference.inj (pointer.symm.trans otherPointer))
      cases Option.some.inj (read.symm.trans otherRead)
      exact out.trans otherOut.symm

theorem target_memory_temporary_helper_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : NativeIR.MemoryOperation}
    {identity : Nat} {type : NativeType} (raw : TargetRawResult World)
    (callExact : ∀ other, TargetMemoryCall interface heap frame operation state other ↔ other = raw)
    (unused : frame.temporaryNames.contains identity = false) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.helper (some (.temporary identity type)) operation) frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity raw.value, raw.state⟩ := by
  constructor
  · intro ran
    cases ran with
    | helper called stored =>
        cases (callExact _).mp called
        cases stored with
        | fresh _ => rfl
        | existing notTemporary _ => exact False.elim (notTemporary identity type rfl)
  · intro same
    subst out
    exact .helper ((callExact raw).mpr rfl) (.fresh unused)

theorem target_raw_reference_read_exact {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceRaw : SourceRawResult SourceWorld} {targetRaw : TargetRawResult TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    {frame : TargetFrame} {state : TargetState TargetWorld} {operation : NativeIR.MemoryOperation}
    {locationIdentity valueIdentity : Nat} {type : NativeType} {default : TargetValue}
    (rawRelated : RawResultRelated worldRelated sourceRaw targetRaw)
    (callExact : ∀ other, TargetMemoryCall interface heap frame operation state other ↔ other = targetRaw)
    (locationUnused : frame.temporaryNames.contains locationIdentity = false)
    (valueUnused : (targetDeclareTemporary frame locationIdentity targetRaw.value).temporaryNames.contains
      valueIdentity = false)
    (zero : TargetZero interface result default) (root : List Instruction) (out : TargetBlockOutcome TargetWorld) :
    TargetRun interface heap calls result root
      [.helper (some (.temporary locationIdentity (.ref type))) operation, .checkContext,
        .temporary valueIdentity type (.indirectRead (.temporary locationIdentity (.ref type)))]
      frame state out ↔
      match sourceRaw.state.fault with
      | some _ => out = ⟨.returned default,
          targetDeclareTemporary frame locationIdentity targetRaw.value, targetRaw.state⟩
      | none => ∃ address value, sourceRaw.value = .reference (some address) ∧
          sourceRead sourceRaw.state.memory address = some value ∧
          out = ⟨.normal,
            targetDeclareTemporary (targetDeclareTemporary frame locationIdentity targetRaw.value)
              valueIdentity (encodeValue value), targetRaw.state⟩ := by
  rw [target_normal_then_exact (target_memory_temporary_helper_exact targetRaw callExact locationUnused)]
  cases failed : sourceRaw.state.fault with
  | some fault =>
      exact target_returning_then_exact
        (target_context_fault_exact _ _ (rawRelated.state.fault.trans failed) zero) root _ out
  | none =>
      rw [target_normal_then_exact (target_context_clear_exact _ _ (rawRelated.state.fault.trans failed))]
      rw [target_pure_temporary_any_exact interface heap calls result root _ targetRaw.state
        valueIdentity type (.indirectRead (.temporary locationIdentity (.ref type))) valueUnused]
      constructor
      · rintro ⟨value, computed, same⟩
        cases computed with
        | indirect pointer read =>
            have rawPointer := target_atom_unique
              (declared_temporary_atom interface frame targetRaw.state locationIdentity (.ref type) targetRaw.value)
              pointer
            have sourcePointer : sourceRaw.value = .reference (some _) :=
              encodeValue_injective (rawRelated.value.symm.trans rawPointer)
            rw [memory_read_correspondence sourceRaw.state.memory targetRaw.state.memory
              rawRelated.state.memory] at read
            obtain ⟨original, selected, encoded⟩ := Option.map_eq_some_iff.mp read
            cases encoded
            exact ⟨_, original, sourcePointer, selected, same⟩
      · rintro ⟨address, value, pointer, read, same⟩
        refine ⟨encodeValue value, TargetPureEval.indirect (address := address) ?_ ?_, same⟩
        · have selected := declared_temporary_atom interface frame targetRaw.state locationIdentity
            (.ref type) targetRaw.value
          simpa only [rawRelated.value, pointer, encodeValue] using selected
        · rw [memory_read_correspondence sourceRaw.state.memory targetRaw.state.memory
            rawRelated.state.memory, read]
          rfl


theorem target_reference_call_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {frame : TargetFrame} {state : TargetState World}
    {atom : Atom} {pointer : Option Address}
    (read : TargetAtomEval interface frame state atom (.reference pointer))
    (raw : TargetRawResult World) :
    TargetMemoryCall interface heap frame (.reference atom) state raw ↔
      raw = targetReferenceCall state pointer := by
  constructor
  · intro called
    cases called with
    | reference otherRead =>
        cases target_atom_unique read otherRead
        rfl
  · intro same
    subst raw
    exact .reference read

theorem target_reference_helper_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {pointer : Option Address}
    (read : TargetAtomEval interface frame state atom (.reference pointer))
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (.helper none (.reference atom))
      frame state out ↔ out = ⟨.normal, frame, (targetReferenceCall state pointer).state⟩ := by
  constructor
  · intro ran
    cases ran with
    | helper called stored =>
        cases (target_reference_call_exact read _).mp called
        cases stored
        rfl
  · intro same
    subst out
    exact .helper (.reference read) (.discard _ _ _)

theorem target_reference_clear_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {pointer : Option Address}
    (read : TargetAtomEval interface frame state atom (.reference pointer))
    (clear : (targetReferenceCall state pointer).state.fault = none)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (NativeLowering.checkReference atom ++ rest)
      frame state out ↔
      TargetRun interface heap calls result root rest frame (targetReferenceCall state pointer).state out := by
  change TargetRun _ _ _ _ _ (.helper none (.reference atom) :: .checkContext :: rest) _ _ _ ↔ _
  rw [target_normal_then_exact (target_reference_helper_exact read)]
  exact target_normal_then_exact
    (target_context_clear_exact frame (targetReferenceCall state pointer).state clear) root rest out

theorem target_reference_fault_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {pointer : Option Address}
    {fault : NativeWord64.Fault} {default : TargetValue}
    (read : TargetAtomEval interface frame state atom (.reference pointer))
    (failed : (targetReferenceCall state pointer).state.fault = some fault)
    (zero : TargetZero interface result default)
    (root rest : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (NativeLowering.checkReference atom ++ rest)
      frame state out ↔ out = ⟨.returned default, frame, (targetReferenceCall state pointer).state⟩ := by
  change TargetRun _ _ _ _ _ (.helper none (.reference atom) :: .checkContext :: rest) _ _ _ ↔ _
  rw [target_normal_then_exact (target_reference_helper_exact read)]
  exact target_returning_then_exact
    (target_context_fault_exact frame (targetReferenceCall state pointer).state failed zero) root rest out

theorem target_reference_fragment_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {pointer : Option Address}
    {default : TargetValue}
    (read : TargetAtomEval interface frame state atom (.reference pointer))
    (zero : TargetZero interface result default)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (NativeLowering.checkReference atom) frame state out ↔
      out = match (targetReferenceCall state pointer).state.fault with
        | none => ⟨.normal, frame, (targetReferenceCall state pointer).state⟩
        | some _ => ⟨.returned default, frame, (targetReferenceCall state pointer).state⟩ := by
  cases found : (targetReferenceCall state pointer).state.fault with
  | none =>
      simpa only [List.append_nil, found] using
        (target_reference_clear_then_exact read found root [] out).trans
          (target_run_empty_exact root frame (targetReferenceCall state pointer).state out)
  | some fault =>
      simpa only [List.append_nil, found] using
        target_reference_fault_then_exact read found zero root [] out

theorem target_index_call_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {frame : TargetFrame} {state : TargetState World}
    {array index : Atom} {element : NativeType} {pointer : Option Address}
    {length offset : BitVec 64}
    (view : TargetAtomEval interface frame state array (.array element pointer length))
    (position : TargetAtomEval interface frame state index (.word offset))
    (raw : TargetRawResult World) :
    TargetMemoryCall interface heap frame (.index array index element) state raw ↔
      raw = targetIndexCall state length (heap.width element) offset pointer := by
  constructor
  · intro called
    cases called with
    | index otherView otherPosition =>
        cases target_atom_unique view otherView
        cases target_atom_unique position otherPosition
        rfl
  · intro same
    subst raw
    exact .index view position

theorem target_index_helper_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {array index : Atom}
    {element : NativeType} {pointer : Option Address} {length offset : BitVec 64} {identity : Nat}
    (view : TargetAtomEval interface frame state array (.array element pointer length))
    (position : TargetAtomEval interface frame state index (.word offset))
    (unused : frame.temporaryNames.contains identity = false) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.helper (some (.temporary identity (.ref element))) (.index array index element)) frame state out ↔
      out = ⟨.normal,
        targetDeclareTemporary frame identity (targetIndexCall state length (heap.width element) offset pointer).value,
        (targetIndexCall state length (heap.width element) offset pointer).state⟩ := by
  exact target_memory_temporary_helper_exact
    (targetIndexCall state length (heap.width element) offset pointer)
    (target_index_call_exact view position) unused out

theorem target_index_fragment_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {array index : Atom}
    {element : NativeType} {pointer : Option Address} {length offset : BitVec 64}
    {identity : Nat} {default : TargetValue}
    (view : TargetAtomEval interface frame state array (.array element pointer length))
    (position : TargetAtomEval interface frame state index (.word offset))
    (unused : frame.temporaryNames.contains identity = false)
    (zero : TargetZero interface result default) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.helper (some (.temporary identity (.ref element))) (.index array index element), .checkContext]
      frame state out ↔
      let raw := targetIndexCall state length (heap.width element) offset pointer
      let after := targetDeclareTemporary frame identity raw.value
      out = match raw.state.fault with
        | none => ⟨.normal, after, raw.state⟩
        | some _ => ⟨.returned default, after, raw.state⟩ := by
  rw [target_normal_then_exact (target_index_helper_exact view position unused)]
  cases found : (targetIndexCall state length (heap.width element) offset pointer).state.fault with
  | none =>
      rw [target_normal_then_exact (target_context_clear_exact _ _ found)]
      simpa only [found] using target_run_empty_exact root _ _ out
  | some fault =>
      simpa only [found] using target_returning_then_exact
        (target_context_fault_exact _ _ found zero) root [] out

theorem target_indirect_read_exact {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (frame : TargetFrame)
    (atom : Atom) (address : Address)
    (pointer : TargetAtomEval interface frame target atom (.reference (some address)))
    (value : TargetValue) :
    TargetPureEval interface frame target (.indirectRead atom) value ↔
      ∃ original, sourceRead source.memory address = some original ∧ value = encodeValue original := by
  constructor
  · intro evaluated
    cases evaluated with
    | indirect otherPointer read =>
        cases target_atom_unique pointer otherPointer
        rw [memory_read_correspondence source.memory target.memory states.memory] at read
        obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp read
        exact ⟨original, selected, same.symm⟩
  · rintro ⟨original, selected, same⟩
    subst value
    apply TargetPureEval.indirect pointer
    rw [memory_read_correspondence source.memory target.memory states.memory, selected]
    rfl

theorem target_indirect_temporary_exact {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    (states : StateRelated worldRelated source target) (frame : TargetFrame)
    (atom : Atom) (address : Address) (identity : Nat) (type : NativeType)
    (pointer : TargetAtomEval interface frame target atom (.reference (some address)))
    (unused : frame.temporaryNames.contains identity = false)
    (root : List Instruction) (out : TargetBlockOutcome TargetWorld) :
    TargetRun interface heap calls result root [.temporary identity type (.indirectRead atom)]
      frame target out ↔ ∃ original, sourceRead source.memory address = some original ∧
        out = ⟨.normal, targetDeclareTemporary frame identity (encodeValue original), target⟩ := by
  rw [target_pure_temporary_any_exact interface heap calls result root frame target identity type
    (.indirectRead atom) unused]
  constructor
  · rintro ⟨value, computed, same⟩
    obtain ⟨original, selected, encoded⟩ := (target_indirect_read_exact states frame atom address pointer value).mp computed
    subst value
    exact ⟨original, selected, same⟩
  · rintro ⟨original, selected, same⟩
    exact ⟨encodeValue original,
      (target_indirect_read_exact states frame atom address pointer _).mpr ⟨original, selected, rfl⟩, same⟩

theorem missing_indirect_has_no_run {SourceWorld TargetWorld : Type} {interface : Interface}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld} {result : NativeType}
    (states : StateRelated worldRelated source target) (frame : TargetFrame)
    (atom : Atom) (address : Address) (identity : Nat) (type : NativeType)
    (pointer : TargetAtomEval interface frame target atom (.reference (some address)))
    (unused : frame.temporaryNames.contains identity = false)
    (missing : sourceRead source.memory address = none) (root : List Instruction)
    (out : TargetBlockOutcome TargetWorld) :
    ¬ TargetRun interface heap calls result root [.temporary identity type (.indirectRead atom)]
      frame target out := by
  intro ran
  obtain ⟨original, read, _⟩ :=
    (target_indirect_temporary_exact states frame atom address identity type pointer unused root out).mp ran
  rw [missing] at read
  cases read

theorem target_length_read_exact {World : Type} {interface : Interface}
    (frame : TargetFrame) (state : TargetState World) (atom : Atom) (element : NativeType)
    (pointer : Option Address) (length : BitVec 64)
    (view : TargetAtomEval interface frame state atom (.array element pointer length))
    (value : TargetValue) :
    TargetPureEval interface frame state (.length atom) value ↔ value = .word length := by
  constructor
  · intro evaluated
    cases evaluated with
    | length otherView => cases target_atom_unique view otherView; rfl
  · intro same
    subst value
    exact .length view

theorem target_array_data_store_exact {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {element : NativeType}
    {previous pointer : Option Address} {length : BitVec 64}
    (read : TargetAtomEval interface frame state (.temporary identity (.array element))
      (.array element previous length)) (outFrame : TargetFrame) (outState : TargetState World) :
    TargetPlaceStore interface (.arrayData (.temporary identity (.array element)) element)
      (.reference pointer) frame state outFrame outState ↔
      outFrame = targetUpdateTemporary frame identity (.array element pointer length) ∧ outState = state := by
  constructor
  · intro stored
    cases stored with
    | arrayData other => cases target_atom_unique read other; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .arrayData read

theorem target_array_length_store_exact {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {element : NativeType}
    {pointer : Option Address} {oldLength length : BitVec 64}
    (read : TargetAtomEval interface frame state (.temporary identity (.array element))
      (.array element pointer oldLength)) (outFrame : TargetFrame) (outState : TargetState World) :
    TargetPlaceStore interface (.arrayLength (.temporary identity (.array element)))
      (.word length) frame state outFrame outState ↔
      outFrame = targetUpdateTemporary frame identity (.array element pointer length) ∧ outState = state := by
  constructor
  · intro stored
    cases stored with
    | arrayLength other => cases target_atom_unique read other; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .arrayLength read

theorem target_array_data_helper_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : NativeIR.MemoryOperation}
    {identity : Nat} {element : NativeType} {previous pointer : Option Address} {length : BitVec 64}
    (raw : TargetRawResult World) (rawReference : raw.value = .reference pointer)
    (callExact : ∀ other, TargetMemoryCall interface heap frame operation state other ↔ other = raw)
    (view : TargetAtomEval interface frame raw.state (.temporary identity (.array element))
      (.array element previous length)) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.helper (some (.arrayData (.temporary identity (.array element)) element)) operation) frame state out ↔
      out = ⟨.normal, targetUpdateTemporary frame identity (.array element pointer length), raw.state⟩ := by
  constructor
  · intro ran
    cases ran with
    | helper called stored =>
        cases (callExact _).mp called
        rw [rawReference] at stored
        cases stored with
        | existing _ stored =>
            obtain ⟨sameFrame, sameState⟩ := (target_array_data_store_exact view _ _).mp stored
            subst_vars; rfl
  · intro same
    subst out
    refine .helper ((callExact raw).mpr rfl) ?_
    rw [rawReference]
    exact .existing (by intro other type impossible; cases impossible) (.arrayData view)

theorem target_array_length_assign_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {identity : Nat} {element : NativeType}
    {pointer : Option Address} {oldLength length : BitVec 64} {atom : Atom}
    (view : TargetAtomEval interface frame state (.temporary identity (.array element))
      (.array element pointer oldLength))
    (value : TargetAtomEval interface frame state atom (.word length)) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.assign (.arrayLength (.temporary identity (.array element))) atom) frame state out ↔
      out = ⟨.normal, targetUpdateTemporary frame identity (.array element pointer length), state⟩ := by
  constructor
  · intro ran
    cases ran with
    | assign other stored =>
        cases target_atom_unique value other
        obtain ⟨sameFrame, sameState⟩ := (target_array_length_store_exact view _ _).mp stored
        subst_vars; rfl
  · intro same; subst out; exact .assign value (.arrayLength view)

theorem target_slice_call_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {frame : TargetFrame} {state : TargetState World}
    {array start count : Atom} {element : NativeType} {pointer : Option Address}
    {length first amount : BitVec 64}
    (arrayRead : TargetAtomEval interface frame state array (.array element pointer length))
    (startRead : TargetAtomEval interface frame state start (.word first))
    (countRead : TargetAtomEval interface frame state count (.word amount)) (raw : TargetRawResult World) :
    TargetMemoryCall interface heap frame (.slice array start count element) state raw ↔
      raw = targetSliceCall state length (heap.width element) first amount pointer := by
  constructor
  · intro called
    cases called with
    | slice otherArray otherStart otherCount =>
        cases target_atom_unique arrayRead otherArray
        cases target_atom_unique startRead otherStart
        cases target_atom_unique countRead otherCount
        rfl
  · intro same; subst raw; exact .slice arrayRead startRead countRead

theorem target_checked_array_descriptor_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : NativeIR.MemoryOperation}
    {identity : Nat} {element : NativeType} {previous pointer : Option Address} {oldLength length : BitVec 64}
    {lengthAtom : Atom} {default : TargetValue}
    (raw : TargetRawResult World) (rawReference : raw.value = .reference pointer)
    (callExact : ∀ other, TargetMemoryCall interface heap frame operation state other ↔ other = raw)
    (view : TargetAtomEval interface frame raw.state (.temporary identity (.array element))
      (.array element previous oldLength))
    (countRead : TargetAtomEval interface
      (targetUpdateTemporary frame identity (.array element pointer oldLength)) raw.state
      lengthAtom (.word length))
    (zero : TargetZero interface result default) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.helper (some (.arrayData (.temporary identity (.array element)) element)) operation,
        .checkContext, .assign (.arrayLength (.temporary identity (.array element))) lengthAtom]
      frame state out ↔
      out = match raw.state.fault with
      | some _ => ⟨.returned default,
          targetUpdateTemporary frame identity (.array element pointer oldLength), raw.state⟩
      | none => ⟨.normal,
          targetUpdateTemporary (targetUpdateTemporary frame identity (.array element pointer oldLength))
            identity (.array element pointer length), raw.state⟩ := by
  rw [target_normal_then_exact (target_array_data_helper_exact raw rawReference callExact view)]
  cases failed : raw.state.fault with
  | some fault =>
      exact target_returning_then_exact
        (target_context_fault_exact _ _ failed zero) root _ out
  | none =>
      rw [target_normal_then_exact (target_context_clear_exact _ _ failed)]
      have live : frame.temporaryNames.contains identity = true := by cases view; assumption
      have descriptor := updated_temporary_atom interface frame raw.state identity (.array element)
        (.array element pointer oldLength) live
      rw [target_normal_then_exact (target_array_length_assign_exact descriptor countRead)]
      exact target_run_empty_exact root _ _ out

theorem target_fresh_array_descriptor_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {operation : NativeIR.MemoryOperation}
    (supply : NativeIR.Supply) (element : NativeType) {pointer : Option Address}
    {length : BitVec 64} {lengthAtom : Atom} {default : TargetValue}
    (raw : TargetRawResult World) (rawReference : raw.value = .reference pointer)
    (callExact : ∀ other, TargetMemoryCall interface heap
      (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
      operation state other ↔ other = raw)
    (bounded : TemporaryNamesBound frame supply.next)
    (countRead : TargetAtomEval interface frame state lengthAtom (.word length))
    (zero : TargetZero interface result default) (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root
      [.temporary (NativeIR.fresh supply).1 (.array element) (.zero (.array element)),
        .helper (some (.arrayData (.temporary (NativeIR.fresh supply).1 (.array element)) element)) operation,
        .checkContext, .assign (.arrayLength (.temporary (NativeIR.fresh supply).1 (.array element))) lengthAtom]
      frame state out ↔
      out = match raw.state.fault with
      | some _ => ⟨.returned default,
          targetUpdateTemporary
            (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
            (NativeIR.fresh supply).1 (.array element pointer 0), raw.state⟩
      | none => ⟨.normal,
          targetUpdateTemporary
            (targetUpdateTemporary
              (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
              (NativeIR.fresh supply).1 (.array element pointer 0))
            (NativeIR.fresh supply).1 (.array element pointer length), raw.state⟩ := by
  have fresh := NativeIR.fresh_strict supply
  rw [target_normal_then_exact (target_temporary_instruction_exact
    (temporary_bound_fresh bounded fresh) (TargetPureEval.zero (.emptyView element)))]
  have preserved := temporary_protection_trans
    (declare_temporary_protects frame (.array element none 0) fresh)
    (update_temporary_protects
      (targetDeclareTemporary frame (NativeIR.fresh supply).1 (.array element none 0))
      (.array element pointer 0) fresh)
  exact target_checked_array_descriptor_exact raw rawReference callExact
    (declared_temporary_atom interface frame raw.state (NativeIR.fresh supply).1 (.array element)
      (.array element none 0))
    ((protection_atom_evaluation preserved lengthAtom
      (target_atom_read_within bounded countRead) state raw.state _).mp countRead)
    zero root out

end Mettapedia.GSLT.LanguageDef.NativeOps
