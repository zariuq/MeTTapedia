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
  constructor
  · intro ran
    cases ran with
    | helper called stored =>
        cases (target_index_call_exact view position _).mp called
        cases stored with
        | fresh _ => rfl
        | existing notTemporary _ => exact False.elim (notTemporary identity (.ref element) rfl)
  · intro same
    subst out
    exact .helper (.index view position) (.fresh unused)

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

end Mettapedia.GSLT.LanguageDef.NativeOps
