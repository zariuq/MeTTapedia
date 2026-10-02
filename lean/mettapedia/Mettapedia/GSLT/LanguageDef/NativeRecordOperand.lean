import Mettapedia.GSLT.LanguageDef.NativeRecordAccess

/-!
The ordered native operand guard. A poisoned view stops before its record is
read. A missing record returns no operand without setting a new flag. Bounds
are checked before the operand pointer, which is checked before the selected
kind. These calls do not test allocator ownership. Record fields use the
declared logical profile; physical size_t, enum and pointer layout remain
concrete ABI obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordOperand

open NativeOps (Address SourceState TargetState StateRelated)
open NativeRecordAccess
open NativeWord64 (Word encode)

inductive Kind where
  | word | bytes | words
  deriving DecidableEq, Repr

def sourceKind : Kind → Word
  | .word => 0 | .bytes => 1 | .words => 2

def targetKind : Kind → BitVec 64
  | .word => 0 | .bytes => 1 | .words => 2

theorem kind_correspondence (kind : Kind) : targetKind kind = encode (sourceKind kind) := by
  cases kind <;> rfl

def element (base : Address) (index : Nat) : Address :=
  { base with element := base.element + index }

def SourceReady {World : Type} (state : SourceState World) (view record : Address) : Prop :=
  sourceReadBool state.memory (field view 1) = some false ∧
    sourceReadPointer state.memory (field view 0) = some (some record)

def TargetReady {World : Type} (state : TargetState World) (view record : Address) : Prop :=
  targetReadBool state.memory (field view 1) = some false ∧
    targetReadPointer state.memory (field view 0) = some (some record)

theorem ready_correspondence {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view record : Address) :
    TargetReady target view record ↔ SourceReady source view record := by
  simp only [TargetReady, SourceReady,
    read_bool_correspondence source.memory target.memory related.memory,
    read_pointer_correspondence source.memory target.memory related.memory]

inductive SourceOperand {World : Type} : SourceState World → Option Address → Word → Kind →
    Option Address → SourceState World → Prop where
  | null (state : SourceState World) (index : Word) (kind : Kind) :
      SourceOperand state none index kind none state
  | poisoned {state : SourceState World} {view : Address} (index : Word) (kind : Kind)
      (poisoned : sourceReadBool state.memory (field view 1) = some true) :
      SourceOperand state (some view) index kind none state
  | absentRecord {state : SourceState World} {view : Address} (index : Word) (kind : Kind)
      (clear : sourceReadBool state.memory (field view 1) = some false)
      (absent : sourceReadPointer state.memory (field view 0) = some none) :
      SourceOperand state (some view) index kind none state
  | outOfRange {state post : SourceState World} {view record : Address} {index count : Word}
      (kind : Kind) (ready : SourceReady state view record)
      (counted : sourceReadWord state.memory (field record 3) = some count)
      (outside : count.val ≤ index.val) (poisoned : sourceSetFault state view = some post) :
      SourceOperand state (some view) index kind none post
  | absentOperands {state post : SourceState World} {view record : Address} {index count : Word}
      (kind : Kind) (ready : SourceReady state view record)
      (counted : sourceReadWord state.memory (field record 3) = some count)
      (inside : index.val < count.val)
      (absent : sourceReadPointer state.memory (field record 2) = some none)
      (poisoned : sourceSetFault state view = some post) :
      SourceOperand state (some view) index kind none post
  | wrongKind {state post : SourceState World} {view record operands : Address}
      {index count actual : Word} (kind : Kind) (ready : SourceReady state view record)
      (counted : sourceReadWord state.memory (field record 3) = some count)
      (inside : index.val < count.val)
      (present : sourceReadPointer state.memory (field record 2) = some (some operands))
      (selected : sourceReadWord state.memory (field (element operands index.val) 1) = some actual)
      (different : actual ≠ sourceKind kind) (poisoned : sourceSetFault state view = some post) :
      SourceOperand state (some view) index kind none post
  | found {state : SourceState World} {view record operands : Address} {index count : Word}
      (kind : Kind) (ready : SourceReady state view record)
      (counted : sourceReadWord state.memory (field record 3) = some count)
      (inside : index.val < count.val)
      (present : sourceReadPointer state.memory (field record 2) = some (some operands))
      (selected : sourceReadWord state.memory (field (element operands index.val) 1) =
        some (sourceKind kind)) :
      SourceOperand state (some view) index kind (some (element operands index.val)) state

inductive TargetOperand {World : Type} : TargetState World → Option Address → BitVec 64 → Kind →
    Option Address → TargetState World → Prop where
  | null (state : TargetState World) (index : BitVec 64) (kind : Kind) :
      TargetOperand state none index kind none state
  | poisoned {state : TargetState World} {view : Address} (index : BitVec 64) (kind : Kind)
      (poisoned : targetReadBool state.memory (field view 1) = some true) :
      TargetOperand state (some view) index kind none state
  | absentRecord {state : TargetState World} {view : Address} (index : BitVec 64) (kind : Kind)
      (clear : targetReadBool state.memory (field view 1) = some false)
      (absent : targetReadPointer state.memory (field view 0) = some none) :
      TargetOperand state (some view) index kind none state
  | outOfRange {state post : TargetState World} {view record : Address} {index count : BitVec 64}
      (kind : Kind) (ready : TargetReady state view record)
      (counted : targetReadWord state.memory (field record 3) = some count)
      (outside : count.toNat ≤ index.toNat) (poisoned : targetSetFault state view = some post) :
      TargetOperand state (some view) index kind none post
  | absentOperands {state post : TargetState World} {view record : Address} {index count : BitVec 64}
      (kind : Kind) (ready : TargetReady state view record)
      (counted : targetReadWord state.memory (field record 3) = some count)
      (inside : index.toNat < count.toNat)
      (absent : targetReadPointer state.memory (field record 2) = some none)
      (poisoned : targetSetFault state view = some post) :
      TargetOperand state (some view) index kind none post
  | wrongKind {state post : TargetState World} {view record operands : Address}
      {index count actual : BitVec 64} (kind : Kind) (ready : TargetReady state view record)
      (counted : targetReadWord state.memory (field record 3) = some count)
      (inside : index.toNat < count.toNat)
      (present : targetReadPointer state.memory (field record 2) = some (some operands))
      (selected : targetReadWord state.memory (field (element operands index.toNat) 1) = some actual)
      (different : actual ≠ targetKind kind) (poisoned : targetSetFault state view = some post) :
      TargetOperand state (some view) index kind none post
  | found {state : TargetState World} {view record operands : Address} {index count : BitVec 64}
      (kind : Kind) (ready : TargetReady state view record)
      (counted : targetReadWord state.memory (field record 3) = some count)
      (inside : index.toNat < count.toNat)
      (present : targetReadPointer state.memory (field record 2) = some (some operands))
      (selected : targetReadWord state.memory (field (element operands index.toNat) 1) =
        some (targetKind kind)) :
      TargetOperand state (some view) index kind (some (element operands index.toNat)) state

private theorem different_kind (actual : Word) (kind : Kind)
    (different : actual ≠ sourceKind kind) : encode actual ≠ targetKind kind := by
  intro same
  rw [kind_correspondence] at same
  apply different
  apply Fin.ext
  have values := congrArg BitVec.toNat same
  simpa only [NativeWord64.encode_toNat] using values

theorem operand_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address)
    (index : Word) (kind : Kind) (selected : Option Address) (post : SourceState SourceWorld)
    (called : SourceOperand source view index kind selected post) :
    ∃ native, TargetOperand target view (encode index) kind selected native ∧
      StateRelated worldRelated post native := by
  cases called with
  | null => exact ⟨target, .null target (encode index) kind, related⟩
  | poisoned _ _ poisoned =>
    exact ⟨target, .poisoned (encode index) kind
      (by rwa [read_bool_correspondence source.memory target.memory related.memory]), related⟩
  | absentRecord _ _ clear absent =>
    exact ⟨target, .absentRecord (encode index) kind
      (by rwa [read_bool_correspondence source.memory target.memory related.memory])
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory]), related⟩
  | @outOfRange _ view record _ count kind ready counted outside poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .outOfRange kind
      ((ready_correspondence source target related view record).mpr ready)
      ((read_word_result_iff source.memory target.memory related.memory _ count).mpr counted)
      (by simpa only [NativeWord64.encode_toNat] using outside) nativePoisoned, postRelated⟩
  | @absentOperands _ view record _ count kind ready counted inside absent poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .absentOperands kind
      ((ready_correspondence source target related view record).mpr ready)
      ((read_word_result_iff source.memory target.memory related.memory _ count).mpr counted)
      (by simpa only [NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory])
      nativePoisoned, postRelated⟩
  | @wrongKind _ view record operands _ count actual kind ready counted inside present selected
      different poisoned =>
    obtain ⟨native, nativePoisoned, postRelated⟩ :=
      set_fault_forward source target related view post poisoned
    exact ⟨native, .wrongKind kind
      ((ready_correspondence source target related view record).mpr ready)
      ((read_word_result_iff source.memory target.memory related.memory _ count).mpr counted)
      (by simpa only [NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory])
      (by simpa only [NativeWord64.encode_toNat] using
        (read_word_result_iff source.memory target.memory related.memory
          (field (element operands index.val) 1) actual).mpr selected)
      (different_kind actual kind different) nativePoisoned, postRelated⟩
  | @found view record operands _ count kind ready counted inside present selected =>
    have nativeSelected : targetReadWord target.memory
        (field (element operands (encode index).toNat) 1) = some (targetKind kind) := by
      simpa only [NativeWord64.encode_toNat, kind_correspondence] using
        (read_word_result_iff source.memory target.memory related.memory
          (field (element operands index.val) 1) (sourceKind kind)).mpr selected
    refine ⟨target, ?_, related⟩
    simpa only [NativeWord64.encode_toNat] using TargetOperand.found kind
      ((ready_correspondence source target related view record).mpr ready)
      ((read_word_result_iff source.memory target.memory related.memory _ count).mpr counted)
      (by simpa only [NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory]) nativeSelected

theorem operand_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address)
    (index : Word) (kind : Kind) (selected : Option Address) (native : TargetState TargetWorld)
    (called : TargetOperand target view (encode index) kind selected native) :
    ∃ post, SourceOperand source view index kind selected post ∧
      StateRelated worldRelated post native := by
  cases called with
  | null => exact ⟨source, .null source index kind, related⟩
  | poisoned _ _ poisoned =>
    exact ⟨source, .poisoned index kind
      (by rwa [read_bool_correspondence source.memory target.memory related.memory] at poisoned),
      related⟩
  | absentRecord _ _ clear absent =>
    exact ⟨source, .absentRecord index kind
      (by rwa [read_bool_correspondence source.memory target.memory related.memory] at clear)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at absent),
      related⟩
  | @outOfRange _ view record _ count kind ready counted outside poisoned =>
    obtain ⟨value, sourceCount, countEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ count counted
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    exact ⟨post, .outOfRange kind
      ((ready_correspondence source target related view record).mp ready) sourceCount
      (by simpa only [countEqual, NativeWord64.encode_toNat] using outside) sourcePoisoned,
      postRelated⟩
  | @absentOperands _ view record _ count kind ready counted inside absent poisoned =>
    obtain ⟨value, sourceCount, countEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ count counted
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    exact ⟨post, .absentOperands kind
      ((ready_correspondence source target related view record).mp ready) sourceCount
      (by simpa only [countEqual, NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at absent)
      sourcePoisoned, postRelated⟩
  | @wrongKind _ view record operands _ count actual kind ready counted inside present selected
      different poisoned =>
    obtain ⟨value, sourceCount, countEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ count counted
    obtain ⟨actualValue, sourceActual, actualEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ actual selected
    obtain ⟨post, sourcePoisoned, postRelated⟩ :=
      set_fault_backward source target related view native poisoned
    have differentSource : actualValue ≠ sourceKind kind := by
      intro same
      apply different
      rw [actualEqual, same, kind_correspondence]
    exact ⟨post, .wrongKind kind
      ((ready_correspondence source target related view record).mp ready) sourceCount
      (by simpa only [countEqual, NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at present)
      (by simpa only [NativeWord64.encode_toNat] using sourceActual)
      differentSource sourcePoisoned, postRelated⟩
  | @found view record operands _ count kind ready counted inside present selected =>
    obtain ⟨value, sourceCount, countEqual⟩ :=
      read_word_backward source.memory target.memory related.memory _ count counted
    have sourceSelected : sourceReadWord source.memory
        (field (element operands index.val) 1) = some (sourceKind kind) := by
      apply (read_word_result_iff source.memory target.memory related.memory _ _).mp
      simpa only [NativeWord64.encode_toNat, kind_correspondence] using selected
    refine ⟨source, ?_, related⟩
    simpa only [NativeWord64.encode_toNat] using SourceOperand.found kind
      ((ready_correspondence source target related view record).mp ready) sourceCount
      (by simpa only [countEqual, NativeWord64.encode_toNat] using inside)
      (by rwa [read_pointer_correspondence source.memory target.memory related.memory] at present)
      sourceSelected

theorem operand_preserves_nonmemory_state {World : Type} (state : SourceState World)
    (view : Option Address) (index : Word) (kind : Kind) (selected : Option Address)
    (post : SourceState World) (called : SourceOperand state view index kind selected post) :
    post.fault = state.fault ∧ post.external = state.external ∧
      post.allocatorStats = state.allocatorStats ∧ post.allocatorAvailable = state.allocatorAvailable ∧
      post.releaseAvailable = state.releaseAvailable := by
  cases called with
  | null => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | poisoned _ _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | absentRecord _ _ _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | outOfRange _ _ _ _ poisoned => exact source_set_fault_preserves_context _ _ _ poisoned
  | absentOperands _ _ _ _ _ poisoned => exact source_set_fault_preserves_context _ _ _ poisoned
  | wrongKind _ _ _ _ _ _ _ poisoned => exact source_set_fault_preserves_context _ _ _ poisoned
  | found _ _ _ _ _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem poisoned_view_cannot_select_an_operand {World : Type} (state : SourceState World)
    (view operand : Address) (index : Word) (kind : Kind) (post : SourceState World)
    (poisoned : sourceReadBool state.memory (field view 1) = some true) :
    ¬ SourceOperand state (some view) index kind (some operand) post := by
  intro called
  cases called with
  | found _ ready _ _ _ _ =>
    have incompatible : some true = some false := poisoned.symm.trans ready.1
    cases incompatible

theorem null_view_returns_no_operand {World : Type} (state : SourceState World)
    (index : Word) (kind : Kind) : SourceOperand state none index kind none state :=
  .null state index kind

theorem a_poisoned_view_needs_no_record_read {World : Type} (state : SourceState World)
    (view : Address) (index : Word) (kind : Kind)
    (poisoned : sourceReadBool state.memory (field view 1) = some true) :
    SourceOperand state (some view) index kind none state := .poisoned index kind poisoned

end Mettapedia.GSLT.LanguageDef.NativeRecordOperand
