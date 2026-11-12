import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryCodec
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoRefinement

/-!
# Word-coded node entries retain completed source inquiries

The entry projection is connected to the established heap/reset invariant.
The source instance is the actual occurrence-scoped inference driver at its
structural completion depth, with unfinished or malformed observations kept
distinct from a completed empty family. Historical retained-read evidence
derives the value recorded for a native question code.

The lookup/record theorems concern the occupied-entry projection and correctly
read metadata. Physical probing, C layout and metadata-reader fidelity remain
implementation obligations. Heap operations use the established immutable
cell/allocation/reset protocol, not arbitrary writes within one incarnation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntrySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeEntryCodec
open NativeTypeCallGraph NativeTypeSourcePorts
open RetainedTypePayloads (ExternalView)

abbrev Meaning := Bool → Atom → Option (List Atom)

def Sound (heap : ShapeTyping.Heap UInt64) (meaning : Meaning) (entries : Table) (states : States) : Prop :=
  ∀ direct, ShapeTyping.Sound heap (meaning direct) (memo entries states (modeCode direct))

theorem empty_sound (heap : ShapeTyping.Heap UInt64) (meaning : Meaning) (states : States) :
    Sound heap meaning [] states := by
  intro direct
  exact ShapeTyping.sound_empty heap (meaning direct)

theorem sound_heap_run (heap : ShapeTyping.Heap UInt64) (meaning : Meaning) (entries : Table) (states : States)
    (valid : Sound heap meaning entries states) (operations : List (ShapeTyping.HeapOp UInt64)) :
    Sound (heap.run operations) meaning entries states :=
  fun direct => ShapeTyping.sound_run (valid direct) operations

theorem source_hit (heap : ShapeTyping.Heap UInt64) (meaning : Meaning) (entries : Table) (states : States)
    (valid : Sound heap meaning entries states) (address : UInt64) (direct : Bool)
    (arena : UInt32) (epoch : UInt64) (atom : Atom) (types : List Atom)
    (cell : heap.cell address = some (atom, arena.toNat))
    (current : heap.epoch arena.toNat = epoch.toNat)
    (hit : read entries states address (modeCode direct) arena epoch = some types) :
    meaning direct atom = some types := by
  rw [read_eq_lookup entries states heap address (modeCode direct) arena epoch atom cell current] at hit
  change (ShapeTyping.lookupAt heap (memo entries states (modeCode direct)) address).bind id = some types at hit
  obtain ⟨retained, found, returned⟩ := Option.bind_eq_some_iff.mp hit
  change retained = some types at returned
  rw [returned] at found
  obtain ⟨other, otherArena, present, answer⟩ := ShapeTyping.validated_hit (valid direct) found
  have same := Option.some.inj (present.symm.trans cell)
  cases (Prod.mk.inj same).1
  exact answer.symm

theorem modeCode_injective : Function.Injective modeCode := by
  intro first second same
  cases first <;> cases second <;> simp_all [modeCode]

/-- A native record is sound for the selected inquiry and does not replace
the other inquiry's entry at the same address. -/
theorem record_sound (heap : ShapeTyping.Heap UInt64) (meaning : Meaning) (entries : Table) (states : States)
    (valid : Sound heap meaning entries states) (entry : Entry) (direct : Bool) (atom : Atom) (types : List Atom)
    (occupied : entry.address ≠ 0) (question : entry.question = modeCode direct)
    (cell : heap.cell entry.address = some (atom, entry.arena.toNat))
    (current : heap.epoch entry.arena.toNat = entry.epoch.toNat)
    (materialized : payload states entry.state = some types)
    (computed : meaning direct atom = some types) :
    Sound heap meaning (replace entry entries) states := by
  intro other
  by_cases same : other = direct
  · subst other
    rw [← question, memo_replace_same entries states entry occupied]
    simp only [storedPayload, materialized, Option.map_some]
    have old : ShapeTyping.Sound heap (meaning direct) (memo entries states entry.question) := by
      simpa only [question] using valid direct
    have recorded := ShapeTyping.sound_record old cell
    rw [current, computed] at recorded
    exact recorded
  · have different : modeCode other ≠ entry.question := by
      intro equal
      rw [question] at equal
      exact same (modeCode_injective equal)
    rw [memo_replace_other_question entries states entry (modeCode other) different]
    exact valid other

def replyTypes : Option Reply → Option (List Atom)
  | some (.types types) => some types
  | _ => none

noncomputable def sourceMeaning (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) : Meaning := fun direct atom =>
  let call := NativeTypeCallGraph.Call.infer direct atom
  replyTypes (NativeTypeScopedReads.evaluate ops source external
    (TypeReadQueryMemoRefinement.completionDepth call) call ⟨[], 0⟩).1

theorem recorded_meaning (source : Source) (external : ExternalView)
    (safe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (direct : Bool) (atom : Atom) (types : List Atom)
    (recorded : TypeReadQueryMemo.Recorded (TypeScopeMatcher.currentOps external normalize subtypes)
      source external TypeReadQueryMemoRefinement.completionDepth (.infer direct atom) types) :
    sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes) source external direct atom = some types := by
  have returned := TypeReadQueryMemoRefinement.recorded_at source external safe alpha normalize normalizer subtypes
    TypeReadQueryMemoRefinement.completionDepth TypeReadQueryMemoRefinement.completion_saturated
    (.infer direct atom) types recorded
    (TypeReadQueryMemoRefinement.completionDepth (.infer direct atom))
    (TypeReadQueryMemoRefinement.completion_saturated _) ⟨[], 0⟩
  exact congrArg replyTypes returned

/-- The semantic value premise of a native record is discharged by an
actual historical completed read, retaining the immutable payload test. -/
theorem record_from_source (source : Source) (external : ExternalView)
    (safe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom)
    (heap : ShapeTyping.Heap UInt64) (entries : Table) (states : States)
    (valid : Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      source external) entries states)
    (entry : Entry) (direct : Bool) (atom : Atom) (types : List Atom)
    (occupied : entry.address ≠ 0) (question : entry.question = modeCode direct)
    (cell : heap.cell entry.address = some (atom, entry.arena.toNat))
    (current : heap.epoch entry.arena.toNat = entry.epoch.toNat)
    (materialized : payload states entry.state = some types)
    (recorded : TypeReadQueryMemo.Recorded (TypeScopeMatcher.currentOps external normalize subtypes)
      source external TypeReadQueryMemoRefinement.completionDepth (.infer direct atom) types) :
    Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      source external) (replace entry entries) states :=
  record_sound heap _ entries states valid entry direct atom types occupied question cell current materialized
    (recorded_meaning source external safe alpha normalize normalizer subtypes direct atom types recorded)

/-- Native field validation after heap activity returns the independently
defined source inquiry, not an address-only remembered answer. -/
theorem source_hit_after_heap_run (source : Source) (external : ExternalView)
    (normalize : Atom → Atom) (subtypes : List Atom → List Atom)
    (heap : ShapeTyping.Heap UInt64) (entries : Table) (states : States)
    (valid : Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      source external) entries states)
    (operations : List (ShapeTyping.HeapOp UInt64)) (address : UInt64) (direct : Bool)
    (arena : UInt32) (epoch : UInt64) (atom : Atom) (types : List Atom)
    (cell : (heap.run operations).cell address = some (atom, arena.toNat))
    (current : (heap.run operations).epoch arena.toNat = epoch.toNat)
    (hit : read entries states address (modeCode direct) arena epoch = some types) :
    sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes) source external direct atom = some types :=
  source_hit (heap.run operations) _ entries states (sound_heap_run heap _ entries states valid operations)
    address direct arena epoch atom types cell current hit

/-- Relevant occupied entries already name a materialized state, or the
explicit zero sentinel. Merely being a miss today is not sufficient. -/
def StateIdsPresent (entries : Table) (states : States) : Prop :=
  ∀ entry ∈ entries, (mode entry.question).isSome = true →
    entry.state = 0 ∨ ∃ types, payload states entry.state = some types

theorem state_ids_record (entries : Table) (states : States) (present : StateIdsPresent entries states)
    (entry : Entry) (types : List Atom) (materialized : payload states entry.state = some types) :
    StateIdsPresent (replace entry entries) states := by
  intro other member known
  rcases List.mem_cons.mp member with rfl | member
  · exact .inr ⟨types, materialized⟩
  · exact present other (List.mem_of_mem_filter member) known

theorem payload_intern_preserved (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (states : States) (index : Nat) (after : States)
    (stored : RetainedTypePayloads.intern external hash query states = some (index, after))
    (id : UInt32) (types : List Atom) (before : payload states id = some types) :
    payload after id = some types := by
  by_cases zero : id = 0
  · simp [zero, zero_is_miss] at before
  · simp only [payload, zero, if_false] at before ⊢
    exact RetainedTypePayloads.intern_preserves_materialized external hash query states index after stored
      (id.toNat - 1) types before

theorem state_ids_after_intern (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (entries : Table) (states : States) (index : Nat) (after : States)
    (present : StateIdsPresent entries states)
    (stored : RetainedTypePayloads.intern external hash query states = some (index, after)) :
    StateIdsPresent entries after := by
  intro entry member known
  rcases present entry member known with zero | ⟨types, materialized⟩
  · exact .inl zero
  · exact .inr ⟨types, payload_intern_preserved external hash query states index after stored
      entry.state types materialized⟩

/-- The old entries keep their exact semantic memo after actual interning.
Unknown inquiry roles are outside this type-family projection. -/
theorem memo_after_intern (external : ExternalView) (hash : List Atom → Nat)
    (query : List Atom) (entries : Table) (states : States) (index : Nat) (after : States)
    (present : StateIdsPresent entries states)
    (stored : RetainedTypePayloads.intern external hash query states = some (index, after))
    (direct : Bool) : memo entries after (modeCode direct) = memo entries states (modeCode direct) := by
  funext address
  cases found : find entries address (modeCode direct) with
  | none => simp [memo, found]
  | some entry =>
      obtain ⟨member, _, _, question⟩ := find_fields entries address (modeCode direct) entry found
      have known : (mode entry.question).isSome = true := by rw [question, mode_readback]; rfl
      rcases present entry member known with zero | ⟨types, materialized⟩
      · simp [memo, found, zero, zero_is_miss]
      · have preserved := payload_intern_preserved external hash query states index after stored
          entry.state types materialized
        simp [memo, found, materialized, preserved]

theorem sound_after_intern (heap : ShapeTyping.Heap UInt64) (meaning : Meaning)
    (external : ExternalView) (hash : List Atom → Nat) (query : List Atom)
    (entries : Table) (states : States) (index : Nat) (after : States)
    (valid : Sound heap meaning entries states) (present : StateIdsPresent entries states)
    (stored : RetainedTypePayloads.intern external hash query states = some (index, after)) :
    Sound heap meaning entries after := by
  intro direct
  rw [memo_after_intern external hash query entries states index after present stored direct]
  exact valid direct

/-- Completed source evidence, the actual interner and the one-based word
codec jointly discharge a newly recorded entry. No injective hash is needed. -/
theorem intern_record_from_source (source : Source) (external : ExternalView)
    (safe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (hash : List Atom → Nat)
    (heap : ShapeTyping.Heap UInt64) (entries : Table) (states : States)
    (valid : Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      source external) entries states)
    (present : StateIdsPresent entries states) (statesSafe : RetainedTypePayloads.Valid states)
    (entry : Entry) (direct : Bool) (atom : Atom) (types : List Atom)
    (occupied : entry.address ≠ 0) (question : entry.question = modeCode direct)
    (cell : heap.cell entry.address = some (atom, entry.arena.toNat))
    (current : heap.epoch entry.arena.toNat = entry.epoch.toNat)
    (recorded : TypeReadQueryMemo.Recorded (TypeScopeMatcher.currentOps external normalize subtypes)
      source external TypeReadQueryMemoRefinement.completionDepth (.infer direct atom) types)
    (index : Nat) (after : States)
    (stored : RetainedTypePayloads.intern external hash types states = some (index, after))
    (bounded : index + 1 < UInt32.size) :
    Sound heap (sourceMeaning (TypeScopeMatcher.currentOps external normalize subtypes)
      source external) (replace { entry with state := UInt32.ofNat (index + 1) } entries) after := by
  have old := sound_after_intern heap _ external hash types entries states index after valid present stored
  have materialized := (RetainedTypePayloads.intern_sound external hash types states statesSafe index after stored).2.1
  exact record_from_source source external safe alpha normalize normalizer subtypes heap entries after old
    { entry with state := UInt32.ofNat (index + 1) } direct atom types occupied question cell current
    (payload_from_materialize after index types bounded materialized) recorded

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntrySource
