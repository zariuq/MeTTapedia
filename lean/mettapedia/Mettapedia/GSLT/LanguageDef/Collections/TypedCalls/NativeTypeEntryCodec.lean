import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ShapeTyping
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RetainedTypePayloads

/-!
# Native node-entry fields, query modes and retained state identifiers

The represented entry uses the native address/epoch word widths and the
arena/question/state widths. Address and question select an occupied entry;
arena and epoch then validate its incarnation. State identifiers are one-based:
zero is a miss, whereas a nonzero identifier may denote a completed empty list.

The entry view is an association-list projection of occupied native slots.
Its search/replace laws do not verify the physical linear-probing loop, C
structure layout, allocation or the evaluator's metadata reader. The semantic
lookup is the independently established heap/arena lookup in `ShapeTyping`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryCodec

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

structure Entry where
  address : UInt64
  epoch : UInt64
  arena : UInt32
  question : UInt32
  state : UInt32
  deriving DecidableEq, Repr

abbrev Table := List Entry
abbrev States := List (List Atom)

def mode (question : UInt32) : Option Bool :=
  if question = 0 then some true else if question = 1 then some false else none

def modeCode (direct : Bool) : UInt32 := if direct then 0 else 1

theorem mode_readback (direct : Bool) : mode (modeCode direct) = some direct := by
  cases direct <;> decide

theorem mode_unique (question : UInt32) (direct : Bool) (selected : mode question = some direct) :
    question = modeCode direct := by
  cases direct <;> by_cases zero : question = 0 <;> by_cases one : question = 1 <;>
    simp_all [mode, modeCode]

def call (question : UInt32) (atom : Atom) : Option NativeTypeCallGraph.Call :=
  (mode question).map fun direct => .infer direct atom

theorem call_readback (direct : Bool) (atom : Atom) :
    call (modeCode direct) atom = some (.infer direct atom) := by
  simp [call, mode_readback]

def payload (states : States) (id : UInt32) : Option (List Atom) :=
  if id = 0 then none else RetainedTypePayloads.materialize states (id.toNat - 1)

theorem zero_is_miss (states : States) : payload states 0 = none := by simp [payload]

theorem nonzero_payload (states : States) (id : UInt32) (nonzero : id ≠ 0) :
    payload states id = states[id.toNat - 1]? := by
  cases found : states[id.toNat - 1]? <;>
    simp [payload, nonzero, RetainedTypePayloads.materialize, found, RetainedTypePayloads.copyList_eq]

theorem payload_from_materialize (states : States) (index : Nat) (types : List Atom)
    (bounded : index + 1 < UInt32.size)
    (materialized : RetainedTypePayloads.materialize states index = some types) :
    payload states (UInt32.ofNat (index + 1)) = some types := by
  have value := UInt32.toNat_ofNat_of_lt' bounded
  have nonzero : UInt32.ofNat (index + 1) ≠ 0 := by
    intro zero
    have impossible := congrArg UInt32.toNat zero
    simp only [value, UInt32.toNat_zero] at impossible
    omega
  simpa only [payload, nonzero, if_false, value, Nat.add_sub_cancel] using materialized

def keyMatches (address : UInt64) (question : UInt32) (entry : Entry) : Bool :=
  entry.address != 0 && entry.address == address && entry.question == question

def find (entries : Table) (address : UInt64) (question : UInt32) : Option Entry :=
  entries.find? (keyMatches address question)

theorem find_fields (entries : Table) (address : UInt64) (question : UInt32)
    (entry : Entry) (found : find entries address question = some entry) :
    entry ∈ entries ∧ entry.address ≠ 0 ∧ entry.address = address ∧ entry.question = question := by
  have member := List.mem_of_find?_eq_some found
  have selected := List.find?_some (p := keyMatches address question) found
  simpa [keyMatches, Bool.and_eq_true, and_assoc] using And.intro member selected

def nodeState (entries : Table) (address : UInt64) (question arena : UInt32) (epoch : UInt64) : UInt32 :=
  match find entries address question with
  | none => 0
  | some entry => if entry.arena = arena ∧ entry.epoch = epoch then entry.state else 0

def read (entries : Table) (states : States) (address : UInt64)
    (question arena : UInt32) (epoch : UInt64) : Option (List Atom) :=
  payload states (nodeState entries address question arena epoch)

def inquiryRead (entries : Table) (states : States) (address : UInt64)
    (question arena : UInt32) (epoch : UInt64) : Option (List Atom) :=
  if (mode question).isSome then read entries states address question arena epoch else none

theorem inquiryRead_code (entries : Table) (states : States) (address : UInt64)
    (direct : Bool) (arena : UInt32) (epoch : UInt64) :
    inquiryRead entries states address (modeCode direct) arena epoch =
      read entries states address (modeCode direct) arena epoch := by
  simp only [inquiryRead, mode_readback, Option.isSome_some, if_true]

theorem inquiryRead_unsupported (entries : Table) (states : States) (address : UInt64)
    (question arena : UInt32) (epoch : UInt64) (unsupported : mode question = none) :
    inquiryRead entries states address question arena epoch = none := by
  simp only [inquiryRead, unsupported, Option.isSome_none, Bool.false_eq_true, if_false]

/-- The abstract memo retains all incarnation fields, rather than treating
the address/question hash as proof of ownership. -/
def memo (entries : Table) (states : States) (question : UInt32) :
    ShapeTyping.AddrMemo UInt64 (Option (List Atom)) := fun address => do
  let entry ← find entries address question
  let types ← payload states entry.state
  some (entry.arena.toNat, entry.epoch.toNat, some types)

/-- A metadata reader that supplies this cell and epoch makes native field
validation exactly the existing arena-validated logical lookup. -/
theorem read_eq_lookup (entries : Table) (states : States) (heap : ShapeTyping.Heap UInt64)
    (address : UInt64) (question arena : UInt32) (epoch : UInt64) (atom : Atom)
    (cell : heap.cell address = some (atom, arena.toNat))
    (current : heap.epoch arena.toNat = epoch.toNat) :
    read entries states address question arena epoch =
      (ShapeTyping.lookupAt heap (memo entries states question) address).join := by
  cases found : find entries address question with
  | none => simp [read, nodeState, memo, found, ShapeTyping.lookupAt, zero_is_miss]
  | some entry =>
      by_cases same : entry.arena = arena ∧ entry.epoch = epoch
      · obtain ⟨sameArena, sameEpoch⟩ := same
        subst sameArena
        subst sameEpoch
        cases retained : payload states entry.state <;>
          simp [read, nodeState, memo, found, retained, ShapeTyping.lookupAt, cell, current]
      · have different : ¬ (entry.arena.toNat = arena.toNat ∧ entry.epoch.toNat = epoch.toNat) := by
          rintro ⟨sameArena, sameEpoch⟩
          exact same ⟨UInt32.toNat_inj.mp sameArena, UInt64.toNat_inj.mp sameEpoch⟩
        cases retained : payload states entry.state <;>
          simp [read, nodeState, memo, found, same, retained, ShapeTyping.lookupAt, cell, current, different,
            zero_is_miss]

def replace (entry : Entry) (entries : Table) : Table :=
  entry :: entries.filter (fun old => !keyMatches entry.address entry.question old)

theorem find_replace_same (entries : Table) (entry : Entry) (occupied : entry.address ≠ 0) :
    find (replace entry entries) entry.address entry.question = some entry := by
  simp [find, replace, keyMatches, occupied]

theorem find_replace_other (entries : Table) (entry : Entry) (address : UInt64) (question : UInt32)
    (different : address ≠ entry.address ∨ question ≠ entry.question) :
    find (replace entry entries) address question = find entries address question := by
  have rejected : keyMatches address question entry = false := by
    rcases different with different | different <;> simp [keyMatches, Ne.symm different]
  simp only [find, replace, List.find?_cons, rejected]
  induction entries with
  | nil => rfl
  | cons old entries ih =>
      by_cases removed : keyMatches entry.address entry.question old = true
      · have fields : old.address = entry.address ∧ old.question = entry.question := by
          have all : old.address ≠ 0 ∧ old.address = entry.address ∧ old.question = entry.question := by
            simpa [keyMatches, Bool.and_eq_true, and_assoc] using removed
          exact all.2
        have skip : keyMatches address question old = false := by
          rcases different with different | different <;> simp [keyMatches, fields.1, fields.2, Ne.symm different]
        simpa only [List.filter_cons, removed, Bool.not_true, Bool.false_eq_true, if_false,
          List.find?_cons, skip] using ih
      · have kept : keyMatches entry.address entry.question old = false := Bool.eq_false_of_not_eq_true removed
        cases selected : keyMatches address question old <;>
          simp only [List.filter_cons, kept, Bool.not_false, if_true, List.find?_cons, selected]
        exact ih

def storedPayload (states : States) (entry : Entry) : Option (Nat × Nat × Option (List Atom)) :=
  (payload states entry.state).map fun types => (entry.arena.toNat, entry.epoch.toNat, some types)

theorem memo_replace_same (entries : Table) (states : States) (entry : Entry)
    (occupied : entry.address ≠ 0) :
    memo (replace entry entries) states entry.question =
      Function.update (memo entries states entry.question) entry.address (storedPayload states entry) := by
  funext address
  by_cases same : address = entry.address
  · subst address
    cases retained : payload states entry.state <;>
      simp [memo, find_replace_same entries entry occupied, storedPayload, retained]
  · simp only [Function.update_of_ne same, memo,
      find_replace_other entries entry address entry.question (.inl same)]

theorem memo_replace_other_question (entries : Table) (states : States) (entry : Entry)
    (question : UInt32) (different : question ≠ entry.question) :
    memo (replace entry entries) states question = memo entries states question := by
  funext address
  simp only [memo, find_replace_other entries entry address question (.inr different)]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryCodec
