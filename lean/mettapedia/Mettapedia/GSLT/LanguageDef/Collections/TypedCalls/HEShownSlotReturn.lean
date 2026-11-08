import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedFieldProjection
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorSource
import Mettapedia.Machines.RegisterCode

/-!
# Compact equation bindings and a shown slot's retained return

These are the local/source/field records used by compact equation entry.
The compiler's first occurrence emits BIND; a later occurrence emits SAME
and cannot be dropped into the compact all-BIND form. Successful compact
entry installs field reads before whole-argument reads. The resulting slot
is exactly the value found by static first-record lookup, including every
evaluation mark. The body uses the existing register lowering and executor.

The origin of each supplied occurrence is the inspected pattern walk's
remaining native lowering obligation. Logical-list decomposition, pointer
ownership and the native key tests are not certified by this module. The
completed-return theorem names the requested reader evidence separately;
typing or a mark alone does not manufacture that evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownSlotReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open Spec.Bindings.ScopeObservation
open Mettapedia.Machines

structure CodeBind where
  slot : Nat
  source : Nat
  field : Option Nat
  deriving DecidableEq, Repr

inductive BindingUse where
  | bind (entry : CodeBind)
  | same (entry : CodeBind)
  deriving DecidableEq, Repr

/-- The variable-occurrence branch of the actual pattern emission walk.
Only a BIND introduces a slot; the recorded slot remains seen thereafter. -/
def emitUses (seen : List Nat) : List CodeBind → List BindingUse
  | [] => []
  | entry :: rest =>
      if entry.slot ∈ seen then .same entry :: emitUses seen rest
      else .bind entry :: emitUses (entry.slot :: seen) rest

def writes : List BindingUse → List CodeBind := List.filterMap fun
  | .bind entry => some entry
  | .same _ => none

def compact (uses : List BindingUse) : Bool := uses.all fun
  | .bind _ => true
  | .same _ => false

def BindingUse.entry : BindingUse → CodeBind
  | .bind entry | .same entry => entry

theorem emitted_entries (seen : List Nat) (occurrences : List CodeBind) :
    (emitUses seen occurrences).map BindingUse.entry = occurrences := by
  induction occurrences generalizing seen with
  | nil => rfl
  | cons first rest ih =>
      simp only [emitUses]
      split <;> simp only [List.map_cons, BindingUse.entry, ih]

theorem compact_writes (uses : List BindingUse) (admitted : compact uses = true) :
    writes uses = uses.map BindingUse.entry := by
  induction uses with
  | nil => rfl
  | cons use rest ih =>
      cases use with
      | same entry => simp [compact] at admitted
      | bind entry =>
          have tail : compact rest = true := by simpa [compact] using admitted
          simpa [writes, BindingUse.entry] using congrArg (List.cons entry) (ih tail)

theorem emitted_not_seen (seen : List Nat) (occurrences : List CodeBind) :
    ∀ entry ∈ writes (emitUses seen occurrences), entry.slot ∉ seen := by
  induction occurrences generalizing seen with
  | nil => simp [emitUses, writes]
  | cons first rest ih =>
      simp only [emitUses]
      split
      next present =>
        simpa only [writes, List.filterMap_cons, List.filterMap_nil] using ih seen
      next fresh =>
        simp only [writes, List.filterMap_cons, List.mem_cons]
        intro entry member
        rcases member with rfl | later
        · exact fresh
        · exact fun wasSeen => ih (first.slot :: seen) entry later (List.mem_cons_of_mem _ wasSeen)

theorem emitted_unique (seen : List Nat) (occurrences : List CodeBind) :
    ((writes (emitUses seen occurrences)).map CodeBind.slot).Nodup := by
  induction occurrences generalizing seen with
  | nil => simp [emitUses, writes]
  | cons first rest ih =>
      simp only [emitUses]
      split
      next present => simpa only [writes, List.filterMap_cons] using ih seen
      next fresh =>
        simp only [writes, List.filterMap_cons, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih (first.slot :: seen)⟩
        intro member
        obtain ⟨entry, written, same⟩ := List.mem_map.mp member
        exact emitted_not_seen (first.slot :: seen) rest entry written (by simp [same])

theorem compact_occurrences_unique (seen : List Nat) (occurrences : List CodeBind)
    (admitted : compact (emitUses seen occurrences) = true) :
    (occurrences.map CodeBind.slot).Nodup := by
  have unique := emitted_unique seen occurrences
  rw [compact_writes _ admitted, emitted_entries] at unique
  exact unique

/-- A repeated occurrence is retained as SAME; compact entry cannot
silently replace its equality test by a second write. -/
theorem repeated_refuses_compact (entry : CodeBind) (seen : List Nat) (rest : List CodeBind)
    (present : entry.slot ∈ seen) : compact (emitUses seen (entry :: rest)) = false := by
  simp [emitUses, present, compact]

def fieldFirst (entries : List CodeBind) : List CodeBind :=
  entries.filter (fun entry => entry.field.isSome) ++ entries.filter (fun entry => !entry.field.isSome)

theorem fieldFirst_perm (entries : List CodeBind) : (fieldFirst entries).Perm entries :=
  List.filter_append_perm _ _

theorem fieldFirst_unique (seen : List Nat) (occurrences : List CodeBind) :
    ((fieldFirst (writes (emitUses seen occurrences))).map CodeBind.slot).Nodup :=
  ((fieldFirst_perm _).map CodeBind.slot).nodup_iff.mpr (emitted_unique seen occurrences)

/-- Native field indices include the constructor head at index zero. The
static type projection separately refuses zero as a data-field index. -/
def readBinding (arguments : List Entry.Value) (entry : CodeBind) : Option Entry.Value :=
  (arguments[entry.source]?).bind fun argument =>
    match entry.field with
    | none => some argument
    | some index => match argument with
        | .expression _ fields => fields[index]?
        | _ => none

def install (arguments : List Entry.Value) :
    List CodeBind → RegisterCode.Regs Entry.Value → Option (RegisterCode.Regs Entry.Value)
  | [], registers => some registers
  | entry :: rest, registers =>
      (readBinding arguments entry).bind fun value =>
        install arguments rest (Function.update registers entry.slot (some value))

theorem install_preserves_other (arguments : List Entry.Value) :
    ∀ (entries : List CodeBind) (before after : RegisterCode.Regs Entry.Value) (slot : Nat),
      (∀ entry ∈ entries, entry.slot ≠ slot) →
      install arguments entries before = some after → after slot = before slot
  | [], before, after, slot, _, entered => by cases Option.some.inj entered; rfl
  | entry :: rest, before, after, slot, absent, entered => by
      simp only [install, Option.bind_eq_some_iff] at entered
      obtain ⟨value, _, entered⟩ := entered
      rw [install_preserves_other arguments rest _ after slot
        (fun next member => absent next (List.mem_cons_of_mem _ member)) entered]
      exact Function.update_of_ne (Ne.symm (absent entry (by simp))) _ _

theorem install_member (arguments : List Entry.Value) :
    ∀ (entries : List CodeBind) (before after : RegisterCode.Regs Entry.Value)
      (entry : CodeBind),
      (entries.map CodeBind.slot).Nodup → entry ∈ entries →
      install arguments entries before = some after →
      after entry.slot = readBinding arguments entry
  | [], _, _, _, _, member, _ => by simp at member
  | first :: rest, before, after, entry, unique, member, entered => by
      obtain ⟨notWritten, restUnique⟩ := List.nodup_cons.mp unique
      simp only [install, Option.bind_eq_some_iff] at entered
      obtain ⟨value, readValue, entered⟩ := entered
      rcases List.mem_cons.mp member with rfl | member
      · rw [install_preserves_other arguments rest _ after entry.slot (by
          intro next member same
          exact notWritten (List.mem_map.mpr ⟨next, member, same⟩)) entered]
        simpa only [Function.update_self] using readValue.symm
      · exact install_member arguments rest _ after entry restUnique member entered

/-- Static first-record lookup and runtime field-first installation agree
because the compiler, rather than a caller assumption, makes writes unique. -/
theorem emitted_lookup_read (seen : List Nat) (occurrences : List CodeBind)
    (arguments : List Entry.Value) (before after : RegisterCode.Regs Entry.Value)
    (slot : Nat) (entry : CodeBind)
    (found : (writes (emitUses seen occurrences)).find? (fun entry => entry.slot == slot) = some entry)
    (entered : install arguments (fieldFirst (writes (emitUses seen occurrences))) before = some after) :
    entry.slot = slot ∧ after slot = readBinding arguments entry := by
  have member := List.mem_of_find?_eq_some found
  have selected := List.find?_some found
  have same : entry.slot = slot := by simpa using selected
  refine ⟨same, ?_⟩
  rw [← same]
  exact install_member arguments _ before after entry (fieldFirst_unique seen occurrences)
    ((fieldFirst_perm _).mem_iff.mpr member) entered

theorem compact_lookup_read (seen : List Nat) (occurrences : List CodeBind)
    (admitted : compact (emitUses seen occurrences) = true)
    (arguments : List Entry.Value) (before after : RegisterCode.Regs Entry.Value)
    (slot : Nat) (entry : CodeBind)
    (found : occurrences.find? (fun entry => entry.slot == slot) = some entry)
    (entered : install arguments (fieldFirst occurrences) before = some after) :
    entry.slot = slot ∧ after slot = readBinding arguments entry := by
  have same : writes (emitUses seen occurrences) = occurrences :=
    (compact_writes _ admitted).trans (emitted_entries seen occurrences)
  apply emitted_lookup_read seen occurrences arguments before after slot entry
  · simpa only [same] using found
  · simpa only [same] using entered

theorem field_read (arguments : List Entry.Value) (entry : CodeBind) (parent : Entry.Status)
    (fields : List Entry.Value) (index : Nat) (value : Entry.Value)
    (source : arguments[entry.source]? = some (.expression parent fields))
    (field : entry.field = some index) (selected : fields[index]? = some value) :
    readBinding arguments entry = some value := by simp [readBinding, source, field, selected]

/-- A slot lowers to an ordinary register return. It does not invoke the
term held in that slot, even when its spelling resembles executable code. -/
theorem slot_code_returns {L O P H : Type} (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (registers : RegisterCode.Regs Entry.Value) (slot destination next : Nat) (value : Entry.Value)
    (present : registers slot = some value) :
    RegisterCode.exec sem answer
      (RegisterCode.compile fuses (.slot slot) true destination next).1 registers = some (.ret value) := by
  simp [RegisterCode.compile, RegisterCode.exec, RegisterCode.step, RegisterCode.read, present,
    RegisterCode.andThen]

/-- Compact entry, ordinary slot lowering, and the existing completed-value
gate compose without re-evaluating the selected field. The requested reader
has to be justified at the reached frame; no diagnostic get-type role is
silently substituted for it. -/
theorem compact_slot_completed {L O P H : Type}
    (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (seen : List Nat) (occurrences : List CodeBind)
    (admitted : compact (emitUses seen occurrences) = true)
    (arguments : List Entry.Value) (before after : RegisterCode.Regs Entry.Value)
    (slot destination next : Nat) (entry : CodeBind) (value : Entry.Value)
    (found : occurrences.find? (fun entry => entry.slot == slot) = some entry)
    (entered : install arguments (fieldFirst occurrences) before = some after)
    (readValue : readBinding arguments entry = some value)
    (space : Space) (lookup : Spec.Type.TypeLookupRel) (policy : Policy) (frame : Frame)
    (range : Atom) (earlier later : List Atom)
    (closedRange : TypeSubst.typeVars range = [])
    (queried : lookup frame.bindings value.erase range (earlier ++ range :: later))
    (rejected : ∀ prior ∈ earlier, ∀ output, ¬policy.matching.Rel range prior frame.bindings output) :
    RegisterCode.exec sem answer
      (RegisterCode.compile fuses (.slot slot) true destination next).1 after = some (.ret value) ∧
    NativeCompletedReturnRel space lookup policy value range frame [(value, frame)] := by
  have stored : after slot = some value :=
    (compact_lookup_read seen occurrences admitted arguments before after slot entry found entered).2.trans readValue
  exact ⟨slot_code_returns sem answer fuses after slot destination next value stored,
    HESelectedConstructorSource.completed_at_closed_range space lookup policy value range frame earlier later
      closedRange queried rejected⟩

/-- Joining a real fresh source capture to compact entry preserves both
representations' value, including held children and the caller's record.
The return service consumes that same value at that same reached frame. -/
theorem captured_slot_completed {L O P H : Type}
    (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (seen : List Nat) (occurrences : List CodeBind)
    (admitted : compact (emitUses seen occurrences) = true)
    (arguments : List Entry.Value) (before after : RegisterCode.Regs Entry.Value)
    (slot destination next : Nat) (entry : CodeBind) (value : Entry.Value)
    (found : occurrences.find? (fun entry => entry.slot == slot) = some entry)
    (entered : install arguments (fieldFirst occurrences) before = some after)
    (readValue : readBinding arguments entry = some value)
    (space : Space) (lookup : Spec.Type.TypeLookupRel) (policy : Policy)
    (caller : Frame) (name : String)
    (fresh : name ∉ specBindingVars caller.bindings)
    (closedValue : TypeSubst.typeVars value.erase = [])
    (range : Atom) (earlier later : List Atom)
    (closedRange : TypeSubst.typeVars range = []) :
    let reached := HEFreshSyntaxBinding.bindFrame policy caller name value fresh (by simp [closedValue])
    lookup reached.bindings value.erase range (earlier ++ range :: later) →
    (∀ prior ∈ earlier, ∀ output, ¬policy.matching.Rel range prior reached.bindings output) →
    RegisterCode.exec sem answer
      (RegisterCode.compile fuses (.slot slot) true destination next).1 after = some (.ret value) ∧
    Entry.Value.UnifyRel policy.rebuilding caller.environment value (.var name) reached.environment ∧
    (∀ readingPolicy, reached.read readingPolicy (.var name) = value) ∧
    NativeCompletedReturnRel space lookup policy value range reached [(value, reached)] ∧
    reached.bindings = HEFreshRangeFrame.extend caller.bindings name value.erase := by
  dsimp only
  intro queried rejected
  have result := compact_slot_completed sem answer fuses seen occurrences admitted arguments before after
    slot destination next entry value found entered readValue space lookup policy _ range earlier later
    closedRange queried rejected
  exact ⟨result.1, HEFreshSyntaxBinding.source_binding policy caller name value fresh closedValue,
    HEFreshSyntaxBinding.bound_read policy caller name value fresh closedValue, result.2,
    HEFreshSyntaxBinding.binding_keeps_caller policy caller name value fresh _⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownSlotReturn
