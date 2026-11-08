import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotOrigins

/-!
# Successful compiled pattern matching retains its recovered field

The ordinary EXPR operation copies a contiguous block of annotated fields.
Its origin analysis records only whole arguments and their immediate fields,
as the native static slot reader does. Nested expression registers are fresh
but receive no first-level origin. SAME checks never overwrite a local slot.
The source pattern compiler supplies allocation and single-write facts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotReadback

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval
open Mettapedia.Machines
open HEPatternSlotOrigins

def writeBlock {Value : Type} (base : Nat) (values : List Value)
    (registers : RegisterCode.Regs Value) : RegisterCode.Regs Value := fun index =>
  if base ≤ index then (values[index - base]?).or (registers index) else registers index

theorem writeBlock_before {Value : Type} (base : Nat) (values : List Value)
    (registers : RegisterCode.Regs Value) (index : Nat) (before : index < base) :
    writeBlock base values registers index = registers index := by simp [writeBlock, Nat.not_le.mpr before]

theorem writeBlock_at {Value : Type} (base : Nat) (values : List Value)
    (registers : RegisterCode.Regs Value) (index : Nat) (value : Value)
    (selected : values[index]? = some value) :
    writeBlock base values registers (base + index) = some value := by
  simp [writeBlock, selected]

theorem writeBlock_after {Value : Type} (base : Nat) (values : List Value)
    (registers : RegisterCode.Regs Value) (index : Nat) (after : base + values.length ≤ index) :
    writeBlock base values registers index = registers index := by
  have past : values[index - base]? = none := List.getElem?_eq_none (by omega)
  simp [writeBlock, past]

abbrev Origin := Nat × Option Nat

def readOrigin (arguments : List Entry.Value) (origin : Origin) : Option Entry.Value :=
  HEShownSlotReturn.readBinding arguments ⟨0, origin.1, origin.2⟩

def initialOrigins (arity : Nat) : RegisterCode.Regs Origin := fun index =>
  if index < arity then some (index, none) else none

def fieldOrigins (argument count : Nat) : List Origin :=
  (List.range count).map fun index => (argument, some index)

def originsAfter (origins : RegisterCode.Regs Origin) : Op → RegisterCode.Regs Origin
  | .expr source first count =>
      match origins source with
      | some (argument, none) => writeBlock first (fieldOrigins argument count) origins
      | _ => origins
  | _ => origins

def recoverSlot (slot : Nat) : List Op → RegisterCode.Regs Origin → Option Origin
  | [], _ => none
  | .bind source destination :: rest, origins =>
      if destination == slot then origins source else recoverSlot slot rest origins
  | op :: rest, origins => recoverSlot slot rest (originsAfter origins op)

def Supported {Value : Type} (limit : Nat) (registers : RegisterCode.Regs Value) : Prop :=
  ∀ index, limit ≤ index → registers index = none

def Known (arguments : List Entry.Value) (origins : RegisterCode.Regs Origin)
    (registers : RegisterCode.Regs Entry.Value) : Prop :=
  ∀ index origin, origins index = some origin → registers index = readOrigin arguments origin

theorem initial_supported (arity : Nat) : Supported arity (initialOrigins arity) := by
  intro index after
  simp [initialOrigins, Nat.not_lt.mpr after]

theorem initial_known (arguments : List Entry.Value) :
    Known arguments (initialOrigins arguments.length) (fun index => arguments[index]?) := by
  intro index origin present
  simp only [initialOrigins] at present
  split at present
  · cases Option.some.inj present
    simp [readOrigin, HEShownSlotReturn.readBinding]
  · contradiction

theorem fieldOrigins_at (argument count index : Nat) (inside : index < count) :
    (fieldOrigins argument count)[index]? = some (argument, some index) := by
  simp [fieldOrigins, inside]

theorem block_supported {Value : Type} (base : Nat) (values : List Value)
    (registers : RegisterCode.Regs Value) (supported : Supported base registers) :
    Supported (base + values.length) (writeBlock base values registers) := by
  intro index after
  rw [writeBlock_after base values registers index after]
  exact supported index (by omega)

theorem expr_origins_supported (origins : RegisterCode.Regs Origin) (base source count : Nat)
    (supported : Supported base origins) :
    Supported (base + count) (originsAfter origins (.expr source base count)) := by
  simp only [originsAfter]
  split
  · simpa [fieldOrigins] using block_supported base (fieldOrigins _ count) origins supported
  · exact fun index after => supported index (by omega)

theorem expr_origins_known (arguments : List Entry.Value) (origins : RegisterCode.Regs Origin)
    (registers : RegisterCode.Regs Entry.Value) (base source : Nat) (status : Entry.Status)
    (fields : List Entry.Value)
    (supported : Supported base origins) (known : Known arguments origins registers)
    (loaded : registers source = some (.expression status fields)) :
    Known arguments (originsAfter origins (.expr source base fields.length))
      (writeBlock base fields registers) := by
  have old : Known arguments origins (writeBlock base fields registers) := by
    intro index origin present
    have earlier : index < base := by
      by_contra notEarlier
      rw [supported index (by omega)] at present
      contradiction
    rw [writeBlock_before base fields registers index earlier]
    exact known index origin present
  cases recovered : origins source with
  | none => simpa only [originsAfter, recovered] using old
  | some origin =>
      obtain ⟨argument, field⟩ := origin
      cases field with
      | some index => simpa only [originsAfter, recovered] using old
      | none =>
          simp only [originsAfter, recovered]
          intro index origin present
          by_cases earlier : index < base
          · rw [writeBlock_before base fields registers index earlier]
            apply known index origin
            simpa only [writeBlock_before _ _ _ index earlier] using present
          · have baseLe : base ≤ index := by omega
            have wholeRead : arguments[argument]? = some (.expression status fields) := by
              have actual := known source (argument, none) recovered
              simp only [readOrigin, HEShownSlotReturn.readBinding] at actual
              simpa using actual.symm.trans loaded
            by_cases inside : index - base < fields.length
            · have metaRead := fieldOrigins_at argument fields.length (index - base) inside
              have same : origin = (argument, some (index - base)) := by
                have copied := writeBlock_at base (fieldOrigins argument fields.length) origins
                  (index - base) (argument, some (index - base)) metaRead
                rw [Nat.add_sub_cancel' baseLe] at copied
                exact Option.some.inj (present.symm.trans copied)
              subst origin
              simp [writeBlock, baseLe, readOrigin, HEShownSlotReturn.readBinding, wholeRead,
                List.getElem?_eq_getElem inside]
            · have after : base + (fieldOrigins argument fields.length).length ≤ index := by
                simp only [fieldOrigins, List.length_map, List.length_range]
                omega
              rw [writeBlock_after _ _ _ index after, supported index baseLe] at present
              contradiction

/-- Successful ordinary match-op execution. Literal and repeated-value
comparison retain their dialect comparator; provenance does not assume it
is syntactic equality. Refusal/error refinements of a failed comparison are
outside this successful-run observation. -/
def run (compare : Atom → Atom → Bool) : List Op → RegisterCode.Regs Entry.Value →
    RegisterCode.Regs Entry.Value → Option (RegisterCode.Regs Entry.Value × RegisterCode.Regs Entry.Value)
  | [], registers, locals => some (registers, locals)
  | .atom source literal :: rest, registers, locals =>
      (registers source).bind fun value =>
        if compare value.erase literal then run compare rest registers locals else none
  | .bind source slot :: rest, registers, locals =>
      (registers source).bind fun value =>
        run compare rest registers (Function.update locals slot (some value))
  | .same source slot :: rest, registers, locals =>
      (registers source).bind fun value => (locals slot).bind fun earlier =>
        if compare earlier.erase value.erase then run compare rest registers locals else none
  | .expr source first count :: rest, registers, locals =>
      match registers source with
      | some (.expression _ fields) =>
          if fields.length == count then run compare rest (writeBlock first fields registers) locals else none
      | _ => none

theorem run_preserves_unwritten (compare : Atom → Atom → Bool) :
    ∀ (code : List Op) (registers locals finalRegisters finalLocals : RegisterCode.Regs Entry.Value)
      (slot : Nat), slot ∉ boundSlots code →
      run compare code registers locals = some (finalRegisters, finalLocals) →
      finalLocals slot = locals slot
  | [], _, _, _, _, _, _, returned => by cases Option.some.inj returned; rfl
  | .atom source literal :: rest, registers, locals, finalRegisters, finalLocals, slot, absent, returned => by
      simp only [run, Option.bind_eq_some_iff] at returned
      obtain ⟨value, _, returned⟩ := returned
      split at returned
      · exact run_preserves_unwritten compare rest registers locals finalRegisters finalLocals slot absent returned
      · contradiction
  | .bind source destination :: rest, registers, locals, finalRegisters, finalLocals, slot, absent, returned => by
      simp only [boundSlots, List.filterMap_cons, List.mem_cons, not_or] at absent
      simp only [run, Option.bind_eq_some_iff] at returned
      obtain ⟨value, _, returned⟩ := returned
      rw [run_preserves_unwritten compare rest registers _ finalRegisters finalLocals slot absent.2 returned]
      exact Function.update_of_ne absent.1 _ _
  | .same source destination :: rest, registers, locals, finalRegisters, finalLocals, slot, absent, returned => by
      simp only [run, Option.bind_eq_some_iff] at returned
      obtain ⟨value, _, earlier, _, returned⟩ := returned
      split at returned
      · exact run_preserves_unwritten compare rest registers locals finalRegisters finalLocals slot absent returned
      · contradiction
  | .expr source first count :: rest, registers, locals, finalRegisters, finalLocals, slot, absent, returned => by
      simp only [run] at returned
      split at returned
      next status fields loaded =>
        split at returned
        · exact run_preserves_unwritten compare rest _ locals finalRegisters finalLocals slot absent returned
        · contradiction
      next _ => contradiction

/-- Static recovery follows the same expression loads as the successful
runtime. Compiler-derived allocation excludes metadata being overwritten by
a nested expression's fresh registers. Single-write BINDs keep the recovered
slot intact through every later SAME comparison. -/
theorem recovered_slot_read (compare : Atom → Atom → Bool) (arguments : List Entry.Value)
    {start finish : Nat} {code : List Op} (allocated : Allocated start code finish) :
    ∀ (origins : RegisterCode.Regs Origin) (registers locals finalRegisters finalLocals : RegisterCode.Regs Entry.Value)
      (slot : Nat) (origin : Origin),
      Supported start origins → Known arguments origins registers → (boundSlots code).Nodup →
      recoverSlot slot code origins = some origin →
      run compare code registers locals = some (finalRegisters, finalLocals) →
      finalLocals slot = readOrigin arguments origin := by
  induction allocated with
  | nil next =>
      intro origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      simp [recoverSlot] at recovered
  | atom valid allocated ih =>
      intro origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      simp only [run, Option.bind_eq_some_iff] at returned
      obtain ⟨value, _, returned⟩ := returned
      split at returned
      · exact ih origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      · contradiction
  | same valid allocated ih =>
      intro origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      simp only [run, Option.bind_eq_some_iff] at returned
      obtain ⟨value, _, earlier, _, returned⟩ := returned
      split at returned
      · exact ih origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      · contradiction
  | @bind next source destination rest finish valid allocated ih =>
      intro origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      simp only [boundSlots, List.filterMap_cons, List.nodup_cons] at unique
      simp only [run, Option.bind_eq_some_iff] at returned
      obtain ⟨value, loaded, returned⟩ := returned
      simp only [recoverSlot] at recovered
      split at recovered
      next same =>
        have sameSlot : destination = slot := by simpa using same
        subst slot
        rw [run_preserves_unwritten compare rest registers _ finalRegisters finalLocals destination unique.1 returned,
          Function.update_self]
        exact loaded.symm.trans (known source origin recovered)
      next different =>
        exact ih origins registers _ finalRegisters finalLocals slot origin supported known unique.2 recovered returned
  | @expr next source count rest finish valid allocated ih =>
      intro origins registers locals finalRegisters finalLocals slot origin supported known unique recovered returned
      simp only [run] at returned
      split at returned
      next status fields loaded =>
        split at returned
        next sameLength =>
          have lengths : fields.length = count := by simpa using sameLength
          subst count
          exact ih (originsAfter origins (.expr source next fields.length)) (writeBlock next fields registers)
            locals finalRegisters finalLocals slot origin (expr_origins_supported origins next source fields.length supported)
            (expr_origins_known arguments origins registers next source status fields supported known loaded)
            unique recovered returned
        next _ => contradiction
      next _ => contradiction

/-- The full authored pattern compilation, not supplied origin/uniqueness
certificates, provides the hypotheses needed for recovered-slot readback. -/
theorem compiled_slot_read (slots : String → Option Nat) (patterns : List Atom) (output : Emitted)
    (emitted : compile slots patterns = some output) (compare : Atom → Atom → Bool)
    (arguments : List Entry.Value) (lengths : arguments.length = patterns.length)
    (locals finalRegisters finalLocals : RegisterCode.Regs Entry.Value) (slot : Nat) (origin : Origin)
    (recovered : recoverSlot slot output.code (initialOrigins arguments.length) = some origin)
    (matched : run compare output.code (fun index => arguments[index]?) locals =
      some (finalRegisters, finalLocals)) : finalLocals slot = readOrigin arguments origin := by
  have allocation := compiled_allocated slots patterns output emitted
  rw [← lengths] at allocation
  exact recovered_slot_read compare arguments allocation (initialOrigins arguments.length)
    (fun index => arguments[index]?) locals finalRegisters finalLocals slot origin
    (initial_supported _) (initial_known arguments) (compiled_bindings_unique slots patterns output emitted)
    recovered matched

/-- A constructor key decides exactly the root expression/length test and
the following head-symbol test. Skipping them starts the same remaining
match program with the same loaded field registers. -/
theorem run_key_prefix (compare : Atom → Atom → Bool) (source first : Nat) (head : String)
    (fields : List Entry.Value) (status : Entry.Status) (rest : List Op)
    (registers locals : RegisterCode.Regs Entry.Value)
    (key : registers source = some (.expression status (.symbol head :: fields)))
    (sameHead : compare (.symbol head) (.symbol head) = true) :
    run compare (.expr source first (fields.length + 1) :: .atom first (.symbol head) :: rest)
      registers locals =
      run compare rest (writeBlock first (.symbol head :: fields) registers) locals := by
  have loaded := writeBlock_at first (.symbol head :: fields) registers 0 (.symbol head) rfl
  simp only [Nat.add_zero] at loaded
  simp [run, key, loaded, sameHead, Entry.Value.erase]

theorem recover_key_prefix (slot source first count : Nat) (head : String)
    (rest : List Op) (origins : RegisterCode.Regs Origin) :
    recoverSlot slot (.expr source first count :: .atom first (.symbol head) :: rest) origins =
      recoverSlot slot rest (originsAfter origins (.expr source first count)) := rfl

/-- The authored first constructor pattern emits this key prefix. It is
not an assumed description of a program's first instructions. -/
theorem emitted_constructor_key (slots : String → Option Nat) (head : String) (fields : List Atom)
    (source next : Nat) (seen : List Nat) (output : Emitted)
    (emitted : emit slots (.expression (.symbol head :: fields)) source next seen = some output) :
    ∃ rest,
      emitFields slots fields (next + 1) (next + fields.length + 1) seen = some rest ∧
      output.code = .expr source next (fields.length + 1) :: .atom next (.symbol head) :: rest.code ∧
      output.next = rest.next ∧ output.seen = rest.seen := by
  simp only [emit, emitFields, Option.bind_some, List.length_cons,
    Option.map_eq_some_iff] at emitted
  obtain ⟨intermediate, ⟨rest, generated, rfl⟩, rfl⟩ := emitted
  refine ⟨rest, ?_, rfl, rfl, rfl⟩
  simpa only [Nat.add_assoc] using generated

/-- Compiled noncompact matching and the existing slot-return lowering
preserve the exact annotated source value recovered from an argument. -/
theorem compiled_slot_returns {L O P H : Type}
    (sem : RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (slots : String → Option Nat) (patterns : List Atom) (output : Emitted)
    (emitted : compile slots patterns = some output) (compare : Atom → Atom → Bool)
    (arguments : List Entry.Value) (lengths : arguments.length = patterns.length)
    (locals finalRegisters finalLocals : RegisterCode.Regs Entry.Value)
    (slot destination next : Nat) (origin : Origin) (value : Entry.Value)
    (recovered : recoverSlot slot output.code (initialOrigins arguments.length) = some origin)
    (matched : run compare output.code (fun index => arguments[index]?) locals =
      some (finalRegisters, finalLocals))
    (readValue : readOrigin arguments origin = some value) :
    RegisterCode.exec sem answer
      (RegisterCode.compile fuses (.slot slot) true destination next).1 finalLocals = some (.ret value) :=
  HEShownSlotReturn.slot_code_returns sem answer fuses finalLocals slot destination next value
    ((compiled_slot_read slots patterns output emitted compare arguments lengths locals finalRegisters finalLocals
      slot origin recovered matched).trans readValue)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotReadback
