import Mathlib.Data.List.Nodup
import Mettapedia.GSLT.Core.Composition

/-!
# Certified compilation of finite environments to dense slots

This module isolates a generic lowering used by rule machines whose authored
presentation declares a finite inventory of runtime keys.  The admission
procedure checks two local properties:

* the inventory contains no duplicate keys;
* every write performed by the program targets a declared key.

An admitted program is compiled from key-carrying writes to writes indexed by
`Fin inventory.length`.  Runtime execution of the compiled artifact therefore
does not resolve keys.  The main refinement theorem proves that decoding the
dense result through the admitted inventory yields exactly the source
environment, including repeated writes.

The construction is independent of the meaning of keys and values.  Native
type information can supply rule variables, binder fields, registers, or other
finite support inventories without adding a guest-specific runtime case.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

universe uKey uValue

/-- A duplicate-free, generated inventory of runtime keys. -/
structure Inventory (Key : Type uKey) where
  keys : List Key
  nodup : keys.Nodup

namespace Inventory

variable {Key : Type uKey} [DecidableEq Key]

/-- Dense runtime slots are bounded by the admitted inventory. -/
abbrev Slot (inventory : Inventory Key) := Fin inventory.keys.length

/-- Recover the authored key represented by a dense slot. -/
def reify (inventory : Inventory Key) (slot : inventory.Slot) : Key :=
  inventory.keys.get slot

/-- Resolve an authored key once, at compilation time. -/
def resolve? (inventory : Inventory Key) (key : Key) :
    Option inventory.Slot :=
  if present : key ∈ inventory.keys then
    some ⟨inventory.keys.idxOf key,
      List.idxOf_lt_length_of_mem present⟩
  else
    none

/-- Resolution selects a slot exactly when that slot reifies to the key. -/
theorem resolve?_eq_some_iff (inventory : Inventory Key) (key : Key)
    (slot : inventory.Slot) :
    inventory.resolve? key = some slot ↔ inventory.reify slot = key := by
  unfold resolve? reify
  split
  next present =>
    constructor
    · intro selected
      have slotEq :
          (⟨inventory.keys.idxOf key,
            List.idxOf_lt_length_of_mem present⟩ :
              Fin inventory.keys.length) = slot := by
        exact Option.some.inj selected
      rw [← slotEq]
      exact List.idxOf_get (List.idxOf_lt_length_of_mem present)
    · intro reified
      apply congrArg some
      apply Fin.ext
      change inventory.keys.idxOf key = slot.val
      rw [← reified]
      exact List.get_idxOf inventory.nodup slot
  next absent =>
    constructor
    · simp
    · intro reified
      exfalso
      apply absent
      rw [← reified]
      exact List.get_mem inventory.keys slot

/-- Every slot round-trips through the generated resolver. -/
@[simp] theorem resolve_reify (inventory : Inventory Key)
    (slot : inventory.Slot) :
    inventory.resolve? (inventory.reify slot) = some slot :=
  (inventory.resolve?_eq_some_iff (inventory.reify slot) slot).2 rfl

/-- A key is resolvable exactly when it belongs to the generated inventory. -/
theorem exists_resolve?_eq_some_iff (inventory : Inventory Key) (key : Key) :
    (∃ slot, inventory.resolve? key = some slot) ↔ key ∈ inventory.keys := by
  constructor
  · rintro ⟨slot, selected⟩
    have reified := (inventory.resolve?_eq_some_iff key slot).1 selected
    rw [← reified]
    exact List.get_mem inventory.keys slot
  · intro present
    let slot : inventory.Slot :=
      ⟨inventory.keys.idxOf key,
        List.idxOf_lt_length_of_mem present⟩
    exact ⟨slot, (inventory.resolve?_eq_some_iff key slot).2
      (List.idxOf_get (List.idxOf_lt_length_of_mem present))⟩

/-- Two keys cannot resolve to the same admitted slot. -/
theorem key_eq_of_resolve?_eq_same (inventory : Inventory Key)
    {first second : Key} {slot : inventory.Slot}
    (firstSelected : inventory.resolve? first = some slot)
    (secondSelected : inventory.resolve? second = some slot) :
    first = second := by
  have firstEq := (inventory.resolve?_eq_some_iff first slot).1 firstSelected
  have secondEq := (inventory.resolve?_eq_some_iff second slot).1 secondSelected
  exact firstEq.symm.trans secondEq

end Inventory

/-! ## Decidable admission -/

/-- Check and package a raw finite inventory. -/
def admitInventory [DecidableEq Key] (keys : List Key) :
    Option (Inventory Key) :=
  if unique : keys.Nodup then
    some { keys := keys, nodup := unique }
  else
    none

/-- Inventory admission succeeds exactly for duplicate-free inputs. -/
theorem admitInventory_isSome_iff [DecidableEq Key] (keys : List Key) :
    (admitInventory keys).isSome = true ↔ keys.Nodup := by
  unfold admitInventory
  split <;> simp_all

abbrev SourceEnvironment (Key : Type uKey) (Value : Type uValue) :=
  Key → Option Value

abbrev DenseEnvironment {Key : Type uKey} (inventory : Inventory Key)
    (Value : Type uValue) :=
  inventory.Slot → Option Value

abbrev SourceWrite (Key : Type uKey) (Value : Type uValue) := Key × Value

abbrev DenseWrite {Key : Type uKey} (inventory : Inventory Key)
    (Value : Type uValue) := inventory.Slot × Value

def emptySourceEnvironment : SourceEnvironment Key Value := fun _ => none

def emptyDenseEnvironment {Key : Type uKey} (inventory : Inventory Key) :
    DenseEnvironment inventory Value := fun _ => none

/-- Source semantics of a key-carrying write. -/
def writeSource [DecidableEq Key]
    (environment : SourceEnvironment Key Value)
    (write : SourceWrite Key Value) : SourceEnvironment Key Value :=
  fun candidate =>
    if candidate = write.1 then some write.2 else environment candidate

/-- Compiled semantics of a direct dense-slot write. -/
def writeDense {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key)
    (environment : DenseEnvironment inventory Value)
    (write : DenseWrite inventory Value) : DenseEnvironment inventory Value :=
  fun candidate =>
    if candidate = write.1 then some write.2 else environment candidate

/-- Decode a dense environment at the source-language observation boundary. -/
def decodeDense {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key)
    (environment : DenseEnvironment inventory Value) :
    SourceEnvironment Key Value :=
  fun key => (inventory.resolve? key).bind environment

/-- Compiling a write resolves its key and erases it from the runtime write. -/
def compileWrite? {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) (write : SourceWrite Key Value) :
    Option (DenseWrite inventory Value) :=
  match inventory.resolve? write.1 with
  | none => none
  | some slot => some (slot, write.2)

/-- Compile a sequence of key-carrying writes in source order. -/
def compileWrites? {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) :
    List (SourceWrite Key Value) → Option (List (DenseWrite inventory Value))
  | [] => some []
  | write :: writes => do
      let compiled ← compileWrite? inventory write
      let tail ← compileWrites? inventory writes
      pure (compiled :: tail)

/-- A single write is admitted exactly when its key is declared. -/
theorem compileWrite?_isSome_iff {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) (write : SourceWrite Key Value) :
    (compileWrite? inventory write).isSome = true ↔
      write.1 ∈ inventory.keys := by
  cases selected : inventory.resolve? write.1 with
  | none =>
      simp only [compileWrite?, selected, Option.isSome_none,
        Bool.false_eq_true, false_iff]
      intro present
      obtain ⟨slot, slotEq⟩ :=
        (inventory.exists_resolve?_eq_some_iff write.1).2 present
      rw [selected] at slotEq
      contradiction
  | some slot =>
      simp only [compileWrite?, selected, Option.isSome_some, true_iff]
      exact (inventory.exists_resolve?_eq_some_iff write.1).1 ⟨slot, selected⟩

/-- Exact characterization of the finite-support recognizer. -/
theorem compileWrites?_accepts_iff {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) (writes : List (SourceWrite Key Value)) :
    (∃ compiled, compileWrites? inventory writes = some compiled) ↔
      ∀ write ∈ writes, write.1 ∈ inventory.keys := by
  induction writes with
  | nil => simp [compileWrites?]
  | cons write writes ih =>
      constructor
      · rintro ⟨compiled, accepted⟩
        unfold compileWrites? at accepted
        cases headEq : compileWrite? inventory write with
        | none => simp [headEq] at accepted
        | some compiledWrite =>
            cases tailEq : compileWrites? inventory writes with
            | none => simp [headEq, tailEq] at accepted
            | some compiledTail =>
                intro candidate membership
                rcases List.mem_cons.mp membership with equal | tailMembership
                · subst candidate
                  have headSome :
                      (compileWrite? inventory write).isSome = true := by
                    simp [headEq]
                  exact (compileWrite?_isSome_iff inventory write).1 headSome
                · exact ih.1 ⟨compiledTail, tailEq⟩
                    candidate tailMembership
      · intro declared
        have headDeclared : write.1 ∈ inventory.keys :=
          declared write (by simp)
        have tailDeclared :
            ∀ candidate ∈ writes, candidate.1 ∈ inventory.keys := by
          intro candidate membership
          exact declared candidate (by simp [membership])
        have headSome : (compileWrite? inventory write).isSome = true :=
          (compileWrite?_isSome_iff inventory write).2 headDeclared
        cases headEq : compileWrite? inventory write with
        | none => simp [headEq] at headSome
        | some compiledWrite =>
            obtain ⟨compiledTail, tailEq⟩ := ih.2 tailDeclared
            exact ⟨compiledWrite :: compiledTail, by
              simp [compileWrites?, headEq, tailEq]⟩

/-! ## Source and dense execution -/

def runSourceFrom [DecidableEq Key]
    (environment : SourceEnvironment Key Value) :
    List (SourceWrite Key Value) → SourceEnvironment Key Value
  | [] => environment
  | write :: writes => runSourceFrom (writeSource environment write) writes

def runDenseFrom {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) (environment : DenseEnvironment inventory Value) :
    List (DenseWrite inventory Value) → DenseEnvironment inventory Value
  | [] => environment
  | write :: writes => runDenseFrom inventory
      (writeDense inventory environment write) writes

def runSource [DecidableEq Key] (writes : List (SourceWrite Key Value)) :
    SourceEnvironment Key Value :=
  runSourceFrom emptySourceEnvironment writes

def runDense {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) (writes : List (DenseWrite inventory Value)) :
    DenseEnvironment inventory Value :=
  runDenseFrom inventory (emptyDenseEnvironment inventory) writes

/-- Empty source and dense environments have the same decoded observation. -/
theorem decodeDense_empty {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key) :
    decodeDense inventory (emptyDenseEnvironment inventory :
      DenseEnvironment inventory Value) = emptySourceEnvironment := by
  funext key
  unfold decodeDense emptyDenseEnvironment emptySourceEnvironment
  cases inventory.resolve? key <;> rfl

/-- A resolved dense write has exactly the source key-write observation. -/
theorem decodeDense_writeDense {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key)
    (environment : DenseEnvironment inventory Value)
    (key : Key) (value : Value) (slot : inventory.Slot)
    (selected : inventory.resolve? key = some slot) :
    decodeDense inventory
        (writeDense inventory environment (slot, value)) =
      writeSource (decodeDense inventory environment) (key, value) := by
  funext candidate
  by_cases sameKey : candidate = key
  · subst candidate
    simp [decodeDense, writeDense, writeSource, selected]
  · unfold decodeDense
    cases candidateEq : inventory.resolve? candidate with
    | none => simp [candidateEq, writeSource, sameKey]
    | some candidateSlot =>
        have differentSlot : candidateSlot ≠ slot := by
          intro sameSlot
          subst candidateSlot
          exact sameKey (inventory.key_eq_of_resolve?_eq_same
            candidateEq selected)
        simp [candidateEq, writeDense, writeSource, sameKey, differentSlot]

/-- Generalized execution refinement from any pair of related environments. -/
theorem runDenseFrom_refines_runSourceFrom
    {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key)
    (writes : List (SourceWrite Key Value))
    (compiled : List (DenseWrite inventory Value))
    (accepted : compileWrites? inventory writes = some compiled)
    (sourceEnvironment : SourceEnvironment Key Value)
    (denseEnvironment : DenseEnvironment inventory Value)
    (related : decodeDense inventory denseEnvironment = sourceEnvironment) :
    decodeDense inventory (runDenseFrom inventory denseEnvironment compiled) =
      runSourceFrom sourceEnvironment writes := by
  induction writes generalizing compiled sourceEnvironment denseEnvironment with
  | nil =>
      simp [compileWrites?] at accepted
      subst compiled
      simpa [runDenseFrom, runSourceFrom] using related
  | cons write writes ih =>
      unfold compileWrites? at accepted
      cases headEq : compileWrite? inventory write with
      | none => simp [headEq] at accepted
      | some compiledWrite =>
          cases tailEq : compileWrites? inventory writes with
          | none => simp [headEq, tailEq] at accepted
          | some compiledTail =>
              simp [headEq, tailEq] at accepted
              subst compiled
              obtain ⟨key, value⟩ := write
              unfold compileWrite? at headEq
              cases selected : inventory.resolve? key with
              | none => simp [selected] at headEq
              | some slot =>
                  simp [selected] at headEq
                  subst compiledWrite
                  simp only [runDenseFrom, runSourceFrom]
                  apply ih compiledTail tailEq
                    (writeSource sourceEnvironment (key, value))
                    (writeDense inventory denseEnvironment (slot, value))
                  rw [decodeDense_writeDense inventory denseEnvironment
                    key value slot selected, related]

/-- Main semantics theorem: dense-slot execution preserves all key lookups. -/
theorem runDense_refines_runSource
    {Key : Type uKey} [DecidableEq Key]
    (inventory : Inventory Key)
    (writes : List (SourceWrite Key Value))
    (compiled : List (DenseWrite inventory Value))
    (accepted : compileWrites? inventory writes = some compiled) :
    decodeDense inventory (runDense inventory compiled) = runSource writes := by
  exact runDenseFrom_refines_runSourceFrom inventory writes compiled accepted
    emptySourceEnvironment (emptyDenseEnvironment inventory)
    (decodeDense_empty inventory)

/-! ## Certified-realization packaging -/

/-- A source write program together with the exact result of admission. -/
structure AdmittedProgram (Key : Type uKey) [DecidableEq Key]
    (inventory : Inventory Key) (Value : Type uValue) where
  source : List (SourceWrite Key Value)
  compiled : List (DenseWrite inventory Value)
  compile_eq : compileWrites? (Value := Value) inventory source = some compiled

/-- Run the decidable compiler and retain its acceptance equation. -/
def admitProgram {Key : Type uKey} [DecidableEq Key] {Value : Type uValue}
    (inventory : Inventory Key) (source : List (SourceWrite Key Value)) :
    Option (AdmittedProgram Key inventory Value) :=
  match accepted : compileWrites? inventory source with
  | none => none
  | some compiled => some
      { source := source, compiled := compiled, compile_eq := accepted }

/-- Dense finite-environment compilation as a composable realization. -/
def denseEnvironmentRealization
    {Key : Type uKey} [DecidableEq Key] {Value : Type uValue}
    (inventory : Inventory Key) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedProgram Key inventory Value)
      (List (DenseWrite inventory Value))
      (SourceEnvironment Key Value) where
  compile := fun _ admitted => admitted.compiled
  observeSource := fun _ admitted => runSource admitted.source
  observeArtifact := fun _ compiled =>
    decodeDense inventory (runDense inventory compiled)
  adequate := by
    intro _ admitted
    exact runDense_refines_runSource inventory admitted.source
      admitted.compiled admitted.compile_eq

/-! ## Cross-shape and rejection canaries -/

private inductive Field where
  | binder
  | body
  | support
deriving DecidableEq

private def fieldInventory : Inventory Field where
  keys := [.binder, .body, .support]
  nodup := by decide

/-- A field-shaped inventory admits repeated writes and preserves last-write
semantics through dense compilation. -/
example :
    ∃ compiled,
      compileWrites? fieldInventory
          [(.binder, 3), (.body, 7), (.binder, 5)] = some compiled ∧
        (decodeDense fieldInventory (runDense fieldInventory compiled))
          Field.binder = some 5 := by
  exact ⟨[(⟨0, by decide⟩, 3), (⟨1, by decide⟩, 7),
      (⟨0, by decide⟩, 5)], by decide, by decide⟩

/-- A numeric rule-variable inventory exercises the same compiler with a
different key family and inventory size. -/
example :
    compileWrites?
      ({ keys := [10, 20, 30, 40], nodup := by decide } : Inventory Nat)
      [(10, "left"), (40, "right")] =
        some [(⟨0, by decide⟩, "left"), (⟨3, by decide⟩, "right")] := by
  decide

/-- Duplicate inventories fail before a dense slot type is admitted. -/
example : (admitInventory ["x", "y", "x"]).isSome = false := by
  decide

/-- A write to an undeclared key is rejected rather than assigned a fallback
slot. -/
example :
    compileWrites?
      ({ keys := ["x", "y"], nodup := by decide } : Inventory String)
      [("x", 1), ("z", 2)] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
