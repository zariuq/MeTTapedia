import Mettapedia.Machines.TIsa.StoreInstructions.NativeWords
import Mettapedia.Machines.TIsa.StoreInstructions.PrivateArrayPlan

/-!
# Native preparation of a snapshot and its index

The word plan determines the native code independently of the values
loaded by a copy. Its execution gives a new representation of the
entire data array and the entire index at a disjoint destination.
The result is still private; publication is a separate instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePreparation

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Cell Controls Reads CodeApart footprint)
open PrivateArrayPlan (Slot Operand Write)
open NativeWords (Wiring Move touched written)
open StorePublication (Snapshot)
local instance : MemoryPrimitives := X86Memory.ordinary

structure AddressMap (pointer : Word) where
  offset : Slot → BitVec 32
  cell : ∀ slot, Cell pointer (offset slot)

variable {oldBase newBase : Word}

abbrev Native := X86RegisterRefinement.State

def AddressMap.addr {ptr : Word} (mem : AddressMap ptr) (slot : Slot) : BitVec 48 :=
  (mem.cell slot).address

def Represents {ptr : Word} (mem : AddressMap ptr) (state : Native) (snapshot : Snapshot) : Prop :=
  ∀ field value, PrivateArrayPlan.read snapshot field = some value → Reads state (mem.addr field) value

def source (old : AddressMap oldBase) : Operand → NativeWords.Source oldBase
  | .copy field => .copy (old.offset field) (old.cell field)
  | .literal value => .literal value

def place (old : AddressMap oldBase) (next : AddressMap newBase) (move : Write) (value : Word) :
    Move oldBase newBase :=
  ⟨source old move.2, value, next.offset move.1, next.cell move.1⟩

def skeleton (old : AddressMap oldBase) (next : AddressMap newBase) (plan : List Write) :
    List (Move oldBase newBase) :=
  plan.map fun m => place old next m 0

def code (w : Wiring) (old : AddressMap oldBase) (next : AddressMap newBase) (plan : List Write) : List ℕ :=
  NativeWords.emitted w (skeleton old next plan)

private def erase (move : Move oldBase newBase) : Move oldBase newBase :=
  {move with value := 0}

def link (old : AddressMap oldBase) (next : AddressMap newBase) (before : Snapshot) (plan : List Write) :
    Option (List (Move oldBase newBase)) :=
  plan.mapM fun write => (write.2.get before).map (place old next write)

private theorem load_source (old : AddressMap oldBase) {before : Snapshot} {state : Native}
    (view : Represents old state before) (operand : Operand) (value : Word)
    (computed : operand.get before = some value) : (source old operand).Ready state value := by
  cases operand with
  | copy field => exact view field value computed
  | literal _ => exact Option.some.inj computed

private theorem linked (old : AddressMap oldBase) (next : AddressMap newBase)
    (before : Snapshot) (plan : List Write) {state : Native} (view : Represents old state before)
    {values : List (Slot × Word)} (computed : PrivateArrayPlan.evaluate before plan = some values) :
    ∃ issued : List (Move oldBase newBase),
      link old next before plan = some issued ∧
      issued.map erase = skeleton old next plan ∧
      (∀ w ∈ issued, w.source.Ready state w.value) ∧
      issued.map (fun w => (w.cell.address, w.value)) = values.map (fun (slot, v) => (next.addr slot, v)) := by
  induction plan generalizing values with
  | nil =>
    have empty : values = [] := (Option.some.inj computed).symm
    subst values
    exact ⟨[], rfl, rfl, fun _ h => (List.not_mem_nil h).elim, rfl⟩
  | cons first rest ih =>
    unfold PrivateArrayPlan.evaluate at computed
    rw [List.mapM_cons] at computed
    obtain ⟨head, firstPlaced, later⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨remaining, tailComputed, result⟩ := Option.bind_eq_some_iff.mp later
    obtain ⟨value, read, same⟩ := Option.map_eq_some_iff.mp firstPlaced
    obtain rfl := Option.some.inj result
    obtain ⟨issued, compiled, layout, inputs, outputs⟩ := ih tailComputed
    refine ⟨place old next first value :: issued, ?_, ?_, ?_, ?_⟩
    · change (List.mapM (fun write => (write.2.get before).map (place old next write)) (first :: rest)) = _
      rw [List.mapM_cons, read]
      change (link old next before rest).bind (fun tail => some (place old next first value :: tail)) = _
      rw [compiled]
      rfl
    · change place old next first 0 :: issued.map erase = place old next first 0 :: skeleton old next rest
      rw [layout]
    · intro w belongs
      rcases List.mem_cons.mp belongs with rfl | more
      · exact load_source old view first.2 value read
      · exact inputs w more
    · rw [← same]
      change (next.addr first.1, value) :: issued.map (fun w => (w.cell.address, w.value)) =
        (next.addr first.1, value) :: remaining.map (fun (slot, v) => (next.addr slot, v))
      rw [outputs]

private theorem erased_bytes (w : Wiring) (moves : List (Move oldBase newBase)) :
    NativeWords.emitted w (moves.map erase) = NativeWords.emitted w moves := by
  induction moves with
  | nil => rfl
  | cons m later ih =>
    change m.bytes w ++ NativeWords.emitted w (later.map erase) = m.bytes w ++ NativeWords.emitted w later
    rw [ih]

private theorem erased_writes (moves : List (Move oldBase newBase)) :
    written (moves.map erase) = written moves := by
  induction moves with
  | nil => rfl
  | cons m later ih =>
    change footprint m.cell.address ∪ written (later.map erase) = footprint m.cell.address ∪ written later
    rw [ih]

private theorem erased_separation (moves : List (Move oldBase newBase)) :
    NativeWords.Separate (moves.map erase) ↔ NativeWords.Separate moves := by
  unfold NativeWords.Separate
  rw [List.pairwise_map]
  rfl

structure Geometry (w : Wiring) (image : NativeImage.View) (base : BitVec 48)
    (old : AddressMap oldBase) (next : AddressMap newBase) (plan : List Write) : Prop where
  separate : NativeWords.Separate (skeleton old next plan)
  sources : ∀ m ∈ skeleton old next plan, Disjoint m.source.uses (written (skeleton old next plan))
  codeApart : CodeApart image base (written (skeleton old next plan))

theorem fetch_plan (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    (old : AddressMap oldBase) (next : AddressMap newBase) (before : Snapshot) (plan : List Write)
    {values : List (Slot × Word)} (computed : PrivateArrayPlan.evaluate before plan = some values)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {state : Native}
    (point : At image state base start) (controls : Controls state)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (view : Represents old state before) (placement : Geometry w image base old next plan)
    (extent : start + (code w old next plan).length ≤ image.size)
    (installed : Code image start (code w old next plan)) :
    letI : OtherOpcodeHandlers := NativeWords.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (X86FuelPrefix.fetches (2 * plan.length)).run state = .ok () after ∧
      X86StateFrame.Frame (touched w) (written (skeleton old next plan)) state after ∧
      (∀ p ∈ values, Reads after (next.addr p.1) p.2 ∧ footprint (next.addr p.1) ⊆ written (skeleton old next plan)) ∧
      Nonempty (At image after base (start + (code w old next plan).length)) := by
  let : OtherOpcodeHandlers := NativeWords.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨moves, _, layout, inputs, outputs⟩ := linked old next before plan view computed
  have bytes : NativeWords.emitted w moves = code w old next plan := by
    rw [code, ← layout, erased_bytes]
  have limits : written moves = written (skeleton old next plan) := by rw [← layout, erased_writes]
  have sameLength : moves.length = plan.length := by
    have width := congrArg List.length layout
    simpa only [skeleton, List.length_map] using width
  have separated := (erased_separation moves).mp (layout.symm ▸ placement.separate)
  have fromOld (m : Move oldBase newBase) (member : m ∈ moves) : Disjoint m.source.uses (written moves) := by
    have here : erase m ∈ skeleton old next plan := layout ▸ List.mem_map.mpr ⟨m, member, rfl⟩
    exact limits.symm ▸ placement.sources (erase m) here
  have verified := NativeWords.checked_of_emitted w image start moves (bytes.symm ▸ extent) (bytes.symm ▸ installed)
  obtain ⟨after, ran, framed, cells, endpoint⟩ := NativeWords.fetch_all other vector w moves
    point controls verified readBase writeBase inputs fromOld separated (limits.symm ▸ placement.codeApart)
  refine ⟨after, sameLength ▸ ran, limits ▸ framed, ?_, ?_⟩
  · intro entry included
    have writtenSlot : (next.addr entry.1, entry.2) ∈ values.map (fun (slot, v) => (next.addr slot, v)) :=
      List.mem_map.mpr ⟨entry, included, rfl⟩
    rw [← outputs] at writtenSlot
    obtain ⟨move, made, exactValue⟩ := List.mem_map.mp writtenSlot
    have address : move.cell.address = next.addr entry.1 := congrArg Prod.fst exactValue
    have content : move.value = entry.2 := congrArg Prod.snd exactValue
    exact ⟨content ▸ address ▸ cells move made, address ▸ limits ▸ NativeWords.member_written made⟩
  · rwa [← NativeWords.emitted_size, bytes] at endpoint

variable {V : Type*} {keys : ℕ}

theorem fetch_assembled (codes : PackedOccurrences.Codes V) (classify : V → Fin keys)
    {before target : Snapshot} {edit : PrivateArrayPlan.Edit V} {plan : List Write}
    (assembled : PrivateArrayPlan.assemble codes classify before edit = some (target, plan))
    (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (w : Wiring)
    (old : AddressMap oldBase) (next : AddressMap newBase) {state : Native}
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ}
    (point : At image state base start) (controls : Controls state)
    (readBase : lookup state w.readBase = some oldBase) (writeBase : lookup state w.writeBase.base = some newBase)
    (view : Represents old state before) (placement : Geometry w image base old next plan)
    (extent : start + (code w old next plan).length ≤ image.size)
    (installed : Code image start (code w old next plan)) :
    letI : OtherOpcodeHandlers := NativeWords.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (X86FuelPrefix.fetches (2 * plan.length)).run state = .ok () after ∧
      Represents next after target ∧
      (∀ field word, PrivateArrayPlan.read target field = some word →
        footprint (next.addr field) ⊆ written (skeleton old next plan)) ∧
      X86StateFrame.Frame (touched w) (written (skeleton old next plan)) state after ∧
      Nonempty (At image after base (start + (code w old next plan).length)) := by
  obtain ⟨after, fetched, framed, values, reached⟩ := fetch_plan other vector w old next before plan
    (PrivateArrayPlan.evaluate_assembled codes classify assembled)
    point controls readBase writeBase view placement extent installed
  refine ⟨after, fetched, ?_, ?_, framed, reached⟩
  · exact fun field word read => (values (field, word) (PrivateArrayPlan.read_mem_contents read)).1
  · exact fun field word read => (values (field, word) (PrivateArrayPlan.read_mem_contents read)).2

end Mettapedia.Machines.TIsa.StoreInstructions.NativePreparation
