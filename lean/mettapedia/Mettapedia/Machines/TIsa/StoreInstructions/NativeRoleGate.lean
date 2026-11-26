import Mettapedia.Machines.TIsa.StoreInstructions.MemoryBinding
import Mettapedia.Machines.TIsa.StoreInstructions.PlannedPremise

/-!
# Testing occurrence use before matching

The forbidden sequence comes from the current match. READ scans
only the taken identities; TAKE also scans the read identities.
The native gate loads the candidate identity once, and stops at
the first equal held identity. No test compares atom values.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleGate

open Derivation (Match Role)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Reads)
open X86PlacedScalar (Code CompareBranch)
open MemoryBinding (Native handlers bitWire termWire)
local instance : MemoryPrimitives := X86Memory.ordinary

def forbidden {V B : Type*} (role : Role) (entry : Match V B) : List ℕ :=
  match role with
  | .read => entry.taken
  | .take => entry.taken ++ entry.read

theorem allowed_iff {V B : Type*} (role : Role) (entry : Match V B) (identity : ℕ) :
    role.allows entry identity = true ↔ identity ∉ forbidden role entry := by
  cases role <;> simp [Role.allows, forbidden]

def probes (identity : ℕ) : List ℕ → ℕ
  | [] => 0
  | held :: rest => if identity = held then 1 else 1 + probes identity rest

theorem probes_le (identity : ℕ) (ids : List ℕ) : probes identity ids ≤ ids.length := by
  induction ids with
  | nil => rfl
  | cons held rest ih =>
    simp only [probes, List.length_cons]
    split <;> omega

structure WordAt (pointer : Word) where
  offset : BitVec 32
  cell : Cell pointer offset

def WordAt.source {pointer : Word} (spot : WordAt pointer) : NativeWords.Source pointer :=
  .copy spot.offset spot.cell

def WordAt.ReadsId {pointer : Word} (spot : WordAt pointer) (state : Native) (identity : ℕ) : Prop :=
  identity < 2 ^ 64 ∧ Reads state spot.cell.address (BitVec.ofNat 64 identity)

abbrev resident {pointer : Word} (spots : List (WordAt pointer)) (state : Native) (ids : List ℕ) : Prop :=
  List.Forall₂ (fun spot identity => spot.ReadsId state identity) spots ids

theorem resident_preserved {pointer : Word} {spots : List (WordAt pointer)} {ids : List ℕ}
    {before after : Native} {regs : Finset Register} (held : resident spots before ids)
    (frame : X86StateFrame.Frame regs ∅ before after) : resident spots after ids := by
  induction held with
  | nil => exact .nil
  | cons view _ ih => exact .cons ⟨view.1, view.2.preserved frame (by simp)⟩ ih

theorem resident_kept {pointer : Word} {spots : List (WordAt pointer)} {ids : List ℕ}
    {before after : Native} {regs : Finset Register} {bytes : Finset ℕ} (held : resident spots before ids)
    (frame : X86StateFrame.Frame regs bytes before after)
    (separate : ∀ spot ∈ spots, Disjoint (X86PlacedMemory.footprint spot.cell.address) bytes) :
    resident spots after ids := by
  induction held with
  | nil => exact .nil
  | cons view _ ih =>
    exact .cons ⟨view.1, view.2.preserved frame (separate _ List.mem_cons_self)⟩
      (ih (fun spot member => separate spot (List.mem_cons_of_mem _ member)))

private theorem resident_append {pointer : Word} {state : Native}
    {left right : List (WordAt pointer)} {old new : List ℕ}
    (first : resident left state old) (second : resident right state new) :
    resident (left ++ right) state (old ++ new) := by
  induction first with
  | nil => exact second
  | cons word _ next => exact .cons word next

/-- Addresses of the taken and read identity words, in port order. -/
structure Ports (pointer : Word) where
  taken : List (WordAt pointer)
  read : List (WordAt pointer)

variable {pointer : Word}

def Ports.Represents {V B : Type*} (ports : Ports pointer) (state : Native) (entry : Match V B) : Prop :=
  resident ports.taken state entry.taken ∧ resident ports.read state entry.read

def Ports.forRole (ports : Ports pointer) : Role → List (WordAt pointer)
  | .take => ports.taken ++ ports.read
  | .read => ports.taken

theorem Ports.restrict {V B : Type*} {ports : Ports pointer} {state : Native} {entry : Match V B}
    (known : ports.Represents state entry) (role : Role) :
    resident (ports.forRole role) state (forbidden role entry) := by
  cases role
  · exact resident_append known.1 known.2
  · exact known.1

def Ports.add (ports : Ports pointer) (cell : WordAt pointer) : Role → Ports pointer
  | .take => { ports with taken := ports.taken ++ [cell] }
  | .read => { ports with read := ports.read ++ [cell] }

theorem Ports.record {V B : Type*} {ports : Ports pointer} {state : Native} {entry : Match V B}
    (known : ports.Represents state entry) (role : Role) (cell : WordAt pointer) (id : ℕ) (binding : B)
    (found : cell.ReadsId state id) :
    (ports.add cell role).Represents state (entry.select role id binding) := by
  have one : resident [cell] state [id] := .cons found .nil
  cases role
  · exact ⟨resident_append known.1 one, known.2⟩
  · exact ⟨known.1, resident_append known.2 one⟩

theorem Ports.preserved {V B : Type*} {ports : Ports pointer} {before after : Native} {entry : Match V B}
    (known : ports.Represents before entry) {regs : Finset Register} {bytes : Finset ℕ}
    (frame : X86StateFrame.Frame regs bytes before after)
    (separate : ∀ spot ∈ ports.taken ++ ports.read, Disjoint (X86PlacedMemory.footprint spot.cell.address) bytes) :
    ports.Represents after entry :=
  ⟨resident_kept known.1 frame (fun spot h => separate spot (List.mem_append_left _ h)),
    resident_kept known.2 frame (fun spot h => separate spot (List.mem_append_right _ h))⟩

abbrev probeWrites : Finset Register := {.rax, .rflags, .rip}
abbrev clobbers : Finset Register := {.rax, .rdx, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

structure Probe (image : NativeImage.View) (start refused : ℕ) {pointer : Word} (spot : WordAt pointer) : Prop where
  extent : start + 7 ≤ image.size
  load : Code image start (spot.source.bytes bitWire)
  compare : CompareBranch image (start + 7) refused .notEqual 2 0

inductive Placed (image : NativeImage.View) (refused : ℕ) {pointer : Word} :
    ℕ → ℕ → List (WordAt pointer) → Prop where
  | nil (offset : ℕ) : Placed image refused offset offset []
  | cons {start finish : ℕ} {spot : WordAt pointer} {rest : List (WordAt pointer)}
      (probe : Probe image start refused spot) (tail : Placed image refused (start + 16) finish rest) :
      Placed image refused start finish (spot :: rest)

theorem Placed.width {image : NativeImage.View} {refused start finish : ℕ} {pointer : Word}
    {spots : List (WordAt pointer)} (placed : Placed image refused start finish spots) :
    finish = start + 16 * spots.length := by
  induction placed with
  | nil => simp
  | cons _ _ ih =>
    rw [ih, List.length_cons]
    omega

private theorem same_word {left right : ℕ} (l : left < 2 ^ 64) (r : right < 2 ^ 64) :
    BitVec.ofNat 64 left = BitVec.ofNat 64 right ↔ left = right := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt l, Nat.mod_eq_of_lt r]

private theorem probe_fetches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {start refused : ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    {pointer : Word} {spot : WordAt pointer} (placed : Probe image start refused spot)
    (baseRead : lookup before 6 = some pointer) (identity held : ℕ) (fits : identity < 2 ^ 64)
    (candidate : lookup before 2 = some (BitVec.ofNat 64 identity))
    (record : spot.ReadsId before held) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧
      X86StateFrame.Frame probeWrites ∅ before after ∧
      Nonempty (At image after base (if identity = held then refused else start + 16)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨loaded, fetched, frame, received, ⟨atBranch⟩⟩ :=
    spot.source.fetch (handlers other extra) vector bitWire (BitVec.ofNat 64 held) point controls
      baseRead record.2 placed.extent placed.load
  obtain ⟨after, ran, compared, arrived⟩ := X86PlacedScalar.compare_branch
    (X86FrameLoad.linkedHandlers other) extra vector atBranch .notEqual 2 0 placed.compare
    (BitVec.ofNat 64 identity) (BitVec.ofNat 64 held)
    ((frame.lookup 2 (by decide)).trans candidate) received
  have equal := same_word fits record.1
  have next : Nonempty (At image after base (if identity = held then refused else start + 16)) := by
    by_cases same : identity = held
    · have words := equal.mpr same
      simpa [if_pos same, Comparison.evaluate, words] using arrived
    · have words := fun identityWords => same (equal.mp identityWords)
      have passes : Comparison.notEqual.evaluate (BitVec.ofNat 64 identity) (BitVec.ofNat 64 held) = true := by
        change (BitVec.ofNat 64 identity != BitVec.ofNat 64 held) = true
        exact bne_iff_ne.mpr words
      simpa [if_neg same, passes, WordAt.source, NativeWords.Source.width, Nat.add_assoc] using arrived
  exact ⟨after, X86FuelPrefix.fetches_then 1 2 before loaded after fetched ran,
    (frame.trans (X86StateFrame.registerOnly compared)).mono (by decide) (by simp), next⟩

theorem scan_fetches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {start finish refused : ℕ}
    {pointer : Word} {spots : List (WordAt pointer)} (placed : Placed image refused start finish spots)
    (identity : ℕ) (fits : identity < 2 ^ 64) {ids : List ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    (baseRead : lookup before 6 = some pointer) (candidate : lookup before 2 = some (BitVec.ofNat 64 identity))
    (record : resident spots before ids) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (3 * probes identity ids)).run before = .ok () after ∧
      X86StateFrame.Frame probeWrites ∅ before after ∧
      Nonempty (At image after base (if identity ∈ ids then refused else finish)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction placed generalizing before ids with
  | nil offset =>
    cases record
    exact ⟨before, rfl, X86StateFrame.Frame.refl _ _ _, by simpa using Nonempty.intro point⟩
  | @cons atStart atFinish spot tail first later ih =>
    cases record with
    | cons denied rest =>
      rename_i held remaining
      obtain ⟨checked, ran, frame, ⟨next⟩⟩ :=
        probe_fetches other extra vector point controls first baseRead identity held fits candidate denied
      by_cases same : identity = held
      · rw [if_pos same] at next
        refine ⟨checked, ?_, frame, ?_⟩
        · simpa only [probes, if_pos same] using ran
        · exact ⟨(if_pos (List.mem_cons.mpr (Or.inl same))).symm ▸ next⟩
      · rw [if_neg same] at next
        obtain ⟨after, continued, remaining, follow⟩ := ih next (controls.transport frame (by decide))
          ((frame.lookup 6 (by decide)).trans baseRead) ((frame.lookup 2 (by decide)).trans candidate)
          (resident_preserved rest frame)
        refine ⟨after, ?_, (frame.trans remaining).mono (by simp) (by simp), ?_⟩
        · rw [probes, if_neg same, Nat.mul_add]
          exact X86FuelPrefix.fetches_then 3 _ before checked after ran continued
        · simpa only [List.mem_cons, same, false_or] using follow

structure Gate (image : NativeImage.View) (start finish refused : ℕ) {candidate base : Word}
    (identity : WordAt candidate) (spots : List (WordAt base)) : Prop where
  extent : start + 7 ≤ image.size
  load : Code image start (identity.source.bytes termWire)
  probes : Placed image refused (start + 7) finish spots

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start finish refused : ℕ}
    {before : Native} (point : At image before codeBase start) (controls : Controls before)
    {candidate base : Word} {identity : WordAt candidate} {spots : List (WordAt base)}
    (placed : Gate image start finish refused identity spots)
    (candidateRead : lookup before 7 = some candidate) (heldRead : lookup before 6 = some base)
    (id : ℕ) (offered : identity.ReadsId before id) {V B : Type*}
    (role : Role) (entry : Match V B) (held : resident spots before (forbidden role entry)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (1 + 3 * probes id (forbidden role entry))).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 2 = some (BitVec.ofNat 64 id) ∧
      Nonempty (At image after codeBase (if role.allows entry id then finish else refused)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨loaded, ran, frame, actual, ⟨atScan⟩⟩ :=
    identity.source.fetch (handlers other extra) vector termWire (BitVec.ofNat 64 id) point controls
      candidateRead offered.2 placed.extent placed.load
  obtain ⟨after, checked, scanFrame, arrived⟩ := scan_fetches other extra vector placed.probes id offered.1
    atScan (controls.transport frame (by decide)) ((frame.lookup 6 (by decide)).trans heldRead) actual
    (resident_preserved held frame)
  refine ⟨after, X86FuelPrefix.fetches_then 1 _ before loaded after ran checked,
    (frame.trans scanFrame).mono (by decide) (by simp), (scanFrame.lookup 2 (by decide)).trans actual, ?_⟩
  by_cases valid : id ∈ forbidden role entry
  · have rejected : role.allows entry id = false := Bool.eq_false_iff.mpr (fun h => (allowed_iff role entry id).mp h valid)
    simpa [valid, rejected] using arrived
  · have allowed := (allowed_iff role entry id).mpr valid
    simpa [valid, allowed] using arrived

namespace Examples

private def prefixUse : Match Word Unit := ⟨(), [7], [3], [], []⟩

theorem a_prior_read_blocks_take_but_not_read :
    Role.take.allows prefixUse 3 = false ∧ Role.read.allows prefixUse 3 = true := by decide +kernel

theorem a_prior_take_blocks_both :
    Role.take.allows prefixUse 7 = false ∧ Role.read.allows prefixUse 7 = false := by decide +kernel

theorem early_hit_avoids_later_probes : probes 7 (forbidden .take prefixUse) = 1 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleGate
