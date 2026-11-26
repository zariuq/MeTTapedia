import Mettapedia.Machines.TIsa.StoreInstructions.NativeCandidateLookup
import Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPublish
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleGate

/-!
# From the occurrence ordinal to the published MATCH result

The native entry reads the ordinal's projected bank. The pattern
code does not depend on which bank is selected. Accepted bindings
are published at the next level; rejected work keeps the original
levels. A missing ordinal exits before starting the matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSelectedMatch

open Mettapedia.Logic.LP
open Derivation (Role)
open Derivation.FirstOrderTerms (Bindings matcher)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart footprint)
open NativeMatchPlan (Bank PlacedPlan Ready Geometry)
open NativeLevels (Native Directory Resident prepare)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u q
variable {σ : LPSignature.{u,u,q,u}} {count n : ℕ}

structure Prepared (tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ)))
    (values : PackedOccurrences.Codes (GroundTerm σ)) (tests : List (MatchPlan.Test σ))
    (packed : PackedOccurrences.Layout) (count : ℕ) (state : Native) where
  layout : NativeCandidateLookup.Layout count
  pointers : Fin count → Word
  words : Array (Array Word)
  regions : Array (ProjectedCandidate.Region tests)
  projection : CandidateProjection.prepare tags values tests packed = some words
  resident : ProjectedCandidate.Banks tests words regions state
  native : layout.Represents pointers state
  size : regions.size = count
  resolves : ∀ (index : Fin count) (region : ProjectedCandidate.Region tests),
    regions[index.val]? = some region → pointers index = region.pointer

private theorem binding_bank_kept (codes : PackedOccurrences.Codes (GroundTerm σ))
    {slot : Word} {bank : Bank σ slot} {table : BindingSlots.Table σ} {before after : Native} {regs : Finset Register}
    (resident : bank.Represents codes table before)
    (frame : X86StateFrame.Frame regs ∅ before after) :
    bank.Represents codes table after := by
  intro name needed
  obtain ⟨word, entry⟩ := resident name needed
  exact ⟨word, entry.bit.preserved frame (by simp), entry.value.preserved frame (by simp), entry.code⟩

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- A single fetched path selects an in-range occurrence and
checks its role before running the matcher. A role refusal does
not enter the match code or touch the private bank. -/
theorem fetched (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ)) {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes st.store = some packed)
    (role : Role) (pattern : Term σ) (identity level : ℕ) (index dst : P1Source.Reg) (term : GroundTerm σ)
    (row : PackedOccurrences.at? codes packed (st.machine.registers index).toNat = some (identity, term))
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start matchAt success refused invalid : ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    {tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ))}
    (prepared : Prepared tags codes (MatchPlan.compile pattern) packed count before)
    (source : Fin 16) (sourceSafe : source ≠ 14) (indexRead : lookup before source = some (st.machine.registers index))
    (header : lookup before 7 = some prepared.layout.header)
    (candidateBase : lookup before 2 = some prepared.layout.directory.pointer)
    (entry : NativeCandidateLookup.Checked image start invalid source prepared.layout.countOffset)
    {slot : Word} {bank : Bank σ slot} (table : BindingSlots.Table σ)
    (tableView : BindingSlots.Represents table (st.levels level).bindings)
    (initial : bank.Represents codes table before)
    (slotRead : lookup before 6 = some slot) (zero : lookup before 8 = some 0) (one : lookup before 9 = some 1)
    (roleSite : ∀ region, prepared.regions[(st.machine.registers index).toNat]? = some region →
      ∃ (offered : NativeRoleGate.WordAt region.pointer) (held : List (NativeRoleGate.WordAt slot)),
        NativeRoleGate.Gate image (start + 30) matchAt refused offered held ∧
        offered.ReadsId before identity ∧ NativeRoleGate.resident held before (NativeRoleGate.forbidden role (st.levels level)))
    (reference : ProjectedCandidate.Region (MatchPlan.compile pattern))
    (plan : PlacedPlan tags (ProjectedCandidate.candidate (MatchPlan.compile pattern) reference)
      bank image refused matchAt success (MatchPlan.compile pattern))
    (geometry : ∀ region, prepared.regions[(st.machine.registers index).toNat]? = some region →
      Geometry (MatchPlan.demand (MatchPlan.compile pattern))
        (ProjectedCandidate.candidate (MatchPlan.compile pattern) region) bank image base)
    (returns : NativePremise.Return image success refused (X86BoundedLoad.physical dst))
    (levels : Directory σ n) (old : Fin n → Resident σ)
    (published : levels.Represents codes st.levels old before)
    (privateBank : ∀ i, Disjoint (levels.protected old i) bank.writes)
    (next : Fin n) (nextIs : next.val = level + 1)
    (commit : NativeMatchPublish.Commit levels next) (commitCode : commit.Checked image (success + 6))
    (commitSafe : CodeApart image base (footprint (levels.root next)))
    (keepsOthers : ∀ i, i ≠ next → Disjoint (levels.protected old i) (footprint (levels.root next)))
    (handle : Word) (resolves : levels.lookup handle = some (prepare bank (st.levels level) role identity))
    (addressReg : lookup before commit.encoding.base = some commit.pointer)
    (handleReg : lookup before commit.source = some handle)
    (keepLookupAddress : key commit.encoding.base ∉ NativeCandidateLookup.clobbers)
    (keepLookupHandle : key commit.source ∉ NativeCandidateLookup.clobbers)
    (keepRoleAddress : key commit.encoding.base ∉ NativeRoleGate.clobbers)
    (keepRoleHandle : key commit.source ∉ NativeRoleGate.clobbers)
    (keepMatchAddress : key commit.encoding.base ∉ NativePremise.clobbers dst)
    (keepMatchHandle : key commit.source ∉ NativePremise.clobbers dst) :
    letI : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps abstract resident,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      levels.Represents codes abstract.levels resident after ∧
      match PlannedPremise.planned role pattern (st.levels level) (identity, term) table with
      | none => resident = old ∧ Nonempty (At image after base (refused + 6))
      | some _ => resident = Function.update old next (handle, prepare bank (st.levels level) role identity) ∧
          Nonempty (At image after base (success + 6 + commit.encoding.length)) := by
  let : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨words, projectedRow, expected⟩ := CandidateProjection.selected_projection tags codes (MatchPlan.compile pattern)
    formed prepared.projection (st.machine.registers index).toNat identity term row
  obtain ⟨region, allocated, bankMemory⟩ := prepared.resident _ _ projectedRow
  have inside : (st.machine.registers index).toNat < count := prepared.size ▸ (Array.getElem?_eq_some_iff.mp allocated).choose
  obtain ⟨selected, length, ranLookup, frame, found⟩ := NativeCandidateLookup.fetched other extra vector point controls
    prepared.layout prepared.pointers prepared.native header candidateBase source sourceSafe _ indexRead entry
  rw [dif_pos inside] at found
  obtain ⟨rfl, pointer, ⟨atRole⟩⟩ := found
  rw [prepared.resolves ⟨_, inside⟩ region allocated] at pointer
  obtain ⟨spot, uses, roleCode, offered, held⟩ := roleSite region allocated
  obtain ⟨checked, ranRole, roleFrame, _, ⟨atExit⟩⟩ :=
    NativeRoleGate.fetched (X86PlacedFrameAddress.nativeBase other) extra vector
      atRole (controls.transport frame NativeCandidateLookup.clobbers_data)
      roleCode pointer ((frame.lookup 6 (by decide)).trans slotRead) identity
      ⟨offered.1, offered.2.preserved frame (by simp)⟩ role (st.levels level)
      (NativeRoleGate.resident_preserved held frame)
  rw [NativeCandidateLookup.match_handlers] at ranRole
  let prelude := 6 + (1 + 3 * NativeRoleGate.probes identity (NativeRoleGate.forbidden role (st.levels level)))
  have ranPrelude := X86FuelPrefix.fetches_then 6 _ before selected checked ranLookup ranRole
  have all : X86StateFrame.Frame (NativeCandidateLookup.clobbers ∪ NativeRoleGate.clobbers) ∅ before checked :=
    (frame.trans roleFrame).mono (Finset.Subset.refl _) (by simp)
  have existing := levels.preserved codes published all (by intro i; simp)
  cases eligible : role.allows (st.levels level) identity with
  | false =>
    have denied : At image checked base refused := by simpa [eligible] using atExit
    obtain ⟨after, ended, returned, word, location⟩ := X86PlacedScalar.rex_immediate
      (X86FrameLoad.linkedHandlers (X86PlacedFrameAddress.nativeBase other)) extra vector denied
      returns.noFits (X86BoundedLoad.physical dst) 0 returns.no
    have original := levels.preserved codes existing (X86StateFrame.registerOnly returned) (by intro i; simp)
    have execution := PlannedPremise.unavailable_occurrence_refuses codes st formed role pattern level index dst identity term row eligible
    have exactResult : lookup after (X86BoundedLoad.physical dst) = some ((st.write dst 0).machine.registers dst) := by
      simpa [StoreInstructions.State.write, P1WordExecution.State.write] using word
    refine ⟨after, prelude + 1, st.write dst 0, old,
      X86FuelPrefix.fetches_then prelude 1 before checked after ranPrelude ended, execution, exactResult, original, ?_⟩
    simpa [PlannedPremise.planned, eligible] using And.intro (Eq.refl old) location
  | true =>
    have atMatch : At image checked base matchAt := by simpa [eligible] using atExit
    have memory := ProjectedCandidate.readouts tags codes region expected (bankMemory.preserved all)
    have ready : Ready (MatchPlan.demand (MatchPlan.compile pattern)) tags codes
        (ProjectedCandidate.candidate (MatchPlan.compile pattern) region) bank (MatchPlan.observe term) table checked :=
      ⟨⟨(all.lookup 6 (by decide)).trans slotRead, (roleFrame.lookup 7 (by decide)).trans pointer,
        (all.lookup 8 (by decide)).trans zero, (all.lookup 9 (by decide)).trans one⟩, memory,
        binding_bank_kept codes initial all⟩
    have address := (roleFrame.lookup _ keepRoleAddress).trans ((frame.lookup _ keepLookupAddress).trans addressReg)
    have savedHandle := (roleFrame.lookup _ keepRoleHandle).trans ((frame.lookup _ keepLookupHandle).trans handleReg)
    obtain ⟨after, depth, abstract, resident, run, exactInstruction, result, newLevels, finish⟩ :=
      NativeMatchPublish.fetched codes st formed role pattern identity level index dst term row eligible table tableView
        (X86PlacedFrameAddress.nativeBase other) extra vector (ProjectedCandidate.relocate reference region plan)
        atMatch ((controls.transport frame NativeCandidateLookup.clobbers_data).transport roleFrame NativeRoleGate.clobbers_data)
        ready (geometry region allocated) returns
        levels old existing privateBank next nextIs commit commitCode commitSafe keepsOthers handle resolves
        address savedHandle keepMatchAddress keepMatchHandle
    rw [NativeCandidateLookup.match_handlers] at run
    refine ⟨after, prelude + depth, abstract, resident,
      X86FuelPrefix.fetches_then prelude depth before checked after ranPrelude run,
      exactInstruction, result, newLevels, ?_⟩
    cases verdict : MatchPlan.run (MatchPlan.observe term) (MatchPlan.compile pattern) table <;>
      simpa [PlannedPremise.planned, eligible, verdict] using finish

/-- A missing ordinal gives the source's invalid-input result, and
native execution has not entered the matcher or touched any bank. -/
theorem invalid_ordinal (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ)) {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes st.store = some packed)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start invalid : ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    (layout : NativeCandidateLookup.Layout st.store.occurrences.length)
    (pointers : Fin st.store.occurrences.length → Word) (resident : layout.Represents pointers before)
    (outside : ¬ (st.machine.registers index).toNat < st.store.occurrences.length)
    (source : Fin 16) (sourceSafe : source ≠ 14) (indexRead : lookup before source = some (st.machine.registers index))
    (header : lookup before 7 = some layout.header) (candidateBase : lookup before 2 = some layout.directory.pointer)
    (entry : NativeCandidateLookup.Checked image start invalid source layout.countOffset) :
    letI : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧
      X86StateFrame.Frame {.r14, .rflags, .rip} ∅ before after ∧ Nonempty (At image after base invalid) ∧
      executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .error .invalidInput := by
  obtain ⟨after, steps, run, _, found⟩ := NativeCandidateLookup.fetched other extra vector point controls layout pointers
    resident header candidateBase source sourceSafe (st.machine.registers index) indexRead entry
  rw [dif_neg outside] at found
  obtain ⟨rfl, frame, refused⟩ := found
  refine ⟨after, run, frame, refused, PlannedPremise.out_of_range_refuses codes st formed role pattern level index dst ?_⟩
  rw [PackedOccurrences.at_exact codes formed]
  exact List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt outside)

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSelectedMatch
