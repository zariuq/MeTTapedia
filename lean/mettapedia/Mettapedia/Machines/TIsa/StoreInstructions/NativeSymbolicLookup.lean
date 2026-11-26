import Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicPremise
import Mettapedia.Machines.TIsa.StoreInstructions.NativePackedOccurrence

/-! # Native symbolic MATCH from a packed occurrence ordinal -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicLookup

open Mettapedia.Logic.LP
open Derivation (Role Match)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open PackedEquations (Arena Node)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {slot candidate : Word} {capacity : ℕ} {arena : Arena}

structure Context {V B : Type*} (layout : NativeSymbolicPremise.Layout slot candidate capacity arena)
    (node : Node) (entry : Match V B) (before : Native) : Prop where
  slot : lookup before 6 = some slot
  uses : layout.uses.Represents before entry
  prior : Reads before layout.operands.previous.cell.address node.older
  left : layout.operands.left.Ready before node.left
  arena : layout.destination.Ready before
  bankAcrossLookup : key layout.destination.encoding.base ∉ NativeCandidateLookup.clobbers
  rootAcrossLookup : key layout.destination.rootEncoding.base ∉ NativeCandidateLookup.clobbers
  handleAcrossLookup : key layout.destination.root.source ∉ NativeCandidateLookup.clobbers
  bankAcrossRole : key layout.destination.encoding.base ∉ NativeRoleGate.clobbers
  rootAcrossRole : key layout.destination.rootEncoding.base ∉ NativeRoleGate.clobbers
  handleAcrossRole : key layout.destination.root.source ∉ NativeRoleGate.clobbers

universe u q
variable {σ : LPSignature.{u,u,q,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Both the role test's identity and the append's right operand
come from the selected packed occurrence. The native entry only
needs the ordinal register, not either of those values. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start remember refused invalid : ℕ}
    {before : Native} (point : At image before codeBase start) (controls : Controls before)
    (knowledge : SymbolicExecution.Equations σ) (codes : PackedOccurrences.Codes (Term σ))
    (st : SymbolicExecution.Frame σ) {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes st.store = some packed)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg) (id : ℕ) (term : Term σ)
    (selected : PackedOccurrences.at? codes packed (st.machine.registers index).toNat = some (id, term))
    (ready : NativePackedOccurrence.Prepared packed before)
    (header : lookup before 7 = some ready.lookupCode.header)
    (directory : lookup before 2 = some ready.lookupCode.directory.pointer)
    (source : Fin 16) (safe : source ≠ 14) (indexRead : lookup before source = some (st.machine.registers index))
    (entry : NativeCandidateLookup.Checked image start invalid source ready.lookupCode.countOffset)
    (ordinal : Fin packed.occurrences.size) (ordinalExact : ordinal.val = (st.machine.registers index).toNat)
    (layout : NativeSymbolicPremise.Layout slot (ready.banks ordinal).pointer capacity arena)
    (identityPlace : layout.identity = NativePackedOccurrence.identity (ready.banks ordinal))
    (termPlace : layout.value = NativePackedOccurrence.termCode (ready.banks ordinal))
    (node : Node) (rawTerm : node.right = (packed.occurrences[ordinal.val]).2)
    (fitHead : PackedEquations.CanAppend arena node.older)
    (context : Context layout node (st.levels level) before)
    (placed : layout.Placed node role image (start + 30) remember refused (X86BoundedLoad.physical dst))
    (geometry : layout.Geometry node image codeBase)
    (older : PackedEquations.read codes arena node.older = some (st.levels level).bindings.newer)
    (lhs : codes.decode node.left = some pattern) :
    letI : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps abstract,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      executeInstructionWith (SymbolicExecution.profile knowledge).step st
        (.transform (.premise role pattern level index dst)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      if role.allows (st.levels level) id then
        NativeEquationAppend.Represents layout.destination.bank (arena.push node) after ∧
        Reads after layout.destination.root.cell.address (PackedEquations.next arena) ∧
        PackedEquations.Symbolic.Represents codes (arena.push node) (PackedEquations.next arena)
          (abstract.levels (level + 1)).bindings ∧
        (layout.uses.add layout.record role).Represents after (abstract.levels (level + 1)) ∧
        Reads after layout.operands.previous.cell.address node.older ∧
        Nonempty (At image after codeBase (layout.finish remember + 6))
      else
        (∀ address, after.mem.get? address = before.mem.get? address) ∧
        abstract = st.write dst 0 ∧ Nonempty (At image after codeBase (refused + 6)) := by
  let : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨located, found, ranLookup, frame, exactOrdinal, points, identitySeen, termSeen, interpreted, ⟨atMatch⟩⟩ :=
    NativePackedOccurrence.fetched codes other extra vector point controls ready header directory source safe _ indexRead
      entry id term selected
  have same : found = ordinal := Fin.ext (exactOrdinal.trans ordinalExact.symm)
  subst found
  have noWrites (spot : NativeRoleGate.WordAt slot) (_ : spot ∈ layout.uses.taken ++ layout.uses.read) :
      Disjoint (X86PlacedMemory.footprint spot.cell.address) ∅ := by simp
  have actualId : layout.identity.ReadsId located id := identityPlace.symm ▸ identitySeen
  have actualValue : layout.operands.right.Ready located node.right := by
    rw [layout.readsValue, termPlace, rawTerm]
    exact termSeen
  have decoded : codes.decode node.right = some term := rawTerm.symm ▸ interpreted
  have next : layout.Ready node (st.levels level) id located :=
    ⟨points, (frame.lookup 6 (by decide)).trans context.slot, actualId,
      NativeRoleGate.Ports.preserved context.uses frame noWrites,
      ⟨context.prior.preserved frame (by simp), layout.operands.left.ready_preserved context.left frame (by simp), actualValue⟩,
      context.arena.preserved frame (by intro _ _; simp) context.bankAcrossLookup context.rootAcrossLookup context.handleAcrossLookup,
      context.bankAcrossRole, context.rootAcrossRole, context.handleAcrossRole⟩
  obtain ⟨after, cost, abstract, ranMatch, executes, value, finish⟩ :=
    NativeSymbolicPremise.fetched (X86PlacedFrameAddress.nativeBase other) extra vector atMatch
      (controls.transport frame NativeCandidateLookup.clobbers_data) knowledge codes st formed role pattern level index dst id term
      selected layout node fitHead next placed geometry older lhs decoded
  rw [NativeCandidateLookup.match_handlers] at ranMatch
  refine ⟨after, 6 + cost, abstract, X86FuelPrefix.fetches_then 6 cost before located after ranLookup ranMatch,
    executes, value, ?_⟩
  cases allowed : role.allows (st.levels level) id with
  | true => simpa [allowed] using finish
  | false =>
    rw [allowed] at finish
    obtain ⟨memory, refused, reached⟩ := finish
    exact ⟨fun address => (memory address).trans (frame.memory _ (by simp)), refused, reached⟩

/-- An out-of-range ordinal exits before reading an occurrence or
any part of the symbolic match. It is invalid input, not a role
refusal or an inconsistent equation. -/
theorem invalid_ordinal (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start invalid : ℕ}
    {before : Native} (point : At image before codeBase start) (controls : Controls before)
    (knowledge : SymbolicExecution.Equations σ) (codes : PackedOccurrences.Codes (Term σ))
    (st : SymbolicExecution.Frame σ) {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes st.store = some packed)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg)
    (ready : NativePackedOccurrence.Prepared packed before)
    (header : lookup before 7 = some ready.lookupCode.header)
    (directory : lookup before 2 = some ready.lookupCode.directory.pointer)
    (source : Fin 16) (safe : source ≠ 14) (indexRead : lookup before source = some (st.machine.registers index))
    (entry : NativeCandidateLookup.Checked image start invalid source ready.lookupCode.countOffset)
    (outside : ¬ (st.machine.registers index).toNat < packed.occurrences.size) :
    letI : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧
      X86StateFrame.Frame {.r14, .rflags, .rip} ∅ before after ∧
      Nonempty (At image after codeBase invalid) ∧
      executeInstructionWith (SymbolicExecution.profile knowledge).step st
        (.transform (.premise role pattern level index dst)) = .error .invalidInput := by
  obtain ⟨after, steps, execution, _, reply⟩ := NativeCandidateLookup.fetched other extra vector point controls
    ready.lookupCode _ ready.resident header directory source safe _ indexRead entry
  rw [dif_neg outside] at reply
  obtain ⟨rfl, memory, refused⟩ := reply
  refine ⟨after, execution, memory, refused, ?_⟩
  have invalidPacked : PackedOccurrences.at? codes packed (st.machine.registers index).toNat = none := by
    simp only [PackedOccurrences.at?, Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt outside), Option.bind_none]
  rw [PackedOccurrences.at_exact codes formed] at invalidPacked
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, invalidPacked]

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicLookup
