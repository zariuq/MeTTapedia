import Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEffect
import Mettapedia.Machines.TIsa.StoreInstructions.NativePremise

/-!
# Native MATCH on a selected open occurrence

After selecting an occurrence, the code checks its identity
against the current ports. On success it writes the new use and
appends one equation using the term read from the occurrence.
The next level's equation head is the last store. On refusal
the only result is zero; there is no private or published write.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicPremise

open Mettapedia.Logic.LP
open Derivation (Role Match)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart footprint Reads)
open X86PlacedScalar (Code)
open NativeRoleGate (WordAt Ports)
open NativeEquationInputs (Operands)
open NativeEquationEffect (Destination)
open PackedEquations (Arena Node)
open MemoryBinding (Native handlers storeEncoding)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Layout (slot candidate : Word) (capacity : ℕ) (arena : Arena) where
  identity : WordAt candidate
  value : WordAt candidate
  uses : Ports slot
  record : WordAt slot
  operands : Operands slot candidate
  readsValue : operands.right = value.source
  destination : Destination capacity arena

variable {slot candidate : Word} {capacity : ℕ} {arena : Arena}

def Layout.finish (layout : Layout slot candidate capacity arena) (remember : ℕ) : ℕ :=
  remember + 7 + layout.operands.width + layout.destination.width

structure Layout.Placed (layout : Layout slot candidate capacity arena) (node : Node) (role : Role)
    (image : NativeImage.View) (start remember refused : ℕ) (result : Fin 16) : Prop where
  useGate : NativeRoleGate.Gate image start remember refused layout.identity (layout.uses.forRole role)
  rememberFits : remember + 7 ≤ image.size
  rememberCode : Code image remember (storeEncoding.bytes 2 layout.record.offset)
  load : layout.operands.Checked image (remember + 7)
  append : layout.destination.Placed node image (remember + 7 + layout.operands.width)
  returns : NativePremise.Return image (layout.finish remember) refused result

structure Layout.Geometry (layout : Layout slot candidate capacity arena) (node : Node)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  markCode : CodeApart image base (footprint layout.record.cell.address)
  append : layout.destination.Geometry node image base
  priorUses : ∀ spot ∈ layout.uses.taken ++ layout.uses.read,
    Disjoint (footprint spot.cell.address) (footprint layout.record.cell.address ∪ layout.destination.writes node)
  priorArena : ∀ (entry : Fin capacity) (field : Fin 3),
    Disjoint (footprint (NativeEquationAppend.location layout.destination.bank entry field))
      (footprint layout.record.cell.address)
  parent : Disjoint (footprint layout.operands.previous.cell.address)
    (footprint layout.record.cell.address ∪ layout.destination.writes node)
  left : Disjoint layout.operands.left.uses (footprint layout.record.cell.address)
  right : Disjoint layout.operands.right.uses (footprint layout.record.cell.address)
  writtenUse : Disjoint (footprint layout.record.cell.address) (layout.destination.writes node)

structure Layout.Ready {V B : Type*} (layout : Layout slot candidate capacity arena) (node : Node)
    (entry : Match V B) (id : ℕ) (state : Native) : Prop where
  candidate : lookup state 7 = some candidate
  level : lookup state 6 = some slot
  identity : layout.identity.ReadsId state id
  uses : layout.uses.Represents state entry
  operands : layout.operands.Ready state node
  arena : layout.destination.Ready state
  keepBank : key layout.destination.encoding.base ∉ NativeRoleGate.clobbers
  keepRoot : key layout.destination.rootEncoding.base ∉ NativeRoleGate.clobbers
  keepHandle : key layout.destination.root.source ∉ NativeRoleGate.clobbers

universe u q
variable {σ : LPSignature.{u,u,q,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def extended (st : SymbolicExecution.Frame σ) (role : Role) (pattern : Term σ)
    (level id : ℕ) (term : Term σ) : Match (Term σ) (SymbolicExecution.Work σ) :=
  (st.levels level).select role id ((st.levels level).bindings.extend (pattern, term))

theorem source (knowledge : SymbolicExecution.Equations σ)
    (codes : PackedOccurrences.Codes (Term σ)) (st : SymbolicExecution.Frame σ)
    {packed : PackedOccurrences.Layout} (formed : PackedOccurrences.pack codes st.store = some packed)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg) (id : ℕ) (term : Term σ)
    (selected : PackedOccurrences.at? codes packed (st.machine.registers index).toNat = some (id, term)) :
    executeInstructionWith (SymbolicExecution.profile knowledge).step st
      (.transform (.premise role pattern level index dst)) =
      .ok (if role.allows (st.levels level) id then
        (st.setLevel (level + 1) (extended st role pattern level id term)).write dst 1
      else st.write dst 0) := by
  rw [PackedOccurrences.at_exact codes formed] at selected
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, selected,
    SymbolicExecution.profile, SymbolicExecution.propose]
  cases role.allows (st.levels level) id <;> rfl

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start remember refused : ℕ}
    {before : Native} (point : At image before codeBase start) (controls : Controls before)
    (knowledge : SymbolicExecution.Equations σ) (codes : PackedOccurrences.Codes (Term σ))
    (st : SymbolicExecution.Frame σ) {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes st.store = some packed)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg) (id : ℕ) (term : Term σ)
    (selected : PackedOccurrences.at? codes packed (st.machine.registers index).toNat = some (id, term))
    (layout : Layout slot candidate capacity arena) (node : Node) (fitHead : PackedEquations.CanAppend arena node.older)
    (ready : layout.Ready node (st.levels level) id before)
    (placed : layout.Placed node role image start remember refused (X86BoundedLoad.physical dst))
    (geometry : layout.Geometry node image codeBase)
    (older : PackedEquations.read codes arena node.older = some (st.levels level).bindings.newer)
    (lhs : codes.decode node.left = some pattern) (rhs : codes.decode node.right = some term) :
    letI : OtherOpcodeHandlers := handlers other extra
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
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let probeCost := 1 + 3 * NativeRoleGate.probes id (NativeRoleGate.forbidden role (st.levels level))
  obtain ⟨checked, ranRole, roleFrame, received, ⟨gate⟩⟩ :=
    NativeRoleGate.fetched other extra vector point controls placed.useGate ready.candidate ready.level id
      ready.identity role (st.levels level) (NativeRoleGate.Ports.restrict ready.uses role)
  have abstract := source knowledge codes st formed role pattern level index dst id term selected
  cases allowed : role.allows (st.levels level) id with
  | false =>
    have denied : At image checked codeBase refused := by simpa [allowed] using gate
    obtain ⟨after, ranNo, returned, value, point⟩ := X86PlacedScalar.rex_immediate
      (X86FrameLoad.linkedHandlers other) extra vector denied placed.returns.noFits (X86BoundedLoad.physical dst) 0 placed.returns.no
    have memory := roleFrame.trans (X86StateFrame.registerOnly returned)
    refine ⟨after, probeCost + 1, st.write dst 0,
      X86FuelPrefix.fetches_then probeCost 1 before checked after ranRole ranNo, ?_, ?_, ?_⟩
    · simpa [allowed] using abstract
    · simpa [StoreInstructions.State.write, P1WordExecution.State.write] using value
    · exact ⟨fun address => memory.memory address (by simp), rfl, point⟩
  | true =>
    have atMark : At image checked codeBase remember := by simpa [allowed] using gate
    have interpreted := controls.transport roleFrame NativeRoleGate.clobbers_data
    obtain ⟨marked, ranMark, markFrame, identity, ⟨atOperands⟩⟩ :=
      X86PlacedMemory.stores (handlers other extra) vector atMark interpreted storeEncoding 2 layout.record.offset
        slot (BitVec.ofNat 64 id) layout.record.cell ((roleFrame.lookup 6 (by decide)).trans ready.level)
        received placed.rememberFits placed.rememberCode geometry.markCode
    have markedFrame : X86StateFrame.Frame NativeRoleGate.clobbers (footprint layout.record.cell.address) before marked :=
      (roleFrame.trans markFrame).mono (by simp) (by simp)
    have input : layout.operands.Ready marked node :=
      ⟨ready.operands.previous.preserved markedFrame (geometry.parent.mono_right Finset.subset_union_left),
        layout.operands.left.ready_preserved ready.operands.left markedFrame geometry.left,
        layout.operands.right.ready_preserved ready.operands.right markedFrame geometry.right⟩
    have keep := ready.arena.preserved markedFrame geometry.priorArena ready.keepBank ready.keepRoot ready.keepHandle
    have atLoad : At image marked codeBase (remember + 7) := atOperands
    obtain ⟨published, ranAppend, appendFrame, newArena, newRoot, newProblem, _, ⟨atReturn⟩⟩ :=
      NativeEquationEffect.fetched other extra vector atLoad (controls.transport markedFrame NativeRoleGate.clobbers_data)
        layout.operands placed.load node fitHead input ((markedFrame.lookup 6 (by decide)).trans ready.level)
        ((markedFrame.lookup 7 (by decide)).trans ready.candidate) layout.destination keep placed.append
        geometry.append codes _ older (pattern, term) lhs rhs
    have atFlag : At image published codeBase (layout.finish remember) := atReturn
    obtain ⟨after, ranYes, returned, value, endpoint⟩ := X86PlacedScalar.rex_immediate
      (X86FrameLoad.linkedHandlers other) extra vector atFlag placed.returns.yesFits (X86BoundedLoad.physical dst) 1 placed.returns.yes
    let result := (st.setLevel (level + 1) (extended st role pattern level id term)).write dst 1
    have returnedFrame := X86StateFrame.registerOnly returned
    have output : X86StateFrame.Frame _ (layout.destination.writes node) marked after :=
      (appendFrame.trans returnedFrame).mono (Finset.Subset.refl _) (by simp)
    have memory := markedFrame.trans output
    have oldUses := NativeRoleGate.Ports.preserved ready.uses memory geometry.priorUses
    have keptIdentity := identity.preserved output geometry.writtenUse
    have picked := NativeRoleGate.Ports.record oldUses role layout.record id
      ((st.levels level).bindings.extend (pattern, term)) ⟨ready.identity.1, keptIdentity⟩
    have levelExact : result.levels (level + 1) = extended st role pattern level id term := by
      simp [result, StoreInstructions.State.setLevel, StoreInstructions.State.write]
    have rolePrefix := X86FuelPrefix.fetches_then probeCost 1 before checked marked ranRole ranMark
    have appended := X86FuelPrefix.fetches_then (probeCost + 1) 7 before marked published rolePrefix ranAppend
    refine ⟨after, (probeCost + 1 + 7) + 1, result,
      X86FuelPrefix.fetches_then (probeCost + 1 + 7) 1 before published after appended ranYes, ?_, ?_, ?_⟩
    · simpa [allowed, result] using abstract
    · simpa [result, StoreInstructions.State.setLevel, StoreInstructions.State.write, P1WordExecution.State.write] using value
    · simp only [if_true, levelExact]
      refine ⟨newArena.preserved returnedFrame (by intro _ _; simp), newRoot.preserved returnedFrame (by simp),
        ?_, picked, ready.operands.previous.preserved memory geometry.parent, endpoint⟩
      cases role <;> exact ⟨newProblem, rfl⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicPremise
