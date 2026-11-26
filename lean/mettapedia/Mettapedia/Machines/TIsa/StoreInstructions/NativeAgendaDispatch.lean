import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaRead

/-!
# The emitted entry and dispatch of a packed solver iteration

The agenda pop leaves the two raw operands in their argument
registers. The next bytes select the term records and transfer
to the continuation for the chosen action. In particular the
header comparisons do not overwrite the advanced agenda root.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaDispatch

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open NativeTermDispatch (Targets)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def emit (start done : ℕ) (target : Targets) : List ℕ :=
  NativeAgendaRead.emit start done target.malformed ++ NativeTermDispatch.emit (start + 72) target

structure Placed (image : NativeImage.View) (start done : ℕ) (target : Targets) : Prop where
  pop : NativeAgendaRead.Placed image start done target.malformed
  dispatch : NativeTermDispatch.Placed image (start + 72) target

theorem placed_of_emitted (image : NativeImage.View) (start done : ℕ) (target : Targets)
    (size : start + (emit start done target).length ≤ image.size) (finished : done ≤ image.size)
    (targets : target.inImage image) (short : image.size < 2 ^ 31) (bytes : Code image start (emit start done target)) :
    Placed image start done target := by
  obtain ⟨pop, dispatch⟩ := NativeWords.code_append (show Code image start
    (NativeAgendaRead.emit start done target.malformed ++ NativeTermDispatch.emit (start + 72) target) from bytes)
  rw [NativeAgendaRead.emit_size] at dispatch
  simp only [emit, List.length_append, NativeAgendaRead.emit_size] at size
  exact ⟨NativeAgendaRead.placed_of_emitted image start done target.malformed (by omega) finished
      (targets .malformed) short pop,
    NativeTermDispatch.placed_of_emitted image (start + 72) target (by omega) targets short dispatch⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := NativeAgendaRead.clobbers ∪ NativeTermDispatch.clobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {agendaCapacity nodeCapacity edgeCapacity : ℕ}

structure Context (agendaLayout : NativeAgendaRecords.Layout agendaCapacity)
    (termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (agenda : PackedEquations.Arena) (terms : PackedTerms.Arena) (root : Word) (before : Native) : Prop where
  agendaReady : NativeAgendaRecords.Ready agendaLayout agenda before
  termReady : NativeTermArena.Ready termLayout terms before
  agendaBase : lookup before 5 = some agendaLayout.words.pointer
  termBase : lookup before 3 = some termLayout.nodes.pointer
  cursor : lookup before 11 = some root
  termCount : lookup before 15 = some (BitVec.ofNat 64 terms.nodes.size)
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1
  two : lookup before 14 = some 2

theorem Context.next {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
    {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {agenda : PackedEquations.Arena}
    {terms : PackedTerms.Arena} {root next : Word} {before after : Native}
    (context : Context agendaLayout termLayout agenda terms root before)
    (frame : X86StateFrame.Frame clobbers ∅ before after) (cursor : lookup after 11 = some next) :
    Context agendaLayout termLayout agenda terms next after :=
  ⟨context.agendaReady.preserved frame, context.termReady.preserved frame, (frame.lookup 5 (by decide)).trans context.agendaBase,
    (frame.lookup 3 (by decide)).trans context.termBase, cursor, (frame.lookup 15 (by decide)).trans context.termCount,
    (frame.lookup 12 (by decide)).trans context.zero, (frame.lookup 13 (by decide)).trans context.one,
    (frame.lookup 14 (by decide)).trans context.two⟩

def cost (agenda : PackedEquations.Arena) (terms : PackedTerms.Arena) (root : Word) : ℕ :=
  NativeAgendaRead.cost agenda root + match NativeAgendaRecords.top agenda root with
  | .equation node => NativeTermDispatch.cost terms node.left node.right
  | _ => 0

def Selected {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {terms : PackedTerms.Arena}
    {before : Native} (ready : NativeTermArena.Ready termLayout terms before) (left right : Word) (after : Native) : Prop :=
  ∀ (l : left.toNat < terms.nodes.size) (r : right.toNat < terms.nodes.size),
    lookup after 6 = some (ready.bank ⟨left.toNat, l⟩).pointer ∧
      lookup after 7 = some (ready.bank ⟨right.toNat, r⟩).pointer ∧
      ∀ reg ∈ NativeUnifierHeaders.tree.reads, lookup after reg = some
        (NativeUnifierHeaders.registers terms.nodes[left.toNat].header terms.nodes[right.toNat].header reg)

def Arrival (agenda : PackedEquations.Arena) (terms : PackedTerms.Arena) (root : Word)
    {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {before : Native}
    (ready : NativeTermArena.Ready termLayout terms before) (image : NativeImage.View) (base : BitVec 48)
    (done : ℕ) (target : Targets) (after : Native) : Prop :=
  match NativeAgendaRecords.top agenda root with
  | .empty => lookup after 11 = some root ∧ Nonempty (At image after base done)
  | .malformed => lookup after 11 = some root ∧ Nonempty (At image after base target.malformed)
  | .equation node => lookup after 11 = some node.older ∧
    lookup after 1 = some node.left ∧ lookup after 2 = some node.right ∧ Selected ready node.left node.right after ∧
    Nonempty (At image after base (target.at (NativeTermDispatch.choose terms node.left node.right)))

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start done : ℕ} {target : Targets} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start done target)
    {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
    {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {agenda : PackedEquations.Arena}
    {terms : PackedTerms.Arena} {root : Word}
    (context : Context agendaLayout termLayout agenda terms root before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (cost agenda terms root)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ Arrival agenda terms root context.termReady image base done target after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨popped, popRun, popFrame, atTop⟩ := NativeAgendaRead.fetched other extra vector point controls placed.pop
    context.agendaReady context.agendaBase root context.cursor context.zero
  cases reading : NativeAgendaRecords.top agenda root with
  | empty =>
    simp only [cost, Arrival, reading, Nat.add_zero]
    exact ⟨popped, popRun, popFrame.mono Finset.subset_union_left (by simp),
      by simpa only [NativeAgendaRead.Arrival, reading] using atTop⟩
  | malformed =>
    simp only [cost, Arrival, reading, Nat.add_zero]
    exact ⟨popped, popRun, popFrame.mono Finset.subset_union_left (by simp),
      by simpa only [NativeAgendaRead.Arrival, reading] using atTop⟩
  | equation node =>
    rw [NativeAgendaRead.Arrival, reading] at atTop
    obtain ⟨tail, left, right, ⟨atTerms⟩⟩ := atTop
    have inputs : NativeTermDispatch.Inputs termLayout terms popped node.left node.right :=
      ⟨context.termReady.preserved popFrame, left, right, (popFrame.lookup 15 (by decide)).trans context.termCount,
        (popFrame.lookup 3 (by decide)).trans context.termBase, (popFrame.lookup 12 (by decide)).trans context.zero,
        (popFrame.lookup 13 (by decide)).trans context.one, (popFrame.lookup 14 (by decide)).trans context.two⟩
    obtain ⟨after, chooseRun, chooseFrame, kept, continuation⟩ :=
      NativeTermDispatch.fetched other extra vector atTerms (controls.transport popFrame NativeAgendaRead.clobbers_data)
        target placed.dispatch inputs
    simp only [cost, Arrival, reading]
    refine ⟨after, X86FuelPrefix.fetches_then _ _ before popped after popRun chooseRun,
      (popFrame.trans chooseFrame).mono (Finset.Subset.refl _) (by simp),
      (chooseFrame.lookup 11 (by decide)).trans tail,
      (chooseFrame.lookup 1 (by decide)).trans left, (chooseFrame.lookup 2 (by decide)).trans right, ?_, continuation⟩
    intro l r
    rw [NativeTermDispatch.Retained, dif_pos l, dif_pos r] at kept
    refine ⟨?_, ?_, kept.2.2⟩
    · rw [context.termReady.bank_word node.left l]
      simpa only [inputs.ready.bank_word] using kept.1
    · rw [context.termReady.bank_word node.right r]
      simpa only [inputs.ready.bank_word] using kept.2.1

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaDispatch
