import Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingGate
import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaDispatch
import Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

/-!
# Binding from the actual agenda and dispatch outcome

Both branch entries agree with the packed unifier's binding
decision. The selected register word is the canonical variable
symbol and the other operand is the replacement handle. A true
occurrence bit reaches the cycle handler; exhaustion is separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingSelection

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads footprint)
open NativeArenaGeometry (Region)
open NativeBindEntry (Side)
open NativeOccurs (word)
open PackedTerms (Arena)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def symbol (side : Side) (l r : UnifierHeaders.Header) : Word :=
  match side with | .left => l.symbol | .right => r.symbol

universe u p
variable {σ : LPSignature.{u,u,p,u}}

structure Choice (symbols : UnifierHeaders.Symbols σ) (arena : Arena)
    (left right : Word) (side : Side) [DecidableEq σ.vars] where
  l : left.toNat < arena.nodes.size
  r : right.toNat < arena.nodes.size
  name : σ.vars
  term : Term σ
  code : symbols.vars.encode name = some (symbol side arena.nodes[left.toNat].header arena.nodes[right.toNat].header)
  resolved : PackedTerms.lookup symbols arena (side.replacement left right) = some term
  inspection : PackedUnifierAction.inspect arena left right = some
    (if term.occursIn name then .refuse .occurs else
      .bindVar (symbol side arena.nodes[left.toNat].header arena.nodes[right.toNat].header) (side.replacement left right))

def Choice.query [DecidableEq σ.vars] {symbols : UnifierHeaders.Symbols σ} {arena : Arena} {left right : Word} {side : Side}
    (choice : Choice symbols arena left right side) : Word :=
  symbol side (arena.nodes[left.toNat]'choice.l).header (arena.nodes[right.toNat]'choice.r).header

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem choice_of_dispatch (symbols : UnifierHeaders.Symbols σ) (arena : Arena) (side : Side) (left right : Word)
    (lTerm rTerm : Term σ) (leftRead : PackedTerms.lookup symbols arena left = some lTerm)
    (rightRead : PackedTerms.lookup symbols arena right = some rTerm)
    (routed : NativeTermDispatch.choose arena left right = side.exiting) :
    Nonempty (Choice symbols arena left right side) := by
  obtain ⟨lNode, atL⟩ := PackedTermEdges.node_at symbols arena left lTerm leftRead
  obtain ⟨rNode, atR⟩ := PackedTermEdges.node_at symbols arena right rTerm rightRead
  obtain ⟨l, lNodeAt⟩ := Array.getElem?_eq_some_iff.mp atL
  obtain ⟨r, rNodeAt⟩ := Array.getElem?_eq_some_iff.mp atR
  have compiled := NativeTermDispatch.chosen_source_action symbols arena left right lTerm rTerm leftRead rightRead
  rw [routed] at compiled
  have act : UnifierHeaders.dispatch lNode.header rNode.header = side.exiting := by
    simpa only [NativeTermDispatch.choose, atL, atR] using routed
  cases side with
  | left =>
    cases lTerm with
    | const _ => cases compiled
    | app _ _ => cases compiled
    | var v =>
      have code := PackedUnifierAction.variable_code symbols v lNode
        (PackedTerms.lookup_header symbols arena left (.var v) lNode leftRead atL)
      have occurs := PackedOccurs.find_exact symbols arena v lNode.header.symbol code right rTerm rightRead
      refine ⟨⟨l, r, v, rTerm, ?_, rightRead, ?_⟩⟩
      · simpa only [symbol, lNodeAt] using code
      · simp [PackedUnifierAction.inspect, atL, atR, act, Side.exiting, PackedUnifierAction.binding, occurs,
          symbol, lNodeAt, Side.replacement]
  | right =>
    cases rTerm with
    | const _ => cases compiled
    | app _ _ => cases compiled
    | var v =>
      have code := PackedUnifierAction.variable_code symbols v rNode
        (PackedTerms.lookup_header symbols arena right (.var v) rNode rightRead atR)
      have occurs := PackedOccurs.find_exact symbols arena v rNode.header.symbol code left lTerm leftRead
      refine ⟨⟨l, r, v, lTerm, ?_, leftRead, ?_⟩⟩
      · simpa only [symbol, rNodeAt] using code
      · simp [PackedUnifierAction.inspect, atL, atR, act, Side.exiting, PackedUnifierAction.binding, occurs,
          symbol, rNodeAt, Side.replacement]

variable {nodeCapacity edgeCapacity markCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : Arena}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {table : Region markCapacity} {descriptor : WordRegion.Region 2}

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem selected_name {symbols : UnifierHeaders.Symbols σ} {left right : Word} {side : Side}
    (choice : Choice symbols arena left right side) {before after : Native}
    (ready : NativeTermArena.Ready layout arena before) (selected : NativeAgendaDispatch.Selected ready left right after) :
    lookup after side.nameSource = some choice.query := by
  have inputs := (selected choice.l choice.r).2.2
  cases side
  · exact inputs 10 (by decide)
  · exact inputs 0 (by decide)

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register :=
  NativeAgendaDispatch.clobbers ∪ NativeBindEntry.entryClobbers ∪ NativeBindingGate.clobbers

def Separated {l r : ℕ} (left : Region l) (right : Region r) : Prop :=
  left.pointer.toNat + 8 * l ≤ right.pointer.toNat ∨ right.pointer.toNat + 8 * r ≤ left.pointer.toNat

def descriptorRegion (descriptor : WordRegion.Region 2) : Region 2 :=
  ⟨descriptor.pointer, descriptor.aligned, descriptor.area⟩

private theorem descriptor_cell (descriptor : WordRegion.Region 2) (i : Fin 2) :
    (((descriptorRegion descriptor).slice 0 2 (by decide) (by decide) (by decide)).cell i).address =
      (descriptor.cell i).address := by
  rw [Region.slice_address]
  change X86CanonicalSpan.narrow (descriptor.pointer + BitVec.ofNat 64 (8 * (0 + i.val))) =
    X86CanonicalSpan.narrow (descriptor.pointer + BitVec.ofNat 64 (8 * i.val))
  rw [Nat.zero_add]

private theorem keep_agenda {agenda : PackedEquations.Arena} {before after : Native}
    {registers : Finset Register} {bytes : Finset ℕ} {begin finish : ℕ}
    (ready : NativeAgendaRecords.Ready agendaLayout agenda before)
    (frame : X86StateFrame.Frame registers bytes before after)
    (confined : NativeMarkTable.Within table begin finish bytes)
    (separate : Separated agendaLayout.words table) :
    NativeAgendaRecords.Ready agendaLayout agenda after := by
  refine ⟨ready.fits, ready.count.preserved frame ?_, fun index column => (ready.node index column).preserved frame ?_⟩
  · apply confined.apart
    intro slot
    exact agendaLayout.words.separate_arenas table separate 0 1 slot.val 1 (by decide) (by decide)
      (by omega) slot.isLt (by decide) (by decide) 0 0
  · apply confined.apart
    intro slot
    have bound := index.isLt.trans_le ready.fits
    exact agendaLayout.words.separate_arenas table separate (3 * (index.val + 1)) 3 slot.val 1 (by decide) (by decide)
      (by omega) slot.isLt (by decide) (by decide) column 0

private theorem keep_descriptor {before after : Native} {registers : Finset Register} {bytes : Finset ℕ}
    {begin finish : ℕ} (frame : X86StateFrame.Frame registers bytes before after)
    (confined : NativeMarkTable.Within table begin finish bytes)
    (separate : Separated (descriptorRegion descriptor) table) (index : Fin 2) (value : Word)
    (held : Reads before (descriptor.cell index).address value) :
    Reads after (descriptor.cell index).address value := by
  apply held.preserved frame
  apply confined.apart
  intro slot
  rw [← descriptor_cell descriptor index]
  exact (descriptorRegion descriptor).separate_arenas table separate 0 2 slot.val 1 (by decide) (by decide)
    (by decide) slot.isLt (by decide) (by decide) index 0

/-- The native execution from the agenda computes the binding
decision of the packed solver. The binding itself is only proposed;
no rewrite or trail publication has happened at either exit. -/
theorem fetched_binding (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {entry done shared cycle exhausted : ℕ}
    {targets : NativeTermDispatch.Targets} {before : Native}
    (point : At image before base entry) (controls : Controls before) (side : Side)
    (agendaCode : NativeAgendaDispatch.Placed image entry done targets)
    (entryCode : NativeBindEntry.EntryPlaced image side (targets.at side.exiting) shared)
    (gateCode : NativeBindingGate.Placed image shared cycle exhausted targets.malformed)
    (geometry : NativeOccursLoop.Geometry layout agendaLayout table image base)
    (agendaApart : Separated agendaLayout.words table) (descriptorApart : Separated (descriptorRegion descriptor) table)
    (agenda : PackedEquations.Arena) (root left right : Word) (history : PackedWorklist.Words)
    (context : NativeAgendaDispatch.Context agendaLayout layout agenda arena root before)
    (environment : NativeBindEntry.Environment layout arena agendaLayout table descriptor before)
    (held : PackedEquations.readWords agenda root = some ((left, right) :: history))
    (symbols : UnifierHeaders.Symbols σ) (lTerm rTerm : Term σ)
    (leftRead : PackedTerms.lookup symbols arena left = some lTerm) (rightRead : PackedTerms.lookup symbols arena right = some rTerm)
    (routed : NativeTermDispatch.choose arena left right = side.exiting) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ (choice : Choice symbols arena left right side) (after : Native) (steps : ℕ),
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      if (side.replacement left right).toNat < markCapacity then
        ∃ writes cursor,
          X86StateFrame.Frame clobbers writes before after ∧ lookup after 11 = some cursor ∧
          PackedEquations.readWords agenda cursor = some history ∧
          NativeMarkTable.Within table 0 ((side.replacement left right).toNat + 1) writes ∧
          NativeAgendaDispatch.Context agendaLayout layout agenda arena cursor after ∧
          NativeBindEntry.Environment layout arena agendaLayout table descriptor after ∧
          lookup after 0 = some (word (choice.term.occursIn choice.name)) ∧ lookup after 8 = some choice.query ∧
          lookup after 9 = some (side.replacement left right) ∧
          Nonempty (At image after base (if choice.term.occursIn choice.name then cycle else shared + 273))
      else X86StateFrame.Frame clobbers ∅ before after ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨choice⟩ := choice_of_dispatch symbols arena side left right lTerm rTerm leftRead rightRead routed
  obtain ⟨node, top, operands, later⟩ := NativeAgendaRecords.top_of_read agenda root ((left, right) :: history) held
  obtain ⟨leftEq, rightEq⟩ := Prod.mk.inj operands
  obtain ⟨selected, chosen, selectedFrame, position⟩ :=
    NativeAgendaDispatch.fetched other extra vector point controls agendaCode context
  simp only [NativeAgendaDispatch.Arrival, top] at position
  rw [leftEq, rightEq] at position
  obtain ⟨tail, leftReg, rightReg, selectedInputs, ⟨atEntry⟩⟩ := position
  rw [routed] at atEntry
  have pickedName := selected_name choice context.termReady selectedInputs
  have pickedTerm : lookup selected side.termSource = some (side.replacement left right) := by
    cases side
    · exact rightReg
    · exact leftReg
  obtain ⟨normalized, selectedEntry, entryFrame, query, target, ⟨atShared⟩⟩ :=
    NativeBindEntry.fetched_entry other extra vector atEntry side entryCode choice.query (side.replacement left right)
      pickedName pickedTerm
  have prelude := selectedFrame.trans entryFrame
  have registerFootprint : ∀ r ∈ ({3, 4, 5, 12, 13, 14} : Finset (Fin 16)),
      key r ∉ (NativeAgendaDispatch.clobbers ∪ NativeBindEntry.entryClobbers) := by decide +kernel
  have env := environment.preserved prelude registerFootprint
  obtain ⟨after, steps, decided, result⟩ := NativeBindingGate.fetched other extra vector atShared
    (controls.transport prelude (by decide)) gateCode geometry env symbols choice.name choice.query
    (side.replacement left right) query target choice.code choice.term choice.resolved
  refine ⟨choice, after, _, X86FuelPrefix.fetches_then _ _ before normalized after
    (X86FuelPrefix.fetches_then (NativeAgendaDispatch.cost agenda arena root) 3 before selected normalized chosen selectedEntry) decided, ?_⟩
  by_cases room : (side.replacement left right).toNat < markCapacity
  · rw [if_pos room] at result ⊢
    obtain ⟨writes, frame, confined, _, bit, name, replacement, endpoint⟩ := result
    have keeps := entryFrame.trans frame
    have all : X86StateFrame.Frame clobbers writes before after :=
      (prelude.trans frame).mono (Finset.Subset.refl _) (by simp)
    have remaining : lookup after 11 = some node.older := (keeps.lookup 11 (by decide)).trans tail
    have graph := context.termReady.kept all (fun i j => confined.apart _ (geometry.nodes i j))
      (fun i => confined.apart _ (geometry.edges i))
    have snapshot : NativeAgendaDispatch.Context agendaLayout layout agenda arena node.older after :=
      ⟨keep_agenda context.agendaReady all confined agendaApart, graph,
        (all.lookup 5 (by decide)).trans context.agendaBase, (all.lookup 3 (by decide)).trans context.termBase,
        remaining, (all.lookup 15 (by decide)).trans context.termCount, (all.lookup 12 (by decide)).trans context.zero,
        (all.lookup 13 (by decide)).trans context.one, (all.lookup 14 (by decide)).trans context.two⟩
    have ready : NativeBindEntry.Environment layout arena agendaLayout table descriptor after :=
      ⟨graph, snapshot.termBase, snapshot.agendaBase, environment.pool.preserved all (confined.apart _ geometry.pool),
        (all.lookup 4 (by decide)).trans environment.stack,
        keep_descriptor all confined descriptorApart 0 _ environment.markTable,
        keep_descriptor all confined descriptorApart 1 _ environment.capacity, snapshot.zero, snapshot.one, snapshot.two⟩
    exact ⟨writes, node.older, all, remaining, later, confined, snapshot, ready, bit, name, replacement, endpoint⟩
  · rw [if_neg room] at result ⊢
    exact ⟨(prelude.trans result.2.1).mono (Finset.Subset.refl _) (by simp), result.2.2⟩

namespace Examples

private def graphExample : Arena :=
  ⟨#[⟨⟨0, 9⟩, 0, 0⟩, ⟨⟨1, 7⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩], #[0]⟩

theorem both_sides_pass_the_same_canonical_variable_and_term :
    PackedUnifierAction.inspect graphExample 0 1 = some (.bindVar 9 1) ∧
      PackedUnifierAction.inspect graphExample 1 0 = some (.bindVar 9 1) := by decide +kernel

theorem both_sides_reject_the_same_cycle :
    PackedUnifierAction.inspect graphExample 0 2 = some (.refuse .occurs) ∧
      PackedUnifierAction.inspect graphExample 2 0 = some (.refuse .occurs) := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingSelection
