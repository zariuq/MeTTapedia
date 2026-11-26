import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermSelection
import Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisionTargets
import Mettapedia.Machines.TIsa.StoreInstructions.PackedTermEdges

/-!
# Native term dispatch with no preselected headers

The code accepts two term handles, checks each against the live
arena, loads the selected headers, and branches to the next
unification action. The raw handles and selected record addresses
remain available to the continuations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeTermDispatch

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Controls Reads)
open UnifierHeaders (Exit dispatch Symbols)
open PackedTerms (Arena lookup_header)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Targets where
  malformed : ℕ
  discard : ℕ
  bindLeft : ℕ
  bindRight : ℕ
  expand : ℕ
  clash : ℕ

def Targets.at : Targets → Exit → ℕ
  | t, .malformed => t.malformed
  | t, .discard => t.discard
  | t, .bindLeft => t.bindLeft
  | t, .bindRight => t.bindRight
  | t, .expand => t.expand
  | t, .clash => t.clash

def Targets.fromWord (t : Targets) (word : BitVec 32) : ℕ :=
  match word.toNat with
  | 1 => t.discard
  | 2 => t.bindLeft
  | 3 => t.bindRight
  | 4 => t.expand
  | 5 => t.clash
  | _ => t.malformed

theorem Targets.afterCode (t : Targets) (exit : Exit) : t.fromWord exit.word = t.at exit := by
  cases exit <;> rfl

def Targets.inImage (t : Targets) (image : NativeImage.View) : Prop :=
  ∀ exit : Exit, t.at exit ≤ image.size

theorem Targets.word_inImage (t : Targets) (image : NativeImage.View) (known : t.inImage image) (word : BitVec 32) :
    t.fromWord word ≤ image.size := by
  unfold Targets.fromWord
  split
  · exact known .discard
  · exact known .bindLeft
  · exact known .bindRight
  · exact known .expand
  · exact known .clash
  · exact known .malformed

def choose (arena : Arena) (left right : Word) : Exit :=
  match arena.nodes[left.toNat]?, arena.nodes[right.toNat]? with
  | some l, some r => dispatch l.header r.header
  | _, _ => .malformed

def cost (arena : Arena) (left right : Word) : ℕ :=
  if l : left.toNat < arena.nodes.size then
    if r : right.toNat < arena.nodes.size then
      13 + NativeDecisionTargets.cost
        (NativeUnifierHeaders.registers arena.nodes[left.toNat].header arena.nodes[right.toNat].header)
        NativeUnifierHeaders.tree
    else 4
  else 2

def emit (start : ℕ) (target : Targets) : List ℕ :=
  NativeTermSelection.emit start target.malformed ++
    (NativeUnifierHeaders.headerLoads ++ NativeDecisionTargets.emit target.fromWord NativeUnifierHeaders.tree (start + 65))

theorem emit_size (start : ℕ) (target : Targets) :
    (emit start target).length = 65 + NativeDecisionTargets.width NativeUnifierHeaders.tree := by
  simp only [emit, List.length_append, NativeTermSelection.emit_size, NativeUnifierHeaders.header_load_size,
    NativeDecisionTargets.emit_size]
  omega

structure Placed (image : NativeImage.View) (start : ℕ) (target : Targets) : Prop where
  selection : NativeTermSelection.Placed image start target.malformed
  headerSpace : start + 65 ≤ image.size
  headers : Code image (start + 37) NativeUnifierHeaders.headerLoads
  branch : NativeDecisionTargets.Placed image target.fromWord (start + 65) NativeUnifierHeaders.tree

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (target : Targets)
    (extent : start + (emit start target).length ≤ image.size) (ends : target.inImage image) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit start target)) :
    Placed image start target := by
  obtain ⟨selection, body⟩ := NativeWords.code_append (show Code image start
    (NativeTermSelection.emit start target.malformed ++ _) from installed)
  rw [NativeTermSelection.emit_size] at body
  obtain ⟨headers, branch⟩ := NativeWords.code_append body
  rw [NativeUnifierHeaders.header_load_size] at branch
  rw [emit_size] at extent
  exact ⟨NativeTermSelection.placed_of_emitted image start target.malformed (by omega) (ends .malformed) short selection,
    by omega, headers, NativeDecisionTargets.placed_of_emitted image target.fromWord NativeUnifierHeaders.tree
      (start + 65) (by omega) (target.word_inImage image ends) short branch⟩

noncomputable abbrev handlers := NativeTermSelection.handlers

abbrev clobbers : Finset Register := NativeTermSelection.clobbers ∪ NativeUnifierHeaders.loadClobbers

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

structure Inputs {nodeCapacity edgeCapacity : ℕ} (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (arena : Arena) (before : Native) (left right : Word) : Prop where
  ready : NativeTermArena.Ready layout arena before
  left : lookup before 1 = some left
  right : lookup before 2 = some right
  count : lookup before 15 = some (BitVec.ofNat 64 arena.nodes.size)
  table : lookup before 3 = some layout.nodes.pointer
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1
  two : lookup before 14 = some 2

def Retained {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
    {arena : Arena} {before : Native} {left right : Word} (inputs : Inputs layout arena before left right)
    (after : Native) : Prop :=
  if l : left.toNat < arena.nodes.size then
    if r : right.toNat < arena.nodes.size then
      lookup after 6 = some (inputs.ready.bank ⟨left.toNat, l⟩).pointer ∧
        lookup after 7 = some (inputs.ready.bank ⟨right.toNat, r⟩).pointer ∧
        (∀ reg ∈ NativeUnifierHeaders.tree.reads, lookup after reg = some
          (NativeUnifierHeaders.registers arena.nodes[left.toNat].header arena.nodes[right.toNat].header reg))
    else X86StateFrame.Frame NativeTermSelection.compareClobbers ∅ before after
  else X86StateFrame.Frame NativeTermSelection.compareClobbers ∅ before after

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (target : Targets)
    (placed : Placed image start target)
    {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity}
    {arena : Arena} {left right : Word} (entry : Inputs layout arena before left right) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (cost arena left right)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧ Retained entry after ∧
      Nonempty (At image after base (target.at (choose arena left right))) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨located, steps, ran, selection, arrived⟩ := NativeTermSelection.fetched other extra vector point placed.selection
    layout arena entry.ready left right entry.left entry.right entry.count entry.table entry.zero
  by_cases leftInside : left.toNat < arena.nodes.size
  · rw [NativeTermSelection.Arrival, dif_pos leftInside] at arrived
    by_cases rightInside : right.toNat < arena.nodes.size
    · rw [dif_pos rightInside] at arrived
      obtain ⟨rfl, pointsL, pointsR, ⟨atHeaders⟩⟩ := arrived
      let leftBank := entry.ready.bank ⟨left.toNat, leftInside⟩
      let rightBank := entry.ready.bank ⟨right.toNat, rightInside⟩
      let l := arena.nodes[left.toNat].header
      let r := arena.nodes[right.toNat].header
      obtain ⟨lt, ls⟩ := entry.ready.header_read ⟨left.toNat, leftInside⟩
      obtain ⟨rt, rs⟩ := entry.ready.header_read ⟨right.toNat, rightInside⟩
      have present : NativeUnifierHeaders.Resident leftBank rightBank l r located :=
        ⟨pointsL, pointsR, lt.preserved selection (by simp), rt.preserved selection (by simp),
          ls.preserved selection (by simp), rs.preserved selection (by simp), (selection.lookup 12 (by decide)).trans entry.zero,
          (selection.lookup 13 (by decide)).trans entry.one, (selection.lookup 14 (by decide)).trans entry.two⟩
      have bytes : Code image (start + 37) (NativeUnifierHeaders.loadBytes leftBank rightBank) := by
        rw [NativeUnifierHeaders.loads_independent]
        exact placed.headers
      obtain ⟨loaded, ranLoad, headerFrame, operands, ⟨atDispatch⟩⟩ := NativeUnifierHeaders.fetched_loads
        (X86PlacedFrameAddress.nativeBase other) extra vector atHeaders
        (controls.transport selection NativeTermSelection.clobbers_data) leftBank rightBank l r present
        (NativeUnifierHeaders.checked_loads leftBank rightBank image (start + 37)
          (show start + 65 ≤ image.size from placed.headerSpace) bytes)
      rw [NativeCandidateLookup.match_handlers] at ranLoad
      obtain ⟨after, hopped, branchFrame, endpoint⟩ := NativeDecisionTargets.fetched
        (X86PlacedFrameAddress.nativeBase other) extra vector target.fromWord NativeUnifierHeaders.tree
        (NativeUnifierHeaders.registers l r) (show At image loaded base (start + 65) from atDispatch) placed.branch operands
      rw [NativeUnifierHeaders.decision, target.afterCode] at endpoint
      have running := X86FuelPrefix.fetches_then 9 4 before located loaded ran ranLoad
      have all := (selection.trans headerFrame).trans branchFrame
      rw [cost, dif_pos leftInside, dif_pos rightInside, choose,
        Array.getElem?_eq_getElem leftInside, Array.getElem?_eq_getElem rightInside]
      refine ⟨after, X86FuelPrefix.fetches_then 13 _ before loaded after running hopped,
        all.mono (by decide) (by simp), ?_, endpoint⟩
      rw [Retained, dif_pos leftInside, dif_pos rightInside]
      have keeps := headerFrame.trans branchFrame
      exact ⟨(keeps.lookup 6 (by decide)).trans pointsL, (keeps.lookup 7 (by decide)).trans pointsR,
        fun reg read => (branchFrame.lookup reg (by fin_cases reg <;> decide)).trans (operands reg read)⟩
    · rw [dif_neg rightInside] at arrived
      obtain ⟨rfl, frame, endpoint⟩ := arrived
      simp only [cost, dif_pos leftInside, dif_neg rightInside, choose,
        Array.getElem?_eq_getElem leftInside, Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt rightInside)]
      exact ⟨located, ran, selection.mono (by decide) (by simp), by
        simpa only [Retained, dif_pos leftInside, dif_neg rightInside] using frame, endpoint⟩
  · rw [NativeTermSelection.Arrival, dif_neg leftInside] at arrived
    obtain ⟨rfl, frame, endpoint⟩ := arrived
    simp only [cost, dif_neg leftInside, choose, Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt leftInside)]
    exact ⟨located, ran, selection.mono (by decide) (by simp), by
      simpa only [Retained, dif_neg leftInside] using frame, endpoint⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem chosen_source_action (symbols : Symbols σ) (arena : Arena) (left right : Word) (l r : Term σ)
    (leftRead : PackedTerms.lookup symbols arena left = some l) (rightRead : PackedTerms.lookup symbols arena right = some r) :
    UnifierHeaders.operation l r (choose arena left right) = some (Derivation.FiniteUnifier.action l r) := by
  obtain ⟨lNode, lFound⟩ := PackedTermEdges.node_at symbols arena left l leftRead
  obtain ⟨rNode, rFound⟩ := PackedTermEdges.node_at symbols arena right r rightRead
  simp only [choose, lFound, rFound]
  exact UnifierHeaders.decoded_action symbols l r lNode.header rNode.header
    (lookup_header symbols arena left l lNode leftRead lFound) (lookup_header symbols arena right r rNode rightRead rFound)

end Mettapedia.Machines.TIsa.StoreInstructions.NativeTermDispatch
