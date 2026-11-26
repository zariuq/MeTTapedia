import Mettapedia.Machines.TIsa.StoreInstructions.NativePremise
import Mettapedia.Machines.TIsa.StoreInstructions.NativeLevels

/-!
# Publishing a successful native open match

The fetched MATCH body writes only its private bank. The refusal
endpoint keeps every published root. The success endpoint stores
one handle; that descriptor denotes the computed binding words,
not a precomputed match. Every other published level remains live.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPublish

open Mettapedia.Logic.LP
open Derivation (Role)
open Derivation.FirstOrderTerms (Bindings matcher)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Encoding CodeApart footprint)
open X86PlacedScalar (Code)
open NativeMatchPlan (Candidate Bank PlacedPlan Ready Geometry)
open NativeLevels (Native Directory Resident prepare)
open NativePremise (Return clobbers)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u q
variable {σ : LPSignature.{u,u,q,u}} {n : ℕ}

structure Commit (directory : Directory σ n) (next : Fin n) where
  encoding : Encoding
  pointer : Word
  offset : BitVec 32
  cell : Cell pointer offset
  target : cell.address = directory.root next
  source : Fin 16

def Commit.Checked {directory : Directory σ n} {next : Fin n} (commit : Commit directory next)
    (image : NativeImage.View) (start : ℕ) : Prop :=
  start + commit.encoding.length ≤ image.size ∧ Code image start (commit.encoding.bytes commit.source commit.offset)

private theorem key_outside_rip : ∀ r : Fin 16, key r ∉ ({.rip} : Finset Register) := by
  decide +kernel

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem fetched (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ))
    {memory : PackedOccurrences.Layout} (packed : PackedOccurrences.pack codes st.store = some memory)
    (role : Role) (pattern : Term σ) (identity level : ℕ) (index dst : P1Source.Reg) (term : GroundTerm σ)
    (row : PackedOccurrences.at? codes memory (st.machine.registers index).toNat = some (identity, term))
    (eligible : role.allows (st.levels level) identity = true)
    (table : BindingSlots.Table σ) (tableView : BindingSlots.Represents table (st.levels level).bindings)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ))}
    {slot candidate : Word} {input : Candidate candidate} {bank : Bank σ slot}
    {image : NativeImage.View} {base : BitVec 48} {start success refused : ℕ}
    (placed : PlacedPlan tags input bank image refused start success (MatchPlan.compile pattern))
    {before : Native} (point : At image before base start) (controls : Controls before)
    (ready : Ready (MatchPlan.demand (MatchPlan.compile pattern)) tags codes input bank (MatchPlan.observe term) table before)
    (geometry : Geometry (MatchPlan.demand (MatchPlan.compile pattern)) input bank image base)
    (returns : Return image success refused (X86BoundedLoad.physical dst))
    (directory : Directory σ n) (old : Fin n → Resident σ)
    (published : directory.Represents codes st.levels old before)
    (privateBank : ∀ i, Disjoint (directory.protected old i) bank.writes)
    (next : Fin n) (nextIs : next.val = level + 1)
    (commit : Commit directory next) (commitCode : commit.Checked image (success + 6))
    (commitSafe : CodeApart image base (footprint (directory.root next)))
    (keepsOthers : ∀ i, i ≠ next → Disjoint (directory.protected old i) (footprint (directory.root next)))
    (handle : Word) (resolves : directory.lookup handle = some (prepare bank (st.levels level) role identity))
    (addressReg : lookup before commit.encoding.base = some commit.pointer)
    (handleReg : lookup before commit.source = some handle)
    (keepAddress : key commit.encoding.base ∉ clobbers dst) (keepHandle : key commit.source ∉ clobbers dst) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps abstract resident,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      directory.Represents codes abstract.levels resident after ∧
      match MatchPlan.run (MatchPlan.observe term) (MatchPlan.compile pattern) table with
      | none => resident = old ∧ Nonempty (At image after base (refused + 6))
      | some _ => resident = Function.update old next (handle, prepare bank (st.levels level) role identity) ∧
          Nonempty (At image after base (success + 6 + commit.encoding.length)) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨tested, depth, abstract, ran, frame, executed, result, branch⟩ := NativePremise.fetched_match codes st packed role
    pattern identity level index dst term row eligible table tableView other extra vector
    placed point controls ready geometry returns
  have same := directory.preserved codes published frame privateBank
  cases planned : MatchPlan.run (MatchPlan.observe term) (MatchPlan.compile pattern) table with
  | none =>
    rw [planned] at branch
    exact ⟨tested, depth, abstract, old, ran, executed, result, branch.1.symm ▸ same, rfl, branch.2⟩
  | some following =>
    rw [planned] at branch
    obtain ⟨bindings, interpretation, denotes, stored, ⟨accept⟩⟩ := branch
    obtain ⟨after, wrote, storeFrame, written, finalPoint⟩ :=
      X86PlacedMemory.stores (MemoryBinding.handlers other extra) vector accept
        (controls.transport frame (NativePremise.clobbers_data dst)) commit.encoding commit.source commit.offset
        commit.pointer handle commit.cell
        ((frame.lookup _ keepAddress).trans addressReg)
        ((frame.lookup _ keepHandle).trans handleReg)
        commitCode.1 commitCode.2 (commit.target ▸ commitSafe)
    have newWords := NativeLevels.prepared_represents codes bank (st.levels level) role identity denotes stored
    have bankSafe := ((privateBank next).mono_left Finset.subset_union_left).symm
    have newReady := NativeLevels.Descriptor.preserved codes newWords (commit.target ▸ storeFrame) bankSafe
    have now := directory.retarget codes same (commit.target ▸ storeFrame) keepsOthers (commit.target ▸ written) resolves newReady
    refine ⟨after, depth + 1, abstract, _, X86FuelPrefix.fetches_then depth 1 before tested after ran wrote,
      executed, (storeFrame.lookup _ (key_outside_rip _)).trans result, ?_, rfl, finalPoint⟩
    rw [interpretation]
    simpa only [StoreInstructions.State.write, StoreInstructions.State.setLevel, nextIs] using now

end Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPublish
