import Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPlan
import Mettapedia.Machines.TIsa.StoreInstructions.PlannedPremise

/-!
# Native decision and bindings for a packed MATCH occurrence

The selected identity and its term come from the packed store.
The native test sequence works on that term's path projection,
then writes the p1 boolean. On success its private binding bank
represents the new abstract level. Installing that level as the
caller's current continuation is a separate publication.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePremise

open Mettapedia.Logic.LP
open Derivation (Role)
open Derivation.FirstOrderTerms (Bindings matcher)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open NativeMatchPlan (Bank Candidate Ready Geometry PlacedPlan)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Native := X86RegisterRefinement.State

structure Return (image : NativeImage.View) (success refused : ℕ) (result : Fin 16) : Prop where
  yesFits : success + 6 ≤ image.size
  noFits : refused + 6 ≤ image.size
  yes : Code image success (X86Immediate32.code result 1)
  no : Code image refused (X86Immediate32.code result 0)

def clobbers (dst : P1Source.Reg) : Finset Register :=
  insert (key (X86BoundedLoad.physical dst)) MemoryBinding.registerWrites

theorem clobbers_data (dst : P1Source.Reg) : clobbers dst ⊆ dataRegisters := by
  intro r member
  rcases Finset.mem_insert.mp member with rfl | registers
  · exact data_key _
  · exact (by decide : MemoryBinding.registerWrites ⊆ dataRegisters) registers

private theorem return_clobbers (dst : P1Source.Reg) :
    MemoryBinding.registerWrites ∪ X86Immediate32.writes (X86BoundedLoad.physical dst) ⊆ clobbers dst := by
  intro r member
  rcases Finset.mem_union.mp member with prior | returned
  · exact Finset.mem_insert_of_mem prior
  · rcases Finset.mem_insert.mp returned with rfl | rip
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mp rip ▸ (by decide : Register.rip ∈ MemoryBinding.registerWrites))

universe u q
variable {σ : LPSignature.{u,u,q,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Fetched evaluation of the term tests for an eligible in-range
occurrence, followed by the exact word register result of MATCH. -/
theorem fetched_match (codes : PackedOccurrences.Codes (GroundTerm σ))
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
    (returns : Return image success refused (X86BoundedLoad.physical dst)) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps abstract,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers dst) bank.writes before after ∧
      executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      match MatchPlan.run (MatchPlan.observe term) (MatchPlan.compile pattern) table with
      | none => abstract = st.write dst 0 ∧ Nonempty (At image after base (refused + 6))
      | some following => ∃ bindings,
          abstract = (st.setLevel (level + 1) ((st.levels level).select role identity bindings)).write dst 1 ∧
          BindingSlots.Represents following bindings ∧
          bank.Represents codes following after ∧ Nonempty (At image after base (success + 6)) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨result, ranAbstract, refined⟩ :=
    PlannedPremise.executed codes st packed role pattern level index dst (identity, term) row table tableView
  simp only [PlannedPremise.planned, eligible, if_true] at refined
  obtain ⟨native, cost, ranNative, preparation, outcome⟩ :=
    NativeMatchPlan.fetch_plan other extra vector placed point controls ready
      (fun _ listed _ used => MatchPlan.demand_covers listed used) geometry
  cases verdict : MatchPlan.run (MatchPlan.observe term) (MatchPlan.compile pattern) table with
  | none =>
    rw [verdict] at refined outcome
    obtain ⟨atNo⟩ := outcome
    obtain ⟨after, fired, frame, bit, reached⟩ := X86PlacedScalar.rex_immediate
      (X86FrameLoad.linkedHandlers other) extra vector atNo returns.noFits _ 0 returns.no
    refine ⟨after, cost + 1, result, X86FuelPrefix.fetches_then cost 1 before native after ranNative fired,
      (preparation.trans (X86StateFrame.registerOnly frame)).mono (return_clobbers dst) (by simp),
      ranAbstract, ?_, refined, reached⟩
    simpa [refined, StoreInstructions.State.write, P1WordExecution.State.write] using bit
  | some following =>
    rw [verdict] at refined outcome
    obtain ⟨bindings, executed, represented⟩ := refined
    obtain ⟨next, ⟨atYes⟩⟩ := outcome
    obtain ⟨after, fired, frame, bit, reached⟩ := X86PlacedScalar.rex_immediate
      (X86FrameLoad.linkedHandlers other) extra vector atYes returns.yesFits _ 1 returns.yes
    have unchanged := X86StateFrame.registerOnly frame
    have surviving : bank.Represents codes following after := by
      intro name live
      obtain ⟨word, view⟩ := next.bindings name live
      exact ⟨word, ⟨view.bit.preserved unchanged (by simp), view.value.preserved unchanged (by simp), view.code⟩⟩
    refine ⟨after, cost + 1, result, X86FuelPrefix.fetches_then cost 1 before native after ranNative fired,
      (preparation.trans unchanged).mono (return_clobbers dst) (by simp),
      ranAbstract, ?_, bindings, executed, represented, surviving, reached⟩
    simpa [executed, StoreInstructions.State.setLevel, StoreInstructions.State.write, P1WordExecution.State.write] using bit

end Mettapedia.Machines.TIsa.StoreInstructions.NativePremise
