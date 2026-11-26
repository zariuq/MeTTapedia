import Mettapedia.Machines.TIsa.StoreInstructions.MatchPlan
import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences

/-!
# An open pattern plan refines the store MATCH instruction

The position still identifies an occurrence, not a value. Eligibility
is separate from term matching. A successful plan determines exactly
the next level's bindings; a refusal leaves all levels unmodified.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PlannedPremise

open Mettapedia.Logic.LP
open Derivation (Role Match attempt)
open Derivation.FirstOrderTerms (Bindings extend matcher)
open BindingSlots (Table Represents)

universe u p
variable {σ : LPSignature.{u, u, p, u}} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

def planned (role : Role) (pattern : Term σ) (entry : Match (GroundTerm σ) (Bindings σ))
    (candidate : ℕ × GroundTerm σ) (table : Table σ) : Option (Table σ) :=
  if role.allows entry candidate.1 then MatchPlan.run (σ := σ) (MatchPlan.observe candidate.2) (MatchPlan.compile pattern) table
  else none

theorem executed (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ))
    {memory : PackedOccurrences.Layout} (packed : PackedOccurrences.pack codes st.store = some memory)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg)
    (candidate : ℕ × GroundTerm σ) (row : PackedOccurrences.at? codes memory (st.machine.registers index).toNat = some candidate)
    (table : Table σ) (represented : Represents (σ := σ) table (st.levels level).bindings) :
    ∃ after, executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .ok after ∧
      match planned (σ := σ) role pattern (st.levels level) candidate table with
      | none => after = st.write dst 0
      | some following => ∃ bindings,
          after = (st.setLevel (level + 1) ((st.levels level).select role candidate.1 bindings)).write dst 1 ∧
          Represents (σ := σ) following bindings := by
  rw [PackedOccurrences.at_exact codes packed] at row
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, row, attempt, planned]
  cases permitted : role.allows (st.levels level) candidate.1 with
  | false => exact ⟨st.write dst 0, rfl, rfl⟩
  | true =>
    have same := MatchPlan.run_accepts.{0, u, p} (σ := σ) represented pattern candidate.2
    cases native : MatchPlan.run (MatchPlan.observe candidate.2) (MatchPlan.compile pattern) table with
    | none =>
      have missed : extend (st.levels level).bindings pattern candidate.2 = none := by
        cases source : extend (st.levels level).bindings pattern candidate.2
        · rfl
        · rw [native, source] at same
          cases same
      simp only [if_true, matcher, missed, Option.map_none]
      exact ⟨st.write dst 0, rfl, rfl⟩
    | some following =>
      have accepted : (extend (st.levels level).bindings pattern candidate.2).isSome = true := by
        rw [← same, native]
        rfl
      obtain ⟨bindings, reference⟩ := Option.isSome_iff_exists.mp accepted
      simp only [if_true, matcher, reference, Option.map_some]
      let next := (st.setLevel (level + 1) ((st.levels level).select role candidate.1 bindings)).write dst 1
      exact ⟨next, rfl, bindings, rfl,
        MatchPlan.run_represents.{0, u, p} (σ := σ) represented pattern candidate.2 native reference⟩

theorem out_of_range_refuses (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ))
    {memory : PackedOccurrences.Layout} (packed : PackedOccurrences.pack codes st.store = some memory)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg)
    (missing : PackedOccurrences.at? codes memory (st.machine.registers index).toNat = none) :
    executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .error .invalidInput := by
  rw [PackedOccurrences.at_exact codes packed] at missing
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, missing]

theorem unavailable_occurrence_refuses (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ))
    {memory : PackedOccurrences.Layout} (packed : PackedOccurrences.pack codes st.store = some memory)
    (role : Role) (pattern : Term σ) (level : ℕ) (index dst : P1Source.Reg) (identity : ℕ) (term : GroundTerm σ)
    (row : PackedOccurrences.at? codes memory (st.machine.registers index).toNat = some (identity, term))
    (used : role.allows (st.levels level) identity = false) :
    executeInstruction (matcher (σ := σ)) st (.transform (.premise role pattern level index dst)) = .ok (st.write dst 0) := by
  rw [PackedOccurrences.at_exact codes packed] at row
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, row, attempt, used,
    Bool.false_eq_true, if_false]

end Mettapedia.Machines.TIsa.StoreInstructions.PlannedPremise
