import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellCorrespondence
import Mettapedia.Machines.TIsa.Fuel

/-!
# Occurrence, authority and budget controls for the cell bridge

Duplicate edge ordinals are distinct firings even when they have identical
cell results. The finite resource observation forgets values outside its
declared keys. The existing native fuel predicate may be exhausted at either
an admitted or a refused call; exhaustion alone decides neither.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellControls

open Mettapedia.Machines.TIsa Cells CellEffects Control
open CellOccurrences
open CheckedCells.Controls (edge keys initial proposal badProposal)

def state : State Nat := CellCorrespondence.Controls.state
def first : Firing [edge, edge] := ⟨⟨0, by decide⟩, proposal⟩
def second : Firing [edge, edge] := ⟨⟨1, by decide⟩, proposal⟩

theorem first_admitted : (step [edge, edge]).Admits (s := state) first := by
  change CheckedAdmission.eligible first.edge state.keys state.values first.candidate
  decide

theorem second_admitted : (step [edge, edge]).Admits (s := state) second := by
  change CheckedAdmission.eligible second.edge state.keys state.values second.candidate
  decide

theorem distinct_firings : first ≠ second := by
  intro same
  have ordinals := congrArg (fun firing : Firing [edge, edge] => firing.ordinal.val) same
  change 0 = 1 at ordinals
  omega

theorem duplicate_origins_same_result :
    first ≠ second ∧ (step [edge, edge]).result first first_admitted =
      (step [edge, edge]).result second second_admitted := ⟨distinct_firings, rfl⟩

def firstRun : (step [edge, edge]).Run state := .cons first first_admitted (.nil _)
def secondRun : (step [edge, edge]).Run state := .cons second second_admitted (.nil _)

/-- The exact interface run retains the duplicate source ordinal, while
its endpoint observation alone cannot recover which copy fired. -/
theorem run_origins_not_recoverable_from_result :
    firstRun.last = secondRun.last ∧ firstRun ≠ secondRun := by
  refine ⟨rfl, ?_⟩
  intro same
  have words := congrArg (fun run : (step [edge, edge]).Run state => run.word) same
  have firings := (List.cons.inj words).1
  exact distinct_firings (eq_of_heq (Sigma.mk.inj firings).2)

def hiddenChange : Location Nat → Word := Function.update initial (.inr 2) 42

theorem same_declared_cells_different_hidden_value :
    encode keys initial = encode keys hiddenChange ∧ initial ≠ hiddenChange := by
  constructor
  · apply encode_congr
    intro key member
    have different : key ≠ (.inr 2 : Location Nat) := by
      rintro rfl
      exact (by decide : (.inr 2 : Location Nat) ∉ keys) member
    simp [hiddenChange, different]
  · intro equal
    have values := congrFun equal (.inr 2)
    change (7#64) = Function.update initial (.inr 2) (42#64) (.inr 2) at values
    simp only [Function.update_self] at values
    exact (by decide : (7#64) ≠ (42#64)) values

theorem exhausted_at_admitted_call :
    fuelAvailable (1#64) (1#64) = false ∧
      CheckedAdmission.step? [edge] 0 keys initial proposal =
        some (CheckedAdmission.commit edge initial proposal) := ⟨rfl, rfl⟩

theorem exhausted_at_refused_call :
    fuelAvailable (1#64) (1#64) = false ∧
      CheckedAdmission.step? [edge] 0 keys initial badProposal = none := ⟨rfl, rfl⟩

/-- In the existing native fuel convention zero means unlimited, whereas a
positive consumed allowance means exhausted. Neither means a false guard. -/
theorem zero_allowance_is_unlimited :
    fuelAvailable (0#64) (1#64) = true ∧ fuelAvailable (1#64) (1#64) = false := ⟨rfl, rfl⟩

def aliasedOutputs : Edge Nat := { edge with effect := {
  inputs := []
  outputs := [0, 0]
  guard := fun _ results => match results with
    | [first, second] => first == 7 && second == 8
    | _ => false } }

/-- Repeated output positions refer to one cell. A proposal cannot give
that same cell two inconsistent words to satisfy a guard. -/
theorem inconsistent_aliased_outputs_refused (candidate : Nat → Word) :
    CheckedAdmission.step? [aliasedOutputs] 0 keys initial candidate = none := by
  have impossible : ¬ CheckedAdmission.eligible aliasedOutputs keys initial candidate := by
    rintro ⟨_, _, guard⟩
    have values : candidate 0 = (7#64) ∧ candidate 0 = (8#64) := by
      simpa [aliasedOutputs] using guard
    exact (by decide : (7#64) ≠ (8#64)) (values.1.symm.trans values.2)
  simp [CheckedAdmission.step?, impossible]

def repeatedInput : Edge Nat := { edge with effect := {
  inputs := [0, 0]
  outputs := []
  guard := fun arguments results => match arguments, results with
    | [first, second], [] => first == second
    | _, _ => false } }

def repeatedFiring : Firing [repeatedInput] := ⟨⟨0, by decide⟩, proposal⟩

/-- Repeated read ports share the same physical occurrence, while the
guard still receives every declared argument position. -/
theorem repeated_reads_share_occurrence :
    (step [repeatedInput]).Admits (s := state) repeatedFiring ∧
      (selection state repeatedFiring).read = [((.inr 0, 0) : Occurrence Nat)] := by
  constructor
  · change CheckedAdmission.eligible repeatedFiring.edge state.keys state.values repeatedFiring.candidate
    decide
  · decide

#print axioms duplicate_origins_same_result
#print axioms run_origins_not_recoverable_from_result
#print axioms same_declared_cells_different_hidden_value
#print axioms exhausted_at_admitted_call
#print axioms exhausted_at_refused_call
#print axioms inconsistent_aliased_outputs_refused
#print axioms repeated_reads_share_occurrence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellControls
