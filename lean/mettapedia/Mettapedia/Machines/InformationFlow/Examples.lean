import Mettapedia.Machines.InformationFlow.CheckErasure
import Mettapedia.Logic.InformationFlow.Label

/-!
# Information-flow controls for private queries and untrusted inputs

The examples use synthetic natural numbers. They exercise the executable monitor,
its independent unchecked semantics, and static check erasure. Confidentiality
and integrity use the same flow order, with integrity reversed. Blocking an
untrusted output here is a theorem about this mediated interface; it is not a
claim to solve unrestricted prompt injection or foreign-function isolation.
-/

namespace Mettapedia.Machines.InformationFlow.FloatingLabel.Examples

local instance : SemilatticeSup Bool := Bool.instDistribLattice.toLattice.toSemilatticeSup
local instance : SemilatticeInf Bool := Bool.instDistribLattice.toLattice.toSemilatticeInf
local instance : OrderBot Bool := Bool.instBoundedOrder.toOrderBot

private theorem true_not_le_false : ¬ (true ≤ false) := by decide

/-- Space zero is public; every other space is private. -/
def medicalPolicy (space : Nat) : Bool := space != 0

def medicalState (records : List Nat) : State Bool :=
  ⟨false, [], fun space => if space = 1 then records else [], []⟩

def privateCount : Command Bool :=
  .seq (.primitive (.query 1 (fun _ => true)))
    (.seq (.primitive .count) (.primitive (.emit false)))

def privateBranchWrite : Command Bool :=
  .seq (.primitive (.query 1 (fun _ => true)))
    (.ifEmpty .skip
      (.seq (.primitive (.literal [1])) (.primitive (.write 0))))

def privateCopy : Command Bool :=
  .seq (.primitive (.query 1 (fun _ => true)))
    (.seq (.primitive (.write 2)) (.primitive (.emit true)))

def publicComputation : Command Bool :=
  .seq (.primitive (.literal [42]))
    (.seq (.primitive (.write 0)) (.primitive (.emit false)))

theorem medicalState_lowEquivalent (left right : List Nat) :
    LowEquivalent medicalPolicy false (medicalState left) (medicalState right) := by
  refine ⟨⟨?_, rfl⟩, Iff.rfl, fun _ => rfl, fun _ => rfl⟩
  intro space visible
  by_cases isPrivate : space = 1
  · subst space
    simp [medicalPolicy, true_not_le_false] at visible
  · simp [medicalState, isPrivate]

/-- Even an empty private query raises the current label before the count is used. -/
theorem privateCount_no_public_output (records : List Nat) :
    (run medicalPolicy privateCount (medicalState records)).trace = [] := by
  simp [privateCount, run, step, medicalPolicy, medicalState, true_not_le_false]

theorem unchecked_count_releases_cardinality (records : List Nat) :
    (uncheckedRun privateCount (erase (medicalState records))).trace =
      [(false, [records.length])] := by
  simp [privateCount, uncheckedRun, uncheckedStep, erase, medicalState]

/-- Equal payload labels would not stop a write controlled by a private query. -/
theorem privateBranchWrite_preserves_public_space (records : List Nat) :
    (run medicalPolicy privateBranchWrite (medicalState records)).store 0 = [] := by
  by_cases empty : records = [] <;>
    simp [privateBranchWrite, run, step, medicalPolicy, medicalState, true_not_le_false, empty]

theorem unchecked_branch_leaks_existence :
    (uncheckedRun privateBranchWrite (erase (medicalState []))).store 0 ≠
      (uncheckedRun privateBranchWrite (erase (medicalState [7]))).store 0 := by
  decide

theorem privateCopy_retains_private_data (records : List Nat) :
    (run medicalPolicy privateCopy (medicalState records)).store 2 = records ∧
      (run medicalPolicy privateCopy (medicalState records)).trace = [(true, records)] := by
  simp [privateCopy, run, step, medicalPolicy, medicalState]

theorem publicComputation_has_observable_effects (records : List Nat) :
    (run medicalPolicy publicComputation (medicalState records)).store 0 = [42] ∧
      (run medicalPolicy publicComputation (medicalState records)).trace = [(false, [42])] := by
  simp [publicComputation, run, step, medicalPolicy, medicalState]

theorem privateCopy_wellTyped : WellTyped medicalPolicy true privateCopy := by
  refine .seq _ _ _ (.primitive _ _ (.query _ _)) ?_
  refine .seq _ _ _ (.primitive _ _ (.write _ ?_)) (.primitive _ _ (.emit _ ?_))
  all_goals decide

theorem privateCopy_checks_erase (records : List Nat) :
    erase (run medicalPolicy privateCopy (medicalState records)) =
      uncheckedRun privateCopy (erase (medicalState records)) :=
  run_check_erasure privateCopy_wellTyped _ (by change false ≤ true; decide)

/-- The static checker rejects the cardinality release that the monitor blocks. -/
theorem privateCount_not_wellTyped : ¬ WellTyped medicalPolicy false privateCount := by
  intro typed
  have erased := run_check_erasure typed (medicalState [7]) (by decide)
  have traceEquality := congrArg RawState.trace erased
  change (run medicalPolicy privateCount (medicalState [7])).trace = _ at traceEquality
  rw [privateCount_no_public_output, unchecked_count_releases_cardinality] at traceEquality
  contradiction

/-- The first component orders secrecy; the second orders trust in reverse. -/
abbrev SecurityLabel := Bool × OrderDual Bool

def publicTrusted : SecurityLabel := (false, OrderDual.toDual true)
def publicUntrusted : SecurityLabel := (false, OrderDual.toDual false)

def agentPolicy (space : Nat) : SecurityLabel :=
  if space = 1 then publicUntrusted else publicTrusted

def agentState (input : List Nat) : State SecurityLabel :=
  ⟨publicTrusted, [], fun space => if space = 1 then input else [], []⟩

def forwardToPrivilegedTool : Command SecurityLabel :=
  .seq (.primitive (.query 1 (fun _ => true))) (.primitive (.emit publicTrusted))

theorem untrusted_input_cannot_drive_privileged_output (input : List Nat) :
    (run agentPolicy forwardToPrivilegedTool (agentState input)).trace = [] := by
  simp [forwardToPrivilegedTool, run, step, agentPolicy, agentState,
    publicTrusted, publicUntrusted, true_not_le_false]

theorem unchecked_input_drives_privileged_output (input : List Nat) :
    (uncheckedRun forwardToPrivilegedTool (erase (agentState input))).trace =
      [(publicTrusted, input)] := by
  simp [forwardToPrivilegedTool, uncheckedRun, uncheckedStep, erase, agentState]

theorem trusted_computation_can_call_privileged_tool :
    (run agentPolicy
      (.seq (.primitive (.literal [42])) (.primitive (.emit publicTrusted)))
      (agentState [])).trace = [(publicTrusted, [42])] := by
  simp [run, step, agentState]

/-- Captured secrets must label generated code. Checking two closed programs
separately does not establish a relation between their choice of constants. -/
def generatedCommand (secret : Bool) : Command Bool :=
  .seq (.primitive (.literal [if secret then 1 else 0])) (.primitive (.emit false))

theorem generatedCommand_individually_wellTyped (secret : Bool) :
    WellTyped medicalPolicy false (generatedCommand secret) := by
  refine .seq _ _ _ (.primitive _ _ (.literal _)) (.primitive _ _ (.emit _ ?_))
  change false ≤ false
  exact le_rfl

theorem secret_dependent_code_choice_leaks :
    (run medicalPolicy (generatedCommand false) (medicalState [])).trace ≠
      (run medicalPolicy (generatedCommand true) (medicalState [])).trace := by
  decide

end Mettapedia.Machines.InformationFlow.FloatingLabel.Examples
