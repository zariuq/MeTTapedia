import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SplitPhaseRuns

/-!
# Private alternative worlds do not multiply a shared resource

Two private branches may each take their copy of one token. This is a valid
execution of isolated alternatives, not two consumptions in the shared world.
The existing split-phase model opens a private view on its first branch event;
it does not silently fork every branch at one earlier common call.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.BranchWorlds

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def label (_ : Nat) : Unit := ()
def takeToken : Commit Nat Unit := Commit.takeOne 0
def start : RunState Nat Unit := RunState.start {0}

theorem isolated_branches_both_take :
    RunValid label start [.branch 0 takeToken, .branch 1 takeToken] := by
  simp only [RunValid, Valid]
  decide

theorem shared_store_is_unchanged :
    (final start [.branch 0 takeToken, .branch 1 takeToken]).store = {0} := by decide

theorem both_private_stores_are_empty :
    let result := final start [.branch 0 takeToken, .branch 1 takeToken]
    result.branchStore 0 = ∅ ∧ result.branchStore 1 = ∅ := by decide

theorem shared_branches_cannot_both_take :
    ¬ RunValid label start [.fire takeToken, .fire takeToken] := by
  simp only [RunValid, Valid]
  decide

theorem private_histories_cannot_be_blindly_merged :
    ¬ Executable label {0} [takeToken, takeToken] := by
  rw [executable_cons_iff, executable_cons_iff]
  intro valid
  have live := valid.2.1.taken_subset
  have member := live (show 0 ∈ takeToken.taken by decide)
  simp [takeToken, fire, Commit.takeOne] at member

/-- Schedules and isolated alternatives are separated by a concrete linear
resource, without probabilities or a quantum interpretation. -/
theorem private_is_not_shared :
    RunValid label start [.branch 0 takeToken, .branch 1 takeToken] ∧
      ¬ RunValid label start [.fire takeToken, .fire takeToken] :=
  ⟨isolated_branches_both_take, shared_branches_cannot_both_take⟩

end Mettapedia.Machines.StoreInteraction.BranchWorlds
