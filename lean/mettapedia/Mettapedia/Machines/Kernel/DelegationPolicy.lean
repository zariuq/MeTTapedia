import Mettapedia.Machines.Kernel.Delegation

/-!
# Additional policies for capability passing

A policy may restrict a pass admitted by the authority core. It cannot grant
authority that the core refuses, or disable cascading revocation. Stateful
trace erasure relates every policy run to an actual run of the original core.
Confinement therefore holds for every policy, without claiming that every
originally reachable authority remains reachable under a restrictive policy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.Delegation.Policy

variable {S O : Type} [DecidableEq S] [DecidableEq O]

abbrev Rule (S O : Type) := State S O → Cap S O → S → Bool → Bool

def allowed (rule : Rule S O) (st : State S O) : Op S O → Bool
  | .pass actor target grant recipient =>
      match source st actor target grant with
      | none => false
      | some cap => mayGrant st actor recipient && rule st cap recipient grant
  | .revoke _ _ => true

def step (rule : Rule S O) (st : State S O) (op : Op S O) : State S O :=
  if allowed rule st op then Delegation.step st op else st

def run (rule : Rule S O) (st : State S O) : List (Op S O) → State S O
  | [] => st
  | op :: rest => run rule (step rule st op) rest

def admittedTrace (rule : Rule S O) (st : State S O) : List (Op S O) → List (Op S O)
  | [] => []
  | op :: rest => if allowed rule st op then
      op :: admittedTrace rule (Delegation.step st op) rest
    else admittedTrace rule st rest

theorem run_is_core_run (rule : Rule S O) (st : State S O) (ops : List (Op S O)) :
    run rule st ops = Delegation.run st (admittedTrace rule st ops) := by
  induction ops generalizing st with
  | nil => rfl
  | cons op rest ih =>
      by_cases admissible : allowed rule st op = true
      · simpa [run, step, admittedTrace, admissible, Delegation.run] using
          ih (Delegation.step st op)
      · simpa [run, step, admittedTrace, admissible] using ih st

theorem confined (rule : Rule S O) (st : State S O) (ops : List (Op S O))
    {actor : S} {target : Target S O} {grant : Bool}
    (held : Holds (run rule st ops) actor target grant) : CanHold st actor target grant := by
  rw [run_is_core_run] at held
  exact holds_confined st _ held

theorem revocation_unchanged (rule : Rule S O) (st : State S O) (actor : S) (id : Nat) :
    step rule st (.revoke actor id) = Delegation.step st (.revoke actor id) := rfl

theorem failed_policy_preserves_state (rule : Rule S O) (st : State S O) (op : Op S O)
    (refused : allowed rule st op = false) : step rule st op = st := by
  simp [step, refused]

/-- Passing the object itself, including a use-only copy, requires its source
capability's grant right. Destination authority is still checked by the core. -/
def sourceGrant : Rule S O := fun _ cap _ _ => cap.grant

theorem use_only_not_passed (st : State S O) (actor recipient : S)
    (target : Target S O) (requested : Bool) (cap : Cap S O)
    (found : source st actor target requested = some cap) (useOnly : cap.grant = false) :
    step sourceGrant st (.pass actor target requested recipient) = st := by
  simp [step, allowed, sourceGrant, found, useOnly]

def exampleGenesis : State (Fin 3) (Fin 2) :=
  { caps := [⟨0, 0, .subj 1, true, []⟩, ⟨1, 0, .obj 0, false, []⟩,
      ⟨2, 0, .obj 1, true, []⟩, ⟨3, 1, .subj 2, true, []⟩]
    next := 4 }

def exampleRun : State (Fin 3) (Fin 2) :=
  run sourceGrant exampleGenesis [.pass 0 (.obj 0) false 1,
    .pass 0 (.obj 1) false 1, .pass 1 (.obj 1) false 2]

theorem example_use_copy_arrives : Holds exampleRun 1 (.obj 1) false := by
  exact ⟨⟨4, 1, .obj 1, false, [2]⟩, by decide, rfl, rfl, by simp⟩

theorem example_no_use_only_forward :
    ¬ Holds exampleRun 2 (.obj 1) false := by
  simp [Holds, exampleRun, run, step, allowed, sourceGrant, exampleGenesis,
    source, mayGrant, Delegation.step]

theorem example_policy_blocks_original_copy :
    (step sourceGrant exampleGenesis (.pass 0 (.obj 0) false 1)).next = 4 ∧
    (Delegation.step exampleGenesis (.pass 0 (.obj 0) false 1)).next = 5 := by decide

#print axioms run_is_core_run
#print axioms confined
#print axioms use_only_not_passed

end Mettapedia.Machines.Kernel.Delegation.Policy
