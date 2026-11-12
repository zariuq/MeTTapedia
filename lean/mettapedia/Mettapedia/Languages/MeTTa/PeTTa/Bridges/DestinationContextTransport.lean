import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextSurface

/-!
# Complete owned source execution commutes with context transport

The proofs compose the actual local, collection, primitive and surface
operations. No equality of source executions is supplied as an assumption.
Published packets retain their complete order, records and occurrence tags;
every outcome carrying a state retains the transported reached state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination

variable {A B : Type}

theorem base_step (map : A → B) (policy : Policy) (program : SpaceSemantics.Program) (source : ScopedCursor A) :
    ScopedQuerySource.step policy program (state map source) =
      action map (ScopedQuerySource.step policy program source) := by
  unfold ScopedQuerySource.step
  rw [syntax_step]
  cases expanded : ScopedQuerySource.syntaxStep source with
  | some next => rfl
  | none =>
      simp only [Option.map_none]
      rw [constrained_call]
      cases constrained : ScopedQuerySource.constrainedCall source with
      | some next => rfl
      | none =>
          simp only [Option.map_none]
          rw [mutation_call]
          cases mutation : ScopedQuerySource.mutationCall source with
          | some next => rfl
          | none =>
              simp only [Option.map_none]
              rw [query_step]
              cases query : ScopedQuerySource.queryStep source with
              | some next => rfl
              | none =>
                  simp only [Option.map_none]
                  exact scope_step map policy program source

theorem owned_step (map : A → B) (policy : Policy) (program : SpaceSemantics.Program) (source : ScopedCursor A) :
    ScopedQuerySource.ownedStep policy program (state map source) =
      action map (ScopedQuerySource.ownedStep policy program source) := by
  unfold ScopedQuerySource.ownedStep
  rw [case_entry]
  cases entry : ScopedCaseSource.entryStep source with
  | some next => rfl
  | none =>
      simp only [Option.map_none]
      rw [case_ready]
      cases ready : ScopedCaseSource.readyStep ScopedQuerySource.plainQueryPattern source with
      | some next => rfl
      | none =>
          simp only [Option.map_none]
          rw [ownership_step]
          cases ownership : ScopedQuerySource.ownershipStep program source with
          | some next => rfl
          | none =>
              simp only [Option.map_none]
              rw [base_step]
              cases ordinary : ScopedQuerySource.step policy program source with
              | silent next | publish events next | finish next | fail events => rfl
              | call request retained =>
                  cases request with
                  | allocation | associatedWork | invalidScope | fault reason => rfl
                  | branch request =>
                      cases request with
                      | invalidEnvironment | invalidDelimiter callerDepth available | openCommit | commit retained => rfl
                      | query location pattern template destination => rfl
                      | invoke head arguments destination =>
                          rcases retained with ⟨retainedAllocator, retainedConfiguration⟩
                          simp only [action, unifying_query_step]
                          simp only [state]
                          by_cases named : head = "match"
                          · subst head
                            cases arguments with
                            | nil => rfl
                            | cons first rest =>
                                cases rest with
                                | nil => rfl
                                | cons second rest =>
                                    cases rest with
                                    | nil => rfl
                                    | cons third rest =>
                                        cases rest with
                                        | cons fourth rest => rfl
                                        | nil => cases served : ScopedQuerySource.unifyingQueryStep source <;> rfl
                          · cases served : ScopedQuerySource.unifyingQueryStep source <;>
                              simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
                            all_goals repeat' first
                              | rfl
                              | (split <;> try simp_all)

def outcome (map : A → B) :
    Outcome (ScopedCursor A) (ScopedCursor A) ScopeBoundary →
    Outcome (ScopedCursor B) (ScopedCursor B) ScopeBoundary
  | .finished final => .finished (state map final)
  | .suspended request retained => .suspended request (state map retained)
  | .stuck retained => .stuck (state map retained)
  | .exhausted retained => .exhausted (state map retained)
  | .faulted => .faulted

theorem owned_run (map : A → B) (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor A) :
    (ScopedQuerySource.ownedMachine policy program).run fuel (state map source) =
      let result := (ScopedQuerySource.ownedMachine policy program).run fuel source
      (result.1, outcome map result.2) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      simp only [Machine.run, ScopedQuerySource.ownedMachine, owned_step]
      cases advanced : ScopedQuerySource.ownedStep policy program source with
      | silent next => simpa only [advanced, action, ScopedQuerySource.ownedMachine] using ih next
      | publish events next =>
          simpa only [advanced, action, ScopedQuerySource.ownedMachine] using congrArg
            (fun result : List CollectedAnswer × Outcome (ScopedCursor B) (ScopedCursor B) ScopeBoundary =>
              (events ++ result.1, result.2)) (ih next)
      | finish final | call request retained | fail events => rfl

/-- Equality preserves and reflects the full ordered occurrence prefix, not
just value membership or successful termination. -/
theorem owned_run_packets (map : A → B) (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor A) :
    ((ScopedQuerySource.ownedMachine policy program).run fuel (state map source)).1 =
      ((ScopedQuerySource.ownedMachine policy program).run fuel source).1 :=
  congrArg Prod.fst (owned_run map policy program fuel source)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap
