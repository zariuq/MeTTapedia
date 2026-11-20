import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgramRuns

/-!
# No infinite value administration in the compiled program

Every nonterminal step of an initialized value episode is an actual worker
step and lowers its potential. Its only additional outgoing step is the
actual finish clause, whose done endpoint admits no further program rewrite.
Thus the containing program adds no infinite administrative value episode.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank

open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

theorem compiled_accessible {dev : Definitions.Development} (built : Compiled dev)
    (original : MClosed) (cursor : Cursor) (invariant : ValueWorker.Invariant original cursor.view) :
    Acc (fun after before => ProgramBinders.Rewrites built.rules.get before after) cursor.view := by
  have all : ∀ bound : Nat, ∀ cursor : Cursor, cursor.potential = bound →
      ValueWorker.Invariant original cursor.view →
      Acc (fun after before => ProgramBinders.Rewrites built.rules.get before after) cursor.view := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound smaller =>
        intro cursor atBound before
        refine .intro cursor.view ?_
        intro next edge
        rcases ValueWorker.program_step_cases built before edge with worker | finished
        · obtain ⟨after, rfl, lower⟩ := advance cursor worker
          exact smaller after.potential (atBound ▸ lower) after rfl
            (ValueWorker.step_preserves worker before)
        · obtain ⟨datum, _, rfl⟩ := finished
          exact .intro _ (fun later step => False.elim (ValueWorker.no_step_at_done built datum later step))
  exact all cursor.potential cursor rfl invariant

theorem compiled_initialized_normalizes {dev : Definitions.Development} (built : Compiled dev)
    (datum : MClosed) :
    Acc (fun after before => ProgramBinders.Rewrites built.rules.get before after)
      (valueC datum finishContinuation) :=
  compiled_accessible built datum (.checking datum .base) (ValueWorker.initialized datum)

theorem compiled_normalizes_of_invariant {dev : Definitions.Development} (built : Compiled dev)
    {original current : MClosed} (invariant : ValueWorker.Invariant original current) :
    Acc (fun after before => ProgramBinders.Rewrites built.rules.get before after) current := by
  rcases invariant with checking | returning
  · obtain ⟨datum, stack, rfl, valid, restored⟩ := checking
    exact compiled_accessible built original (.checking datum stack)
      (.inl ⟨datum, stack, rfl, valid, restored⟩)
  · obtain ⟨datum, stack, isValue, rfl, valid, restored⟩ := returning
    exact compiled_accessible built original (.returning (encodeTm datum) stack)
      (.inr ⟨datum, stack, isValue, rfl, valid, restored⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank.compiled_initialized_normalizes
