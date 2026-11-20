import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies

/-!
# A common token: exclusion, not a complete consistency or progress contract

The bound is derived from the existing round semantics and its no-double-take
theorem. It concerns one matched wave and one occurrence identity. Reissuing a
payload with a fresh occurrence enables another round, not another use of the
same occurrence. An unrelated writer need not respect this token.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.TokenPolicies

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O R : Type} [DecidableEq O]

theorem common_token_bounds_commits {label : O → R} {mode : Commit O R → Finset Check}
    {store final : Finset O} {proposals committed : List (Commit O R)} (token : O)
    (matched : MatchedAt store proposals)
    (checks : ∀ c ∈ proposals, Check.takes ∈ mode c)
    (common : ∀ c ∈ proposals, token ∈ c.taken)
    (round : Round label mode store proposals committed final) : committed.length ≤ 1 := by
  have pairwise := no_double_take matched checks round
  cases committed with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil => simp
    | cons second later =>
      have apart := (List.pairwise_cons.mp pairwise).1 second List.mem_cons_self
      have firstMem := round.sublist.subset (List.mem_cons_self : first ∈ first :: second :: later)
      have secondMem := round.sublist.subset
        (List.mem_cons_of_mem first (List.mem_cons_self : second ∈ second :: later))
      exact False.elim (Finset.disjoint_left.mp apart (common first firstMem) (common second secondMem))

namespace Controls

def label (o : Nat) : Nat := o
def left : Commit Nat Nat := ⟨{0}, ∅, {1}, []⟩
def right : Commit Nat Nat := ⟨{0}, ∅, {2}, []⟩

theorem left_can_win : Round label (fun _ => Mode.snapshot) {0} [left, right] [left] {1} := by
  refine .commit ?_ (.drop (.done _))
  simp only [Permits]
  decide

theorem right_can_win : Round label (fun _ => Mode.snapshot) {0} [right, left] [right] {2} := by
  refine .commit ?_ (.drop (.done _))
  simp only [Permits]
  decide

theorem token_does_not_determine_the_winner :
    fire {0} left ≠ fire {0} right := by decide

theorem exclusion_alone_promises_no_progress :
    Round label (fun _ => Mode.serializable) {0} [left, right] [] {0} :=
  .drop (.drop (.done _))

def depending : Commit Nat Nat := ⟨{0}, {3}, {1}, []⟩

/-- The candidate held a valid read when proposed. -/
theorem protected_candidate_initially_enabled : Enabled label {0, 3} depending := by decide

/-- Taking a token cannot protect another dependency from a writer which
does not participate in that token protocol. -/
theorem token_is_not_a_read_validation :
    Permits label Mode.snapshot (fire {0, 3} (Commit.takeOne 3 : Commit Nat Nat)) depending ∧
      ¬ Permits label Mode.claims (fire {0, 3} (Commit.takeOne 3 : Commit Nat Nat)) depending := by
  simp only [Permits]
  decide

end Controls

end Mettapedia.Machines.StoreInteraction.TokenPolicies
