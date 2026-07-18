import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AtomicResourceTryClaim

/-!
# Speculative occurrence-claim examples

These closed examples distinguish a successful exact claim from two failed
attempts.  In the contention case the first resource is individually
claimable, but failure on the second resource exposes the original state.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

namespace AtomicResourceTryClaimExamples

open SpeculativeOccurrenceClaims

inductive Transaction
  | alice
  | bob
  deriving DecidableEq

def empty : State Transaction (Fin 3) := ⟨fun _ => none⟩

def afterZero : State Transaction (Fin 3) :=
  ⟨Function.update empty.owner 0 (some .alice)⟩

def afterZeroAndTwo : State Transaction (Fin 3) :=
  ⟨Function.update afterZero.owner 2 (some .alice)⟩

def exactResources : List (Fin 3) := [0, 2]

theorem exact_acquisition_succeeds :
    acquireAll empty .alice exactResources = some afterZeroAndTwo := by
  rfl

theorem exact_attempt_commits :
    attempt empty .alice exactResources = .committed afterZeroAndTwo := by
  rfl

theorem exact_commit_owns_only_requested :
    afterZeroAndTwo.owner 0 = some .alice ∧
      afterZeroAndTwo.owner 1 = none ∧
      afterZeroAndTwo.owner 2 = some .alice := by
  decide

def contested : State Transaction (Fin 3) :=
  ⟨fun resource => if resource = 2 then some .bob else none⟩

def contestedAfterZero : State Transaction (Fin 3) :=
  ⟨Function.update contested.owner 0 (some .alice)⟩

theorem contended_prefix_is_individually_claimable :
    claimOne contested .alice 0 = some contestedAfterZero := by
  rfl

/-- Although resource zero can be claimed first, contention on resource two
rolls the whole public attempt back to `contested`. -/
theorem later_contention_rolls_back :
    attempt contested .alice exactResources = .contended contested := by
  rfl

theorem rollback_exposes_no_partial_owner :
    contested.owner 0 = none := by
  decide

/-- A duplicate request is not an admissible occurrence family: after the
first claim, the repeated occurrence conflicts with itself, and the public
attempt rolls back. -/
theorem duplicate_request_rolls_back :
    attempt empty .alice [0, 0] = .contended empty := by
  rfl

end AtomicResourceTryClaimExamples

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
