import Mettapedia.Languages.MeTTa.CollapseSuperposeRoundTrip

/-!
# The frontier algebra: pending is absorbing, budgets only extend

Coverage is not a decoration on a run; it is an algebra, and the laws are
what make it safe to merge, bind, and resume searches without accidentally
promoting ignorance to knowledge.

Two clauses do the work.

**Pending is absorbing.**  A union of searches is finished only if every part
was, so combining anything with an unfinished search yields an unfinished
one.  With `exhausted` as the identity this makes `Completion` a bounded
semilattice, and it is why a merge can never repair a gap in one of its
operands.

**Budgets only extend.**  Raising a bound adds answers to the end and never
revises the ones already reported (`boundedObserve_values_monotone`), and a
run that already reported completion still reports it
(`boundedObserve_completeness_persists`).  Together these are the formal
content of "resumption extends the cone rather than rewriting it": a later,
larger observation is a *refinement* of an earlier one, never a
contradiction of it.

Coverage carries a reason in the outcome type and only its completion status
is algebraic, so the connection is stated as a homomorphism
(`completionOf_merge`) rather than by conflating the two.
-/

namespace Mettapedia.Languages.MeTTa.Frontier

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.RoundTrip

/-! ## The semilattice -/

/-- Whether a run's frontier is closed.  The algebraic residue of coverage,
with the reason forgotten. -/
inductive Completion where
  /-- The search finished. -/
  | exhausted
  /-- The search did not. -/
  | pending
deriving DecidableEq, Repr

namespace Completion

/-- Combining runs.  Finished only if both were. -/
def merge : Completion → Completion → Completion
  | .exhausted, .exhausted => .exhausted
  | _, _ => .pending

@[simp] theorem merge_comm (left right : Completion) :
    merge left right = merge right left := by
  cases left <;> cases right <;> rfl

theorem merge_assoc (first second third : Completion) :
    merge (merge first second) third = merge first (merge second third) := by
  cases first <;> cases second <;> cases third <;> rfl

@[simp] theorem merge_idem (completion : Completion) :
    merge completion completion = completion := by
  cases completion <;> rfl

@[simp] theorem merge_exhausted_left (completion : Completion) :
    merge .exhausted completion = completion := by
  cases completion <;> rfl

@[simp] theorem merge_exhausted_right (completion : Completion) :
    merge completion .exhausted = completion := by
  cases completion <;> rfl

/-- **Pending is absorbing.**  Nothing repairs an unfinished search by
merging something else into it — which is exactly why a combined result may
never be reported as complete on the strength of one complete operand. -/
@[simp] theorem merge_pending_left (completion : Completion) :
    merge .pending completion = .pending := by
  cases completion <;> rfl

@[simp] theorem merge_pending_right (completion : Completion) :
    merge completion .pending = .pending := by
  cases completion <;> rfl

/-- A merge is exhausted exactly when both parts were. -/
theorem merge_eq_exhausted_iff {left right : Completion} :
    merge left right = .exhausted ↔ left = .exhausted ∧ right = .exhausted := by
  cases left <;> cases right <;> simp [merge]

/-- Information order: an exhausted run knows at least as much as a pending
one about what is absent. -/
def Below : Completion → Completion → Prop
  | .exhausted, _ => True
  | .pending, .pending => True
  | .pending, .exhausted => False

theorem below_refl (completion : Completion) : Below completion completion := by
  cases completion <;> trivial

theorem below_merge_left (left right : Completion) :
    Below left (merge left right) := by
  cases left <;> cases right <;> trivial

end Completion

/-! ## Coverage projects onto it -/

/-- Forget the reason. -/
def completionOf : Coverage → Completion
  | .complete => .exhausted
  | .incomplete _ => .pending

/-- Merging coverage: complete only if both were, and otherwise reporting a
reason from an unfinished part. -/
def mergeCoverage : Coverage → Coverage → Coverage
  | .complete, .complete => .complete
  | .incomplete reason, _ => .incomplete reason
  | .complete, .incomplete reason => .incomplete reason

/-- **Observation is a frontier homomorphism.**  Merging coverage and then
forgetting the reason agrees with forgetting first and merging in the
semilattice, so the algebra above governs real reports. -/
theorem completionOf_merge (left right : Coverage) :
    completionOf (mergeCoverage left right) =
      Completion.merge (completionOf left) (completionOf right) := by
  cases left <;> cases right <;> rfl

/-- A merged report claims completeness only when both parts did. -/
theorem mergeCoverage_complete_iff {left right : Coverage} :
    mergeCoverage left right = .complete ↔
      left = .complete ∧ right = .complete := by
  cases left <;> cases right <;> simp [mergeCoverage]

/-! ## Budgets only extend

A larger bound refines an earlier observation.  It adds answers at the end
and never revises the ones already given, and it cannot retract a completion
that was already claimed. -/

private theorem take_prefix_take {α : Type _} {small large : Nat}
    (grows : small ≤ large) (list : List α) :
    (list.take small).IsPrefix (list.take large) := by
  have restated : list.take small = (list.take large).take small := by
    rw [List.take_take, Nat.min_eq_left grows]
  rw [restated]
  exact List.take_prefix small (list.take large)

/-- **Raising the bound extends the answers.**  Everything already reported
stays reported, in the same order; new answers can only appear after them. -/
theorem boundedObserve_values_monotone {small large : Nat} (grows : small ≤ large)
    (outcome : Outcome) :
    ((boundedObserve small outcome).values).IsPrefix
      ((boundedObserve large outcome).values) :=
  take_prefix_take grows outcome.values

/-- **Raising the bound cannot retract a completion.**  A run that already
reported that it finished still reports it. -/
theorem boundedObserve_completeness_persists {small large : Nat}
    (grows : small ≤ large) (outcome : Outcome)
    (claimed : (boundedObserve small outcome).coverage = .complete) :
    (boundedObserve large outcome).coverage = .complete := by
  by_cases withinSmall : outcome.values.length ≤ small
  · have withinLarge : outcome.values.length ≤ large := Nat.le_trans withinSmall grows
    simp only [boundedObserve, withinSmall, if_true] at claimed
    simp [boundedObserve, withinLarge, claimed]
  · simp [boundedObserve, withinSmall] at claimed

/-- **Resumption refines, never rewrites.**  Both halves together: a larger
observation extends the earlier answers and preserves any completion the
earlier one claimed.  This is what licenses resuming a search instead of
re-running it. -/
theorem resumption_refines {small large : Nat} (grows : small ≤ large)
    (outcome : Outcome) :
    ((boundedObserve small outcome).values).IsPrefix
        ((boundedObserve large outcome).values) ∧
      ((boundedObserve small outcome).coverage = .complete →
        (boundedObserve large outcome).coverage = .complete) :=
  ⟨boundedObserve_values_monotone grows outcome,
    boundedObserve_completeness_persists grows outcome⟩

/-! ## Absorbing is forced, not chosen

The laws above are true of the merge defined here.  The stronger question is
whether any *other* merge could have been chosen, and the answer is no: a
merging rule that ever reports a combined run as finished when one part was
not is unsound, on a two-line counterexample.  Absorbing is therefore a
consequence of what `exhausted` means, not a design preference. -/

/-- A rule for merging completion claims is **sound** when a combined claim of
exhaustion really implies the combined report was exhaustive.  The parts are
assumed sound in the same sense; nothing else is assumed about them. -/
def SoundMerge (rule : Completion → Completion → Completion) : Prop :=
  ∀ (leftScope rightScope leftFound rightFound : List Datum)
    (leftClaim rightClaim : Completion),
    (leftClaim = .exhausted → leftFound = leftScope) →
    (rightClaim = .exhausted → rightFound = rightScope) →
    rule leftClaim rightClaim = .exhausted →
      leftFound ++ rightFound = leftScope ++ rightScope

/-- **Any sound merging rule is absorbing on the left.**  If an unfinished
search could be completed by merging, then a search that missed an answer
would report exhaustion — so the gap must propagate. -/
theorem soundMerge_absorbs_left {rule : Completion → Completion → Completion}
    (sound : SoundMerge rule) (claim : Completion) :
    rule .pending claim = .pending := by
  cases result : rule .pending claim with
  | pending => rfl
  | exhausted =>
      have contradiction' :=
        sound [.unit] [] [] [] .pending claim
          (by intro impossible; cases impossible)
          (by intro _; rfl) result
      simp at contradiction'

/-- and on the right, by the same witness. -/
theorem soundMerge_absorbs_right {rule : Completion → Completion → Completion}
    (sound : SoundMerge rule) (claim : Completion) :
    rule claim .pending = .pending := by
  cases result : rule claim .pending with
  | pending => rfl
  | exhausted =>
      have contradiction' :=
        sound [] [.unit] [] [] claim .pending
          (by intro _; rfl)
          (by intro impossible; cases impossible) result
      simp at contradiction'

/-- The merge defined above is sound, so the forcing theorem is not vacuous. -/
theorem merge_sound : SoundMerge Completion.merge := by
  intro leftScope rightScope leftFound rightFound leftClaim rightClaim
    leftSound rightSound exhausted
  obtain ⟨leftExhausted, rightExhausted⟩ :=
    Completion.merge_eq_exhausted_iff.mp exhausted
  rw [leftSound leftExhausted, rightSound rightExhausted]

/-- **The characterization.**  A sound merging rule agrees with the
semilattice merge wherever either part is unfinished — there was never a
choice to make. -/
theorem soundMerge_agrees_on_pending {rule : Completion → Completion → Completion}
    (sound : SoundMerge rule) (claim : Completion) :
    rule .pending claim = Completion.merge .pending claim ∧
      rule claim .pending = Completion.merge claim .pending := by
  refine ⟨?_, ?_⟩
  · rw [soundMerge_absorbs_left sound claim, Completion.merge_pending_left]
  · rw [soundMerge_absorbs_right sound claim, Completion.merge_pending_right]

/-- The bottom of the information order: nothing found, nothing finished.
Every observation refines it, and it licenses no conclusion at all. -/
def leastInformative : Outcome := ⟨[], .incomplete "unstarted", []⟩

theorem leastInformative_is_pending :
    completionOf leastInformative.coverage = .pending := rfl

end Mettapedia.Languages.MeTTa.Frontier
