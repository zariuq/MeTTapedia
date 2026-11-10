import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.AtomicFusion
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication.RevisionValidation

/-!
# Reusing preparation at the store publication boundary

The sufficient condition is agreement on the prepared effect's dependencies,
not equality of whole stores and not merely disjoint taken sets. A checked
publication and a direct publication agree under that condition. Executable
batches admit a check-free fold; the existing independence and fusion results
supply concrete ways to establish its premises.

No statement here turns an epoch read into a concurrent atomic operation.
The before/after states are observations at the serialized publication boundary.
Callbacks, freshness, permissions or other facts not represented by the occurrence
effect need their own stability evidence in a richer adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.ValidationReuse

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v
variable {O : Type u} {R : Type v}

/-- Facts used by this effect have not changed. The rest of the store may change. -/
structure Agreement (label : O → R) (before after : Finset O) (effect : Commit O R) : Prop where
  taken : ∀ o ∈ effect.taken, o ∈ before ↔ o ∈ after
  kept : ∀ o ∈ effect.kept, o ∈ before ↔ o ∈ after
  made : ∀ o ∈ effect.made, o ∈ before ↔ o ∈ after
  queries : ∀ query ∈ effect.queries,
    regionOf label before query.region = regionOf label after query.region

theorem Agreement.refl (label : O → R) (store : Finset O) (effect : Commit O R) :
    Agreement label store store effect :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem Agreement.symm {label : O → R} {before after : Finset O} {effect : Commit O R}
    (agree : Agreement label before after effect) : Agreement label after before effect :=
  ⟨fun o member => (agree.taken o member).symm,
   fun o member => (agree.kept o member).symm,
   fun o member => (agree.made o member).symm,
   fun query member => (agree.queries query member).symm⟩

theorem Agreement.preserves_enabled {label : O → R} {before after : Finset O}
    {effect : Commit O R} (agree : Agreement label before after effect)
    (enabled : Enabled label before effect) : Enabled label after effect := by
  refine ⟨?_, ?_, enabled.apart, ?_, ?_⟩
  · intro o member
    exact (agree.taken o member).mp (enabled.taken_subset member)
  · intro o member
    exact (agree.kept o member).mp (enabled.kept_subset member)
  · apply Finset.disjoint_left.mpr
    intro o made present
    exact Finset.disjoint_left.mp enabled.fresh made ((agree.made o made).mpr present)
  · intro query member
    change regionOf label after query.region = query.seen
    rw [← agree.queries query member]
    exact enabled.queries_hold query member

theorem Agreement.enabled_iff {label : O → R} {before after : Finset O}
    {effect : Commit O R} (agree : Agreement label before after effect) :
    Enabled label before effect ↔ Enabled label after effect :=
  ⟨agree.preserves_enabled, agree.symm.preserves_enabled⟩

variable [DecidableEq O]

/-- A refusal returns the current store, including effects preceding this attempt. -/
def checked (label : O → R) (store : Finset O) (effect : Commit O R) : Bool × Finset O :=
  if Enabled label store effect then (true, fire store effect) else (false, store)

theorem checked_refusal {label : O → R} {store : Finset O} {effect : Commit O R}
    (refused : ¬ Enabled label store effect) : checked label store effect = (false, store) := by
  simp [checked, refused]

/-- The direct application is licensed by established observations, without a second match. -/
theorem direct_after_preparation {label : O → R} {before after : Finset O}
    {effect : Commit O R} (prepared : Enabled label before effect)
    (agree : Agreement label before after effect) :
    checked label after effect = (true, fire after effect) := by
  simp [checked, agree.preserves_enabled prepared]

theorem direct_in_stable_interval {label : O → R} {before after : Finset O}
    {effect : Commit O R} (prepared : Enabled label before effect) (stable : after = before) :
    checked label after effect = (true, fire after effect) := by
  subst after
  exact direct_after_preparation prepared (Agreement.refl _ _ _)

/-- A sequence stops at refusal and retains the already reached store. -/
def checkedRun (label : O → R) : Finset O → List (Commit O R) → Bool × Finset O
  | store, [] => (true, store)
  | store, effect :: rest =>
      if Enabled label store effect then checkedRun label (fire store effect) rest
      else (false, store)

/-- An independently established executable history needs only its effect fold. -/
theorem checkedRun_direct {label : O → R} {store : Finset O} {effects : List (Commit O R)}
    (executable : Executable label store effects) :
    checkedRun label store effects = (true, fireList store effects) := by
  induction executable with
  | nil store => rfl
  | cons enabled after ih => simp [checkedRun, enabled, ih]

theorem checkedRun_complete_iff (label : O → R) (store : Finset O)
    (effects : List (Commit O R)) :
    (checkedRun label store effects).1 = true ↔ Executable label store effects := by
  induction effects generalizing store with
  | nil => simp [checkedRun, Executable.nil]
  | cons effect rest ih =>
      by_cases enabled : Enabled label store effect
      · simp [checkedRun, enabled, executable_cons_iff, ih]
      · simp [checkedRun, enabled, executable_cons_iff]

/-- Batch dependency preservation comes from the existing independence theorem. -/
theorem independent_pair_direct {label : O → R} {store : Finset O} {first second : Commit O R}
    (firstReady : Enabled label store first) (secondReady : Enabled label store second)
    (independent : Independent label first second) :
    checkedRun label store [first, second] = (true, fire (fire store first) second) := by
  have orders := (independent_iff_both_orders firstReady secondReady).mp independent
  apply checkedRun_direct
  exact .cons firstReady (.cons orders.1 (.nil _))

/-- Arbitrarily long independent batches reuse their common preparation. -/
theorem independent_batch_direct {label : O → R} {store : Finset O}
    {effects : List (Commit O R)} (prepared : ∀ effect ∈ effects, Enabled label store effect)
    (independent : effects.Pairwise (Independent label)) :
    checkedRun label store effects = (true, fireList store effects) :=
  checkedRun_direct (executable_of_pairwise_independent prepared independent)

/-- Compiled preconditions permit adjacent fusion; unconditional net-effect fusion is not claimed. -/
theorem adjacent_fusion {label : O → R} {store : Finset O} (first second : Commit O R)
    (guard : (CommitPrecondition.sequential label first second).Holds label store) :
    checkedRun label store [first, second] = checkedRun label store [first.compose second] := by
  obtain ⟨firstReady, secondReady⟩ :=
    (CommitPrecondition.sequential_holds_iff label first second store).mp guard
  rw [checkedRun_direct (.cons firstReady (.cons secondReady (.nil _))),
    checkedRun_direct (.cons (Commit.compose_enabled firstReady secondReady) (.nil _))]
  simp [Commit.compose_fire firstReady secondReady]

namespace Controls

/-- Two different consumed occurrences; the first makes the second's forbidden fact. -/
def makeForbidden : Commit Nat Nat := ⟨{0}, ∅, {2}, []⟩
def unlessForbidden : Commit Nat Nat := ⟨{1}, ∅, {3}, [⟨fun n => n == 2, ∅⟩]⟩

theorem disjoint_takes_do_not_establish_independence :
    Disjoint makeForbidden.taken unlessForbidden.taken ∧
    Enabled id {0, 1} makeForbidden ∧ Enabled id {0, 1} unlessForbidden ∧
    ¬ Enabled id (fire {0, 1} makeForbidden) unlessForbidden ∧
    ¬ Independent id makeForbidden unlessForbidden := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro independent
  have orders := (independent_iff_both_orders
    (show Enabled id {0, 1} makeForbidden by decide)
    (show Enabled id {0, 1} unlessForbidden by decide)).mp independent
  exact (by decide : ¬ Enabled id (fire {0, 1} makeForbidden) unlessForbidden) orders.1

theorem earlier_publication_survives_refusal :
    checkedRun id {0, 1} [makeForbidden, unlessForbidden] = (false, {1, 2}) := by decide

/-- Unrelated growth changes the whole store while preserving every dependency. -/
theorem unrelated_growth_reuses_preparation :
    ({0, 1} : Finset Nat) ≠ {0, 1, 7} ∧
    Agreement id {0, 1} {0, 1, 7} unlessForbidden ∧
    checked id {0, 1, 7} unlessForbidden = (true, {0, 3, 7}) := by
  refine ⟨by decide, ?_, by decide⟩
  constructor <;> decide

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus

/-- The conservative revision profile rejects an otherwise independent second writer. -/
theorem whole_store_validation_rejects_independent :
    Independent SerializedPublication.Controls.lab SerializedPublication.Controls.takeFirst
      SerializedPublication.Controls.takeSecond ∧
    Enabled SerializedPublication.Controls.lab
      (fire SerializedPublication.Controls.snapshot SerializedPublication.Controls.takeFirst)
      SerializedPublication.Controls.takeSecond ∧
    ¬ Enabled SerializedPublication.Controls.lab
      (fire SerializedPublication.Controls.snapshot SerializedPublication.Controls.takeFirst)
      (SerializedPublication.widen SerializedPublication.Controls.snapshot
        SerializedPublication.Controls.takeSecond) := by
  refine ⟨SerializedPublication.Controls.takers_independent, ?_, ?_⟩
  · exact ((independent_iff_both_orders SerializedPublication.Controls.takeFirst_enabled
      SerializedPublication.Controls.takeSecond_enabled).mp
        SerializedPublication.Controls.takers_independent).1
  · decide

end Controls
end Mettapedia.Languages.MeTTa.StoreAndDemand.ValidationReuse
