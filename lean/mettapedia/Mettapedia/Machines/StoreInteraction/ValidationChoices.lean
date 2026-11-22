import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies

/-!
# Validation choices form a diamond, not only an isolation ladder

The existing mode algebra permits an additional useful combination: validate
takes and predicate observations, while allowing positive witnesses to remain
historical. This is not serializable in general. The positive-witness and
predicate-observation checks are independent requirements.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.ValidationChoices

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def predicateCurrent : Finset Check := {Check.takes, Check.regions}

theorem modes_are_incomparable :
    ¬ Mode.claims ⊆ predicateCurrent ∧ ¬ predicateCurrent ⊆ Mode.claims := by decide

theorem meet_is_takes_only : Mode.claims ∩ predicateCurrent = Mode.snapshot := by decide
theorem join_checks_everything : Mode.claims ∪ predicateCurrent = Mode.serializable := by decide

variable {O R : Type} [DecidableEq O]

omit [DecidableEq O] in
/-- Executable current admission and a historical witness are distinguished
by exactly the omitted live-witness check for this mode. -/
theorem promotion_iff_current_keeps {label : O → R} {store : Finset O} {c : Commit O R}
    (permitted : Permits label predicateCurrent store c) :
    Permits label Mode.serializable store c ↔ c.kept ⊆ store := by
  constructor
  · intro all
    exact all.2.1 (by simp [Mode.serializable])
  · intro keeps
    refine ⟨fun _ => permitted.1 (by simp [predicateCurrent]), fun _ => keeps,
      fun _ => permitted.2.2.1 (by simp [predicateCurrent]), permitted.2.2.2⟩

omit [DecidableEq O] in
/-- The dual boundary: live positive witnesses do not discharge complete
queries, including absence. -/
theorem promotion_iff_current_queries {label : O → R} {store : Finset O} {c : Commit O R}
    (permitted : Permits label Mode.claims store c) :
    Permits label Mode.serializable store c ↔ ∀ query ∈ c.queries, query.Holds label store := by
  constructor
  · intro all
    exact all.2.2.1 (by simp [Mode.serializable])
  · intro queries
    exact ⟨fun _ => permitted.1 (by simp [Mode.claims]),
      fun _ => permitted.2.1 (by simp [Mode.claims]), fun _ => queries, permitted.2.2.2⟩

namespace Controls

def label (o : Nat) : Nat := o
def oldPositive : Commit Nat Nat := ⟨∅, {0}, ∅, []⟩
def oldAbsence : Commit Nat Nat := ⟨∅, ∅, ∅, [⟨fun _ => true, ∅⟩]⟩

theorem historical_positive_current_predicates :
    Permits label predicateCurrent ∅ oldPositive ∧ ¬ Permits label Mode.claims ∅ oldPositive := by
  simp only [Permits]
  decide

theorem current_positive_historical_predicates :
    Permits label Mode.claims {0} oldAbsence ∧ ¬ Permits label predicateCurrent {0} oldAbsence := by
  simp only [Permits]
  decide

end Controls

end Mettapedia.Machines.StoreInteraction.ValidationChoices
