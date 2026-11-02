import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns

/-!
# Exact readiness persistence under equation refinement

Original universal asks transport under refinement in a fixed occurrence
world. A complete pending firing additionally needs its selected port/tell
problem to remain consistent. That condition is necessary and sufficient
for a firing already valid in the earlier configuration. Entailed added
equations give a useful stronger sufficient condition without making a
new binding. No scheduler or wake-index adequacy is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadinessPersistence

open GuardFreeProcessOrders
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

omit [DecidableEq O] in
theorem extended_problem_refines (action : SubstitutionAction T S) (label : O → T)
    (rule : RuleInstance T) (picked : Selection O) {early late : Configuration T O}
    (refinement : action.Refines late.equations early.equations) :
    action.Refines (picked.problem label rule late) (picked.problem label rule early) := by
  intro assignment solved
  rw [problem_eq, action.models_append] at solved ⊢
  exact ⟨refinement assignment solved.1, solved.2⟩

/-- Shape, occurrence rights-independent enabling and original asks already
transport. Exactly the remaining selected problem's consistency is missing. -/
theorem valid_iff_remaining_consistent (action : SubstitutionAction T S)
    (label : O → T) {rule : RuleInstance T} {picked : Selection O}
    {early late : Configuration T O} (valid : picked.Valid action label rule early)
    (refinement : action.Refines late.equations early.equations)
    (sameWorld : early.present = late.present) :
    picked.Valid action label rule late ↔ action.Consistent (picked.problem label rule late) := by
  constructor
  · exact Selection.Valid.consistent
  · intro consistent
    refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
      valid.outputs, sameWorld ▸ valid.occurrences, consistent, ?_⟩
    intro check member assignment solved
    rw [← sameWorld]
    exact valid.checks check member assignment
      (extended_problem_refines action label rule picked refinement assignment solved)

/-- If the pending ports and tells already follow from the incoming store,
any consistent refinement in the same physical world preserves readiness. -/
theorem valid_of_entailed_added (action : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {picked : Selection O} {early late : Configuration T O}
    (valid : picked.Valid action label rule early)
    (refinement : action.Refines late.equations early.equations)
    (sameWorld : early.present = late.present)
    (noNewBinding : action.Refines early.equations (added label rule picked))
    (consistent : action.Consistent late.equations) :
    picked.Valid action label rule late := by
  apply (valid_iff_remaining_consistent action label valid refinement sameWorld).mpr
  obtain ⟨assignment, solved⟩ := consistent
  refine ⟨assignment, ?_⟩
  rw [problem_eq, action.models_append]
  exact ⟨solved, noNewBinding assignment (refinement assignment solved)⟩

/-- Entailed port equations alone do not license an independent pending tell;
when the rule has no tells they are the complete no-new-binding condition. -/
theorem valid_of_entailed_ports_no_tell (action : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {picked : Selection O} {early late : Configuration T O}
    (valid : picked.Valid action label rule early)
    (refinement : action.Refines late.equations early.equations)
    (sameWorld : early.present = late.present) (noTell : rule.tell = [])
    (ports : action.Refines early.equations
      (Selection.equations label rule.take picked.taken ++
        Selection.equations label rule.read picked.read))
    (consistent : action.Consistent late.equations) :
    picked.Valid action label rule late :=
  valid_of_entailed_added action label valid refinement sameWorld
    (by simpa [added, noTell] using ports) consistent

omit [DecidableEq O] in
theorem incompatible_problem_stays_incompatible (action : SubstitutionAction T S)
    (label : O → T) (rule : RuleInstance T) (picked : Selection O)
    {early late : Configuration T O}
    (refinement : action.Refines late.equations early.equations)
    (incompatible : ¬ action.Consistent (picked.problem label rule early)) :
    ¬ action.Consistent (picked.problem label rule late) := by
  rintro ⟨assignment, solved⟩
  exact incompatible ⟨assignment, extended_problem_refines action label rule picked
    refinement assignment solved⟩

omit [DecidableEq O] in
/-- Chaining the actual direction of refinement needs no equation-list identity. -/
theorem refinement_between (action : SubstitutionAction T S)
    (states : Nat → Configuration T O)
    (refines : ∀ n, action.Refines (states (n + 1)).equations (states n).equations)
    {early late : Nat} (later : early ≤ late) :
    action.Refines (states late).equations (states early).equations := by
  induction late, later using Nat.le_induction with
  | base => exact action.refines_refl _
  | succ n _ ih => exact action.refines_trans (refines n) ih

/-- For one fixed selected row in a fixed physical world, infinitely many
ready moments force eventual continuous readiness. Once its extended
problem is inconsistent, later equation refinement cannot revive it. -/
theorem often_ready_is_eventually_ready (action : SubstitutionAction T S)
    (label : O → T) (rule : RuleInstance T) (picked : Selection O)
    (states : Nat → Configuration T O)
    (refines : ∀ n, action.Refines (states (n + 1)).equations (states n).equations)
    (sameWorld : ∀ early late, (states early).present = (states late).present)
    (often : InfinitelyOften fun n => picked.Valid action label rule (states n)) :
    EventuallyAlways fun n => picked.Valid action label rule (states n) := by
  obtain ⟨start, _, initial⟩ := often 0
  refine ⟨start, ?_⟩
  intro n afterStart
  apply (valid_iff_remaining_consistent action label initial
    (refinement_between action states refines afterStart) (sameWorld start n)).mpr
  obtain ⟨future, later, valid⟩ := often n
  obtain ⟨assignment, solved⟩ := valid.consistent
  exact ⟨assignment, extended_problem_refines action label rule picked
    (refinement_between action states refines later) assignment solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadinessPersistence
