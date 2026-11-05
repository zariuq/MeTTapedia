import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleMetadata

/-!
# Every produced row's saved problem is consistent at its creation

An admitted clause has a model of its complete problem. Its production
descriptors retain that same problem across later declaration transports.
This applies to produced descriptors, not arbitrary dormant input rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem births_solvable (schedule : Schedule S O Γ sort before after) :
    schedule.Admitted → ∀ birth ∈ schedule.births, ContextualConditionalExecution.Solvable birth.problem := by
  induction schedule with
  | nil _ =>
      intro _admitted birth member
      cases member
  | @snoc Middle Query _ middle _ _ _ mid past queries plan picked prior =>
      intro admitted birth member
      change birth ∈ past.births.map (Birth.map (captureFrame queries middle mid.declarations).assignment) ++
        originalBirths mid queries plan picked at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp earlier
        exact prior admitted.1 original oldMember
      · unfold originalBirths at current
        obtain ⟨port, rfl⟩ := List.mem_ofFn.mp current
        exact admitted.2.solvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
