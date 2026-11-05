import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateGuardViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEntryGuardCompilation

/-!
# Original guard cuts for mixed conditional clause bodies

Each cut is represented by surviving entry occurrences and authored prefix
creations. Ordinary segments are traversed with the same accumulated mixed
prefix, so their observations do not restart from a private intermediate
world. The shared row and cut representation theorems supply adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open ContextualSourceSchedules hiding Schedule Birth Plan
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Middle Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {middle : Middle → MetaArity S} {last : Last → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {mid : ContextualClauseSourceState.World middle O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def originalEntryCut {Query : Type} (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort))
    (picked : Selection O) : EntryCut (family queries middle mid.declarations) O Γ sort where
  view := (originalCut mid queries plan picked).represent past.entryBank
    (fun physical => (past.physicalRows physical).map past.entryBank mid.declarations
      (captureEmbedding queries middle mid.declarations))
    ((before.present.image Sum.inl \ past.net.effect.taken) ∪ past.net.effect.made)
  taken := past.net.effect.taken
  made := past.net.effect.made

theorem original_entry_cut_iff {Query : Type} (past : Schedule S O Γ sort before mid)
    (shapes : past.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present past.commits)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort))
    (picked : Selection O) :
    (past.originalEntryCut queries plan picked).Holds ↔ (originalCut mid queries plan picked).Holds := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial past.selections
  change ((originalCut mid queries plan picked).represent past.entryBank
    (fun physical => (past.physicalRows physical).map past.entryBank mid.declarations
      (captureEmbedding queries middle mid.declarations))
    ((before.present.image Sum.inl \ past.net.effect.taken) ∪ past.net.effect.made)).Holds ↔ _
  apply Cut.represent_iff _ _ _ _ cursor.current cursor.injective
  · exact (past.allocated_net_commit resources).2
  · intro Future future candidate pattern occurrence _inside
    change Matches middle _ candidate pattern
      ((mid.rows occurrence).map middle mid.declarations (captureEmbedding queries middle mid.declarations)) ↔
      Matches past.entryBank _ candidate pattern
        ((past.physicalRows (cursor.current occurrence)).map past.entryBank mid.declarations
          (captureEmbedding queries middle mid.declarations))
    rw [matches_map_iff, matches_map_iff]
    exact (past.physical_row_instances shapes occurrence
      (Assignment.compose candidate (captureEmbedding queries middle mid.declarations)) pattern).symm

def appendedEntryCuts (past : Schedule S O Γ sort before mid) :
    {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    ContextualSourceSchedules.Schedule S O Γ sort mid after → List (EntryCut after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, @ContextualSourceSchedules.Schedule.snoc _ _ _ _ _ _ _ _ _ currentLocals _ _ _ current previous queries plan picked =>
      (past.appendedEntryCuts previous).map (EntryCut.map (captureFrame queries currentLocals current.declarations).assignment) ++
        [(Schedule.segment past previous).originalEntryCut queries plan picked]

def entryCuts : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (EntryCut after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, .segment past plain =>
      past.entryCuts.map (EntryCut.map plain.frame.assignment) ++ past.appendedEntryCuts plain
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ current past queries inners rule picked =>
      past.entryCuts.map (EntryCut.map
        (captureFrame (ContextualTemplateSource.Expanded queries inners) _ current.declarations).assignment) ++
        [past.originalEntryCut (ContextualTemplateSource.Expanded queries inners)
          (ContextualConditionalTemplateState.rawPlan queries inners _ current rule) picked]

theorem appended_entry_cuts_length (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    (past.appendedEntryCuts plain).length = plain.cuts.length := by
  induction plain with
  | nil _ => rfl
  | snoc _ _ _ _ prior =>
      change (_ ++ [_]).length = (_ ++ [_]).length
      simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using
        congrArg (fun size => size + 1) (prior _)

theorem entry_cuts_length (body : Schedule S O Γ sort before after) : body.entryCuts.length = body.cuts.length := by
  induction body with
  | nil _ => rfl
  | segment past plain prior =>
      change (_ ++ _).length = (_ ++ _).length
      simp only [List.length_append, List.length_map, past.appended_entry_cuts_length plain, prior]
  | template _ _ _ _ _ _ prior =>
      change (_ ++ [_]).length = (_ ++ [_]).length
      simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using
        congrArg (fun size => size + 1) prior

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
