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
      change (List.map _ past.entryCuts ++ past.appendedEntryCuts plain).length =
        (List.map _ past.cuts ++ plain.cuts).length
      simp only [List.length_append, List.length_map, past.appended_entry_cuts_length plain, prior]
  | template _ _ _ _ _ _ prior =>
      change (_ ++ [_]).length = (_ ++ [_]).length
      simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using
        congrArg (fun size => size + 1) prior

theorem appended_entry_cuts_world (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    ∀ cut ∈ past.appendedEntryCuts plain, cut.view.world = (before.present.image Sum.inl \ cut.taken) ∪ cut.made := by
  induction plain with
  | nil _ => intro cut member; cases member
  | snoc _ _ _ _ prior =>
      intro cut member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        exact prior _ old inside
      · have same := List.mem_singleton.mp current
        subst cut
        rfl

theorem entry_cut_world (body : Schedule S O Γ sort before after) :
    ∀ cut ∈ body.entryCuts, cut.view.world = (before.present.image Sum.inl \ cut.taken) ∪ cut.made := by
  induction body with
  | nil _ => intro cut member; cases member
  | segment past plain prior =>
      intro cut member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        exact prior old inside
      · exact past.appended_entry_cuts_world plain cut current
  | template _ _ _ _ _ _ prior =>
      intro cut member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        exact prior old inside
      · have same := List.mem_singleton.mp current
        subst cut
        rfl

theorem appended_entry_cuts_created_not_initial (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    ∀ cut ∈ past.appendedEntryCuts plain, ∀ occurrence : O, Sum.inl occurrence ∉ cut.made := by
  induction plain with
  | nil _ => intro cut member; cases member
  | snoc previous _ _ _ prior =>
      intro cut member occurrence
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        exact prior _ old inside occurrence
      · have same := List.mem_singleton.mp current
        subst cut
        exact (Schedule.segment _ previous).net_made_not_inherited occurrence

theorem entry_cut_created_not_initial (body : Schedule S O Γ sort before after) :
    ∀ cut ∈ body.entryCuts, ∀ occurrence : O, Sum.inl occurrence ∉ cut.made := by
  induction body with
  | nil _ => intro cut member; cases member
  | segment past plain prior =>
      intro cut member occurrence
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        exact prior old inside occurrence
      · exact past.appended_entry_cuts_created_not_initial plain cut current occurrence
  | template _ past _ _ _ _ prior =>
      intro cut member occurrence
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        exact prior old inside occurrence
      · have same := List.mem_singleton.mp current
        subst cut
        exact past.net_made_not_inherited occurrence

theorem appended_entry_cut_inputs (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    ∀ cut ∈ past.appendedEntryCuts plain, ∀ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment after.declarations future) (pattern : Term (signature S future) Γ sort) (occurrence : O),
      Matches cut.view.locals after.declarations candidate pattern (cut.view.rows (.inl occurrence)) ↔
        Matches first before.declarations (Assignment.compose candidate (Schedule.segment past plain).frame.assignment)
          pattern (before.rows occurrence) := by
  induction plain with
  | nil _ => intro cut member; cases member
  | @snoc Middle Query _ middle _ _ start current previous queries plan picked prior =>
      intro cut member Future future candidate pattern occurrence
      rw [frame_segment_assignment, ContextualSourceSchedules.Schedule.frame_snoc_assignment]
      rcases List.mem_append.mp member with earlier | now
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        change Matches old.view.locals _ candidate pattern
          ((old.view.rows (.inl occurrence)).map old.view.locals _ (captureFrame queries middle current.declarations).assignment) ↔ _
        rw [matches_map_iff]
        have original := prior past old inside Future future
          (Assignment.compose candidate (captureFrame queries middle current.declarations).assignment) pattern occurrence
        rw [frame_segment_assignment] at original
        rw [original, Assignment.compose_associative, Assignment.compose_associative, Assignment.compose_associative]
      · have same := List.mem_singleton.mp now
        subst cut
        change Matches (Schedule.segment past previous).entryBank _ candidate pattern
          (((Schedule.segment past previous).physicalRows (.inl occurrence)).map (Schedule.segment past previous).entryBank
            current.declarations (captureEmbedding queries middle current.declarations)) ↔ _
        rw [matches_map_iff, (Schedule.segment past previous).input_row_instances occurrence, frame_segment_assignment,
          captureFrame_assignment]
        simp only [Assignment.compose_associative]

theorem entry_cut_inputs (body : Schedule S O Γ sort before after) :
    ∀ cut ∈ body.entryCuts, ∀ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment after.declarations future) (pattern : Term (signature S future) Γ sort) (occurrence : O),
      Matches cut.view.locals after.declarations candidate pattern (cut.view.rows (.inl occurrence)) ↔
        Matches first before.declarations (Assignment.compose candidate body.frame.assignment)
          pattern (before.rows occurrence) := by
  induction body with
  | nil _ => intro cut member; cases member
  | segment past plain prior =>
      intro cut member Future future candidate pattern occurrence
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        change Matches old.view.locals _ candidate pattern
          ((old.view.rows (.inl occurrence)).map old.view.locals _ plain.frame.assignment) ↔ _
        rw [matches_map_iff, prior old inside Future future (Assignment.compose candidate plain.frame.assignment) pattern occurrence,
          frame_segment_assignment, Assignment.compose_associative]
      · exact past.appended_entry_cut_inputs plain cut current Future future candidate pattern occurrence
  | @template Middle Query Inner _ middle _ _ _ _ current past queries inners rule picked prior =>
      intro cut member Future future candidate pattern occurrence
      rcases List.mem_append.mp member with earlier | now
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp earlier
        change Matches old.view.locals _ candidate pattern
          ((old.view.rows (.inl occurrence)).map old.view.locals _
            (captureFrame (ContextualTemplateSource.Expanded queries inners) middle current.declarations).assignment) ↔ _
        rw [matches_map_iff, prior old inside Future future _ pattern occurrence, frame_template_assignment,
          Assignment.compose_associative]
      · have same := List.mem_singleton.mp now
        subst cut
        change Matches past.entryBank _ candidate pattern
          ((past.physicalRows (.inl occurrence)).map past.entryBank current.declarations
            (captureEmbedding (ContextualTemplateSource.Expanded queries inners) middle current.declarations)) ↔ _
        rw [matches_map_iff, past.input_row_instances occurrence, frame_template_assignment, captureFrame_assignment,
          Assignment.compose_associative]

theorem appended_entry_cuts_compare (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after)
    (shapes : (Schedule.segment past plain).ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present (Schedule.segment past plain).commits) :
    List.Forall₂
      (fun entry source => entry.view.problem = source.problem ∧ entry.view.checks = source.checks ∧
        (entry.Holds ↔ source.Holds)) (past.appendedEntryCuts plain) plain.cuts := by
  induction plain with
  | nil _ => exact .nil
  | @snoc Middle Query _ middle _ _ start current previous queries plan picked prior =>
      have whole := (shapes_segment past _).mp shapes
      have plainShapes := (ContextualSourceSchedules.Schedule.shapes_snoc previous queries plan picked).mp whole.2
      have prefixShapes : (Schedule.segment past previous).ShapesHold :=
        (shapes_segment past previous).mpr ⟨whole.1, plainShapes.1⟩
      have prefixResources :
          Executable ContextualSourceSchedules.Schedule.unitLabel before.present (Schedule.segment past previous).commits := by
        rw [commits_segment, ContextualSourceSchedules.Schedule.commits_snoc, ← List.append_assoc,
          executable_snoc_iff] at resources
        rw [commits_segment]
        exact resources.1
      have previousPairs := prior past prefixShapes prefixResources
      change List.Forall₂ _ ((past.appendedEntryCuts previous).map _ ++ [_]) (previous.cuts.map _ ++ [_])
      apply List.rel_append
      · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.Forall₂.imp ?_ previousPairs
        intro entry source pair
        exact entry.comparison_map source (captureFrame queries middle current.declarations) pair
      · exact .cons ⟨rfl, rfl,
          (Schedule.segment past previous).original_entry_cut_iff prefixShapes prefixResources queries plan picked⟩ .nil

/-- Each compiled entry cut of a mixed body has the original problem, checks
and full guard meaning; no successful cut is assumed while producing them. -/
theorem entry_cuts_compare (body : Schedule S O Γ sort before after) (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits) :
    List.Forall₂
      (fun entry source => entry.view.problem = source.problem ∧ entry.view.checks = source.checks ∧
        (entry.Holds ↔ source.Holds)) body.entryCuts body.cuts := by
  induction body with
  | nil _ => exact .nil
  | segment past plain prior =>
      have parts := (shapes_segment past plain).mp shapes
      have split := resources
      rw [commits_segment, executable_append_iff] at split
      change List.Forall₂ _ (past.entryCuts.map _ ++ past.appendedEntryCuts plain) (past.cuts.map _ ++ plain.cuts)
      apply List.rel_append
      · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.Forall₂.imp ?_ (prior parts.1 split.1)
        intro entry source pair
        exact entry.comparison_map source plain.frame pair
      · exact past.appended_entry_cuts_compare plain shapes resources
  | @template Middle Query Inner _ middle _ _ _ _ current past queries inners rule picked prior =>
      have parts := (shapes_template past queries inners rule picked).mp shapes
      rw [commits_template, executable_snoc_iff] at resources
      change List.Forall₂ _ (past.entryCuts.map _ ++ [_]) (past.cuts.map _ ++ [_])
      apply List.rel_append
      · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.Forall₂.imp ?_ (prior parts.1 resources.1)
        intro entry source pair
        exact entry.comparison_map source
          (captureFrame (ContextualTemplateSource.Expanded queries inners) middle current.declarations) pair
      · exact .cons ⟨rfl, rfl, past.original_entry_cut_iff parts.1 resources.1 _ _ picked⟩ .nil

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
