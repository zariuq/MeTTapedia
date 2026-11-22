import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardEntryViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCutRepresentation

/-!
# Finite entry and creation data for every authored guard cut

The entry cuts of a schedule store the prefix resource delta and row origins. Its physical
left summand reads the original input; the right summand reads authored
creations. Later clauses transport its declarations without adding their
equations to its information cut. Compilation requires no guard verdict.

This is the source-side data for native actual-row queries and internal
creation checks, not a callback evaluating a source program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O V Next Later : Type} [DecidableEq O]
    {declaration : V → MetaArity S} {next : Next → MetaArity S} {later : Later → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

namespace Schedule

variable {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def originalEntryCut {Query : Type} (schedule : Schedule S O Γ sort before after) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries after.declarations)) Γ sort))
    (picked : Selection O) : EntryCut (family queries last after.declarations) O Γ sort where
  view := (originalCut after queries plan picked).represent schedule.entryBank
    (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations
      (captureEmbedding queries last after.declarations))
    ((before.present.image Sum.inl \ schedule.net.effect.taken) ∪ schedule.net.effect.made)
  taken := schedule.net.effect.taken
  made := schedule.net.effect.made

/-- Complete equality, absence and count judgments agree with the independently
updated source prefix, including the current clause's own information. -/
theorem original_entry_cut_iff {Query : Type} (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries after.declarations)) Γ sort))
    (picked : Selection O) :
    (schedule.originalEntryCut queries plan picked).Holds ↔ (originalCut after queries plan picked).Holds := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
  change ((originalCut after queries plan picked).represent schedule.entryBank
    (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations
      (captureEmbedding queries last after.declarations))
    ((before.present.image Sum.inl \ schedule.net.effect.taken) ∪ schedule.net.effect.made)).Holds ↔ _
  apply Cut.represent_iff _ _ _ _ cursor.current cursor.injective
  · exact schedule.assembled_physical_of_resources resources
  · intro Future future candidate pattern occurrence _inside
    change Matches last _ candidate pattern
      ((after.rows occurrence).map last after.declarations (captureEmbedding queries last after.declarations)) ↔
      Matches schedule.entryBank _ candidate pattern
        ((schedule.physicalRows (cursor.current occurrence)).map schedule.entryBank after.declarations
          (captureEmbedding queries last after.declarations))
    rw [matches_map_iff, matches_map_iff]
    exact (schedule.physical_row_instances shapes occurrence future
      (Assignment.compose candidate (captureEmbedding queries last after.declarations)) pattern).symm

def entryCuts : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (EntryCut after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ middle _ _ _ mid past queries plan picked =>
      past.entryCuts.map (EntryCut.map (captureFrame queries middle mid.declarations).assignment) ++
        [past.originalEntryCut queries plan picked]

theorem entry_cuts_length (schedule : Schedule S O Γ sort before after) :
    schedule.entryCuts.length = schedule.cuts.length := by
  induction schedule with
  | nil _ => rfl
  | snoc _ _ _ _ prior =>
      change (_ ++ [_]).length = (_ ++ [_]).length
      simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using
        congrArg (fun size => size + 1) prior

/-- Each compiled entry cut has the original problem, checks and full guard
meaning. No successful cut is assumed while producing these data. -/
theorem entry_cuts_compare (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits) :
    List.Forall₂
      (fun entry source => entry.view.problem = source.problem ∧ entry.view.checks = source.checks ∧
        (entry.Holds ↔ source.Holds)) schedule.entryCuts schedule.cuts := by
  induction schedule with
  | nil _ => exact .nil
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      have pastShapes := (shapes_snoc past queries plan picked).mp shapes |>.1
      rw [commits_snoc, executable_snoc_iff] at resources
      have previous := prior pastShapes resources.1
      change List.Forall₂ _ (_ ++ [_]) (_ ++ [_])
      apply List.rel_append
      · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.Forall₂.imp ?_ previous
        intro entry source pair
        exact entry.comparison_map source (captureFrame queries middle mid.declarations) pair
      · exact .cons ⟨rfl, rfl, past.original_entry_cut_iff pastShapes resources.1 queries plan picked⟩ .nil

theorem entry_cut_inputs (schedule : Schedule S O Γ sort before after) :
    ∀ cut ∈ schedule.entryCuts, ∀ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment after.declarations future) (pattern : Term (signature S future) Γ sort) (occurrence : O),
      Matches cut.view.locals after.declarations candidate pattern (cut.view.rows (.inl occurrence)) ↔
        Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment)
          pattern (before.rows occurrence) := by
  induction schedule with
  | nil start => intro cut member; cases member
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      intro cut member Future future candidate pattern occurrence
      change cut ∈ past.entryCuts.map (EntryCut.map (captureFrame queries middle mid.declarations).assignment) ++
        [past.originalEntryCut queries plan picked] at member
      rcases List.mem_append.mp member with previous | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp previous
        change Matches old.view.locals _ candidate pattern
          ((old.view.rows (.inl occurrence)).map old.view.locals _ (captureFrame queries middle mid.declarations).assignment) ↔ _
        rw [matches_map_iff]
        have original := prior old inside Future future
          (Assignment.compose candidate (captureFrame queries middle mid.declarations).assignment) pattern occurrence
        rw [frame_snoc_assignment, Assignment.compose_associative]
        exact original
      · have same := List.mem_singleton.mp current
        subst cut
        change Matches past.entryBank _ candidate pattern
          ((past.inputRow occurrence).map past.entryBank mid.declarations (captureEmbedding queries middle mid.declarations)) ↔ _
        rw [matches_map_iff, past.input_row_instances occurrence future]
        rw [frame_snoc_assignment, Assignment.compose_associative, captureFrame_assignment]

theorem entry_cut_world (schedule : Schedule S O Γ sort before after) :
    ∀ cut ∈ schedule.entryCuts,
      cut.view.world = (before.present.image Sum.inl \ cut.taken) ∪ cut.made := by
  induction schedule with
  | nil start => intro cut member; cases member
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      intro cut member
      change cut ∈ past.entryCuts.map (EntryCut.map (captureFrame queries middle mid.declarations).assignment) ++
        [past.originalEntryCut queries plan picked] at member
      rcases List.mem_append.mp member with previous | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp previous
        exact prior old inside
      · have same := List.mem_singleton.mp current
        subst cut
        rfl

theorem entry_cut_created_not_initial (schedule : Schedule S O Γ sort before after) :
    ∀ cut ∈ schedule.entryCuts, ∀ occurrence : O, Sum.inl occurrence ∉ cut.made := by
  induction schedule with
  | nil start => intro cut member; cases member
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      intro cut member occurrence
      change cut ∈ past.entryCuts.map (EntryCut.map (captureFrame queries middle mid.declarations).assignment) ++
        [past.originalEntryCut queries plan picked] at member
      rcases List.mem_append.mp member with previous | current
      · obtain ⟨old, inside, rfl⟩ := List.mem_map.mp previous
        exact prior old inside occurrence
      · have same := List.mem_singleton.mp current
        subst cut
        exact past.net_made_not_inherited occurrence

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
