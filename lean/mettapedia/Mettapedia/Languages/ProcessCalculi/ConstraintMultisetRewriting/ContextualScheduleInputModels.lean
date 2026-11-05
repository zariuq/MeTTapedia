import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAmalgamation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationInputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProductionAllocation

/-!
# Initial input rows remain jointly realizable in every source model

The input footprint is computed from authored selections and allocation
names. Only entry occurrences actually used by a source port are included.
Every model of the final source problem supplies matching witnesses for
these rows. A common fresh declaration extension realizes any finite list
of them while retaining the given caller assignment.

No guard success or source-admission proof is assumed. Conditions of unused
stored rows are not added to the problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def inputFootprint : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → Finset (OccurrenceAllocationRenaming.Name O)
  | _, _, _, .nil _ => ∅
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ past _ _ picked =>
      past.inputFootprint ∪
        ((picked.taken.toFinset ∪ picked.read.toFinset).image
          (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial past.selections).current)

def initialInputs (schedule : Schedule S O Γ sort before after) : Finset O :=
  schedule.inputFootprint.biUnion fun physical =>
    match physical with
    | .inl occurrence => {occurrence}
    | .inr _ => ∅

theorem mem_initialInputs (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    occurrence ∈ schedule.initialInputs ↔ Sum.inl occurrence ∈ schedule.inputFootprint := by
  simp only [initialInputs, Finset.mem_biUnion]
  constructor
  · rintro ⟨physical, used, selected⟩
    cases physical with
    | inl original =>
        have same : occurrence = original := Finset.mem_singleton.mp selected
        exact same.symm ▸ used
    | inr created => exact False.elim (Finset.notMem_empty _ selected)
  · intro used
    exact ⟨Sum.inl occurrence, used, Finset.mem_singleton_self _⟩

private theorem rename_append (cursor : OccurrenceAllocationRenaming.Cursor O)
    (left right : List (Selection O)) :
    OccurrenceAllocationRenaming.rename cursor (left ++ right) =
      OccurrenceAllocationRenaming.rename cursor left ++
        OccurrenceAllocationRenaming.rename (OccurrenceAllocationRenaming.finish cursor left) right := by
  induction left generalizing cursor with
  | nil => rfl
  | cons picked rest prior =>
      change cursor.rename picked :: OccurrenceAllocationRenaming.rename (cursor.advance picked) (rest ++ right) =
        cursor.rename picked ::
          (OccurrenceAllocationRenaming.rename (cursor.advance picked) rest ++
            OccurrenceAllocationRenaming.rename
              (OccurrenceAllocationRenaming.finish (cursor.advance picked) rest) right)
      rw [prior]

theorem footprint_has_port (schedule : Schedule S O Γ sort before after)
    (physical : OccurrenceAllocationRenaming.Name O) :
    physical ∈ schedule.inputFootprint ↔
      ∃ picked ∈ schedule.allocated, physical ∈ picked.taken ∨ physical ∈ picked.read := by
  induction schedule with
  | nil start =>
      simp only [inputFootprint, allocated, selections, OccurrenceAllocationRenaming.rename,
        Finset.notMem_empty, List.not_mem_nil, false_and, exists_false]
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      change physical ∈ past.inputFootprint ∪ _ ↔
        ∃ selected ∈ OccurrenceAllocationRenaming.rename OccurrenceAllocationRenaming.Cursor.initial
          (past.selections ++ [picked]), physical ∈ selected.taken ∨ physical ∈ selected.read
      rw [rename_append]
      constructor
      · intro member
        rcases Finset.mem_union.mp member with old | current
        · obtain ⟨selected, inside, used⟩ := prior.mp old
          exact ⟨selected, List.mem_append_left _ inside, used⟩
        · obtain ⟨occurrence, used, rfl⟩ := Finset.mem_image.mp current
          refine ⟨_, List.mem_append_right _ (List.mem_cons_self), ?_⟩
          rcases Finset.mem_union.mp used with taken | read
          · exact .inl (List.mem_map.mpr ⟨occurrence, List.mem_toFinset.mp taken, rfl⟩)
          · exact .inr (List.mem_map.mpr ⟨occurrence, List.mem_toFinset.mp read, rfl⟩)
      · rintro ⟨selected, inside, used⟩
        rcases List.mem_append.mp inside with old | current
        · exact Finset.mem_union.mpr (.inl (prior.mpr ⟨selected, old, used⟩))
        · have equal := List.mem_singleton.mp current
          subst selected
          apply Finset.mem_union.mpr
          right
          rcases used with taken | read
          · obtain ⟨occurrence, member, same⟩ := List.mem_map.mp taken
            exact Finset.mem_image.mpr ⟨occurrence,
              Finset.mem_union.mpr (.inl (List.mem_toFinset.mpr member)), same⟩
          · obtain ⟨occurrence, member, same⟩ := List.mem_map.mp read
            exact Finset.mem_image.mpr ⟨occurrence,
              Finset.mem_union.mpr (.inr (List.mem_toFinset.mpr member)), same⟩


theorem net_input_in_footprint (schedule : Schedule S O Γ sort before after)
    (physical : OccurrenceAllocationRenaming.Name O)
    (used : physical ∈ schedule.net.effect.taken ∪ schedule.net.effect.kept) :
    physical ∈ schedule.inputFootprint := by
  obtain ⟨commit, member, port⟩ := OccurrenceAllocationRenaming.compiled_input_has_port OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) physical used
  obtain ⟨picked, selected, rfl⟩ := List.mem_map.mp member
  exact (schedule.footprint_has_port physical).mpr
    ⟨picked, selected, (by simpa only [Selection.commit, List.mem_toFinset] using port)⟩

/-- Every net input is an entry occurrence whose schema was actually used.
Resource executability suffices; guard admission is not an input. -/
theorem net_input_is_initial (schedule : Schedule S O Γ sort before after)
    (resources : Executable unitLabel before.present schedule.commits)
    (physical : OccurrenceAllocationRenaming.Name O)
    (used : physical ∈ schedule.net.effect.taken ∪ schedule.net.effect.kept) :
    ∃ occurrence ∈ before.present,
      physical = Sum.inl occurrence ∧ occurrence ∈ schedule.initialInputs := by
  have executable := (schedule.allocated_resources_of_executable resources).1
  have enabled := ((CompiledSchedule.compile_correct OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) (before.present.image Sum.inl)).2
      ((CompiledSchedule.compile_condition_iff _ _ _).mpr executable)).1
  have present : physical ∈ before.present.image Sum.inl := by
    rcases Finset.mem_union.mp used with taken | kept
    · exact enabled.taken_subset taken
    · exact enabled.kept_subset kept
  obtain ⟨occurrence, member, same⟩ := Finset.mem_image.mp present
  refine ⟨occurrence, member, same.symm, ?_⟩
  apply (mem_initialInputs schedule occurrence).mpr
  rw [same]
  exact schedule.net_input_in_footprint physical used

theorem model_at_entry (schedule : Schedule S O Γ sort before after)
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ContextualResidual.Models (Assignment.compose candidate schedule.frame.assignment) before.equations := by
  rw [schedule.final_equations] at model
  exact (ContextualResidual.models_mapProblem _ _ _).mp
    ((ContextualResidual.models_append candidate _ _).mp model).1

theorem inherited_matches_before_creation (schedule : Schedule S O Γ sort before after)
    (occurrence : O) (unmade : ∀ picked ∈ schedule.selections, occurrence ∉ picked.made)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches last after.declarations candidate pattern (after.rows occurrence) ↔
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment)
        pattern (before.rows occurrence) := by
  induction schedule with
  | nil start =>
      change _ ↔ Matches _ start.declarations
        (Assignment.compose candidate (generator start.declarations)) pattern (start.rows occurrence)
      rw [Assignment.compose_identity_right]
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      have old : ∀ selected ∈ past.selections, occurrence ∉ selected.made := by
        intro selected member
        exact unmade selected (List.mem_append_left _ member)
      have fresh : occurrence ∉ picked.made :=
        unmade picked (List.mem_append_right _ (List.mem_singleton_self _))
      rw [ContextualClauseSourceState.retained_matches occurrence fresh]
      rw [prior old]
      rw [frame_snoc_assignment, ← Assignment.compose_associative, captureFrame_assignment]

/-- Every used inherited row has a match under the caller of this particular
source model. Its witness is extracted from a source port, not assumed. -/
theorem initial_input_matches (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) (occurrence : O)
    (used : occurrence ∈ schedule.initialInputs) :
    ∃ pattern : Term (signature S next) Γ sort,
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment)
        pattern (before.rows occurrence) := by
  induction schedule with
  | nil start =>
      have impossible := (mem_initialInputs (Schedule.nil start) occurrence).mp used
      exact False.elim (Finset.notMem_empty _ impossible)
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      have parts := (shapes_snoc past queries plan picked).mp shapes
      have joined : ContextualResidual.Models candidate
          (ContextualClauseSourceState.information queries middle mid plan picked) := model
      rw [information_eq] at joined
      have previous := (ContextualResidual.models_mapProblem _ _ _).mp
        ((ContextualResidual.models_append candidate _ _).mp joined).1
      have footprint := (mem_initialInputs (Schedule.snoc past queries plan picked) occurrence).mp used
      change Sum.inl occurrence ∈ past.inputFootprint ∪ _ at footprint
      rcases Finset.mem_union.mp footprint with old | current
      · obtain ⟨pattern, matched⟩ := prior parts.1
          (Assignment.compose candidate (captureFrame queries middle mid.declarations).assignment)
          previous ((mem_initialInputs past occurrence).mpr old)
        refine ⟨pattern, ?_⟩
        rw [frame_snoc_assignment, Assignment.compose_associative]
        exact matched
      · obtain ⟨source, selected, same⟩ := Finset.mem_image.mp current
        have physical : source = occurrence := by
          have projected := congrArg OccurrenceAllocationRenaming.erase same
          exact ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial
            past.selections).projects source).symm.trans projected
        subst source
        have unmade : ∀ selected ∈ past.selections, occurrence ∉ selected.made :=
          ((OccurrenceAllocationRenaming.finish_current_inl_iff
            OccurrenceAllocationRenaming.Cursor.initial past.selections occurrence occurrence).mp same).2
        let witness := ContextualClauseWitnesses.witness_of_model queries middle mid.declarations
          picked plan.rule mid.rows mid.equations parts.2.2.2.1 parts.2.2.2.2.1 candidate model
        have currentMatch : ∃ pattern : Term (signature S next) Γ sort,
            Matches middle mid.declarations
              (Assignment.compose candidate (captureEmbedding queries middle mid.declarations))
              pattern (mid.rows occurrence) := by
          rcases Finset.mem_union.mp selected with taken | read
          · obtain ⟨port, equal⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp taken)
            have realized := witness.taken port
            rw [equal] at realized
            rw [ContextualClauseWitnesses.captures_square]
            exact ⟨_, realized.matches middle mid.declarations⟩
          · obtain ⟨port, equal⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp read)
            have realized := witness.read port
            rw [equal] at realized
            rw [ContextualClauseWitnesses.captures_square]
            exact ⟨_, realized.matches middle mid.declarations⟩
        obtain ⟨pattern, matched⟩ := currentMatch
        have original := (past.inherited_matches_before_creation occurrence unmade _ pattern).mp matched
        refine ⟨pattern, ?_⟩
        rw [frame_snoc_assignment, Assignment.compose_associative, captureFrame_assignment]
        exact original

/-- Finitely many input schemas can be opened together without changing the
chosen source model on its existing names. Repeated requests remain allowed. -/
theorem initial_inputs_realize_together (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations)
    (inputs : List O) (used : ∀ occurrence ∈ inputs, occurrence ∈ schedule.initialInputs) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ _filler : Assignment first extension.declarations,
      ∀ occurrence ∈ inputs, ∃ pattern : Term (signature S extension.declarations) Γ sort,
        Realizes first before.declarations
          (Assignment.compose extension.assignment (Assignment.compose candidate schedule.frame.assignment))
          pattern (before.rows occurrence) := by
  classical
  have witnesses : ∀ occurrence : { occurrence : O // occurrence ∈ inputs },
      ∃ pattern : Term (signature S next) Γ sort,
        Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment)
          pattern (before.rows occurrence.val) := by
    intro occurrence
    exact schedule.initial_input_matches shapes candidate model occurrence.val (used occurrence.val occurrence.property)
  let patterns := fun occurrence => Classical.choose (witnesses occurrence)
  let requests := inputs.attach.map fun occurrence => (patterns occurrence, before.rows occurrence.val)
  have matched : ∀ request ∈ requests,
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment) request.1 request.2 := by
    intro request member
    obtain ⟨occurrence, _, rfl⟩ := List.mem_map.mp member
    exact Classical.choose_spec (witnesses occurrence)
  obtain ⟨extension, filler, realized⟩ := finite_realizations first before.declarations
    (Assignment.compose candidate schedule.frame.assignment) requests matched
  refine ⟨extension, filler, ?_⟩
  intro occurrence member
  let selected : { occurrence : O // occurrence ∈ inputs } := ⟨occurrence, member⟩
  exact ⟨instantiate extension.assignment (patterns selected), realized _
    (List.mem_map.mpr ⟨selected, List.mem_attach _ _, rfl⟩)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
