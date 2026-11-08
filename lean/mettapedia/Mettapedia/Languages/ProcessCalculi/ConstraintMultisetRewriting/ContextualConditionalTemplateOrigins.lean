import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSurvivingProductions

/-!
# Latest authored births describe final conditional rows

The lookup uses source selections and saved production descriptions. Later
creations replace earlier origins; capture transports compose through the
remaining source body. A missing production retains the original entry row.
Conditional matching compares the resulting descriptors with the independent
source update, without reading that final store into the lookup.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualGuardMatching
open ContextualSourceSchedules hiding Schedule Birth Plan

variable {S : Signature} {O V W Next : Type} {Γ : Ctx S} {sort : S.Srt}
    {declaration : V → MetaArity S} {later : W → MetaArity S} {next : Next → MetaArity S}

/-- The general saved-row constructor retains a row's whole conditional
meaning; whether it was an entry or a creation is tracked separately. -/
def Birth.origin (birth : Birth declaration O Γ sort) : Origin declaration Γ sort :=
  .retained birth.locals birth.saved birth.row birth.transport

theorem Birth.origin_map (birth : Birth declaration O Γ sort) (change : Assignment declaration later) :
    (birth.map change).origin = birth.origin.map change := rfl

theorem Birth.ofOrdinary_instances (birth : ContextualSourceSchedules.Birth declaration O Γ sort)
    (candidate : Assignment declaration next) (pattern : Term (signature S next) Γ sort) :
    (Birth.ofOrdinary birth).origin.Instances candidate pattern ↔ birth.origin.Instances candidate pattern := by
  by_cases ordinary : birth.reusable = true
  · simp only [Birth.ofOrdinary, Birth.origin, ContextualSourceSchedules.Birth.origin,
      ordinary, if_true, Origin.Instances]
    exact ContextualConditionalPublication.store_matches_iff birth.saved birth.saved _ _ pattern
  · simp only [Birth.ofOrdinary, Birth.origin, ContextualSourceSchedules.Birth.origin,
      ordinary, Bool.false_eq_true, if_false, Origin.Instances]
    rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff, Assignment.instantiate_compose]

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def outputBirth : {First : Type} → {first : First → MetaArity S} →
    {before : ContextualClauseSourceState.World first O Γ sort} →
    {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → O → Option (Birth after.declarations O Γ sort)
  | _, _, _, _, _, _, .nil _, _ => none
  | _, _, _, _, _, _, .segment past plain, occurrence =>
      ((plain.productionIndex occurrence).map fun index => Birth.ofOrdinary (plain.births.get index)).or
        ((past.outputBirth occurrence).map (Birth.map plain.frame.assignment))
  | _, _, _, _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mid past queries inners rule picked, occurrence =>
      (ContextualTemplateSource.assign picked.made (templateBirths mid queries inners rule picked) occurrence).or
        ((past.outputBirth occurrence).map
          (Birth.map (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment))

def productionOrigin (schedule : Schedule S O Γ sort before after) (occurrence : O) : Origin after.declarations Γ sort :=
  ((schedule.outputBirth occurrence).map Birth.origin).getD
    (.retained first before.declarations (before.rows occurrence) schedule.frame.assignment)

section Segment

variable {Middle : Type} {middle : Middle → MetaArity S}
    {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after)

theorem production_origin_segment_some (occurrence : O) (index : plain.BirthIndex)
    (selected : plain.productionIndex occurrence = some index) :
    (Schedule.segment past plain).productionOrigin occurrence = (Birth.ofOrdinary (plain.births.get index)).origin := by
  simp only [productionOrigin, outputBirth, selected, Option.map_some, Option.some_or, Option.getD_some]

theorem production_origin_segment_none (occurrence : O) (selected : plain.productionIndex occurrence = none) :
    (Schedule.segment past plain).productionOrigin occurrence =
      (past.productionOrigin occurrence).map plain.frame.assignment := by
  have inherited : Origin.retained first before.declarations (before.rows occurrence)
      (Schedule.segment past plain).frame.assignment =
      (Origin.retained first before.declarations (before.rows occurrence) past.frame.assignment).map plain.frame.assignment := by
    rw [frame_segment_assignment]
    rfl
  simp only [productionOrigin, outputBirth, selected, Option.map_none, Option.none_or, Option.map_map]
  rw [inherited]
  cases previous : past.outputBirth occurrence <;> rfl

end Segment

section Template

variable {Middle Query Inner : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query] [DecidableEq Inner]
    {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners mid.declarations Γ sort) (picked : Selection O)

theorem production_origin_template_some (occurrence : O)
    (birth : Birth (ContextualConditionalTemplateState.resultFamily queries inners middle mid) O Γ sort)
    (selected : ContextualTemplateSource.assign picked.made (templateBirths mid queries inners rule picked) occurrence = some birth) :
    (Schedule.template mid past queries inners rule picked).productionOrigin occurrence = birth.origin := by
  simp only [productionOrigin, outputBirth, selected, Option.some_or, Option.map_some, Option.getD_some]

theorem production_origin_template_none (occurrence : O)
    (selected : ContextualTemplateSource.assign picked.made (templateBirths mid queries inners rule picked) occurrence = none) :
    (Schedule.template mid past queries inners rule picked).productionOrigin occurrence =
      (past.productionOrigin occurrence).map
        (captureFrame (ContextualTemplateSource.Expanded queries inners) middle mid.declarations).assignment := by
  have inherited : Origin.retained first before.declarations (before.rows occurrence)
      (Schedule.template mid past queries inners rule picked).frame.assignment =
      (Origin.retained first before.declarations (before.rows occurrence) past.frame.assignment).map
        (captureFrame (ContextualTemplateSource.Expanded queries inners) middle mid.declarations).assignment := by
    rw [frame_template_assignment]
    rfl
  simp only [productionOrigin, outputBirth, selected, Option.none_or, Option.map_map]
  rw [inherited]
  cases previous : past.outputBirth occurrence <;> rfl

end Template

theorem outputBirth_none_iff_shapes (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) :
    schedule.outputBirth occurrence = none ↔ ∀ picked ∈ schedule.selections, occurrence ∉ picked.made := by
  induction schedule with
  | nil _ => simp only [outputBirth, selections, List.not_mem_nil, false_implies, implies_true]
  | segment past plain prior =>
      have parts := (shapes_segment past plain).mp shapes
      simp only [outputBirth, Option.or_eq_none_iff, Option.map_eq_none_iff]
      rw [plain.productionIndex_none_iff_shapes parts.2, prior parts.1]
      change (∀ picked ∈ plain.selections, occurrence ∉ picked.made) ∧
        (∀ picked ∈ past.selections, occurrence ∉ picked.made) ↔
        ∀ picked ∈ past.selections ++ plain.selections, occurrence ∉ picked.made
      rw [List.forall_mem_append]
      exact and_comm
  | template mid past queries inners rule picked prior =>
      have parts := (shapes_template past queries inners rule picked).mp shapes
      have outputs : picked.made.length = rule.code.produce.length := by
        simpa only [originalShape, ContextualConditionalTemplateState.rawPlan, ContextualTemplateSource.Rule.lower,
          List.length_mapIdx] using parts.2.2.2.2.2
      have distinct : picked.made.Nodup := parts.2.2.1
      have lengths : picked.made.length = (templateBirths mid queries inners rule picked).length := by
        simpa only [templateBirths, List.length_ofFn] using outputs
      simp only [outputBirth, Option.or_eq_none_iff, Option.map_eq_none_iff]
      rw [assign_none_iff picked.made (templateBirths mid queries inners rule picked) distinct lengths occurrence, prior parts.1]
      change (occurrence ∉ picked.made ∧ ∀ selected ∈ past.selections, occurrence ∉ selected.made) ↔
        ∀ selected ∈ past.selections ++ [picked], occurrence ∉ selected.made
      rw [List.forall_mem_append, List.forall_mem_singleton]
      exact and_comm

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules
