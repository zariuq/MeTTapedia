import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateOrigins

/-!
# Saved conditional births preserve every final source row observation

Only authored port shapes are required. Captured conditions remain local,
ordinary birth conditions remain private, and shared references use their
composed caller transport. Resource validity and guard admission are separate
from this representation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualGuardMatching
open ContextualSourceSchedules hiding Schedule Birth Plan

variable {S : Signature} {O Next : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    {next : Next → MetaArity S}

theorem template_birth_instances {Local Query Inner : Type} {locals : Local → MetaArity S}
    [DecidableEq Local] [DecidableEq Query] [DecidableEq Inner]
    (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners before.declarations Γ sort) (picked : Selection O)
    (distinct : picked.made.Nodup) (outputs : picked.made.length = rule.code.produce.length)
    (occurrence : O)
    (birth : Birth (ContextualConditionalTemplateState.resultFamily queries inners locals before) O Γ sort)
    (selected : ContextualTemplateSource.assign picked.made (templateBirths before queries inners rule picked) occurrence = some birth)
    (candidate : Assignment (ContextualConditionalTemplateState.resultFamily queries inners locals before) next)
    (pattern : Term (signature S next) Γ sort) :
    birth.origin.Instances candidate pattern ↔
      Matches (ContextualConditionalTemplateState.resultLocals queries inners locals before)
        (ContextualConditionalTemplateState.resultFamily queries inners locals before) candidate pattern
        ((ContextualConditionalTemplateState.target queries inners locals before rule picked).rows occurrence) := by
  have member := ContextualTemplateSource.assign_mem _ _ _ _ selected
  obtain ⟨port, same⟩ := List.mem_iff_get.mp member
  have lengths : picked.made.length = (templateBirths before queries inners rule picked).length := by
    simpa only [templateBirths, List.length_ofFn] using outputs
  have assigned := ContextualTemplateSource.assign_get picked.made (templateBirths before queries inners rule picked)
    distinct lengths port
  rw [same, selected] at assigned
  have actual := Option.some.inj assigned
  rw [actual, ← same, ContextualConditionalTemplateState.produced_at_shape distinct outputs port]
  unfold templateBirths
  rw [List.get_ofFn]
  change Matches _ _ (Assignment.compose candidate (generator _)) pattern _ ↔ Matches _ _ candidate pattern _
  rw [Assignment.compose_identity_right]
  simp only [Fin.cast_mk]

namespace Schedule

variable {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

/-- Every computed origin has exactly the final source row's conditional
instances, even before information/resource/guard admission is established. -/
theorem production_origin_instances_of_shapes (schedule : Schedule S O Γ sort before after) :
    schedule.ShapesHold → ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) (occurrence : O),
      (schedule.productionOrigin occurrence).Instances candidate pattern ↔
        Matches last after.declarations candidate pattern (after.rows occurrence) := by
  induction schedule with
  | nil start =>
      intro _shapes Next next candidate pattern occurrence
      simp only [productionOrigin, outputBirth, Option.map_none, Option.getD_none]
      change (Origin.retained _ start.declarations (start.rows occurrence) (generator start.declarations)).Instances
        candidate pattern ↔ _
      exact retained_origin_instances _ _ candidate pattern
  | segment past plain prior =>
      intro shapes Next next candidate pattern occurrence
      have split := (shapes_segment past plain).mp shapes
      have old := plain.origins_instances_of_shapes split.2 next candidate pattern occurrence
      cases selected : plain.productionIndex occurrence with
      | some index =>
          rw [production_origin_segment_some past plain occurrence index selected]
          apply (Birth.ofOrdinary_instances (plain.births.get index) candidate pattern).trans
          rw [plain.selected_production_origin occurrence index selected]
          exact old
      | none =>
          rw [production_origin_segment_none past plain occurrence selected, Origin.map_instances]
          have initial := plain.production_origin occurrence
          simp only [ContextualSourceSchedules.Schedule.productionOrigin, selected, Option.map_none, Option.getD_none] at initial
          rw [← initial] at old
          exact (prior split.1 next (Assignment.compose candidate plain.frame.assignment) pattern occurrence).trans old
  | template mid past queries inners rule picked prior =>
      intro shapes Next next candidate pattern occurrence
      have split := (shapes_template past queries inners rule picked).mp shapes
      have distinct := split.2.2.1
      have outputs : picked.made.length = rule.code.produce.length := by
        simpa only [originalShape, ContextualConditionalTemplateState.rawPlan, ContextualTemplateSource.Rule.lower,
          List.length_mapIdx] using split.2.2.2.2.2
      cases selected : ContextualTemplateSource.assign picked.made (templateBirths mid queries inners rule picked) occurrence with
      | some birth =>
          rw [production_origin_template_some past queries inners rule picked occurrence birth selected]
          exact template_birth_instances mid queries inners rule picked distinct outputs occurrence birth selected candidate pattern
      | none =>
          rw [production_origin_template_none past queries inners rule picked occurrence selected, Origin.map_instances]
          have lengths : picked.made.length = (templateBirths mid queries inners rule picked).length := by
            simpa only [templateBirths, List.length_ofFn] using outputs
          have notMade := (assign_none_iff picked.made _ distinct lengths occurrence).mp selected
          have retained := ContextualConditionalTemplateState.retained_matches (rule := rule) occurrence notMade next candidate pattern
          have square := congrArg (Assignment.compose candidate)
            (captureFrame_assignment (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).symm
          exact (prior split.1 next (Assignment.compose candidate
            (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment)
            pattern occurrence).trans (square ▸ retained.symm)

theorem production_origin_instances (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (pattern : Term (signature S next) Γ sort) (occurrence : O) :
    (schedule.productionOrigin occurrence).Instances candidate pattern ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) :=
  schedule.production_origin_instances_of_shapes (schedule.admitted_characterization.mp admitted).1 next candidate pattern occurrence

theorem selected_birth_instances (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) (birth : Birth after.declarations O Γ sort) (selected : schedule.outputBirth occurrence = some birth)
    (next : Next → MetaArity S) (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    birth.origin.Instances candidate pattern ↔ Matches last after.declarations candidate pattern (after.rows occurrence) := by
  have meaning := schedule.production_origin_instances_of_shapes shapes next candidate pattern occurrence
  simpa only [productionOrigin, selected, Option.map_some, Option.getD_some] using meaning

theorem retained_entry_instances (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) (selected : schedule.outputBirth occurrence = none)
    (next : Next → MetaArity S) (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment) pattern (before.rows occurrence) ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) := by
  have meaning := schedule.production_origin_instances_of_shapes shapes next candidate pattern occurrence
  simpa only [productionOrigin, selected, Option.map_none, Option.getD_none, Origin.Instances] using meaning

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules
