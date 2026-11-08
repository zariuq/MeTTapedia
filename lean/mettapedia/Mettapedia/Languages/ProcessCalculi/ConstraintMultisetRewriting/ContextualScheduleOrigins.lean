import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation

/-!
# Compiled origins for every final conditional row

An origin is retained input data with its capture transport, an ordinary
schema with its own saved problem, or a shared expression. Compilation reads
the initial rows and authored production ports; it does not obtain rows
from the final source world or invoke a source evaluator.

Later information changes a retained or shared capture through its explicit
transport. An ordinary schema retains its own problem and declaration
family. The observation theorem compares the compiled origins with the
independently updated source rows across an arbitrary admitted body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows

variable {S : Signature} {V Next Later O : Type} {declaration : V → MetaArity S}
    {next : Next → MetaArity S} {later : Later → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

inductive Origin (declaration : V → MetaArity S) (context : Ctx S) (sort : S.Srt) : Type 1 where
  | retained {Local Saved : Type} (locals : Local → MetaArity S) (saved : Saved → MetaArity S)
      (row : Row locals saved context sort) (transport : Assignment saved declaration) : Origin declaration context sort
  | schema {Saved : Type} (saved : Saved → MetaArity S) (problem : ContextualResidual.Problem saved)
      (value : Term (signature S saved) context sort) : Origin declaration context sort
  | shared (value : Term (signature S declaration) context sort) : Origin declaration context sort

def Origin.Instances (candidate : Assignment declaration next) (pattern : Term (signature S next) Γ sort) :
    Origin declaration Γ sort → Prop
  | .retained locals saved row transport => Matches locals saved (Assignment.compose candidate transport) pattern row
  | .schema _ problem value => ContextualPublication.SourceInstances problem value next pattern
  | .shared value => pattern = instantiate candidate value

def Origin.map (change : Assignment declaration later) : Origin declaration Γ sort → Origin later Γ sort
  | .retained locals saved row transport => .retained locals saved row (Assignment.compose change transport)
  | .schema saved problem value => .schema saved problem value
  | .shared value => .shared (instantiate change value)

theorem Origin.map_instances (origin : Origin declaration Γ sort) (change : Assignment declaration later)
    (candidate : Assignment later next) (pattern : Term (signature S next) Γ sort) :
    (origin.map change).Instances candidate pattern ↔ origin.Instances (Assignment.compose candidate change) pattern := by
  cases origin with
  | retained locals saved row transport =>
      change Matches _ _ (Assignment.compose candidate (Assignment.compose change transport)) pattern row ↔ _
      rw [Assignment.compose_associative]
      rfl
  | schema _ _ _ => rfl
  | shared value =>
      simp only [Origin.map, Origin.Instances, Assignment.instantiate_compose]

theorem retained_origin_instances {Local : Type} (locals : Local → MetaArity S)
    (row : Row locals declaration Γ sort) (candidate : Assignment declaration next) (pattern : Term (signature S next) Γ sort) :
    (Origin.retained locals declaration row (generator declaration)).Instances candidate pattern ↔
      Matches locals declaration candidate pattern row := by
  have identity : Assignment.compose candidate (generator declaration) = candidate := by
    funext name
    exact instantiate_generator candidate name
  change Matches _ _ (Assignment.compose candidate (generator declaration)) pattern row ↔ _
  rw [identity]

def producedOrigin {Local Query : Type} (locals : Local → MetaArity S)
    (before : ContextualClauseSourceState.World locals O Γ sort) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (port : Fin plan.rule.produce.length) :
    Origin (family queries locals before.declarations) Γ sort :=
  let value := queryView queries locals before.declarations (plan.rule.produce.get port)
  if plan.reusable.get ⟨port.val, plan.shape.symm ▸ port.isLt⟩ then
    .schema (family queries locals before.declarations)
      (ContextualClauseSourceState.information queries locals before plan picked) value
  else .shared value

theorem produced_origin_instances_of_shape {Local Query : Type} [DecidableEq O] [DecidableEq Local] [DecidableEq Query]
    (locals : Local → MetaArity S) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (distinct : picked.made.Nodup) (outputs : picked.made.length = plan.rule.produce.length)
    (port : Fin picked.made.length) (candidate : Assignment (family queries locals before.declarations) next)
    (pattern : Term (signature S next) Γ sort) :
    (producedOrigin locals before queries plan picked ⟨port.val, outputs ▸ port.isLt⟩).Instances candidate pattern ↔
      Matches (ContextualClauseSourceState.resultLocals queries locals before)
        (family queries locals before.declarations) candidate pattern
        ((ContextualClauseSourceState.target queries locals before plan picked).rows (picked.made.get port)) := by
  rw [ContextualClauseSourceState.produced_at_shape distinct outputs port]
  unfold producedOrigin ContextualClauseSourceState.producedRow
  split
  · dsimp only [Origin.Instances]
    exact (ContextualConditionalPublication.ordinary_matches_iff locals
      (family queries locals before.declarations) (family queries locals before.declarations) candidate
      ⟨ContextualClauseSourceState.information queries locals before plan picked,
        queryView queries locals before.declarations
          (plan.rule.produce.get ⟨port.val, outputs ▸ port.isLt⟩)⟩ pattern).symm
  · rw [ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    rfl

theorem produced_origin_instances {Local Query : Type} [DecidableEq O] [DecidableEq Local] [DecidableEq Query]
    (locals : Local → MetaArity S) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (admitted : ContextualClauseSourceState.Admitted queries locals before plan picked)
    (port : Fin picked.made.length) (candidate : Assignment (family queries locals before.declarations) next)
    (pattern : Term (signature S next) Γ sort) :
    (producedOrigin locals before queries plan picked ⟨port.val, admitted.output_shape ▸ port.isLt⟩).Instances candidate pattern ↔
      Matches (ContextualClauseSourceState.resultLocals queries locals before)
        (family queries locals before.declarations) candidate pattern
        ((ContextualClauseSourceState.target queries locals before plan picked).rows (picked.made.get port)) :=
  produced_origin_instances_of_shape locals before queries plan picked admitted.output_distinct admitted.output_shape port candidate pattern

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def origins : {First : Type} → {first : First → MetaArity S} →
    {before : ContextualClauseSourceState.World first O Γ sort} →
    {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → O → Origin after.declarations Γ sort
  | _, _, _, _, _, _, .nil start => fun occurrence => .retained _ start.declarations (start.rows occurrence) (generator start.declarations)
  | _, _, _, _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ middle _ _ start mid past queries plan picked =>
      fun occurrence =>
        (ContextualTemplateSource.assign picked.made
          (List.ofFn (producedOrigin middle mid queries plan picked)) occurrence).getD
          ((origins (before := start) past occurrence).map (captureFrame queries middle mid.declarations).assignment)

/-- Row comparison precedes admission: only the authored output shapes are needed. -/
theorem origins_instances_of_shapes (schedule : Schedule S O Γ sort before after) :
    schedule.ShapesHold → ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) (occurrence : O),
      (schedule.origins occurrence).Instances candidate pattern ↔
        Matches last after.declarations candidate pattern (after.rows occurrence) := by
  induction schedule with
  | nil start =>
      intro _shapes Next next candidate pattern occurrence
      simp only [origins]
      exact retained_origin_instances _ (start.rows occurrence) candidate pattern
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      intro shapes Next next candidate pattern occurrence
      simp only [origins]
      have steps := (shapes_snoc past queries plan picked).mp shapes
      have distinct := steps.2.2.1
      have outputs := steps.2.2.2.2.2
      by_cases made : occurrence ∈ picked.made
      · obtain ⟨port, rfl⟩ := List.mem_iff_get.mp made
        have length : picked.made.length = (List.ofFn (producedOrigin middle mid queries plan picked)).length :=
          outputs.trans (List.length_ofFn).symm
        change Origin.Instances candidate pattern ((ContextualTemplateSource.assign picked.made _ _).getD _) ↔ _
        rw [ContextualTemplateSource.assign_get picked.made _ distinct length port]
        change ((List.ofFn (producedOrigin middle mid queries plan picked)).get _).Instances candidate pattern ↔ _
        rw [List.get_ofFn]
        exact produced_origin_instances_of_shape middle mid queries plan picked distinct outputs port candidate pattern
      · have absent : ContextualTemplateSource.assign picked.made
            (List.ofFn (producedOrigin middle mid queries plan picked)) occurrence = none := by
          cases found : ContextualTemplateSource.assign picked.made
              (List.ofFn (producedOrigin middle mid queries plan picked)) occurrence with
          | none => rfl
          | some origin => exact False.elim (made (ContextualTemplateSource.assign_mem _ _ _ _ found))
        change Origin.Instances candidate pattern ((ContextualTemplateSource.assign picked.made _ _).getD _) ↔ _
        rw [absent]
        change ((past.origins occurrence).map (captureFrame queries middle mid.declarations).assignment).Instances
          candidate pattern ↔ _
        rw [Origin.map_instances, ContextualClauseSourceState.retained_matches occurrence made,
          captureFrame_assignment]
        exact prior steps.1 next (Assignment.compose candidate (captureEmbedding queries middle mid.declarations)) pattern occurrence

theorem origins_instances (schedule : Schedule S O Γ sort before after) :
    schedule.Admitted → ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) (occurrence : O),
      (schedule.origins occurrence).Instances candidate pattern ↔
        Matches last after.declarations candidate pattern (after.rows occurrence) := by
  intro admitted
  exact schedule.origins_instances_of_shapes (schedule.admitted_characterization.mp admitted).1

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
