import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSourceState
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScheduleComposition

/-!
# Selected source schedules before admission

A schedule contains authored clauses and physical selections, without an
execution proof. Intermediate worlds are the independently defined source
updates. Capture extensions, information deltas and physical effects are
compiled from these data. Ill-shaped or refused schedules remain representable
and must be rejected by admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualGuardMatching ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Query Local Shared O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev captureFrame : Extension captures where
  Names := Query ⊕ (Mettapedia.Logic.LP.ScopedVar Local ⊕ Shared)
  declarations := family queries locals captures
  name := fun name => .inr (.inr name)
  injective := fun _ _ same => Sum.inr.inj (Sum.inr.inj same)
  preserves _ := rfl

theorem captureFrame_assignment : (captureFrame queries locals captures).assignment = captureEmbedding queries locals captures := by
  funext name
  change generator (family queries locals captures) (.inr (.inr name)) =
    instantiate (rowEmbedding queries locals captures)
      (generator (rowFamily locals captures) (.inr name))
  erw [instantiate_generator]
  rfl

variable {queries locals captures} {Γ : Ctx S} {sort : S.Srt} [DecidableEq O]

def added (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) : ContextualResidual.Problem (family queries locals before.declarations) :=
  ContextualResidual.observeProblem
      (ContextualConditionalSourceProblem.bindingEquations queries locals before.declarations picked plan.rule before.rows) ++
    ContextualConditionalSourceProblem.latent queries locals before.declarations picked before.rows

omit [DecidableEq O] in
theorem information_eq (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) :
    ContextualClauseSourceState.information queries locals before plan picked =
      ContextualResidual.mapProblem (captureFrame queries locals before.declarations).assignment before.equations ++
        added before queries plan picked := by
  rw [captureFrame_assignment]
  exact List.append_assoc _ _ _

inductive Schedule (S : Signature) (O : Type) [DecidableEq O] (context : Ctx S) (sort : S.Srt) :
    {Local : Type} → {locals : Local → MetaArity S} → ContextualClauseSourceState.World locals O context sort →
    {Last : Type} → {last : Last → MetaArity S} → ContextualClauseSourceState.World last O context sort → Type 1 where
  | nil {Local : Type} {locals : Local → MetaArity S} (before : ContextualClauseSourceState.World locals O context sort) :
      Schedule S O context sort before before
  | snoc {Local Middle Query : Type} {locals : Local → MetaArity S} {middle : Middle → MetaArity S}
      [middleEquality : DecidableEq Middle] [queryEquality : DecidableEq Query]
      {before : ContextualClauseSourceState.World locals O context sort}
      {mid : ContextualClauseSourceState.World middle O context sort}
      (past : Schedule S O context sort before mid) (queries : Query → MetaArity S)
      (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) context sort))
      (picked : Selection O) :
      Schedule S O context sort before (ContextualClauseSourceState.target queries middle mid plan picked)

namespace Schedule

variable {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort} {after : ContextualClauseSourceState.World last O Γ sort}

def Admitted (schedule : Schedule S O Γ sort before after) : Prop := by
  induction schedule with
  | nil start => exact ContextualConditionalExecution.Solvable start.equations
  | @snoc Middle Query _ middle _ _ _ mid past queries plan picked prior =>
      exact prior ∧ ContextualClauseSourceState.Admitted queries middle mid plan picked

def selections : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} → Schedule S O Γ sort before after → List (Selection O)
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ past _ _ picked => past.selections ++ [picked]

def commits (schedule : Schedule S O Γ sort before after) : List (Commit O Unit) :=
  schedule.selections.map (fun picked => picked.commit)

def names : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → before.Names → after.Names
  | _, _, _, .nil _ => id
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ _ _ _ _ _ past _ _ _ => fun name => .inr (.inr (past.names name))

theorem names_injective (schedule : Schedule S O Γ sort before after) : Function.Injective schedule.names := by
  induction schedule with
  | nil _ => exact Function.injective_id
  | snoc _ _ _ _ prior =>
      intro first second same
      exact prior (Sum.inr.inj (Sum.inr.inj same))

theorem names_preserve (schedule : Schedule S O Γ sort before after) (name : before.Names) :
    after.declarations (schedule.names name) = before.declarations name := by
  induction schedule with
  | nil _ => rfl
  | snoc _ _ _ _ prior => exact prior name

abbrev frame (schedule : Schedule S O Γ sort before after) : Extension before.declarations where
  Names := after.Names
  declarations := after.declarations
  name := schedule.names
  injective := schedule.names_injective
  preserves := schedule.names_preserve

theorem frame_snoc_assignment {Middle Query : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query] {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort)) (picked : Selection O) :
    (Schedule.snoc past queries plan picked).frame.assignment =
      Assignment.compose (captureFrame queries middle mid.declarations).assignment past.frame.assignment := by
  exact Extension.trans_assignment past.frame (captureFrame queries middle mid.declarations)

def deltas : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → ContextualResidual.Problem after.declarations
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ middle _ _ _ mid past queries plan picked =>
      ContextualResidual.mapProblem (captureFrame queries middle mid.declarations).assignment past.deltas ++ added mid queries plan picked

theorem final_equations (schedule : Schedule S O Γ sort before after) :
    after.equations = ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas := by
  induction schedule with
  | nil start =>
      change start.equations = ContextualResidual.mapProblem (generator start.declarations) start.equations ++ []
      simp [ContextualResidual.mapProblem, instantiateObservation_identity]
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      change ContextualClauseSourceState.information queries middle mid plan picked = _
      rw [information_eq, prior]
      change ContextualResidual.mapProblem (captureFrame queries middle mid.declarations).assignment
          (ContextualResidual.mapProblem past.frame.assignment start.equations ++ past.deltas) ++ added mid queries plan picked = _
      rw [ContextualResidual.mapProblem, List.map_append]
      change _ = ContextualResidual.mapProblem (Schedule.snoc past queries plan picked).frame.assignment
        start.equations ++ (_ ++ _)
      rw [frame_snoc_assignment, ← ContextualConditionalNaturality.map_problem_compose]
      exact List.append_assoc _ _ _

theorem source_solvable (schedule : Schedule S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations) :
    ContextualConditionalExecution.Solvable before.equations := by
  obtain ⟨Future, future, candidate, model⟩ := consistent
  rw [schedule.final_equations] at model
  have incoming := (ContextualResidual.models_mapProblem _ _ _).mp
    ((ContextualResidual.models_append candidate _ _).mp model).1
  exact ⟨Future, future, Assignment.compose candidate schedule.frame.assignment, incoming⟩

def unitLabel (_ : O) : Unit := ()

theorem physical_trace (schedule : Schedule S O Γ sort before after) :
    fireList before.present schedule.commits = after.present := by
  induction schedule with
  | nil _ => rfl
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      change fireList start.present ((past.selections ++ [picked]).map _) = _
      rw [List.map_append, fireList_append]
      change fireList (fireList start.present past.commits) [picked.commit] = _
      rw [prior]
      rfl

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
