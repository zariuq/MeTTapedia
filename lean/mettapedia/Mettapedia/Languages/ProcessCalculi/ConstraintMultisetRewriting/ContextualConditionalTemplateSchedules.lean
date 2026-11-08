import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateState
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation

/-!
# Finite source bodies with conditional captured productions

Existing ordinary/shared schedules compose with captured-template clauses.
Admission retains the original information cuts and full resource history.
Births record authored conditional rows in their saved declaration family,
with a separate transport for their captures. No native result or final
source row store is an input to these descriptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualGuardMatching
open ContextualSourceSchedules hiding Schedule Birth Plan
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O V W : Type} {Γ : Ctx S} {sort : S.Srt}
    {declaration : V → MetaArity S} {later : W → MetaArity S}

structure Birth (declaration : V → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  PrivateNames : Type
  privateEquality : DecidableEq PrivateNames
  locals : PrivateNames → MetaArity S
  SavedNames : Type
  equality : DecidableEq SavedNames
  saved : SavedNames → MetaArity S
  row : Row locals saved context sort
  occurrence : Option O
  transport : Assignment saved declaration

def Birth.map (change : Assignment declaration later) (birth : Birth declaration O Γ sort) : Birth later O Γ sort :=
  { birth with transport := Assignment.compose change birth.transport }

def Birth.ofOrdinary (birth : ContextualSourceSchedules.Birth declaration O Γ sort) : Birth declaration O Γ sort :=
  ⟨birth.SavedNames, birth.equality, birth.saved, birth.SavedNames, birth.equality, birth.saved,
    if birth.reusable then ContextualConditionalPublication.store birth.saved birth.saved ⟨birth.problem, birth.value⟩
      else ofStored birth.saved birth.saved (.shared birth.value), birth.occurrence, birth.transport⟩

def templateBirths {Local Query Inner : Type} {locals : Local → MetaArity S}
    [DecidableEq Local] [DecidableEq Query] [DecidableEq Inner] [DecidableEq O]
    (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners before.declarations Γ sort) (picked : Selection O) :
    List (Birth (ContextualConditionalTemplateState.resultFamily queries inners locals before) O Γ sort) := by
  let _ := before.equality
  let _ (side : Bool) : DecidableEq
      (ContextualConditionalTemplateState.PrivateNames (Query := Query) (Inner := Inner) locals before side) := by
    cases side <;> infer_instance
  exact List.ofFn fun port : Fin rule.code.produce.length =>
    ⟨_, inferInstance, ContextualConditionalTemplateState.resultLocals queries inners locals before,
      _, (by let _ := before.equality; infer_instance),
      ContextualConditionalTemplateState.resultFamily queries inners locals before,
      ContextualConditionalTemplateState.producedDescription queries inners locals before rule picked
        port.val ⟨rule.code.produce.get port, rule.conditions port⟩,
      picked.made[port.val]?, generator (ContextualConditionalTemplateState.resultFamily queries inners locals before)⟩

inductive Schedule (S : Signature) (O : Type) [DecidableEq O] (context : Ctx S) (sort : S.Srt) :
    {Local : Type} → {locals : Local → MetaArity S} → ContextualClauseSourceState.World locals O context sort →
    {Last : Type} → {last : Last → MetaArity S} → ContextualClauseSourceState.World last O context sort → Type 1 where
  | nil {Local : Type} {locals : Local → MetaArity S} (before : ContextualClauseSourceState.World locals O context sort) :
      Schedule S O context sort before before
  | segment {First Middle Last : Type} {first : First → MetaArity S}
      {middle : Middle → MetaArity S} {last : Last → MetaArity S}
      {before : ContextualClauseSourceState.World first O context sort}
      {mid : ContextualClauseSourceState.World middle O context sort}
      {after : ContextualClauseSourceState.World last O context sort}
      (past : Schedule S O context sort before mid)
      (plain : ContextualSourceSchedules.Schedule S O context sort mid after) :
      Schedule S O context sort before after
  | template {First Middle Query Inner : Type} {first : First → MetaArity S} {middle : Middle → MetaArity S}
      [middleEquality : DecidableEq Middle] [queryEquality : DecidableEq Query] [innerEquality : DecidableEq Inner]
      {before : ContextualClauseSourceState.World first O context sort}
      (mid : ContextualClauseSourceState.World middle O context sort)
      (past : Schedule S O context sort before mid)
      (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
      (rule : ContextualConditionalTemplateSource.Rule queries inners mid.declarations context sort) (picked : Selection O) :
      Schedule S O context sort before (ContextualConditionalTemplateState.target queries inners middle mid rule picked)

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort} {after : ContextualClauseSourceState.World last O Γ sort}

def Admitted (schedule : Schedule S O Γ sort before after) : Prop := by
  induction schedule with
  | nil start => exact ContextualConditionalExecution.Solvable start.equations
  | segment past plain prior => exact prior ∧ plain.Admitted
  | template mid past queries inners rule picked prior =>
      exact prior ∧ ContextualConditionalTemplateState.Admitted queries inners _ mid rule picked

def selections : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Selection O)
  | _, _, _, .nil _ => []
  | _, _, _, .segment past plain => past.selections ++ plain.selections
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ past _ _ _ picked => past.selections ++ [picked]

def commits (schedule : Schedule S O Γ sort before after) : List (Commit O Unit) :=
  schedule.selections.map (fun picked => picked.commit)

def names : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    (schedule : Schedule S O Γ sort before after) → before.Names → after.Names
  | _, _, _, .nil _ => id
  | _, _, _, .segment past plain => plain.names ∘ past.names
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ past _ _ _ _ => fun name => .inr (.inr (past.names name))

theorem names_injective (schedule : Schedule S O Γ sort before after) : Function.Injective schedule.names := by
  induction schedule with
  | nil _ => exact Function.injective_id
  | segment past plain prior => exact plain.names_injective.comp prior
  | template mid past queries inners rule picked prior =>
      intro left right same
      exact prior (Sum.inr.inj (Sum.inr.inj same))

theorem names_preserve (schedule : Schedule S O Γ sort before after) (name : before.Names) :
    after.declarations (schedule.names name) = before.declarations name := by
  induction schedule with
  | nil _ => rfl
  | segment past plain prior => exact (plain.names_preserve _).trans (prior name)
  | template mid past queries inners rule picked prior => exact prior name

abbrev frame (schedule : Schedule S O Γ sort before after) : Extension before.declarations where
  Names := after.Names
  declarations := after.declarations
  name := schedule.names
  injective := schedule.names_injective
  preserves := schedule.names_preserve

def deltas : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → ContextualResidual.Problem after.declarations
  | _, _, _, .nil _ => []
  | _, _, _, .segment past plain => ContextualResidual.mapProblem plain.frame.assignment past.deltas ++ plain.deltas
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mid past queries inners rule picked =>
      ContextualResidual.mapProblem (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment past.deltas ++
        added mid (ContextualTemplateSource.Expanded queries inners)
          (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked

def shapes : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Shape O)
  | _, _, _, .nil _ => []
  | _, _, _, .segment past plain => past.shapes ++ plain.shapes
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mid past queries inners rule picked =>
      past.shapes ++ [originalShape mid (ContextualTemplateSource.Expanded queries inners)
        (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked]

def cuts : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Cut after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, .segment past plain => past.cuts.map (Cut.map plain.frame.assignment) ++ plain.cuts
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mid past queries inners rule picked =>
      past.cuts.map (Cut.map (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment) ++
        [originalCut mid (ContextualTemplateSource.Expanded queries inners)
          (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked]

def births : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Birth after.declarations O Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, .segment past plain => past.births.map (Birth.map plain.frame.assignment) ++ plain.births.map Birth.ofOrdinary
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mid past queries inners rule picked =>
      past.births.map (Birth.map (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment) ++
        templateBirths mid queries inners rule picked

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules
