import Mettapedia.GSLT.Contracts.OccurrenceExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalOnTheStep

/-!
# What a run in a space returns

HE publishes its root results one occurrence at a time. PeTTa returns
an ordered batch when the outer continuation finishes. These are
different observations of the two source theories, not a common
evaluation order. Each observation is exact on the Transform execution,
including duplicates and the tick at which an answer becomes available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations

open Mettapedia.GSLT
open Contracts.OccurrenceObservers (Demand)
open Contracts.OccurrenceExecution (completed readCompleted reports ofTerm MatchingSteps reports_shown_iff)
open IndexedOperational (ExecutionPath)
open Mettapedia.GSLT.Compilation.Uniform
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Result Policy WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (worldObserve)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (SState readsAs_unique)
open StateRulesOnTheStep (packet packet_eq_iff)
open HENativeOnTransform (Presentation historyField historyField_injective)

variable {Context World : Type}

structure HEView where
  published : List Result
  finished : Bool

def heView (state : WorldConfiguration Context World) : HEView :=
  ⟨state.emitted, (worldObserve state).isSome⟩

def heEmit (a b : HEView) : List Result := b.published.drop a.published.length

def heEquationalView : HEEquationalExecution.State Context World → HEView
  | .pending request => ⟨request.emitted, false⟩
  | .running current => heView current

def pettaView (state : Eval.Configuration) : Option (List Atom) :=
  match state.control, state.frames with
  | .returned answers, [] => some answers
  | _, _ => none

abbrev pettaEmit := Contracts.OccurrenceExecution.settlingBatch (Answer := Atom)

def pettaEquationalView : PeTTaEquationalOnTheStep.State → Option (List Atom)
  | .ready _ => none
  | .running current => pettaView current

theorem he_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    (env : WorldEnvironment Context World) (policy : Policy) (code : Presentation Context World)
    {source : WorldConfiguration Context World} {start : SState O}
    (shown : HEControlOnTransform.Shows code source start)
    (demand : Demand) (answer : Contracts.OccurrenceObservers.Result Result demand) :
    reports (completed (sys := HEControlOnTransform.source env policy) heView
      (·.finished = true) heEmit source) demand answer ↔
    reports (readCompleted (sys := HEControlOnTransform.theory O code env policy)
      (ofTerm (HEControlOnTransform.Shows code) heView) (·.finished = true) heEmit start) demand answer := by
  refine reports_shown_iff (source := HEControlOnTransform.source env policy)
    (target := HEControlOnTransform.theory O code env policy)
    (shows := HEControlOnTransform.Shows code) heView ?_ ?_ shown (·.finished = true) heEmit demand answer
  · exact ⟨HEControlOnTransform.realize_step env policy code, HEControlOnTransform.reflect_step env policy code⟩
  · exact fun a b => congrArg heView (HEControlOnTransform.shows_unique code a b)

theorem petta_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    {source : Eval.Configuration} {start : SState O} (shown : EvalOnTheStep.Shows source start)
    (demand : Demand) (answer : Contracts.OccurrenceObservers.Result Atom demand) :
    reports (completed (sys := LiveRegistry.theory) pettaView (·.isSome = true) pettaEmit source) demand answer ↔
    reports (readCompleted (sys := PeTTaLiveOnTheStep.theory O)
      (ofTerm EvalOnTheStep.Shows pettaView) (·.isSome = true) pettaEmit start) demand answer := by
  refine reports_shown_iff (source := LiveRegistry.theory) (target := PeTTaLiveOnTheStep.theory O)
    (shows := EvalOnTheStep.Shows) pettaView ?_ ?_ shown (·.isSome = true) pettaEmit demand answer
  · exact ⟨PeTTaLiveOnTheStep.realize_step, PeTTaLiveOnTheStep.reflect_step⟩
  · exact fun a b => congrArg pettaView (EvalOnTheStep.shows_unique a b)

private theorem he_active_tag (code : Presentation Context World)
    (configuration : WorldConfiguration Context World) (parts : List Expr) :
    HEEquationalExecution.encode code (.running configuration) ≠ packet 11 parts := by
  obtain ⟨tag, bounded, fields, form⟩ :=
    HEControlOnTransform.encoded_ordinary_tag code (HEFocused.focus configuration)
  change HEControlOnTransform.encodeFocus code (HEFocused.focus configuration) ≠ _
  rw [form]
  exact fun eq => (Nat.ne_of_lt bounded) ((packet_eq_iff _ _ _ _).mp eq).1

private theorem he_equational_read {O : Type} [DecidableEq O] (code : Presentation Context World)
    {a b : HEEquationalExecution.State Context World} {mark : SState O}
    (first : HEEquationalExecution.Shows code a mark) (second : HEEquationalExecution.Shows code b mark) :
    heEquationalView a = heEquationalView b := by
  have same := Multiset.singleton_inj.mp (readsAs_unique first.readsAs.1 first.readsAs.2 second.readsAs.2)
  cases a with
  | pending a =>
    cases b with
    | pending b =>
      simp only [HEEquationalExecution.encode, EquationalEntryRules.request, packet_eq_iff] at same
      have field := congrArg (fun parts : List Expr => parts[4]?) same.2
      change some (historyField a.emitted) = some (historyField b.emitted) at field
      exact congrArg (fun list => HEView.mk list false) (historyField_injective (Option.some.inj field))
    | running b => exact (he_active_tag code b _ same.symm).elim
  | running a =>
    cases b with
    | pending b => exact (he_active_tag code a _ same).elim
    | running b => exact congrArg heView (HEControlOnTransform.shows_unique code first second)

theorem he_equational_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    (env : WorldEnvironment Context World) (policy : Policy) (code : Presentation Context World)
    {source : HEEquationalExecution.State Context World} {start : SState O}
    (shown : HEEquationalExecution.Shows code source start)
    (demand : Demand) (answer : Contracts.OccurrenceObservers.Result Result demand) :
    reports (completed (sys := HEEquationalExecution.source env policy) heEquationalView
      (·.finished = true) heEmit source) demand answer ↔
    reports (readCompleted (sys := HEEquationalExecution.theory O code env policy)
      (ofTerm (HEEquationalExecution.Shows code) heEquationalView)
      (·.finished = true) heEmit start) demand answer := by
  refine reports_shown_iff (source := HEEquationalExecution.source env policy)
    (target := HEEquationalExecution.theory O code env policy)
    (shows := HEEquationalExecution.Shows code) heEquationalView ?_ ?_ shown (·.finished = true) heEmit demand answer
  · exact ⟨HEEquationalExecution.realize_step code env policy, HEEquationalExecution.reflect_step code env policy⟩
  · exact he_equational_read code

private theorem petta_active_tag (configuration : Eval.Configuration) (names : List String) (parts : List Expr) :
    PeTTaEquationalOnTheStep.encode (.running configuration) names ≠ packet 7 parts := by
  obtain ⟨other, form⟩ := PeTTaEquationalOnTheStep.running_tag configuration names
  rw [form]
  exact fun eq => (by decide : 2 ≠ 7) ((packet_eq_iff _ _ _ _).mp eq).1

private theorem petta_equational_read {O : Type} [DecidableEq O]
    {a b : PeTTaEquationalOnTheStep.State} {mark : SState O}
    (first : PeTTaEquationalOnTheStep.Shows a mark) (second : PeTTaEquationalOnTheStep.Shows b mark) :
    pettaEquationalView a = pettaEquationalView b := by
  obtain ⟨names, vacant, covers, read⟩ := first
  obtain ⟨more, otherVacant, otherCovers, otherRead⟩ := second
  have same := Multiset.singleton_inj.mp (readsAs_unique read.readsAs.1 read.readsAs.2 otherRead.readsAs.2)
  cases a with
  | ready a =>
    cases b with
    | ready b => rfl
    | running b => exact (petta_active_tag b more _ same.symm).elim
  | running a =>
    cases b with
    | ready b => exact (petta_active_tag a names _ same).elim
    | running b =>
      exact congrArg pettaView (EvalOnTheStep.shows_unique ⟨names, vacant, covers, read⟩
        ⟨more, otherVacant, otherCovers, otherRead⟩)

theorem petta_equational_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    {source : PeTTaEquationalOnTheStep.State} {start : SState O}
    (shown : PeTTaEquationalOnTheStep.Shows source start)
    (demand : Demand) (answer : Contracts.OccurrenceObservers.Result Atom demand)
    (entryView : PeTTaEquationalOnTheStep.EntryView := id) :
    reports (completed (sys := PeTTaEquationalOnTheStep.source entryView) pettaEquationalView
      (·.isSome = true) pettaEmit source) demand answer ↔
    reports (readCompleted (sys := PeTTaEquationalOnTheStep.theory O entryView)
      (ofTerm PeTTaEquationalOnTheStep.Shows pettaEquationalView)
      (·.isSome = true) pettaEmit start) demand answer := by
  refine reports_shown_iff (source := PeTTaEquationalOnTheStep.source entryView)
    (target := PeTTaEquationalOnTheStep.theory O entryView) (shows := PeTTaEquationalOnTheStep.Shows)
    pettaEquationalView ?_ ?_ shown (·.isSome = true) pettaEmit demand answer
  · exact ⟨PeTTaEquationalOnTheStep.realize_step (entryView := entryView),
      PeTTaEquationalOnTheStep.reflect_step (entryView := entryView)⟩
  · exact petta_equational_read

section Publications

private def heRoot (world : World) (scope : Context) (waiting seen : List Result) :
    WorldConfiguration Context World :=
  HEFocused.restore ⟨world, scope, .returning waiting, [], [], seen⟩

/-- The already published prefix is not emitted again. Two equal
occurrences are still two publications, at different budgets. -/
theorem he_two_publications (env : WorldEnvironment Context World) (policy : Policy)
    (world : World) (scope : Context) (answer : Result) (prior : List Result) :
    reports (completed (sys := HEControlOnTransform.source env policy) heView (·.finished = true) heEmit
      (heRoot world scope [answer, answer] prior)) .timed [[answer], [answer]] := by
  let first := heRoot world scope [answer, answer] prior
  let second := heRoot world scope [answer] (prior ++ [answer])
  let finish := heRoot world scope [] ((prior ++ [answer]) ++ [answer])
  have publish₁ : (HEControlOnTransform.source env policy).Step first second :=
    HEControlOnTransform.source_of_focus env policy
      (HEControlOnTransform.all_covered _) .publish
  have publish₂ : (HEControlOnTransform.source env policy).Step second finish :=
    HEControlOnTransform.source_of_focus env policy
      (HEControlOnTransform.all_covered _) .publish
  refine ⟨[[answer], [answer]], ⟨finish, .cons ⟨publish₁⟩ (.cons ⟨publish₂⟩ (.refl finish)), rfl, ?_⟩, rfl⟩
  change [heEmit (heView first) (heView second), heEmit (heView second) (heView finish)] = _
  change [(prior ++ [answer]).drop prior.length,
    ((prior ++ [answer]) ++ [answer]).drop (prior ++ [answer]).length] = _
  simp

theorem petta_finishing_batch (world : Effects.State) (answers : List Atom) :
    reports (completed (sys := LiveRegistry.theory) pettaView (·.isSome = true) pettaEmit
      (⟨world, .sequence [] answers, [], [], []⟩ : Eval.Configuration)) .timed [answers] := by
  let start : Eval.Configuration := ⟨world, .sequence [] answers, [], [], []⟩
  let finish : Eval.Configuration := ⟨world, .returned answers, [], [], []⟩
  have step : LiveRegistry.theory.Step start finish := by
    apply (PeTTaExecution.live_rewrite_iff _ _).mpr
    exact (Eval.theory_step_iff _ _ _).mpr rfl
  exact ⟨[answers], ⟨finish, .cons ⟨step⟩ (.refl finish), rfl, rfl⟩, rfl⟩

theorem petta_step_starts_pending {source target : Eval.Configuration}
    (stepped : LiveRegistry.theory.Step source target) : pettaView source = none := by
  have computes := (Eval.theory_step_iff _ _ _).mp ((PeTTaExecution.live_rewrite_iff _ _).mp stepped)
  cases control : source.control <;> try (simp [pettaView, control]; done)
  case returned answers =>
    cases frames : source.frames with
    | nil => simp [Eval.step, control, frames] at computes
    | cons first rest => simp [pettaView, control, frames]

theorem petta_equational_step_starts_pending {source target : PeTTaEquationalOnTheStep.State}
    (stepped : PeTTaEquationalOnTheStep.source.Step source target) :
    pettaEquationalView source = none := by
  change PeTTaEquationalOnTheStep.Transition id source target at stepped
  cases stepped with
  | enter => rfl
  | ordinary display => exact petta_step_starts_pending display

theorem petta_fault_is_not_absence {source : Eval.Configuration} {fault : Effects.Fault}
    (raised : source.control = .fault fault) :
    ¬reports (completed (sys := LiveRegistry.theory) pettaView (·.isSome = true) pettaEmit source) .absence true := by
  rintro ⟨trace, run, _⟩
  refine Contracts.OccurrenceExecution.stuck_is_not_completed (sys := LiveRegistry.theory)
    pettaView (·.isSome = true) pettaEmit ?_ ?_ trace run
  · intro next live
    have stepped := (Eval.theory_step_iff _ _ _).mp ((PeTTaExecution.live_rewrite_iff _ _).mp live)
    simp [Eval.step, raised] at stepped
  · simp [pettaView, raised]

end Publications

end Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations
