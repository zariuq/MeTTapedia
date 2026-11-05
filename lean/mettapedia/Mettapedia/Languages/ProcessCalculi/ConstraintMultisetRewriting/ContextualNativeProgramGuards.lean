import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeResourceQueries

/-!
# Every authored guard compiles to the native program's query list

Equality checks compare terms at the saved information cut. Absence reads
surviving actual inputs and checks prefix creations. Counts validate a
conditional input table and add authored creations. The finite query list
is computed from all authored cuts before successful admission is known.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uQ

private theorem all_pair {Q : Type uQ} (predicate : Q → Prop) (left right : Q) :
    (∀ query ∈ [left, right], predicate query) ↔ predicate left ∧ predicate right := by
  constructor
  · intro all
    exact ⟨all _ (List.mem_cons_self ..), all _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · rintro ⟨one, two⟩ query member
    rcases List.mem_cons.mp member with rfl | tail
    · exact one
    · have equal := List.mem_singleton.mp tail
      exact equal ▸ two

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

noncomputable def producerEqualityQuery (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex)
    (left right : Term (signature S after.declarations) Γ sort) : schedule.ProducerQuery :=
  liftPoint (ofCondition (fun candidate =>
    instantiate candidate.assignment (instantiate (schedule.nativeGuardCut index) left) =
      instantiate candidate.assignment (instantiate (schedule.nativeGuardCut index) right)) none)

noncomputable def producerCheckQueries (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (index : schedule.CutIndex) : Check (Term (signature S after.declarations) Γ sort) → List schedule.ProducerQuery
  | .equal left right => [schedule.producerEqualityQuery index left right]
  | .absent pattern =>
      [schedule.nativeCutMatchingQuery index pattern ((schedule.entryCutAt index).taken.image some) ∅,
        schedule.nativeVirtualAbsenceQuery index pattern]
  | .count pattern number =>
      let table := schedule.nativeCountTable index occupied schedule.producerValues [] pattern
        ((schedule.entryCutAt index).taken.image some)
      [table.query (schedule.nativeCountPredicate index pattern ((schedule.entryCutAt index).taken.image some)),
        schedule.nativeCountCheckQuery index pattern table number]

noncomputable def producerGuardQueries (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :
    List schedule.ProducerQuery :=
  (List.finRange schedule.cuts.length).flatMap fun index =>
    (schedule.entryCutAt index).view.checks.flatMap (schedule.producerCheckQueries occupied index)

theorem producer_equality_query_iff (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (index : schedule.CutIndex) (left right : Term (signature S after.declarations) Γ sort) :
    AskData (schedule.nativeBindingInformation occupied schedule.producerValues [])
        (schedule.producerEqualityQuery index left right)
        (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world (.equal left right) := by
  erw [producerEqualityQuery, lift_point_ask_iff,
    ask_condition_iff _ _ _ (Finset.mem_insert_self _ _)]
  exact (schedule.native_entry_equal_iff index shapes resources consistent occupied schedule.producerValues [] left right).symm

theorem producer_check_queries_iff (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (index : schedule.CutIndex) (check : Check (Term (signature S after.declarations) Γ sort)) :
    ContextualConditionalGuards.Ask (schedule.entryCutAt index).view.locals (schedule.entryCutAt index).view.problem
        (schedule.entryCutAt index).view.rows (schedule.entryCutAt index).view.world check ↔
      ∀ query ∈ schedule.producerCheckQueries occupied index check,
        AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) query
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present := by
  cases check with
  | equal left right =>
      change _ ↔ ∀ query ∈ [schedule.producerEqualityQuery index left right], _
      rw [List.forall_mem_singleton]
      exact (schedule.producer_equality_query_iff shapes resources consistent occupied index left right).symm
  | absent pattern =>
      change _ ↔ ∀ query ∈ [_, _], _
      rw [all_pair]
      exact schedule.native_entry_absence_iff index shapes resources consistent occupied schedule.producerValues [] pattern
  | count pattern number =>
      change _ ↔ ∀ query ∈ [_, _], _
      rw [all_pair]
      exact schedule.native_entry_count_iff index shapes resources consistent occupied schedule.producerValues [] pattern number

theorem producer_guard_queries_iff (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) :
    schedule.CutsHold ↔
      ∀ query ∈ schedule.producerGuardQueries occupied,
        AskData (schedule.nativeBindingInformation occupied schedule.producerValues []) query
          (nativeLabels schedule.guardNativeBank (schedule.nativeBindingState occupied)) (schedule.nativeBindingState occupied).present := by
  constructor
  · intro source query member
    obtain ⟨index, _valid, atCut⟩ := List.mem_flatMap.mp member
    obtain ⟨check, selected, queried⟩ := List.mem_flatMap.mp atCut
    have cut := (schedule.entry_cut_at_compare shapes resources index).2.2.mpr
      (source _ (List.get_mem _ _))
    exact (schedule.producer_check_queries_iff shapes resources consistent occupied index check).mp
      (cut check selected) query queried
  · intro checked cut member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    apply (schedule.entry_cut_at_compare shapes resources index).2.2.mp
    intro check selected
    apply (schedule.producer_check_queries_iff shapes resources consistent occupied index check).mpr
    intro query queried
    exact checked query (List.mem_flatMap.mpr ⟨index, List.mem_finRange _,
      List.mem_flatMap.mpr ⟨check, selected, queried⟩⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
