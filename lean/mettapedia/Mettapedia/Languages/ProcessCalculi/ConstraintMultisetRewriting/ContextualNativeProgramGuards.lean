import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeResourceQueries

/-!
# Every authored guard compiles to the native program's query list

Equality checks compare terms at the saved information cut. Absence reads
surviving actual inputs and checks prefix creations. Counts validate a
conditional input table and add authored creations. The finite query list
is computed from all authored cuts before successful admission is known.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

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

noncomputable def producerEqualityQuery (body : Body S O Γ sort before after) (index : body.CutIndex)
    (left right : Term (signature S after.declarations) Γ sort) : body.ProducerQuery :=
  liftPoint (ofCondition (fun candidate =>
    instantiate candidate.assignment (instantiate (body.nativeGuardCut index) left) =
      instantiate candidate.assignment (instantiate (body.nativeGuardCut index) right)) none)

noncomputable def producerCheckQueries (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (index : body.CutIndex) : Check (Term (signature S after.declarations) Γ sort) → List body.ProducerQuery
  | .equal left right => [body.producerEqualityQuery index left right]
  | .absent pattern =>
      [body.nativeCutMatchingQuery index pattern ((body.entryCutAt index).taken.image some) ∅,
        body.nativeVirtualAbsenceQuery index pattern]
  | .count pattern number =>
      let table := body.nativeCountTable index occupied produced [] pattern
        ((body.entryCutAt index).taken.image some)
      [table.query (body.nativeCountPredicate index pattern ((body.entryCutAt index).taken.image some)),
        body.nativeCountCheckQuery index pattern table number]

noncomputable def producerGuardQueries (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)) :
    List body.ProducerQuery :=
  (List.finRange body.cuts.length).flatMap fun index =>
    (body.entryCutAt index).view.checks.flatMap (body.producerCheckQueries occupied produced index)

theorem producer_equality_query_iff (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (index : body.CutIndex) (left right : Term (signature S after.declarations) Γ sort) :
    AskData (body.nativeBindingInformation occupied produced [])
        (body.producerEqualityQuery index left right)
        (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present ↔
      ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world (.equal left right) := by
  erw [producerEqualityQuery, lift_point_ask_iff,
    ask_condition_iff _ _ _ (Finset.mem_insert_self _ _)]
  exact (body.native_entry_equal_iff index shapes resources consistent occupied produced [] left right).symm

theorem producer_check_queries_iff (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (index : body.CutIndex) (check : Check (Term (signature S after.declarations) Γ sort)) :
    ContextualConditionalGuards.Ask (body.entryCutAt index).view.locals (body.entryCutAt index).view.problem
        (body.entryCutAt index).view.rows (body.entryCutAt index).view.world check ↔
      ∀ query ∈ body.producerCheckQueries occupied produced index check,
        AskData (body.nativeBindingInformation occupied produced []) query
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present := by
  cases check with
  | equal left right =>
      change _ ↔ ∀ query ∈ [body.producerEqualityQuery index left right], _
      rw [List.forall_mem_singleton]
      exact (body.producer_equality_query_iff shapes resources consistent occupied produced index left right).symm
  | absent pattern =>
      change _ ↔ ∀ query ∈ [_, _], _
      rw [all_pair]
      exact body.native_entry_absence_iff index shapes resources consistent occupied produced [] pattern
  | count pattern number =>
      change _ ↔ ∀ query ∈ [_, _], _
      rw [all_pair]
      exact body.native_entry_count_iff index shapes resources consistent occupied produced [] pattern number

theorem producer_guard_queries_iff (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)) :
    (∀ cut ∈ body.cuts, cut.Holds) ↔
      ∀ query ∈ body.producerGuardQueries occupied produced,
        AskData (body.nativeBindingInformation occupied produced []) query
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied)) (body.nativeBindingState occupied).present := by
  constructor
  · intro source query member
    obtain ⟨index, _valid, atCut⟩ := List.mem_flatMap.mp member
    obtain ⟨check, selected, queried⟩ := List.mem_flatMap.mp atCut
    have cut := (body.entry_cut_at_compare shapes resources index).2.2.mpr
      (source _ (List.get_mem _ _))
    exact (body.producer_check_queries_iff shapes resources consistent occupied produced index check).mp
      (cut check selected) query queried
  · intro checked cut member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    apply (body.entry_cut_at_compare shapes resources index).2.2.mp
    intro check selected
    apply (body.producer_check_queries_iff shapes resources consistent occupied produced index check).mpr
    intro query queried
    exact checked query (List.mem_flatMap.mpr ⟨index, List.mem_finRange _,
      List.mem_flatMap.mpr ⟨check, selected, queried⟩⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
