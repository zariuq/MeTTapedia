import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOutputVisibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathSnapshotControls

/-!
# A produced variable is shared on later reads; an old schema remains schematic

An actual empty-input producer publishes its fresh rule variable as shared
data. Two later reads cannot instantiate that one identity independently.
The original schematic row still admits independent instances. Raw payload
visibility and application of the computed answer are tested separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProducerRowControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualExecution ContextualWorldScopeLedger ContextualScopeSupport
open ContextualSelectionViews.Controls
  (base locals captures active RawTerm atom pair p privateVariable universalRow)
open ContextualGuardedExecutionControls (initial)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def selection : Selection Nat := ⟨[], [], [99]⟩
def rule : RuleInstance RawTerm := ⟨[], [], [], [], [privateVariable]⟩
def sourceValue : Term (signature base active) [] () := generator active (.inl (ScopedVar.at 8 0))
def outputs (_ : Nat) := sourceValue
def problem := ContextualActivatedStep.problem locals captures initial.occupied selection rule
  initial.inventory.rows initial.inventory.configuration
def update := ContextualFrameWorklist.identity (ContextualResidual.observeProblem problem)

theorem rule_covered : RuleCovered (privateScopes initial.scopes) initial.occupied rule := by
  apply (ruleRoots_covered_iff (privateScopes initial.scopes) initial.occupied rule).mp
  change (∅ : Finset Nat) ⊆ initial.occupied
  exact Finset.empty_subset _

theorem admitted : ContextualGuardedStep.Requirements locals captures initial.occupied selection rule
    initial.inventory.rows initial.inventory.configuration outputs := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, ?_, by decide +kernel, fun _ member => by cases member⟩
  with_unfolding_all rfl

def after : Endpoint locals Nat [] () := computedTarget locals initial rule selection outputs rule_covered admitted update
def firing : Firing locals initial after := ⟨rule, rule_covered, selection, outputs, 0, update, admitted, rfl, rfl, rfl⟩

def stored : Term (signature base after.declarations) [] () :=
  generator after.declarations (.inl (.inl (ScopedVar.at 8 0)))
def returned : after.Names := .inr (.inl (.inl (ScopedVar.at 8 0)))

theorem the_actual_producer_stores_its_local_as_a_shared_value :
    after.inventory.rows 99 = .shared stored ∧ 99 ∈ after.inventory.configuration.present := by
  constructor
  · with_unfolding_all rfl
  · exact firing.produced_row_is_present (by decide +kernel)

theorem returned_names_are_not_automatically_in_the_stored_payload :
    returned ∉ support stored := by
  intro present
  change returned ∈ [.inl (.inl (ScopedVar.at 8 0))] at present
  have impossible := List.mem_singleton.mp present
  cases impossible

theorem applying_the_actual_answer_can_reference_a_returned_declaration :
    returned ∈ support (instantiate (ContextualComputedFreshFrame.answer update) stored) := by
  with_unfolding_all exact List.mem_singleton_self _

theorem two_future_views_share_the_producer_variable :
    ContextualStoredRows.viewAt locals after.declarations 20 (after.inventory.rows 99) =
      ContextualStoredRows.viewAt locals after.declarations 21 (after.inventory.rows 99) :=
  firing.produced_shared_views_agree_at_any_two_future_scopes (by decide +kernel) 20 21

abbrev next := ContextualActivatedStep.target locals after.declarations
abbrev rawNext := ContextualActivatedStep.source locals after.declarations
def a : Term (signature base next) [] () := atom next
def b : Term (signature base next) [] () := pair a a
def readTwice (occurrence : Nat) : Selection Nat := ⟨[], [occurrence, occurrence], []⟩
def readRule : RuleInstance (Term (signature base rawNext) [] ()) :=
  ⟨[], [p (atom rawNext), p (pair (atom rawNext) (atom rawNext))], [], [], []⟩
def readProblem (occurrence : Nat) := ContextualActivatedStep.problem locals after.declarations after.occupied
  (readTwice occurrence) readRule after.inventory.rows after.inventory.configuration
def shared : Term (signature base next) [] () :=
  instantiate (ContextualSelectionViews.capturedTarget locals after.declarations) stored
def local11 : Term (signature base next) [] () := generator next (.inl (ScopedVar.at 11 0))
def local12 : Term (signature base next) [] () := generator next (.inl (ScopedVar.at 12 0))

theorem actual_shared_reads_use_one_shared_producer_identity :
    readProblem 99 = [(p a, shared), (p b, shared)] := by with_unfolding_all rfl

theorem the_actual_shared_reads_cannot_choose_two_independent_instances
    {Future : Type} {future : Future → MetaArity base} (candidate : Assignment next future) :
    ¬ ContextualFrameUnifier.Models candidate (readProblem 99) := by
  intro solved
  rw [actual_shared_reads_use_one_shared_producer_identity] at solved
  have first := solved (p a, shared) (by simp)
  have second := solved (p b, shared) (by simp)
  have same := first.trans second.symm
  have sizes := congrArg termSize same
  change 3 = 5 at sizes
  omega

theorem actual_schema_reads_keep_their_two_private_scopes :
    readProblem 7 = [(p a, p local11), (p b, p local12)] := by with_unfolding_all rfl

def schemaModel : Assignment next next
  | .inl name => if name.scope = 12 then b else a
  | .inr name => generator next (.inr name)

theorem the_retained_schema_still_admits_both_independent_instances :
    ContextualFrameUnifier.Models schemaModel (readProblem 7) := by
  rw [actual_schema_reads_keep_their_two_private_scopes]
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> with_unfolding_all rfl

theorem the_exact_old_schema_occurrence_survives_the_actual_two_event_path :
    7 ∈ ContextualPathSnapshotControls.final.inventory.configuration.present ∧
      ContextualPathSnapshotControls.final.inventory.rows 7 =
        (initial.inventory.rows 7).map locals (pathAssignment ContextualPathSnapshotControls.combinedPath) := by
  apply persistent_row_along_path ContextualPathSnapshotControls.combinedPath (by decide +kernel)
  intro selected member
  change selected ∈ [ContextualGuardedStep.Controls.selection, ContextualPathSnapshotControls.consume] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

theorem the_consumed_occurrence_fails_the_persistence_hypothesis :
    ¬ NeverTaken ContextualPathSnapshotControls.consumePath 99 := by
  intro untaken
  exact untaken ContextualPathSnapshotControls.consume (List.mem_singleton_self _)
    (by decide +kernel)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProducerRowControls
