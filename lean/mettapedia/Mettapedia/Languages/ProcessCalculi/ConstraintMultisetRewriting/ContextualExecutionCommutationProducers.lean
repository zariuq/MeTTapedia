import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionTransport

/-!
# Actual scoped symbolic producers and their capture transport

This first commutation profile has no takes, reads, tells or guards and an
empty incoming equation store. Output terms may contain private locals,
caller captures and binders. The source worklist really returns at fuel zero;
its complete returned declaration copy is retained in the target endpoint.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

structure Producer (before : Endpoint locals O Γ sort) where
  made : List O
  distinct : made.Nodup
  fresh : Disjoint made.toFinset before.inventory.configuration.present
  value : O → Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort
  covered : ∀ occurrence ∈ made, Covered (privateScopes before.scopes) before.occupied (value occurrence)

namespace Producer

variable {before : Endpoint locals O Γ sort}

def selection (producer : Producer before) : Selection O := ⟨[], [], producer.made⟩
def rule (producer : Producer before) :=
  (⟨[], [], [], [], producer.made.map producer.value⟩ : RuleInstance
    (Term (signature S (ContextualSelectionViews.source locals before.declarations)) Γ sort))
def scope (producer : Producer before) :=
  ContextualActivationScopes.scopeAt before.occupied (ContextualActivationScopes.rulePort producer.selection)
def outputs (producer : Producer before) : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort :=
  fun occurrence => ContextualFreshening.termAt locals before.declarations producer.scope (producer.value occurrence)

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem rule_covered (producer : Producer before) :
    RuleCovered (privateScopes before.scopes) before.occupied producer.rule := by
  intro value member
  change value ∈ producer.made.map producer.value at member
  obtain ⟨occurrence, present, rfl⟩ := List.mem_map.mp member
  exact producer.covered occurrence present

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem problem_empty (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    ContextualActivatedStep.problem locals before.declarations before.occupied producer.selection producer.rule
      before.inventory.rows before.inventory.configuration = [] := by
  simp [ContextualActivatedStep.problem, ContextualActivatedStep.frame, ContextualActivatedStep.prepared,
    ContextualSelectionViews.prepare, rule, selection, ContextualFreshening.ruleAt, RuleInstance.map,
    ContextualActivatedStep.useEquations, Selection.equations, empty, ContextualFrameUnifier.mapProblem]

def prepared (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    Prepared locals before where
  rule := producer.rule
  ruleCovered := producer.rule_covered
  selection := producer.selection
  outputs := producer.outputs
  formation := by
    refine ⟨rfl, rfl, ?_⟩
    exact (List.map_map ..).symm
  resources := by
    apply (ContextualInteractionFactors.resources_iff producer.outputs producer.selection before.inventory.configuration.present).mpr
    refine ⟨List.nodup_nil, producer.distinct, ?_⟩
    refine ⟨Finset.empty_subset _, Finset.empty_subset _, Finset.disjoint_empty_left _,
      producer.fresh, ?_⟩
    intro query member
    cases member
  fuel := 0
  update := by
    letI := before.equality
    exact ContextualFrameWorklist.identity (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied producer.selection producer.rule
        before.inventory.rows before.inventory.configuration))
  computed := rfl
  finished := by
    change ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied producer.selection producer.rule
        before.inventory.rows before.inventory.configuration) = []
    rw [producer.problem_empty empty]
    rfl

def target (producer : Producer before) (empty : before.inventory.configuration.equations = []) :=
  (producer.prepared empty).target

theorem checks (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    Checked locals (producer.prepared empty).questions := by
  intro question member
  cases member

def firing (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    Firing locals before (producer.target empty) :=
  (producer.prepared empty).firing (producer.checks empty)

theorem target_world (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    (producer.target empty).inventory.configuration.present =
      before.inventory.configuration.present ∪ producer.made.toFinset := by
  change (before.inventory.configuration.present \ (∅ : Finset O)) ∪ producer.made.toFinset = _
  rw [Finset.sdiff_empty]

theorem target_empty (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    (producer.target empty).inventory.configuration.equations = [] := by
  change ContextualFrameUnifier.mapProblem _
    (ContextualActivatedStep.problem locals before.declarations before.occupied producer.selection producer.rule
      before.inventory.rows before.inventory.configuration) = []
  rw [producer.problem_empty empty]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem captures_keep_scopes (producer : Producer before)
    (empty : before.inventory.configuration.equations = []) :
    Respects before.scopes (producer.target empty).scopes
      (ContextualExecutionCommutationNames.intoCapture locals before.declarations) := by
  intro name
  change term (producer.target empty).scopes (generator _ (ContextualExecutionCommutationNames.capture name)) ⊆ _
  rw [term_generator]
  exact Finset.Subset.refl _

theorem target_retains_ledger (producer : Producer before)
    (empty : before.inventory.configuration.equations = []) : before.occupied ⊆ (producer.target empty).occupied :=
  Finset.Subset.trans (ContextualActivationScopes.old_scopes_retained before.occupied producer.selection)
    (ContextualFreshFrameScopeLedger.old_scopes_retained _)

/-- Reuse a source producer after a disjoint producer. Capture transport is
computed through the actual returned frame; private locals remain private. -/
def after (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) : Producer (first.target empty) where
  made := second.made
  distinct := second.distinct
  fresh := by rw [first.target_world empty]; exact Finset.disjoint_union_right.mpr ⟨second.fresh, separate⟩
  value occurrence := instantiate (ContextualStoredRows.liftCaptures locals
    (ContextualExecutionCommutationNames.intoCapture locals before.declarations)) (second.value occurrence)
  covered occurrence member :=
    (covered_instantiate_of_respects _ _ _ _
      (respects_liftCaptures locals before.scopes (first.target empty).scopes
        (ContextualExecutionCommutationNames.intoCapture locals before.declarations)
        (first.captures_keep_scopes empty)) (second.covered occurrence member)).mono
          (first.target_retains_ledger empty)

def twoPath (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    Quiver.Path before ((first.after second empty separate).target (first.target_empty empty)) :=
  (Quiver.Hom.toPath (first.firing empty)).comp
    (Quiver.Hom.toPath ((first.after second empty separate).firing (first.target_empty empty)))

theorem two_path_really_runs_both_producers (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    ContextualExecution.selections (first.twoPath second empty separate) = [first.selection, second.selection] ∧
      ContextualExecution.fuels (first.twoPath second empty separate) = [0, 0] := by
  constructor <;> rfl

end Producer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
