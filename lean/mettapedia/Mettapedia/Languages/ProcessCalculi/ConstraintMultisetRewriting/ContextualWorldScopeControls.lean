import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStepControls

/-!
# Scope ledgers retain continuations and captures across activations

A continuation contains a scope absent from visible rows. The first firing
opens two uses of one physical schema, retains its equation scopes, and
publishes a later schema capturing its rule local. A subsequent activation
keeps that earlier capture while allocating new locals above the ledger.
Omitting the continuation or prior captured scope gives genuine collisions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualScopeSupport
open ContextualActivatedStep
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm ActiveTerm atom pair p
  rawA rawB privateVariable universalRow sharedValue selection occupied split)
open ContextualActivatedStep.Controls (before rows rule outputs afterRows afterOccupied laterSource laterTarget laterSchema)

def initialScopes (name : Nat) : Finset Nat := if name = 42 then {7} else {2}

def initial : Inventory locals captures (O := Nat) [] () where
  configuration := before
  rows := rows
  retained := [observe (generator captures 42)]
  templates := ruleRoots rule

theorem the_initial_footprint_includes_the_continuation_scope :
    footprint locals captures initialScopes initial = {2, 7} := by decide

theorem the_initial_world_has_a_covering_ledger :
    CoveredWorld locals captures initialScopes occupied initial := by
  apply (coveredWorld_iff locals captures initialScopes occupied initial).mpr
  rw [the_initial_footprint_includes_the_continuation_scope]
  decide

theorem the_installed_rule_captures_are_covered :
    RuleCovered (privateScopes initialScopes) occupied rule :=
  rule_covered_from_templates locals captures initialScopes the_initial_world_has_a_covering_ledger rule
    (fun _ member => member)

theorem visible_rows_alone_do_not_cover_the_continuation :
    initial.configuration.present.biUnion (fun occurrence => row locals captures initialScopes (initial.rows occurrence)) = {2} ∧
      7 ∈ footprint locals captures initialScopes initial := by
  constructor
  · decide
  · rw [the_initial_footprint_includes_the_continuation_scope]
    decide

theorem omitting_the_live_continuation_scope_breaks_the_invariant :
    ¬ CoveredWorld locals captures initialScopes {0, 2} initial := by
  intro covered
  have included := (coveredWorld_iff locals captures initialScopes {0, 2} initial).mp covered
  rw [the_initial_footprint_includes_the_continuation_scope] at included
  have impossible := included (by decide : 7 ∈ ({2, 7} : Finset Nat))
  exact (by decide : 7 ∉ ({0, 2} : Finset Nat)) impossible

def firstInventory := afterInventory locals captures occupied selection rule initial outputs
def firstScopes := activeScopes (Local := Nat) initialScopes

theorem the_first_actual_firing_preserves_the_complete_inventory :
    CoveredWorld locals active firstScopes afterOccupied firstInventory :=
  afterInventory_covered locals captures initialScopes occupied selection rule initial outputs
    the_initial_world_has_a_covering_ledger the_installed_rule_captures_are_covered
    ContextualActivatedStep.Controls.the_shared_physical_schema_read_is_a_valid_firing.occurrences
    ContextualActivatedStep.Controls.the_shared_physical_schema_read_is_a_valid_firing.outputs

theorem old_equations_and_both_row_uses_remain_covered :
    footprint locals active firstScopes firstInventory = {2, 7, 8, 9, 10} := by decide

def laterBody : Term (signature base laterSource) [] () :=
  pair (generator laterSource (.inl 0))
    (generator laterSource (.inr (.inl (ScopedVar.at 8 0))))

theorem a_later_schema_records_its_earlier_rule_capture :
    row locals active firstScopes laterSchema = {8} ∧
      term (privateScopes firstScopes) laterBody = {8} := by
  constructor <;> decide

def laterRule : RuleInstance (Term (signature base laterSource) [] ()) :=
  ⟨[], [p (atom laterSource)],
    [(generator laterSource (.inr (.inl (ScopedVar.at 8 0))), atom laterSource)],
    [], []⟩

def published := publish locals active firstInventory (ruleRoots laterRule)
def publishedLedger := publicationLedger locals active firstScopes afterOccupied (ruleRoots laterRule)

theorem publication_retains_earlier_locals_as_captures :
    CoveredWorld locals active firstScopes publishedLedger published :=
  publish_covered locals active firstScopes firstInventory the_first_actual_firing_preserves_the_complete_inventory _

theorem publishing_a_capture_of_scope_eight_needs_no_new_scope : publishedLedger = afterOccupied := by decide

theorem the_later_rule_is_covered_from_its_actual_publication :
    RuleCovered (privateScopes firstScopes) publishedLedger laterRule := by
  apply rule_covered_from_templates locals active firstScopes publication_retains_earlier_locals_as_captures laterRule
  intro root member
  exact List.mem_append_right _ member

def laterSelection : Selection Nat := ⟨[], [7], []⟩
def laterOutputs (_ : Nat) : Term (signature base laterTarget) [] () := atom laterTarget
def secondInventory := afterInventory locals active publishedLedger laterSelection laterRule published laterOutputs
def secondLedger := ContextualActivationScopes.after publishedLedger laterSelection
def secondScopes := activeScopes (Local := Nat) firstScopes

def secondSolution : Assignment laterTarget laterTarget
  | .inl _ => atom laterTarget
  | .inr old => instantiate (ContextualSelectionViews.capturedTarget locals active) (split old)

abbrev SecondAction := ContextualFamilies.action laterTarget [] ()

theorem the_second_firing_is_enabled :
    ContextualGuardedStep.Valid locals active publishedLedger laterSelection laterRule
      published.rows published.configuration laterOutputs := by
  refine { take_distinct := by decide
           output_distinct := by decide
           take_length := rfl
           read_length := rfl
           outputs := rfl
           occurrences := by decide
           solvable := ?_
           checks := ?_ }
  swap
  · apply ContextualFrameUnifier.solvable_of_consistent
    refine ⟨secondSolution, ?_⟩
    change SecondAction.Models secondSolution
      [(generator laterTarget (.inr (.inr 0)), atom laterTarget),
       (p (atom laterTarget), p (generator laterTarget (.inr (.inl (ScopedVar.at 9 0))))),
       (p (pair (atom laterTarget) (atom laterTarget)), p (generator laterTarget (.inr (.inl (ScopedVar.at 10 0))))),
       (generator laterTarget (.inr (.inl (ScopedVar.at 8 0))), atom laterTarget),
       (p (atom laterTarget), p (generator laterTarget (.inl (ScopedVar.at 12 0)))),
       (generator laterTarget (.inr (.inl (ScopedVar.at 8 0))), atom laterTarget)]
    refine (SecondAction.models_cons secondSolution _ _).mpr ⟨?_,
      (SecondAction.models_cons secondSolution _ _).mpr ⟨?_,
      (SecondAction.models_cons secondSolution _ _).mpr ⟨?_,
      (SecondAction.models_cons secondSolution _ _).mpr ⟨?_,
      (SecondAction.models_cons secondSolution _ _).mpr ⟨?_,
      (SecondAction.models_cons secondSolution _ _).mpr ⟨?_, SecondAction.models_nil _⟩⟩⟩⟩⟩⟩
    all_goals with_unfolding_all rfl
  · intro check member
    exact False.elim (List.not_mem_nil member)

theorem two_actual_family_changes_preserve_the_complete_inventory :
    CoveredWorld locals laterTarget secondScopes secondLedger secondInventory :=
  afterInventory_covered locals active firstScopes publishedLedger laterSelection laterRule published laterOutputs
    publication_retains_earlier_locals_as_captures the_later_rule_is_covered_from_its_actual_publication
    the_second_firing_is_enabled.occurrences the_second_firing_is_enabled.outputs

theorem the_second_reservation_does_not_reuse_the_first_rule_or_read_scopes :
    secondLedger = {0, 2, 7, 8, 9, 10, 11, 12} := by decide

theorem an_earlier_rule_local_keeps_its_scope_after_a_further_capture_embedding :
    term secondScopes
      (instantiate (ContextualSelectionViews.capturedTarget locals active)
        (generator active (.inl (ScopedVar.at 8 0)))) = {8} := by decide

theorem missing_an_earlier_captured_scope_is_detected :
    ¬ row locals active firstScopes laterSchema ⊆ ({2, 7, 9, 10} : Finset Nat) := by
  rw [a_later_schema_records_its_earlier_rule_capture.1]
  decide

def collisionLedger : Finset Nat := {0, 2, 3, 4, 5, 6, 7}

theorem an_incomplete_ledger_can_reuse_an_earlier_captured_scope :
    ContextualActivationScopes.scopeAt collisionLedger (ContextualActivationScopes.rulePort laterSelection) = 8 ∧
      8 ∈ row locals active firstScopes laterSchema := by
  constructor
  · decide
  · rw [a_later_schema_records_its_earlier_rule_capture.1]
    decide

theorem a_complete_ledger_prevents_that_collision :
    ContextualActivationScopes.scopeAt publishedLedger
      (ContextualActivationScopes.rulePort laterSelection) ∉ footprint locals active firstScopes published :=
  subsequent_reservation_avoids_every_root locals active firstScopes
    publication_retains_earlier_locals_as_captures laterSelection _

theorem solver_helpers_then_further_rules_get_distinct_scopes :
    ContextualFreshFrameScopeLedger.helperScope afterOccupied = 11 ∧
      ContextualActivationScopes.scopeAt
        (ContextualFreshFrameScopeLedger.helperLedger afterOccupied)
        (ContextualActivationScopes.rulePort laterSelection) = 12 := by decide

def guardOnlyRule : RuleInstance RawTerm :=
  ⟨[], [], [], [.equal privateVariable privateVariable], []⟩

def guardOnlySelection : Selection Nat := ⟨[], [], []⟩
def guardOnlyInventory := afterInventory locals captures occupied guardOnlySelection guardOnlyRule initial outputs

theorem a_check_only_variable_is_not_lost_from_the_scope_inventory :
    equationScopes firstScopes guardOnlyInventory.configuration.equations = {2} ∧
      observations firstScopes guardOnlyInventory.retained = {7, 8} ∧
      8 ∈ footprint locals active firstScopes guardOnlyInventory := by
  constructor
  · decide
  · constructor <;> decide

theorem the_check_only_rule_is_an_actual_guarded_firing :
    ContextualGuardedStep.Valid locals captures occupied guardOnlySelection guardOnlyRule
      initial.rows initial.configuration outputs := by
  refine { take_distinct := by decide
           output_distinct := by decide
           take_length := rfl
           read_length := rfl
           outputs := rfl
           occurrences := by decide
           solvable := ?_
           checks := ?_ }
  swap
  · apply ContextualFrameUnifier.solvable_of_consistent
    refine ⟨split, ?_⟩
    change (ContextualFamilies.action active [] ()).Models split
      [(generator active (.inr 0), atom active)]
    refine ((ContextualFamilies.action active [] ()).models_cons split _ _).mpr ⟨?_,
      (ContextualFamilies.action active [] ()).models_nil _⟩
    with_unfolding_all rfl
  · intro check member
    have same : check = .equal (generator active (.inl (ScopedVar.at 8 0)))
      (generator active (.inl (ScopedVar.at 8 0))) := List.mem_singleton.mp member
    subst check
    exact ContextualGuardSemantics.Ask.equal_refl locals _ _ _ _

theorem retaining_all_checks_preserves_ledger_coverage_even_with_no_output :
    CoveredWorld locals active firstScopes
      (ContextualActivationScopes.after occupied guardOnlySelection) guardOnlyInventory := by
  apply afterInventory_covered locals captures initialScopes occupied guardOnlySelection guardOnlyRule initial outputs
    the_initial_world_has_a_covering_ledger _
    the_check_only_rule_is_an_actual_guarded_firing.occurrences
    the_check_only_rule_is_an_actual_guarded_firing.outputs
  apply (ruleRoots_covered_iff (privateScopes initialScopes) occupied guardOnlyRule).mp
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger.Controls
