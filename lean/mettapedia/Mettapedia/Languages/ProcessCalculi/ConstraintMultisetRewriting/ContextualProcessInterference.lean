import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInformation

/-!
# Resource-disjoint events can interfere through equations and watched rows

A closed count pattern has no captured variables, but its watched shared row
does. A tell can therefore enable that count without changing the physical
world. The source firing below is an actual completed contextual computation,
not a synthetic state update. Transporting the earlier question keeps its
old equation cut, so later information cannot retroactively discharge it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInterference

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualGuardMatching ContextualSchedulePromotion
open ContextualWorldScopeLedger ContextualScopeSupport
open ContextualSelectionViews.Controls (base locals captures active atom p sharedValue)
open ContextualGuardSemantics.Controls (CapturedTerm capturedAtom query sharedRows world assignedA)
open ContextualPathSnapshotControls (tell tellRule tellOutputs)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def bound : EquationStore CapturedTerm := [(sharedValue, capturedAtom)]

theorem a_closed_pattern_can_have_a_hidden_row_dependency :
    support query = [] ∧ support (p sharedValue) = [0] := by
  constructor <;> with_unfolding_all rfl

theorem binding_a_watched_row_entails_the_count :
    ContextualGuardSemantics.Ask locals bound sharedRows world (.count query 1) := by
  intro Next next candidate model
  have same := model (sharedValue, capturedAtom) (List.mem_singleton_self _)
  have matched : Matches locals candidate (instantiate candidate query) (sharedRows 7) := by
    change instantiate candidate (p capturedAtom) = instantiate candidate (p sharedValue)
    have result := congrArg (p (declaration := next)) same.symm
    exact result
  exact (congrArg Finset.card
    (ContextualGuardSemantics.Controls.singleton_region next candidate sharedRows query matched)).trans
      (by decide : ({7} : Finset Nat).card = 1)

theorem same_world_different_information_changes_the_guard :
    ¬ ContextualGuardSemantics.Ask locals ([] : EquationStore CapturedTerm) sharedRows world (.count query 1) ∧
      ContextualGuardSemantics.Ask locals bound sharedRows world (.count query 1) :=
  ⟨ContextualGuardSemantics.Controls.an_unknown_shared_row_does_not_entail_count_one,
    binding_a_watched_row_entails_the_count⟩

def inventory : Inventory locals captures (O := Nat) [] () := ⟨⟨[], world⟩, sharedRows, [], []⟩
def initial : Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := ContextualGuardedExecutionControls.scopes
  occupied := ContextualGuardedStep.Controls.occupied
  inventory := inventory
  covered := (coveredWorld_iff locals captures _ _ inventory).mpr (by decide +kernel)

theorem tell_rule_covered : RuleCovered (privateScopes initial.scopes) initial.occupied tellRule :=
  ContextualPathSnapshotControls.tellRule_covered

theorem tell_admitted : ContextualGuardedStep.Requirements locals captures initial.occupied tell tellRule
    initial.inventory.rows initial.inventory.configuration tellOutputs := by
  exact ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel, fun _ member => by cases member⟩

theorem tell_patterned : ContextualPatternFragment.ProblemPattern
    (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures initial.occupied tell tellRule
      initial.inventory.rows initial.inventory.configuration)) := by
  apply (ContextualPatternFragment.checkProblem_iff _).mp
  decide +kernel

def beforeQuestion : Question locals (O := Nat) [] () :=
  ⟨Nat, captures, [], sharedRows, world, .count query 1⟩
def boundQuestion : Question locals (O := Nat) [] () :=
  ⟨Nat, captures, bound, sharedRows, world, .count query 1⟩

theorem an_actual_equation_only_firing_changes_the_current_count_but_not_the_old_cut :
    ∃ target : Endpoint locals Nat [] (), ∃ firing : Firing locals initial target,
      firing.selection = tell ∧ firing.selection.taken = [] ∧ firing.selection.read = [] ∧
      firing.selection.made = [] ∧ target.inventory.configuration.present = world ∧
      ¬ (beforeQuestion.map (pathAssignment (Quiver.Hom.toPath firing))).Holds locals ∧
      ContextualGuardSemantics.Ask locals target.inventory.configuration.equations target.inventory.rows
        target.inventory.configuration.present
        ((Check.count query 1).map (instantiate (pathAssignment (Quiver.Hom.toPath firing)))) := by
  obtain ⟨fuel, solved | refused⟩ :=
    ContextualTransportedActivation.solve_or_refute locals captures tell_admitted tell_patterned
  · obtain ⟨update, returned⟩ := solved
    let target := computedTarget locals initial tellRule tell tellOutputs tell_rule_covered tell_admitted update
    let firing : Firing locals initial target :=
      ⟨tellRule, tell_rule_covered, tell, tellOutputs, fuel, update, tell_admitted,
        returned.computed, returned.empty, rfl⟩
    let path : Quiver.Path initial target := Quiver.Hom.toPath firing
    refine ⟨target, firing, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · change MeTTaCalculus.OccurrenceCommits.fire world (tell.commit (T := Nat)) = world
      simp [MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, tell]
    · intro accepted
      exact ContextualGuardSemantics.Controls.an_unknown_shared_row_does_not_entail_count_one
        ((Question.holds_extension_iff beforeQuestion (pathExtension path)).mp accepted)
    · have admitted := Question.holds_map boundQuestion (pathAssignment path)
        binding_a_watched_row_entails_the_count
      exact admitted
  · obtain ⟨impossible, _computed⟩ := refused
    apply False.elim
    let constantModel : Assignment active active := fun name => match name with
      | .inl _ => atom active
      | .inr _ => atom active
    apply impossible active constantModel
    apply (ContextualResidual.models_observeProblem _ _).mpr
    intro equation member
    change equation ∈ [(generator active (.inr 0), atom active)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessInterference
