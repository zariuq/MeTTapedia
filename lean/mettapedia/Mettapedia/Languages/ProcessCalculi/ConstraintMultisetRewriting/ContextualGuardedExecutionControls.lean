import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStepControls

/-!
# A completed contextual edge retains its original all-future count ask

The physical row is a schema. Its count is checked before production and
does not instantiate the caller. An unsupported equality ask cannot become
an edge even though the generated output would be closed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedExecutionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualScopeSupport ContextualWorldScopeLedger
open ContextualSelectionViews.Controls (base locals captures active p rawA atom)
open ContextualGuardedStep.Controls (bare rows countRule equalityRule selection occupied outputs)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (ContextualExecution.Endpoint locals Nat [] ()) :=
  ContextualExecution.graph locals Nat

def scopes (_ : Nat) : Finset Nat := ∅
def inventory : Inventory locals captures (O := Nat) [] () := ⟨bare, rows, [], []⟩
def initial : ContextualExecution.Endpoint locals Nat [] () where
  Names := Nat
  equality := inferInstance
  declarations := captures
  scopes := scopes
  occupied := occupied
  inventory := inventory
  covered := (coveredWorld_iff locals captures scopes occupied inventory).mpr (by decide +kernel)

theorem rule_covered : RuleCovered (privateScopes scopes) occupied countRule := by
  apply (ruleRoots_covered_iff (privateScopes scopes) occupied countRule).mp
  decide +kernel

theorem admitted : ContextualGuardedStep.Requirements locals captures occupied selection
    countRule rows bare outputs := by
  have valid := ContextualGuardedStep.Controls.the_schematic_count_guard_has_an_actual_firing
  exact ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
    valid.outputs, valid.occurrences, valid.checks⟩

def update := ContextualFrameWorklist.identity (ContextualResidual.observeProblem
  (ContextualActivatedStep.problem locals captures occupied selection countRule rows bare))

def after : ContextualExecution.Endpoint locals Nat [] () :=
  ContextualExecution.computedTarget locals initial countRule selection outputs rule_covered admitted update

def firing : ContextualExecution.Firing locals initial after where
  rule := countRule
  ruleCovered := rule_covered
  selection := selection
  outputs := outputs
  fuel := 0
  update := update
  admitted := admitted
  computed := rfl
  empty := rfl
  destination := rfl

theorem the_guarded_edge_produces_and_retains_its_original_ask :
    after.inventory.configuration.present = {7, 99} ∧
      firing.rule.checks = [.count (p rawA) 1] ∧
      ContextualGuardSemantics.Ask locals
        (ContextualActivatedStep.problem locals captures occupied selection countRule rows bare)
        (ContextualGuardedStep.guardRows locals captures rows) bare.present (.count (p (atom active)) 1) ∧
      ContextualExecution.selections (Quiver.Hom.toPath firing) = [selection] :=
  ⟨by decide +kernel, rfl,
    ContextualGuardedStep.Controls.the_schematic_count_guard_asks_over_every_future_model, rfl⟩

theorem the_unsupported_guard_cannot_be_admitted :
    ¬ ContextualGuardedStep.Requirements locals captures occupied selection
      equalityRule rows bare outputs := by
  intro admission
  have ask := admission.checks (.equal (generator active (.inr 0)) (atom active))
    (List.mem_singleton_self _)
  have same := ask (ScopedVar Nat ⊕ Nat) active (generator active)
    (fun _ member => False.elim (List.not_mem_nil member))
  change generator active (.inr 0) = atom active at same
  have heads := (Term.op.inj same).1
  cases heads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedExecutionControls
