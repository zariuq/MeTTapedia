import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger

/-!
# Full inventory endpoints of actual family-changing contextual executions

An endpoint packages the existing world inventory, declaration family and
coverage ledger. A selected firing retains the original admission, actual
worklist result and completed update. Its target is computed by the existing
activation/inventory operations. This adds no transition semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameUpdate ContextualWorldScopeLedger ContextualFreshFrameScopeLedger

variable {S : Signature} {Local : Type} (locals : Local → MetaArity S) (O : Type)

structure Endpoint (context : Ctx S) (sort : S.Srt) : Type 1 where
  Names : Type
  equality : DecidableEq Names
  declarations : Names → MetaArity S
  scopes : Names → Finset Nat
  occupied : Finset Nat
  inventory : Inventory locals declarations (O := O) context sort
  covered : CoveredWorld locals declarations scopes occupied inventory

namespace Endpoint

variable {locals O} {Γ : Ctx S} {sort : S.Srt}

theorem configuration_heq {first second : Endpoint locals O Γ sort} (same : first = second) :
    HEq first.inventory.configuration second.inventory.configuration := by
  cases same
  rfl

theorem rows_heq {first second : Endpoint locals O Γ sort} (same : first = second) :
    HEq first.inventory.rows second.inventory.rows := by
  cases same
  rfl

end Endpoint

variable {O} [DecidableEq O] [DecidableEq Local] {Γ : Ctx S} {sort : S.Srt}

def computedTarget (before : Endpoint locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (ruleCovered : RuleCovered (ContextualScopeSupport.privateScopes before.scopes) before.occupied rule)
    (admitted : ContextualGuardedStep.Requirements locals before.declarations before.occupied
      selection rule before.inventory.rows before.inventory.configuration outputs)
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
        before.inventory.rows before.inventory.configuration))) : Endpoint locals O Γ sort where
  Names := (Mettapedia.Logic.LP.ScopedVar Local ⊕ before.Names) ⊕ (update.Variables ⊕ Empty)
  equality := by
    letI := before.equality
    letI := update.equality
    infer_instance
  declarations := ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations)
    update.declaration
  scopes := frameScopes (ContextualScopeSupport.activeScopes before.scopes)
    (helperScope (ContextualActivationScopes.after before.occupied selection))
  occupied := helperLedger (ContextualActivationScopes.after before.occupied selection)
  inventory := mapInventory locals (ContextualActivatedStep.target locals before.declarations)
    (ContextualComputedFreshFrame.includeSource update)
    (afterInventory locals before.declarations before.occupied selection rule before.inventory outputs)
  covered := computed_activation_inventory_covered locals before.declarations before.scopes before.occupied
    selection rule before.inventory outputs before.covered ruleCovered admitted update

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

structure Firing (before after : Endpoint locals O Γ sort) where
  rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)
  ruleCovered : RuleCovered (ContextualScopeSupport.privateScopes before.scopes) before.occupied rule
  selection : Selection O
  outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort
  fuel : Nat
  update : Update (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
      before.inventory.rows before.inventory.configuration))
  admitted : ContextualGuardedStep.Requirements locals before.declarations before.occupied
    selection rule before.inventory.rows before.inventory.configuration outputs
  computed : letI := before.equality
    ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals before.declarations)
      (ContextualResidual.observeProblem
        (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
          before.inventory.rows before.inventory.configuration)) = .residual update
  empty : update.remaining = []
  destination : after = computedTarget locals before rule selection outputs ruleCovered admitted update

namespace Firing

variable {locals} {before after : Endpoint locals O Γ sort}

/-- Every edge recovers the original actual completed-run admission. -/
theorem returned (firing : Firing locals before after) :
    letI := before.equality
    ContextualTransportedActivation.FromRun locals before.declarations firing.fuel before.occupied firing.selection
      firing.rule before.inventory.rows before.inventory.configuration firing.outputs firing.update := by
  let _ := before.equality
  exact ContextualTransportedActivation.from_run locals before.declarations firing.admitted
    firing.update firing.computed firing.empty

theorem native_configuration (firing : Firing locals before after) :
    HEq after.inventory.configuration
      (ContextualTransportedActivation.result locals before.declarations
        (ContextualComputedFreshFrame.includeSource firing.update) before.occupied firing.selection firing.rule
          before.inventory.rows before.inventory.configuration) :=
  Endpoint.configuration_heq firing.destination

theorem native_rows (firing : Firing locals before after) :
    HEq after.inventory.rows (ContextualTransportedActivation.resultRows locals before.declarations
      (ContextualComputedFreshFrame.includeSource firing.update) firing.selection firing.outputs before.inventory.rows) :=
  Endpoint.rows_heq firing.destination

theorem actual_helper_ledger (firing : Firing locals before after) :
    after.occupied = helperLedger (ContextualActivationScopes.after before.occupied firing.selection) :=
  congrArg Endpoint.occupied firing.destination

end Firing

/-- A semantically admitted structural-pattern event constructs an actual
completed edge, including its computed target inventory and helper family.
The premise supplies neither a solver answer nor a source execution. -/
theorem realize_semantic_admission
    (before : Endpoint locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (ruleCovered : RuleCovered (ContextualScopeSupport.privateScopes before.scopes) before.occupied rule)
    (admitted : ContextualGuardedStep.Valid locals before.declarations before.occupied
      selection rule before.inventory.rows before.inventory.configuration outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
        before.inventory.rows before.inventory.configuration))) :
    ∃ after : Endpoint locals O Γ sort, ∃ firing : Firing locals before after,
      firing.rule = rule ∧ firing.selection = selection ∧ firing.outputs = outputs := by
  let _ := before.equality
  obtain ⟨fuel, update, returned⟩ :=
    (ContextualTransportedActivation.semantic_admission_iff_completed_run locals before.declarations patterned).mp admitted
  let after := computedTarget locals before rule selection outputs ruleCovered admitted.toRequirements update
  let firing : Firing locals before after :=
    ⟨rule, ruleCovered, selection, outputs, fuel, update, admitted.toRequirements,
      returned.computed, returned.empty, rfl⟩
  exact ⟨after, firing, rfl, rfl, rfl⟩

namespace Firing

variable {locals} {before after : Endpoint locals O Γ sort}

/-- Actual completed edges do not invent semantic admission. This direction
also covers successful computations outside the complete pattern fragment. -/
theorem semantic_admission (firing : Firing locals before after) :
    ContextualGuardedStep.Valid locals before.declarations before.occupied
      firing.selection firing.rule before.inventory.rows before.inventory.configuration firing.outputs := by
  let _ := before.equality
  exact ContextualTransportedActivation.FromRun.semantic_admission locals before.declarations firing.returned

end Firing
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution
