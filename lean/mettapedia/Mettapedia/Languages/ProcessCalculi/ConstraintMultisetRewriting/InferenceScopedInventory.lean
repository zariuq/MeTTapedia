import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedReturned
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger

/-!
# The full scope inventory accompanies actual inference solver returns

Reservations include actual configuration equations, occupied rows, retained
heterogeneous continuation roots and stored-template captures. The returned
helper namespace and all prepared ports remain in the ledger. Rigid inference
data do not justify dropping unrelated retained or template roots.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedInventory

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualScopeSupport
open ContextualWorldScopeLedger
open ContextualFreshFrameScopeLedger
open ContextualFrameUpdate
open InferenceRequestExecution (Occurrence)
open ScopedInferenceValues (Ready base encode)

variable {Local Shared : Type}
  (locals : Local → MetaArity base) (captures : Shared → MetaArity base)

def inventory (readyLabel : Occurrence → Ready) (state : Configuration Ready Occurrence)
    (retained : List (Observation base captures))
    (templates : List (Observation base (ContextualActivatedStep.source locals captures)))
    (extra : EquationStore (Term (signature base captures) [] ()) := []) :
    Inventory locals captures (O := Occurrence) [] () where
  configuration := ContextualRigidActivation.withFrame captures encode extra state
  rows := ContextualRigidActivation.rows locals captures encode readyLabel
  retained := retained
  templates := templates

def reserve (scopes : Shared → Finset Nat) (old : Finset Nat)
    (readyLabel : Occurrence → Ready) (state : Configuration Ready Occurrence)
    (retained : List (Observation base captures))
    (templates : List (Observation base (ContextualActivatedStep.source locals captures)))
    (extra : EquationStore (Term (signature base captures) [] ()) := []) : Finset Nat :=
  old ∪ footprint locals captures scopes (inventory locals captures readyLabel state retained templates extra)

theorem reserved_world (scopes : Shared → Finset Nat) (old : Finset Nat)
    (readyLabel : Occurrence → Ready) (state : Configuration Ready Occurrence)
    (retained : List (Observation base captures))
    (templates : List (Observation base (ContextualActivatedStep.source locals captures)))
    (extra : EquationStore (Term (signature base captures) [] ()) := []) :
    CoveredWorld locals captures scopes (reserve locals captures scopes old readyLabel state retained templates extra)
      (inventory locals captures readyLabel state retained templates extra) :=
  (coveredWorld_iff locals captures scopes _ _).mpr Finset.subset_union_right

theorem source_rule_covered (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (original : RuleInstance Ready) :
    RuleCovered (privateScopes (Local := Local) scopes) occupied
      (ContextualRigidActivation.rule locals captures encode original) := by
  intro value member
  change value ∈ ruleTerms (original.map
    (ContextualRigidActivation.into encode (ContextualActivatedStep.source locals captures))) at member
  rw [ruleTerms_map] at member
  obtain ⟨originalValue, _, rfl⟩ := List.mem_map.mp member
  unfold Covered term ContextualRigidActivation.into
  rw [Rigid.support_include]
  exact Finset.empty_subset _

variable [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)]

theorem returned_inventory_covered (scopes : Shared → Finset Nat) (old : Finset Nat)
    (readyLabel : Occurrence → Ready) (state : Configuration Ready Occurrence)
    (retained : List (Observation base captures))
    (templates : List (Observation base (ContextualActivatedStep.source locals captures)))
    (extra : EquationStore (Term (signature base captures) [] ()))
    (original : RuleInstance Ready) (selection : Selection Occurrence) (fuel : Nat)
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures
        (reserve locals captures scopes old readyLabel state retained templates extra) selection
        (ContextualRigidActivation.rule locals captures encode original)
        (ContextualRigidActivation.rows locals captures encode readyLabel)
        (ContextualRigidActivation.withFrame captures encode extra state))))
    (returned : ContextualTransportedActivation.FromRun locals captures fuel
      (reserve locals captures scopes old readyLabel state retained templates extra) selection
      (ContextualRigidActivation.rule locals captures encode original)
      (ContextualRigidActivation.rows locals captures encode readyLabel)
      (ContextualRigidActivation.withFrame captures encode extra state)
      (ContextualRigidActivation.outputs locals captures encode readyLabel) update) :
    let occupied := reserve locals captures scopes old readyLabel state retained templates extra
    CoveredWorld locals
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals captures) update.declaration)
      (frameScopes (activeScopes (Local := Local) scopes)
        (helperScope (ContextualActivationScopes.after occupied selection)))
      (helperLedger (ContextualActivationScopes.after occupied selection))
      (mapInventory locals (ContextualActivatedStep.target locals captures)
        (ContextualComputedFreshFrame.includeSource update)
        (afterInventory locals captures occupied selection
          (ContextualRigidActivation.rule locals captures encode original)
          (inventory locals captures readyLabel state retained templates extra)
          (ContextualRigidActivation.outputs locals captures encode readyLabel))) :=
  computed_activation_inventory_covered locals captures scopes _ selection
    (ContextualRigidActivation.rule locals captures encode original)
    (inventory locals captures readyLabel state retained templates extra)
    (ContextualRigidActivation.outputs locals captures encode readyLabel)
    (reserved_world locals captures scopes old readyLabel state retained templates extra)
    (source_rule_covered locals captures scopes _ original) returned.valid.admitted update

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedInventory
