import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution

/-!
# The entire native scoped inference receipt supplies a family-changing path

This presentation retains the caller equations and complete native inventory.
It is separate from the protected logical view, which intentionally forgets
external caller constraints. The edge recovers the exact existing FromRun.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution.Receipt

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open ScopedInferenceValues (base encode)
open InferenceRequestExecution (Occurrence)

variable {Local Shared : Type} {definition : ValidatedCalculusLanguageDef}
  {locals : Local → MetaArity base} {captures : Shared → MetaArity base}
  [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)]
  (receipt : Receipt definition locals captures)

def endpoint : ContextualExecution.Endpoint locals Occurrence [] () where
  Names := Shared
  equality := inferInstance
  declarations := captures
  scopes := receipt.scopes
  occupied := receipt.occupied
  inventory := InferenceScopedInventory.inventory locals captures receipt.readyLabel receipt.state
    receipt.retained receipt.templates receipt.extraFrame
  covered := InferenceScopedInventory.reserved_world locals captures receipt.scopes receipt.oldLedger
    receipt.readyLabel receipt.state receipt.retained receipt.templates receipt.extraFrame

def targetEndpoint : ContextualExecution.Endpoint locals Occurrence [] () :=
  ContextualExecution.computedTarget locals receipt.endpoint
    (ContextualRigidActivation.rule locals captures encode receipt.readyRule) receipt.selection
    (ContextualRigidActivation.outputs locals captures encode receipt.readyLabel)
    (InferenceScopedInventory.source_rule_covered locals captures receipt.scopes receipt.occupied receipt.readyRule)
    receipt.returned.valid.admitted receipt.update

def nativeFiring : ContextualExecution.Firing locals receipt.endpoint receipt.targetEndpoint where
  rule := ContextualRigidActivation.rule locals captures encode receipt.readyRule
  ruleCovered := InferenceScopedInventory.source_rule_covered locals captures receipt.scopes receipt.occupied receipt.readyRule
  selection := receipt.selection
  outputs := ContextualRigidActivation.outputs locals captures encode receipt.readyLabel
  fuel := receipt.fuel
  update := receipt.update
  admitted := receipt.returned.valid.admitted
  computed := receipt.returned.computed
  empty := receipt.returned.empty
  destination := rfl

def nativePath : Quiver.Path receipt.endpoint receipt.targetEndpoint :=
  Quiver.Hom.toPath receipt.nativeFiring

theorem native_target_is_full_result : receipt.targetEndpoint.inventory.configuration = receipt.nativeAfter := rfl

theorem native_path_selection_and_fuel :
    ContextualExecution.selections receipt.nativePath = [receipt.selection] ∧
      ContextualExecution.fuels receipt.nativePath = [receipt.fuel] := ⟨rfl, rfl⟩

theorem original_frame_equations_are_present :
    receipt.endpoint.inventory.configuration =
      ContextualRigidActivation.withFrame captures encode receipt.extraFrame receipt.state := rfl

theorem returned_answer_models_native_endpoint :
    ContextualFrameUnifier.Models (ContextualComputedFreshFrame.answer receipt.update)
      receipt.targetEndpoint.inventory.configuration.equations :=
  receipt.returned_answer_models_native_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution.Receipt
