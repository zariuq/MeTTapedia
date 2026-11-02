import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedInventory

/-!
# Installed inference receipts connect actual scoped returns to open proofs

The receipt contains local source activation and the concrete worklist return,
not a derivability judgment. Its scope reservation is computed from the full
root inventory. The independently constructed ordinary firing feeds the
existing proof-relevant protected-judgment projection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ContextualFrameUpdate
open ContextualWorldScopeLedger
open ContextualFreshFrameScopeLedger
open ContextualScopeSupport
open ScopedInferenceValues (Ready base encode)
open InferenceRequestExecution (Occurrence)
open InferenceSelectedFirings
open InferenceJudgmentBoards
open InferenceTraceClassifying

variable {Local Shared : Type}

structure Receipt (definition : ValidatedCalculusLanguageDef)
    (locals : Local → MetaArity base) (captures : Shared → MetaArity base)
    [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)] where
  id : RuleId
  arguments : List Pattern
  readyRule : RuleInstance Ready
  activated : InferenceScopedActivation.activate definition id arguments = some readyRule
  readyLabel : Occurrence → Ready
  state : Configuration Ready Occurrence
  extraFrame : EquationStore (Term (signature base captures) [] ()) := []
  scopes : Shared → Finset Nat
  oldLedger : Finset Nat
  retained : List (Observation base captures)
  templates : List (Observation base (ContextualActivatedStep.source locals captures))
  selection : Selection Occurrence
  fuel : Nat
  update : Update (ContextualResidual.observeProblem
    (ContextualActivatedStep.problem locals captures
      (InferenceScopedInventory.reserve locals captures scopes oldLedger readyLabel state retained templates extraFrame) selection
      (ContextualRigidActivation.rule locals captures encode readyRule)
      (ContextualRigidActivation.rows locals captures encode readyLabel)
      (ContextualRigidActivation.withFrame captures encode extraFrame state)))
  returned : ContextualTransportedActivation.FromRun locals captures fuel
    (InferenceScopedInventory.reserve locals captures scopes oldLedger readyLabel state retained templates extraFrame) selection
    (ContextualRigidActivation.rule locals captures encode readyRule)
    (ContextualRigidActivation.rows locals captures encode readyLabel)
    (ContextualRigidActivation.withFrame captures encode extraFrame state)
    (ContextualRigidActivation.outputs locals captures encode readyLabel) update
  readback : ∀ occurrence, occurrence ∈ state.present ∨ occurrence ∈ selection.made →
    (readyLabel occurrence).val = InferenceRequestExecution.label occurrence

namespace Receipt

variable {definition : ValidatedCalculusLanguageDef} {locals : Local → MetaArity base}
  {captures : Shared → MetaArity base}
  [DecidableEq Local] [DecidableEq Shared] [∀ result, DecidableEq (base.Op result)]
  (receipt : Receipt definition locals captures)

def occupied : Finset Nat := InferenceScopedInventory.reserve locals captures receipt.scopes receipt.oldLedger
  receipt.readyLabel receipt.state receipt.retained receipt.templates receipt.extraFrame

def firing : SelectedFiring definition true (InferenceScopedReturned.legacyBefore receipt.state)
    (InferenceScopedReturned.legacyAfter receipt.state receipt.readyRule receipt.selection) :=
  InferenceScopedReturned.selected locals captures definition receipt.id receipt.arguments receipt.readyRule
    receipt.activated receipt.readyLabel receipt.state receipt.extraFrame receipt.fuel receipt.occupied receipt.selection
    receipt.update receipt.returned receipt.readback

def nativeAfter := ContextualTransportedActivation.result locals captures
  (ContextualComputedFreshFrame.includeSource receipt.update) receipt.occupied receipt.selection
  (ContextualRigidActivation.rule locals captures encode receipt.readyRule)
  (ContextualRigidActivation.rows locals captures encode receipt.readyLabel)
  (ContextualRigidActivation.withFrame captures encode receipt.extraFrame receipt.state)

def capturedAnswer : Assignment captures
    (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals captures) receipt.update.declaration) :=
  Assignment.compose
    (Assignment.compose (ContextualComputedFreshFrame.answer receipt.update)
      (ContextualComputedFreshFrame.includeSource receipt.update))
    (ContextualSelectionViews.capturedTarget locals captures)

/-- The logical ground inference view erases the external caller constraint
component. The actual native result retains it explicitly as this prefix. -/
theorem native_result_keeps_external_frame :
    receipt.nativeAfter.equations =
      ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource receipt.update)
        (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
          receipt.extraFrame) ++
        OccurrenceRelabeling.equations
          (ContextualRigidActivation.into encode
            (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals captures) receipt.update.declaration))
          (receipt.selection.problem receipt.readyLabel receipt.readyRule receipt.state) :=
  ContextualRigidActivation.result_withFrame_equations locals captures encode _ receipt.extraFrame
    receipt.occupied receipt.selection receipt.readyRule receipt.readyLabel receipt.state

/-- The concrete returned endomorphic answer, rather than a separately
assumed model, solves the whole native result including the caller frame. -/
theorem returned_answer_models_native_result :
    ContextualFrameUnifier.Models (ContextualComputedFreshFrame.answer receipt.update)
      receipt.nativeAfter.equations :=
  (ContextualComputedFreshFrame.principal_on _ receipt.update receipt.returned.empty []).sound

theorem captured_answer_solves_external_frame :
    ContextualFrameUnifier.Models receipt.capturedAnswer receipt.extraFrame := by
  have whole := receipt.returned_answer_models_native_result
  rw [receipt.native_result_keeps_external_frame] at whole
  have framePart := (ContextualFrameUnifier.models_append _ _ _).mp whole |>.1
  exact (ContextualFrameUnifier.models_mapProblem
    (ContextualSelectionViews.capturedTarget locals captures)
    (Assignment.compose (ContextualComputedFreshFrame.answer receipt.update)
      (ContextualComputedFreshFrame.includeSource receipt.update)) receipt.extraFrame).mp
    ((ContextualFrameUnifier.models_mapProblem (ContextualComputedFreshFrame.includeSource receipt.update)
      (ContextualComputedFreshFrame.answer receipt.update)
      (ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
        receipt.extraFrame)).mp framePart)

/-- The ordinary firing retains the same source, input vector and entire
physical selection, including the ordered read list and repeated reads. -/
theorem source_inputs_selection :
    receipt.firing.source = .inl receipt.id ∧ receipt.firing.inputs = .inl receipt.arguments ∧
      receipt.firing.picked = receipt.selection := ⟨rfl, rfl, rfl⟩

theorem exact_return_origin :
    ContextualFrameWorklist.run receipt.fuel (ContextualActivatedStep.target locals captures)
      (ContextualResidual.observeProblem
        (ContextualActivatedStep.problem locals captures receipt.occupied receipt.selection
          (ContextualRigidActivation.rule locals captures encode receipt.readyRule)
          (ContextualRigidActivation.rows locals captures encode receipt.readyLabel)
          (ContextualRigidActivation.withFrame captures encode receipt.extraFrame receipt.state))) = .residual receipt.update :=
  receipt.returned.computed

theorem actual_scope_inventory_is_preserved :
    CoveredWorld locals
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals captures) receipt.update.declaration)
      (frameScopes (activeScopes (Local := Local) receipt.scopes)
        (helperScope (ContextualActivationScopes.after receipt.occupied receipt.selection)))
      (helperLedger (ContextualActivationScopes.after receipt.occupied receipt.selection))
      (mapInventory locals (ContextualActivatedStep.target locals captures)
        (ContextualComputedFreshFrame.includeSource receipt.update)
        (afterInventory locals captures receipt.occupied receipt.selection
          (ContextualRigidActivation.rule locals captures encode receipt.readyRule)
          (InferenceScopedInventory.inventory locals captures receipt.readyLabel receipt.state
            receipt.retained receipt.templates receipt.extraFrame)
          (ContextualRigidActivation.outputs locals captures encode receipt.readyLabel))) :=
  InferenceScopedInventory.returned_inventory_covered locals captures receipt.scopes receipt.oldLedger
    receipt.readyLabel receipt.state receipt.retained receipt.templates receipt.extraFrame receipt.readyRule receipt.selection
    receipt.fuel receipt.update receipt.returned

noncomputable def projection (prior : Board (InferenceScopedReturned.legacyBefore receipt.state)) :
    Σ after : Board (InferenceScopedReturned.legacyAfter receipt.state receipt.readyRule receipt.selection),
      OpenDerivationList definition prior.judgments after.judgments :=
  projectFiring receipt.firing prior

end Receipt
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution
