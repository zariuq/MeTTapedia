import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathControls

/-!
# A real nonidentity solver answer distinguishes inclusion from binding

The actual framed inference return creates the helper frame by a pure
inclusion. An unconstrained caller question remains unentailed there.
Applying the returned binding answer makes that question true, so it cannot
be used to reflect questions about an earlier unconstrained prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (definition)
open Mettapedia.Logic.LP (ScopedVar)
open ScopedInferenceValues (base encode)
open InferenceScopedExecutionControls (locals captures active readyB)
open ContextualGuardMatching

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

def question : Check (Term (signature base captures) [] ()) :=
  .equal (generator captures ()) (ContextualRigidActivation.into encode captures readyB)

def pureFrameExtension (receipt : InferenceScopedExecution.Receipt definition locals captures) : Extension captures :=
  (Extension.withLocals (fun name : ScopedVar Empty => locals name.name) captures).trans
    (ContextualComputedFreshFrame.declarationExtension receipt.update)

theorem pureFrameExtension_assignment (receipt : InferenceScopedExecution.Receipt definition locals captures) :
    (pureFrameExtension receipt).assignment =
      Assignment.compose (ContextualComputedFreshFrame.includeSource receipt.update)
        (ContextualSelectionViews.capturedTarget locals captures) := by
  funext name
  change generator (ContextualComputedFreshFrame.active active receipt.update.declaration) (.inl (.inr name)) =
    instantiate (ContextualComputedFreshFrame.includeSource receipt.update) (generator active (.inr name))
  rw [instantiate_generator]
  exact (ContextualFreshFrameScopeLedger.includeSource_image receipt.update (.inr name)).symm

theorem the_unconstrained_question_is_not_entailed
    (receipt : InferenceScopedExecution.Receipt definition locals captures) :
    ¬ ContextualGuardSemantics.Ask locals []
      (ContextualRigidActivation.rows locals captures encode receipt.readyLabel) receipt.state.present question := by
  intro ask
  have same := ask Unit captures (generator captures) (fun _ member => by cases member)
  change generator captures () = ContextualRigidActivation.into encode captures readyB at same
  have heads := (Term.op.inj same).1
  cases heads

theorem a_real_return_keeps_pure_extension_distinct_from_its_binding_answer :
    ∃ receipt : InferenceScopedExecution.Receipt definition locals captures,
      receipt.id = ⟨"ab"⟩ ∧ receipt.arguments = [] ∧ receipt.fuel = 3 ∧
      receipt.capturedAnswer () ≠ generator
        (ContextualComputedFreshFrame.active active receipt.update.declaration) (.inl (.inr ())) ∧
      ¬ ContextualGuardSemantics.Ask locals
        (ContextualFrameUnifier.mapProblem (pureFrameExtension receipt).assignment [])
        (fun occurrence => (ContextualRigidActivation.rows locals captures encode receipt.readyLabel occurrence).map locals
          (pureFrameExtension receipt).assignment) receipt.state.present
        (question.map (instantiate (pureFrameExtension receipt).assignment)) ∧
      ContextualGuardSemantics.Ask locals (ContextualFrameUnifier.mapProblem receipt.capturedAnswer [])
        (fun occurrence => (ContextualRigidActivation.rows locals captures encode receipt.readyLabel occurrence).map locals
          receipt.capturedAnswer) receipt.state.present
        (question.map (instantiate receipt.capturedAnswer)) := by
  obtain ⟨situated, source, inputs, _selected, fuel, _frame, _roots, _templates, _occupied,
    _ledger, binding, nonidentity, _models, _projection, _sourceId, _sourceArgs, _port, _node⟩ :=
      ScopedInferencePathControls.actual_framed_path
  let receipt := situated.native
  refine ⟨receipt, source, inputs, fuel, nonidentity, ?_, ?_⟩
  · intro included
    exact the_unconstrained_question_is_not_entailed receipt
      ((ContextualGuardSemantics.Ask.extension_iff locals (pureFrameExtension receipt) []
        (ContextualRigidActivation.rows locals captures encode receipt.readyLabel) receipt.state.present question).mp included)
  · have same : instantiate receipt.capturedAnswer (generator captures ()) =
        instantiate receipt.capturedAnswer (ContextualRigidActivation.into encode captures readyB) := by
      exact (instantiate_generator receipt.capturedAnswer ()).trans
        (binding.trans (Rigid.instantiate_include receipt.capturedAnswer (encode readyB)).symm)
    intro Future future candidate _
    exact congrArg (instantiate candidate) same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameControls
