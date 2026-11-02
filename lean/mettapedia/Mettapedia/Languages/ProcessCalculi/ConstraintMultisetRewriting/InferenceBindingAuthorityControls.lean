import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBindingAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedFrameControls

/-!
# A valid inference can still fail the caller's binding policy

The existing concrete worklist receipt binds its caller variable and derives
the original conclusion. It passes a policy protecting a closed value, but
fails a policy protecting that variable. The failure comes from the actual
returned assignment, not from a different execution or an assumed solver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBindingAuthority.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (definition)
open ScopedInferenceValues (base encode)
open InferenceScopedExecutionControls (locals captures readyA)

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

def callerPolicy : List (Observation base captures) := [observe (generator captures ())]
def closedPolicy : List (Observation base captures) :=
  [observe (ContextualRigidActivation.into encode captures readyA)]

theorem actual_return_is_rejected_by_the_caller_policy :
    ∃ execution : InferenceScopedExecution.Receipt definition locals captures,
      Permits execution closedPolicy ∧ ¬ Permits execution callerPolicy := by
  obtain ⟨execution, _extra, _retained, _templates, _binding, nonidentity, _proof⟩ :=
    InferenceScopedFrameControls.actual_framed_execution
  refine ⟨execution, ?_, ?_⟩
  · intro observation member name inside
    have same : observation = observe (ContextualRigidActivation.into encode captures readyA) := by
      simpa [closedPolicy] using member
    subst observation
    change name ∈ support (ContextualRigidActivation.into encode captures readyA) at inside
    have noSupport : support (ContextualRigidActivation.into encode captures readyA) = [] :=
      Rigid.support_include captures (encode readyA)
    rw [noSupport] at inside
    cases inside
  · intro allowed
    have same := allowed (observe (generator captures ())) (by simp [callerPolicy]) () (by
      change () ∈ support (generator captures ())
      simp [support_generator])
    apply nonidentity
    exact same

theorem actual_authorized_receipt_retains_the_original_firing :
    ∃ receipt : AuthorizedReceipt definition locals captures closedPolicy,
      receipt.firing.picked = receipt.execution.selection ∧
      ¬ Permits receipt.execution callerPolicy := by
  obtain ⟨execution, permitted, refused⟩ := actual_return_is_rejected_by_the_caller_policy
  exact ⟨⟨execution, permitted⟩, rfl, refused⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBindingAuthority.Controls
