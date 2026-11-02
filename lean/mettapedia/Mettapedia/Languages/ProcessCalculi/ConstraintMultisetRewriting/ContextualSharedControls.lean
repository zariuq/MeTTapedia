import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSharedApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingControls
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ReferenceInstantiation

/-!
# Executed contextual applications on the shared store

These controls encode intrinsic bodies and actual argument lists with the
existing store operations, then run the reference-only graft. They exercise
symbolic images, reordered and repeated parameters, application under an
object binder, and scope and arity refusals.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSharedApplication.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open ContextualBinding.Controls

abbrev H := CommonABT.Head extended

instance : DecidableEq H := by
  change DecidableEq ((sort : Unit) × (ContextualFrame.Controls.Operator ⊕ Operator declaration sort))
  letI : ∀ sort : Unit, DecidableEq (Operator (S := base) declaration sort) := fun sort =>
    (Operator.key_injective (S := base) (declaration := declaration) (sort := sort)).decidableEq
  infer_instance

def storedBody : Store H × Ref := encodeR [] (CommonABT.lower body)

def repeatedInputs : Store H × List Ref :=
  ContextualPatterns.encodeArguments storedBody.1 [.idx 0, .idx 0]

def swappedInputs : Store H × List Ref :=
  ContextualPatterns.encodeArguments storedBody.1 [.idx 1, .idx 0]

theorem symbolic_shared_application_accepts_repetition :
    (SharedApplication.graftR repeatedInputs.1 2 repeatedInputs.2 storedBody.2).map
      (fun result => unfold result.1 result.2) =
        some (CommonABT.lower (pair (Term.var (Γ := [()]) .zero) (gCall (.var .zero) (.var .zero)))) := by
  decide +kernel

theorem symbolic_shared_application_accepts_swapped_parameters :
    (SharedApplication.graftR swappedInputs.1 2 swappedInputs.2 storedBody.2).map
      (fun result => unfold result.1 result.2) =
        some (CommonABT.lower
          (pair (Term.var (Γ := [(), ()]) (.succ .zero)) (gCall (.var .zero) (.var (.succ .zero))))) := by
  decide +kernel

theorem shared_body_scope_cannot_be_relabelled :
    SharedApplication.graftR repeatedInputs.1 1 [(repeatedInputs.2[0]?).getD storedBody.2] storedBody.2 = none := by
  decide +kernel

theorem shared_missing_parameter_is_refused :
    SharedApplication.graftR repeatedInputs.1 2 [(repeatedInputs.2[0]?).getD storedBody.2] storedBody.2 = none := by
  decide +kernel

def binderBody : Term extended [(), ()] () :=
  .op (.inl .lam)
    (.cons (pair (.var (.succ .zero)) (.var (.succ (.succ .zero)))) .nil)

def storedBinderBody : Store H × Ref := encodeR [] (CommonABT.lower binderBody)

def binderInputs : Store H × List Ref :=
  ContextualPatterns.encodeArguments storedBinderBody.1 [.idx 0, .idx 0]

def binderResult : Term extended [()] () :=
  .op (.inl .lam) (.cons (pair (.var (.succ .zero)) (.var (.succ .zero))) .nil)

theorem shared_application_preserves_the_inner_binder :
    (SharedApplication.graftR binderInputs.1 2 binderInputs.2 storedBinderBody.2).map
      (fun result => unfold result.1 result.2) = some (CommonABT.lower binderResult) := by
  decide +kernel

theorem physical_result_is_scoped_in_its_ambient_context :
    SignatureIndexedABT.Term.supportedAt 1 (CommonABT.lower binderResult) = true :=
  CommonABT.lower_scoped (S := extended) binderResult

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSharedApplication.Controls
