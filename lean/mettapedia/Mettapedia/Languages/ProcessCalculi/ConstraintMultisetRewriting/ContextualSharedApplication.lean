import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies
import Mettapedia.OSLF.Syntax.BindingSignatureABTSubstitution
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication

/-!
# Contextual application through the common shared-reference graft

The intrinsic declaration profile and the physical store use the same
capture-avoiding application. A shared reference represents each image and
argument; the existing reference-only graft returns the intrinsic result and
preserves the canonical store. Equality of the resulting references' trees
characterizes the two-sided equation, with both sides instantiated.

These laws concern represented inputs. Native allocation and schema-selection
correspondence are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSharedApplication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}
  [DecidableEq (CommonABT.Head (signature S target))]

/-- The reference-only engine agrees exactly with intrinsic application;
argument terms may themselves contain unresolved metavariables. -/
theorem application_exact
    (assignment : Assignment source target) (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map (fun sort => ([], sort))) Γ)
    (store : Store (CommonABT.Head (signature S target))) (canonical : Canonical store)
    (image : Ref) (inputs : List Ref) (validImage : CanonRef store image)
    (validInputs : ∀ input ∈ inputs, CanonRef store input)
    (representsImage : unfold store image = CommonABT.lower (assignment identity))
    (representsInputs : inputs.map (unfold store) = CommonABT.lowerSpine (instantiateArgs assignment arguments)) :
    (SharedApplication.graftR store (source identity).1.length inputs image).map
      (fun result => unfold result.1 result.2) =
        some (CommonABT.lower (instantiate assignment (Term.op (.inr (.mk identity)) arguments))) := by
  rw [SharedApplication.graftR_spec store canonical _ inputs image validImage validInputs,
    representsImage, representsInputs]
  exact CommonABT.graft_lower (S := signature S target) (assignment identity)
    (instantiateArgs assignment arguments)

/-- Scope and arity come from the actual declaration. Successful shared
application retains old references and returns a canonically represented,
well-scoped result. -/
theorem application_canonical
    (assignment : Assignment source target) (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S source) ((source identity).1.map (fun sort => ([], sort))) Γ)
    (store : Store (CommonABT.Head (signature S target))) (canonical : Canonical store)
    (image : Ref) (inputs : List Ref) (validImage : CanonRef store image)
    (validInputs : ∀ input ∈ inputs, CanonRef store input)
    (representsImage : unfold store image = CommonABT.lower (assignment identity))
    (representsInputs : inputs.map (unfold store) = CommonABT.lowerSpine (instantiateArgs assignment arguments)) :
    ∃ result, SharedApplication.graftR store (source identity).1.length inputs image = some result ∧
      store <+: result.1 ∧ Canonical result.1 ∧ CanonRef result.1 result.2 ∧
      unfold result.1 result.2 =
        CommonABT.lower (instantiate assignment (Term.op (.inr (.mk identity)) arguments)) ∧
      Scope.check result.2 Γ.length = true := by
  have exactResult := application_exact assignment identity arguments store canonical image inputs
    validImage validInputs representsImage representsInputs
  cases applied : SharedApplication.graftR store (source identity).1.length inputs image with
  | none => simp only [applied, Option.map_none, reduceCtorEq] at exactResult
  | some result =>
      have resultTree : unfold result.1 result.2 =
          CommonABT.lower (instantiate assignment (Term.op (.inr (.mk identity)) arguments)) :=
        Option.some.inj (by simpa only [applied, Option.map_some] using exactResult)
      obtain ⟨grows, finalCanonical, validResult⟩ :=
        SharedApplication.graftR_canonical canonical validImage validInputs applied
      refine ⟨result, rfl, grows, finalCanonical, validResult, resultTree, ?_⟩
      rw [← Scope.check_spec finalCanonical validResult, resultTree]
      exact CommonABT.lower_scoped (S := signature S target)
        (instantiate assignment (Term.op (.inr (.mk identity)) arguments))

/-- A physical equality test after the shared graft solves exactly the
contextual equation; the chosen assignment refines its right side too. -/
theorem solves_iff_shared_equality
    {declaration : V → MetaArity S}
    [DecidableEq (CommonABT.Head (signature S declaration))]
    (assignment : Assignment declaration declaration) (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S declaration) ((declaration identity).1.map (fun sort => ([], sort))) Γ)
    (right : Term (signature S declaration) Γ (declaration identity).2)
    (store : Store (CommonABT.Head (signature S declaration))) (canonical : Canonical store)
    (image : Ref) (inputs : List Ref) (validImage : CanonRef store image)
    (validInputs : ∀ input ∈ inputs, CanonRef store input)
    (representsImage : unfold store image = CommonABT.lower (assignment identity))
    (representsInputs : inputs.map (unfold store) = CommonABT.lowerSpine (instantiateArgs assignment arguments)) :
    (ContextualFamilies.action declaration Γ (declaration identity).2).Solves assignment
        (Term.op (.inr (.mk identity)) arguments, right) ↔
      (SharedApplication.graftR store (declaration identity).1.length inputs image).map
        (fun result => unfold result.1 result.2) = some (CommonABT.lower (instantiate assignment right)) := by
  rw [application_exact assignment identity arguments store canonical image inputs
    validImage validInputs representsImage representsInputs, Option.some.injEq]
  change instantiate assignment (Term.op (.inr (.mk identity)) arguments) = instantiate assignment right ↔ _
  exact ⟨congrArg CommonABT.lower, CommonABT.lower_injective _ _⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSharedApplication
