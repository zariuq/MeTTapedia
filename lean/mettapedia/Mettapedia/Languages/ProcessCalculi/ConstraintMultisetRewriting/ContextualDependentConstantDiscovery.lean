import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantShape
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Discovering an independent-result Pi shape from its actual annotation

The declared Pi type is inspected, its result is inverted across the binder,
and both component types are checked in the original outer context. Failure
to recognize the shape or finish either check leaves the candidate unresolved.
The original whole annotation and universe metadata are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantDiscovery

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentConstantShape

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def discover (fuel : Nat) {Γ : Context S.R} (whole : TypeOver Γ) :
    Option {shape : Shape Γ // shape.whole = whole} :=
  match parsed : whole.code with
  | .pi domain body => do
      let first ← ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ domain
      match inverted : ContextualDependentInversion.invert
          (ContextualDependentInversion.lookup (wk : Ren Γ.arity (Γ.arity + 1))) body with
      | none => none
      | some codomain => do
          let second ← ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ codomain
          return ⟨⟨first.val, second.val, whole, by
            rw [first.property, second.property]
            rw [ContextualDependentInversion.invert_sound body wk _
              (ContextualDependentInversion.lookup_exact wk (Fin.succ_injective _)) codomain inverted]
            exact parsed⟩, rfl⟩
  | _ => none

theorem discover_zero {Γ : Context S.R} (whole : TypeOver Γ) :
    discover facts roots heads algebra declared choices reducer 0 whole = none := by
  unfold discover
  split <;> rfl

end ContextualDependentConstantDiscovery
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
