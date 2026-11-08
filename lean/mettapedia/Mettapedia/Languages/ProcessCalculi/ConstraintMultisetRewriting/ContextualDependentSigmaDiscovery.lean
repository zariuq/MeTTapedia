import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Computed discovery of dependent pair splitting

An explicit Sigma annotation is recognized from its actual code. The
existing executable formation checker reconstructs the domain and the
codomain in the extended context. The resulting split uses the original
whole annotation. An unrecognized or unfinished check keeps every equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSigma

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def discover (fuel : Nat) {Γ : Context S.R} (whole : TypeOver Γ) :
    Option {shape : Shape Γ // shape.whole = whole} :=
  match parsed : whole.code with
  | .sigma domain codomain => do
      let first ← ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ domain
      let second ← ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
        (extend Γ first.val) codomain
      return ⟨⟨first.val, second.val, whole, by rw [first.property, second.property]; exact parsed⟩, rfl⟩
  | _ => none

/-- All branches are certified solver updates. Failure to recognize an
explicit pair type is residual information, never certified refutation. -/
def splitNewest (fuel : Nat) {Γ : Context S.R} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) : Update S.levels problem :=
  match discover facts roots heads algebra declared choices reducer fuel whole with
  | none => Update.pending S.levels problem
  | some found => by
      rcases found with ⟨shape, same⟩
      cases same
      exact shape.update S.levels problem

end ContextualDependentSigma
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
