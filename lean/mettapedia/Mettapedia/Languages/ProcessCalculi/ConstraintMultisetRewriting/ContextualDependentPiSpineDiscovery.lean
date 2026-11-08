import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Checked discovery of a requested dependent argument spine

The requested number of Pi binders is read from the actual annotation.
Each domain and dependent codomain is checked in its proper prefix. The
whole annotation at every discovered binder is retained. Unrecognized or
unfinished formation returns none; a zero-argument view retains its input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpineDiscovery

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def discover (fuel : Nat) : (count : Nat) → {Γ : Context S.R} → (whole : TypeOver Γ) → Option (Spine whole)
  | 0, _, whole => some (.stop whole)
  | count + 1, Γ, whole =>
      match parsed : whole.code with
      | .pi domain codomain => do
          let first ← ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ domain
          let second ← ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
            (extend Γ first.val) codomain
          let rest ← discover fuel count second.val
          return .bind ⟨first.val, second.val, whole, by rw [first.property, second.property]; exact parsed⟩ rest
      | _ => none

theorem discover_zero_arguments (fuel : Nat) {Γ : Context S.R} (whole : TypeOver Γ) :
    discover facts roots heads algebra declared choices reducer fuel 0 whole = some (.stop whole) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem discover_zero_fuel (count : Nat) {Γ : Context S.R} (whole : TypeOver Γ) :
    discover facts roots heads algebra declared choices reducer 0 (count + 1) whole = none := by
  simp only [discover]
  split <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem discovered_length (fuel count : Nat) :
    ∀ {Γ : Context S.R} (whole : TypeOver Γ) (spine : Spine whole),
      discover facts roots heads algebra declared choices reducer fuel count whole = some spine → spine.length = count := by
  induction count with
  | zero =>
      intro Γ whole spine computed
      cases Option.some.inj computed
      rfl
  | succ count ih =>
      intro Γ whole spine computed
      unfold discover at computed
      split at computed
      · obtain ⟨first, _, afterOne⟩ := Option.bind_eq_some_iff.mp computed
        obtain ⟨second, _, afterTwo⟩ := Option.bind_eq_some_iff.mp afterOne
        obtain ⟨rest, restComputed, returned⟩ := Option.bind_eq_some_iff.mp afterTwo
        cases Option.some.inj returned
        exact congrArg Nat.succ (ih second.val rest restComputed)
      · cases computed

end ContextualDependentPiSpineDiscovery
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
