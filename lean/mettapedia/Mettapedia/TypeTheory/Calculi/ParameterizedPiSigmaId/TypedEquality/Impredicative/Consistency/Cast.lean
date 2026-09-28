import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DecoderComputation

/-!
# Identity elimination on every path

The consistency model reads the meaning of a term from its weak-head normal
form, under a reduction that differs from the package's in one rule: identity
elimination returns its method on every path,

`J A x P d y e ⟶ d`.

The package's rule `J A x P d x (refl x) ⟶ d` is an instance, so every
declared computation of the package is one of the model's. Identity
elimination then inspects no argument: it computes at arity six with no
scrutinee.

The rule belongs to the model's reduction only; the typed equality of the
package keeps its own. In the model a path is irrelevant and exists only
between equal points, so returning the method gives a value at the type the
method already has.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

variable {Head : Type}

/-- Identity elimination on every path. -/
def castComputation (J : DeclName) : RootComputation Head where
  step := fun {n} l r => ∃ a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head n,
    l = appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅] ∧ r = a₃
  rename := by
    intro n m ρ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := step
    exact ⟨_, _, _, _, _, _, by rw [rename_appSpine]; rfl, rfl⟩
  substitute := by
    intro n m σ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := step
    exact ⟨_, _, _, _, _, _, by rw [subst_appSpine]; rfl, rfl⟩

/-- The package's rule for identity elimination is an instance of the cast. -/
theorem eliminator_step_cast {J : DeclName} {n : Nat} {l r : Tm Head n}
    (step : (eliminatorComputation J).step l r) : (castComputation J).step l r := by
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
  exact ⟨a₀, a₁, a₂, a₃, a₄, .refl a₅, e₁, e₂⟩

theorem castComputation_spine {roles : Roles Head} {J : DeclName}
    (role : roles J = .computes 6 .leaf) : SpineShaped roles (castComputation J) := by
  intro n t u step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, _⟩ := step
  exact ⟨J, 6, .leaf, [a₀, a₁, a₂, a₃, a₄, a₅], role, rfl, rfl, .leaf _⟩

theorem castComputation_headed {J : DeclName} :
    HeadedBy J (castComputation (Head := Head) J) := by
  intro n t u step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, _⟩ := step
  exact ⟨_, e₁⟩

theorem castComputation_deterministic {J : DeclName} :
    Deterministic (castComputation (Head := Head) J) := by
  intro n t u u' step step'
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, e₃, e₄⟩ := step'
  rw [e₁] at e₃
  obtain ⟨_, args⟩ := appSpine_const_injective e₃
  simp only [List.cons.injEq] at args
  rw [e₂, e₄]
  exact args.2.2.2.1.symm

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
