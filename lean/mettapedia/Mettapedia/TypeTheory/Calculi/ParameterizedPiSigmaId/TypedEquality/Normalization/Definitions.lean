import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.IotaComputation

/-!
# Definitions by one equation

A constant `f : Π Θ. C` defined by one equation with variable patterns,
`f x₁ ⋯ x_k ⟶ rhs`, computes at its authored arity `k` (δ). Its right-hand
side is typed at `C` in the telescope `Θ`, in a rule package without `f`, so it
does not mention `f`. Such a constant is semantic: its full application
reduces in one step to the right-hand side, which is valid by the fundamental
lemma for the earlier package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- The rule package declares `f : Π Θ. C` by the equation `f x₁ ⋯ x_k ⟶ rhs`,
with its type and right-hand side typed in the earlier package `R₀`. -/
structure DeclaresDefinition (S : Setting Head L) (R₀ : Rules Head) (f : DeclName) {k : Nat}
    (Θ : Ctx Head k) (C rhs : Tm Head k) : Prop where
  role : S.roles f = .computes k .leaf
  declared : S.R.constantType f = some (closeType Θ C)
  sub₀ : RulesSub R₀ S.R
  semantic₀ : AllSemantic S R₀
  typed : ∃ w, S.R.isUniverse w ∧ Typed R₀ .nil (closeType Θ C) (.head w)
  body : Typed R₀ Θ rhs C
  rule : ∀ {n : Nat} (σ : Sub Head k n),
    S.R.computation.step (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs)

section Semantics

variable (laws : S.E.Laws S.R S.roles) {R₀ : Rules Head} {f : DeclName} {k : Nat}
  {Θ : Ctx Head k} {C rhs : Tm Head k} (decl : DeclaresDefinition S R₀ f Θ C rhs)
include laws decl

omit laws in
/-- The defined constant at its declared type, in every context. -/
theorem DeclaresDefinition.typing {n : Nat} {Γ : Ctx Head n} :
    Typed S.R Γ (.const f) (liftClosed (closeType Θ C)) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact .const decl.declared (Derivable.mono decl.sub₀ typed) hw

/-- The declared type is a valid term of a universe; the right-hand side is
valid in the telescope. -/
theorem DeclaresDefinition.valid :
    (∃ w, S.R.isUniverse w ∧ ValidTm S .nil (closeType Θ C) (.head w)) ∧
      (ValidCtx S Θ → ValidTm S Θ rhs C) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  exact ⟨⟨w, hw, Derivable.valid_sub laws decl.sub₀
      (AllSemantic.semanticConstantsOf decl.semantic₀) typed trivial⟩,
    Derivable.valid_sub laws decl.sub₀ (AllSemantic.semanticConstantsOf decl.semantic₀)
      decl.body⟩

/-- The full application of the defined constant is valid in its telescope. -/
theorem DeclaresDefinition.full :
    ValidTm S Θ (applyClosed Θ ids (.const f)) C := by
  obtain ⟨⟨w, hw, validType⟩, validBody⟩ := decl.valid laws
  obtain ⟨validΘ, validC⟩ := ValidTy.telescope laws Θ (validType.validTy laws hw)
  have validRhs := validBody validΘ
  have apply : ∀ {m : Nat} (σ : Sub Head k m),
      Presentation.subst σ (applyClosed Θ ids (.const f)) = applyClosed Θ σ (.const f) := by
    intro m σ
    rw [applyClosed_subst]
    rfl
  /- One step to the right-hand side, typed at a type equal to `C[σ]`. -/
  have step : ∀ {m : Nat} {Δ : Ctx Head m} {σ : Sub Head k m} (vσ : ValidSubst S Θ Δ σ)
      {X : Tm Head m}, TypeEq S.R Δ (Presentation.subst σ C) X →
      ∀ {P : Pack Head m}, Reducible S Δ (Presentation.subst σ C) P →
      RedTm S.R S.roles Δ (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs) X := by
    intro m Δ σ vσ X toX P r
    have source := Typed.telescope_apply (vσ.substMor laws) (decl.typing (Γ := Δ))
    have target := ((r.escape laws).redTm (validRhs.red vσ r)).1
    exact RedTm.of_root (decl.rule σ) (Typed.convType source toX) (Typed.convType target toX)
  refine ⟨validC, fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · rw [apply]
    have red := step vσ (laws.convTy_sound (r.escape laws).refl) r
    exact (r.redTm_expand red (validRhs.red vσ r)).1
  · rw [apply, apply]
    have toσ : TypeEq S.R Δ (Presentation.subst σ' C) (Presentation.subst σ C) :=
      (validC.typeEq_at laws vσ vσ' e).symm
    obtain ⟨P', r'⟩ := validC.red vσ'
    have red := step vσ (laws.convTy_sound (r.escape laws).refl) r
    have red' := step vσ' toσ r'
    exact r.eqTm_expand laws red red' (validRhs.ext vσ vσ' e r)

/-- The defined constant is semantic. -/
theorem DeclaresDefinition.semantic : SemanticConstant S f (closeType Θ C) := by
  obtain ⟨⟨w, hw, validType⟩, _⟩ := decl.valid laws
  have typing : Typed S.R .nil (.const f) (closeType Θ C) := by
    have h := decl.typing (Γ := .nil)
    rwa [liftClosed_zero] at h
  intro m Δ formed P r
  exact SemanticConstant.of_telescope laws (.inr ⟨_, decl.role⟩) (Θ := Θ) (C := C) typing
    (validType.validTy laws hw) (decl.full laws) formed r

end Semantics

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
