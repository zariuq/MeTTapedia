import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Generic

/-!
# Facts about the weak-head forms of types

Two facts about the weak-head forms of the types of a rule package (`FormFacts`):
every type of a formed context reduces, typed, to a weak-head form; and the
weak-head forms of two equal types of a formed context match (`FormsMatch`):
they have the same former and equal components, or both are neutral.

These are the facts a model must supply. The consequences of the typed equality
that the conversion algorithm, the bidirectional kernel and the decision of
subtyping use are stated over them, so that they hold for every rule package
with the facts, whichever model supplies them. For a package whose declared
constants are semantic, the normalization model supplies them
(`FormFacts.ofSemantic`).

From the facts alone:

* injectivity of dependent function, pair and identity types, of heads up to the
  package's head equality, and of the type constants of inductive types;
* discrimination of the formers of types: a dependent function type, a
  dependent pair type, an identity type, a head and the type constant of an
  inductive type are pairwise never equal;
* a type equal to a neutral type in weak-head form is neutral when it is in
  weak-head form itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-! ## Matching weak-head forms -/

/-- Two weak-head normal types with the same former and equal components, or
two neutral types. -/
def FormsMatch (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n)
    (A B : Tm Head n) : Prop :=
  (∃ h h', A = .head h ∧ B = .head h' ∧ HeadSame R h h') ∨
  (∃ A₁ B₁ A₂ B₂, A = .pi A₁ B₁ ∧ B = .pi A₂ B₂ ∧ TypeEq R Γ A₁ A₂ ∧
    TypeEq R (.snoc Γ A₁) B₁ B₂) ∨
  (∃ A₁ B₁ A₂ B₂, A = .sigma A₁ B₁ ∧ B = .sigma A₂ B₂ ∧ TypeEq R Γ A₁ A₂ ∧
    TypeEq R (.snoc Γ A₁) B₁ B₂) ∨
  (∃ C x y C' x' y', A = .id C x y ∧ B = .id C' x' y' ∧ TypeEq R Γ C C' ∧ Equal R Γ x x' C ∧
    Equal R Γ y y' C) ∨
  (∃ T ctors, roles T = .inductive ctors ∧ A = .const T ∧ B = .const T) ∨
  (Neutral roles A ∧ Neutral roles B)

section Matches

variable {R : Rules Head} {roles : Roles Head} {n : Nat} {Γ : Ctx Head n} {B : Tm Head n}

theorem FormsMatch.head_left {h : Head} (m : FormsMatch R roles Γ (.head h) B) :
    ∃ h', B = .head h' ∧ HeadSame R h h' := by
  rcases m with ⟨_, h', e, rfl, same⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, _, _, _, e, _⟩ | ⟨_, _, _, e, _⟩ | ⟨neutral, _⟩
  · cases e
    exact ⟨h', rfl, same⟩
  · cases e
  · cases e
  · cases e
  · cases e
  · exact absurd rfl (neutral.not_former.1 h)

theorem FormsMatch.pi_left {A₁ : Tm Head n} {B₁ : Tm Head (n + 1)}
    (m : FormsMatch R roles Γ (.pi A₁ B₁) B) :
    ∃ A₂ B₂, B = .pi A₂ B₂ ∧ TypeEq R Γ A₁ A₂ ∧ TypeEq R (.snoc Γ A₁) B₁ B₂ := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, A₂, B₂, e, rfl, eA, eB⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, _, _, _, e, _⟩ | ⟨_, _, _, e, _⟩ | ⟨neutral, _⟩
  · cases e
  · cases e
    exact ⟨A₂, B₂, rfl, eA, eB⟩
  · cases e
  · cases e
  · cases e
  · exact absurd rfl (neutral.not_former.2.1 A₁ B₁)

theorem FormsMatch.sigma_left {A₁ : Tm Head n} {B₁ : Tm Head (n + 1)}
    (m : FormsMatch R roles Γ (.sigma A₁ B₁) B) :
    ∃ A₂ B₂, B = .sigma A₂ B₂ ∧ TypeEq R Γ A₁ A₂ ∧ TypeEq R (.snoc Γ A₁) B₁ B₂ := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, A₂, B₂, e, rfl, eA, eB⟩ |
    ⟨_, _, _, _, _, _, e, _⟩ | ⟨_, _, _, e, _⟩ | ⟨neutral, _⟩
  · cases e
  · cases e
  · cases e
    exact ⟨A₂, B₂, rfl, eA, eB⟩
  · cases e
  · cases e
  · exact absurd rfl (neutral.not_former.2.2.1 A₁ B₁)

theorem FormsMatch.id_left {C x y : Tm Head n} (m : FormsMatch R roles Γ (.id C x y) B) :
    ∃ C' x' y', B = .id C' x' y' ∧ TypeEq R Γ C C' ∧ Equal R Γ x x' C ∧ Equal R Γ y y' C := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, C', x', y', e, rfl, eC, ex, ey⟩ | ⟨_, _, _, e, _⟩ | ⟨neutral, _⟩
  · cases e
  · cases e
  · cases e
  · cases e
    exact ⟨C', x', y', rfl, eC, ex, ey⟩
  · cases e
  · exact absurd rfl (neutral.not_former.2.2.2 C x y)

theorem FormsMatch.inductive_left {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (role : roles T = .inductive ctors) (m : FormsMatch R roles Γ (.const T) B) :
    B = .const T := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, _, _, _, e, _⟩ | ⟨_, _, _, e, rfl⟩ | ⟨neutral, _⟩
  · cases e
  · cases e
  · cases e
  · cases e
  · cases e
    rfl
  · exact absurd rfl (neutral.ne_inductive role)

theorem FormsMatch.neutral_left {A : Tm Head n} (neutral : Neutral roles A)
    (m : FormsMatch R roles Γ A B) : Neutral roles B := by
  rcases m with ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ |
    ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, _, role, rfl, _⟩ | ⟨_, neutral'⟩
  · exact absurd rfl (neutral.not_former.1 _)
  · exact absurd rfl (neutral.not_former.2.1 _ _)
  · exact absurd rfl (neutral.not_former.2.2.1 _ _)
  · exact absurd rfl (neutral.not_former.2.2.2 _ _ _)
  · exact absurd rfl (neutral.ne_inductive role)
  · exact neutral'

end Matches

/-! ## The facts -/

/-- **Facts about the weak-head forms of types**: every type of a formed context
reduces, typed, to a weak-head form, and the weak-head forms of equal types of a
formed context match. -/
structure FormFacts (R : Rules Head) (roles : Roles Head) : Prop where
  typeForm : ∀ {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}, IsType R Γ A → CtxFormed R Γ →
    ∃ A', RedTy R roles Γ A A' ∧ IsTypeForm roles A'
  forms : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}, TypeEq R Γ A B → CtxFormed R Γ →
    IsTypeForm roles A → IsTypeForm roles B → FormsMatch R roles Γ A B

/-! ## Injectivity -/

section Consequences

variable {R : Rules Head} {roles : Roles Head} (facts : FormFacts R roles) {n : Nat}
  {Γ : Ctx Head n}
include facts

/-- A type equal to a neutral type is neutral when it is in weak-head form. -/
theorem TypeEq.neutral_form {A B : Tm Head n} (equal : TypeEq R Γ A B) (formed : CtxFormed R Γ)
    (neutral : Neutral roles A) (form : IsTypeForm roles B) : Neutral roles B :=
  (facts.forms equal formed (.inr (.inr (.inr (.inr (.inl neutral))))) form).neutral_left neutral

/-- Injectivity of dependent function types. -/
theorem TypeEq.pi_injective {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (equal : TypeEq R Γ (.pi A B) (.pi A' B')) (formed : CtxFormed R Γ) :
    TypeEq R Γ A A' ∧ TypeEq R (.snoc Γ A) B B' := by
  obtain ⟨_, _, e, eA, eB⟩ :=
    (facts.forms equal formed (.inr (.inl ⟨_, _, rfl⟩)) (.inr (.inl ⟨_, _, rfl⟩))).pi_left
  cases e
  exact ⟨eA, eB⟩

/-- Injectivity of dependent pair types. -/
theorem TypeEq.sigma_injective {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (equal : TypeEq R Γ (.sigma A B) (.sigma A' B')) (formed : CtxFormed R Γ) :
    TypeEq R Γ A A' ∧ TypeEq R (.snoc Γ A) B B' := by
  obtain ⟨_, _, e, eA, eB⟩ := (facts.forms equal formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    (.inr (.inr (.inl ⟨_, _, rfl⟩)))).sigma_left
  cases e
  exact ⟨eA, eB⟩

/-- Injectivity of identity types. -/
theorem TypeEq.id_injective {A A' a a' b b' : Tm Head n}
    (equal : TypeEq R Γ (.id A a b) (.id A' a' b')) (formed : CtxFormed R Γ) :
    TypeEq R Γ A A' ∧ Equal R Γ a a' A ∧ Equal R Γ b b' A := by
  obtain ⟨_, _, _, e, eA, ea, eb⟩ := (facts.forms equal formed
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).id_left
  cases e
  exact ⟨eA, ea, eb⟩

/-- Injectivity of heads: equal heads are the same up to head equality. -/
theorem TypeEq.head_injective {h h' : Head} (equal : TypeEq R Γ (.head h) (.head h'))
    (formed : CtxFormed R Γ) : HeadSame R h h' := by
  obtain ⟨_, e, same⟩ := (facts.forms equal formed (.inl ⟨_, rfl⟩) (.inl ⟨_, rfl⟩)).head_left
  cases e
  exact same

/-- Injectivity of inductive type constants: equal inductive types are the same
constant. -/
theorem TypeEq.inductive_injective {T T' : DeclName}
    {ctors ctors' : List (DeclName × List (Field Head))} (role : roles T = .inductive ctors)
    (role' : roles T' = .inductive ctors') (equal : TypeEq R Γ (.const T) (.const T'))
    (formed : CtxFormed R Γ) : T = T' :=
  Tm.const.inj ((facts.forms equal formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))
    (.inr (.inr (.inr (.inr (.inr ⟨T', ctors', role', rfl⟩)))))).inductive_left role).symm

/-! ## Discrimination -/

/-- A dependent function type is not a dependent pair type. -/
theorem TypeEq.pi_ne_sigma {A A' : Tm Head n} {B B' : Tm Head (n + 1)} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.pi A B) (.sigma A' B') := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.inr (.inl ⟨_, _, rfl⟩))
    (.inr (.inr (.inl ⟨_, _, rfl⟩)))).pi_left
  cases e

/-- A dependent function type is not an identity type. -/
theorem TypeEq.pi_ne_id {A C a b : Tm Head n} {B : Tm Head (n + 1)} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.pi A B) (.id C a b) := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.inr (.inl ⟨_, _, rfl⟩))
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).pi_left
  cases e

/-- A dependent function type is not a head. -/
theorem TypeEq.pi_ne_head {A : Tm Head n} {B : Tm Head (n + 1)} {h : Head}
    (formed : CtxFormed R Γ) : ¬ TypeEq R Γ (.pi A B) (.head h) := fun equal => by
  obtain ⟨_, _, e, -⟩ :=
    (facts.forms equal formed (.inr (.inl ⟨_, _, rfl⟩)) (.inl ⟨_, rfl⟩)).pi_left
  cases e

/-- A dependent pair type is not an identity type. -/
theorem TypeEq.sigma_ne_id {A C a b : Tm Head n} {B : Tm Head (n + 1)} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.sigma A B) (.id C a b) := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).sigma_left
  cases e

/-- A dependent pair type is not a head. -/
theorem TypeEq.sigma_ne_head {A : Tm Head n} {B : Tm Head (n + 1)} {h : Head}
    (formed : CtxFormed R Γ) : ¬ TypeEq R Γ (.sigma A B) (.head h) := fun equal => by
  obtain ⟨_, _, e, -⟩ :=
    (facts.forms equal formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) (.inl ⟨_, rfl⟩)).sigma_left
  cases e

/-- An identity type is not a head. -/
theorem TypeEq.id_ne_head {A a b : Tm Head n} {h : Head} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.id A a b) (.head h) := fun equal => by
  obtain ⟨_, _, _, e, -⟩ :=
    (facts.forms equal formed (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (.inl ⟨_, rfl⟩)).id_left
  cases e

section Inductive

variable {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  (role : roles T = .inductive ctors)
include role

/-- An inductive type is not a head. -/
theorem TypeEq.inductive_ne_head {h : Head} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.const T) (.head h) := fun equal => by
  have e := (facts.forms equal formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))
    (.inl ⟨_, rfl⟩)).inductive_left role
  cases e

/-- An inductive type is not a dependent function type. -/
theorem TypeEq.inductive_ne_pi {A : Tm Head n} {B : Tm Head (n + 1)} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.const T) (.pi A B) := fun equal => by
  have e := (facts.forms equal formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))
    (.inr (.inl ⟨_, _, rfl⟩))).inductive_left role
  cases e

/-- An inductive type is not a dependent pair type. -/
theorem TypeEq.inductive_ne_sigma {A : Tm Head n} {B : Tm Head (n + 1)}
    (formed : CtxFormed R Γ) : ¬ TypeEq R Γ (.const T) (.sigma A B) := fun equal => by
  have e := (facts.forms equal formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))
    (.inr (.inr (.inl ⟨_, _, rfl⟩)))).inductive_left role
  cases e

/-- An inductive type is not an identity type. -/
theorem TypeEq.inductive_ne_id {A a b : Tm Head n} (formed : CtxFormed R Γ) :
    ¬ TypeEq R Γ (.const T) (.id A a b) := fun equal => by
  have e := (facts.forms equal formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).inductive_left role
  cases e

end Inductive

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
