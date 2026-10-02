import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Inversion

/-!
# The weak-head forms of annotated types

The annotated counterpart of `Normalization.FormFacts`. Weak-head forms and neutrality
are read off the erasure, with the roles of the rule package.

* **Weak-head forms.** The weak-head form of an annotated type is a type former, the
  type constant of an inductive type, or a type whose erasure is neutral
  (`typeForm_erase_cases`); a type former is in weak-head form (`CFormer.typeForm`) and
  its erasure is not neutral (`CFormer.not_neutral`).
* **Matching forms** (`CFormsMatch`): two types with the same former and equal
  components, the same type constant of an inductive type, or two types whose erasures
  are neutral.
* **The facts** (`CFormFacts`): equal types of a formed context that are in weak-head
  form match.

From the facts:

* the injectivity and no-confusion of the type formers (`CFormFacts.formers`);
* a type equal to a neutral type is neutral when it is in weak-head form
  (`CTypeEq.neutral_form`), and a neutral type is equal to no type former and to no type
  constant of an inductive type (`CTypeEq.neutral_ne_former`, `CTypeEq.neutral_ne_inductive`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (Roles Neutral IsTypeForm Field)

variable {Head : Type} {R : Rules Head}

/-! ## Weak-head forms, through the erasure -/

section Forms

variable {roles : Roles Head} {n : Nat}

/-- A type former is in weak-head form. -/
theorem CFormer.typeForm {A : CTm Head n} (former : CFormer A) : IsTypeForm roles A.erase := by
  cases former with
  | head h => exact .inl ⟨h, rfl⟩
  | pi A B => exact .inr (.inl ⟨_, _, rfl⟩)
  | sigma A B => exact .inr (.inr (.inl ⟨_, _, rfl⟩))
  | id A a b => exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))

/-- The erasure of a type former is not neutral. -/
theorem CFormer.not_neutral {A : CTm Head n} (former : CFormer A) : ¬ Neutral roles A.erase := by
  intro neutral
  cases former with
  | head h => exact neutral.not_former.1 h rfl
  | pi A B => exact neutral.not_former.2.1 _ _ rfl
  | sigma A B => exact neutral.not_former.2.2.1 _ _ rfl
  | id A a b => exact neutral.not_former.2.2.2 _ _ _ rfl

/-- **The weak-head forms of annotated types**: a type whose erasure is in weak-head form
is a type former, the type constant of an inductive type, or has a neutral erasure. -/
theorem typeForm_erase_cases {A : CTm Head n} (form : IsTypeForm roles A.erase) :
    CFormer A ∨ (∃ T ctors, roles T = .inductive ctors ∧ A = .const T) ∨ Neutral roles A.erase := by
  rcases form with ⟨h, e⟩ | ⟨X, Y, e⟩ | ⟨X, Y, e⟩ | ⟨X, a, b, e⟩ | neutral |
    ⟨T, ctors, role, e⟩
  · cases A <;> cases e
    exact .inl (.head _)
  · cases A <;> cases e
    exact .inl (.pi _ _)
  · cases A <;> cases e
    exact .inl (.sigma _ _)
  · cases A <;> cases e
    exact .inl (.id _ _ _)
  · exact .inr (.inr neutral)
  · cases A <;> cases e
    exact .inr (.inl ⟨T, ctors, role, rfl⟩)

end Forms

/-! ## Matching forms and the facts -/

section Facts

variable (P : ChurchRules R) (roles : Roles Head)

/-- **Two equal annotated types in weak-head form match**: the same former with equal
components, the same type constant of an inductive type, or two types whose erasures are
neutral. -/
def CFormsMatch {n : Nat} (Γ : CCtx Head n) (A B : CTm Head n) : Prop :=
  CFormersMatch P Γ A B ∨
    (∃ T ctors, roles T = .inductive ctors ∧ A = .const T ∧ B = .const T) ∨
    (Neutral roles A.erase ∧ Neutral roles B.erase)

/-- **The facts about the weak-head forms of annotated types**: equal types of a formed
context that are in weak-head form match. -/
structure CFormFacts : Prop where
  forms : ∀ {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}, CTypeEq P Γ A B → CCtxFormed P Γ →
    IsTypeForm roles A.erase → IsTypeForm roles B.erase → CFormsMatch P roles Γ A B

end Facts

section Consequences

variable {P : ChurchRules R} {roles : Roles Head} {n : Nat} {Γ : CCtx Head n}

/-- The right side of matching formers is a type former. -/
theorem CFormersMatch.right {A B : CTm Head n} (m : CFormersMatch P Γ A B) : CFormer B := by
  rcases m with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ |
    ⟨_, _, _, _, _, _, _, rfl, _⟩
  · exact .head _
  · exact .pi _ _
  · exact .sigma _ _
  · exact .id _ _ _

/-- A type former matching a type in weak-head form matches it as a type former. -/
theorem CFormsMatch.formers_left {A B : CTm Head n} (former : CFormer A)
    (m : CFormsMatch P roles Γ A B) : CFormersMatch P Γ A B := by
  rcases m with m | ⟨T, _, _, rfl, _⟩ | ⟨neutral, _⟩
  · exact m
  · cases former
  · exact absurd neutral former.not_neutral

/-- A neutral type matches only neutral types. -/
theorem CFormsMatch.neutral_left {A B : CTm Head n} (neutral : Neutral roles A.erase)
    (m : CFormsMatch P roles Γ A B) : Neutral roles B.erase := by
  rcases m with m | ⟨T, _, role, rfl, _⟩ | ⟨_, neutral'⟩
  · rcases m with ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ |
      ⟨_, _, _, _, _, _, rfl, _⟩
    · exact absurd neutral (CFormer.head _).not_neutral
    · exact absurd neutral (CFormer.pi _ _).not_neutral
    · exact absurd neutral (CFormer.sigma _ _).not_neutral
    · exact absurd neutral (CFormer.id _ _ _).not_neutral
  · exact absurd rfl (neutral.ne_inductive role)
  · exact neutral'

variable (facts : CFormFacts P roles)
include facts

/-- **The injectivity and no-confusion of the type formers** follow from the facts. -/
theorem CFormFacts.formers : CFormerFacts P where
  forms equal formed former former' :=
    (facts.forms equal formed former.typeForm former'.typeForm).formers_left former

/-- A type equal to a neutral type is neutral when it is in weak-head form. -/
theorem CTypeEq.neutral_form {A B : CTm Head n} (equal : CTypeEq P Γ A B)
    (formed : CCtxFormed P Γ) (neutral : Neutral roles A.erase) (form : IsTypeForm roles B.erase) :
    Neutral roles B.erase :=
  (facts.forms equal formed (.inr (.inr (.inr (.inr (.inl neutral))))) form).neutral_left neutral

/-- A neutral type is equal to no type former. -/
theorem CTypeEq.neutral_ne_former {A B : CTm Head n} (formed : CCtxFormed P Γ)
    (neutral : Neutral roles A.erase) (former : CFormer B) : ¬ CTypeEq P Γ A B := fun equal =>
  former.not_neutral (CTypeEq.neutral_form facts equal formed neutral former.typeForm)

/-- A neutral type is equal to no type constant of an inductive type. -/
theorem CTypeEq.neutral_ne_inductive {A : CTm Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))} (formed : CCtxFormed P Γ)
    (neutral : Neutral roles A.erase) (role : roles T = .inductive ctors) :
    ¬ CTypeEq P Γ A (.const T) := fun equal =>
  (CTypeEq.neutral_form facts equal formed neutral
    (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))).ne_inductive role rfl

end Consequences

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
