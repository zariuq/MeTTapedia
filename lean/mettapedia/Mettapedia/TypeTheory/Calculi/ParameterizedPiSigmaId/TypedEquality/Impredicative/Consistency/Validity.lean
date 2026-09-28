import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Validity

/-!
# Validity in the consistency model

A type denotes, in a world, its interpretation at some level. Two
substitutions into a world are related at a context when they send each
variable to related terms of its substituted type.

* A type is valid when related substitutions give it one denotation.
* A term is valid at a valid type when related substitutions give related
  instances.
* Two terms are validly equal when related substitutions give related
  instances of the one and the other.
* A type is validly below another when, under related substitutions, the
  denotation of the first is included in that of the second.
* A context is valid when each entry is a valid type in the context before it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-- The denotation of a type in a world: its interpretation at some level. -/
def Den (M : Model Head L) {n : Nat} (ξ : World M.reading n) (A : Tm Head n) (R : Rel Head n) : Prop :=
  ∃ l, InterpAt M l ξ A R

/-- Substitutions into a world that send each variable of a context to related
terms of its type. -/
def EqSubst (M : Model Head L) : {n m : Nat} → Ctx Head n → World M.reading m → Sub Head n m →
    Sub Head n m → Prop
  | _, _, .nil, _, _, _ => True
  | _, _, .snoc Γ A, ξ, σ, σ' => EqSubst M Γ ξ (tailSub σ) (tailSub σ') ∧
      ∃ R, Den M ξ (Presentation.subst (tailSub σ) A) R ∧ R (σ 0) (σ' 0)

/-- A valid type: related substitutions give it one denotation. -/
def ValidTy (M : Model Head L) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Prop :=
  ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}, EqSubst M Γ ξ σ σ' →
    ∃ R, Den M ξ (Presentation.subst σ A) R ∧ Den M ξ (Presentation.subst σ' A) R

/-- A valid context: every entry is a valid type in the context before it. -/
def ValidCtx (M : Model Head L) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc Γ A => ValidCtx M Γ ∧ ValidTy M Γ A

/-- A valid term at a valid type. -/
def ValidTm (M : Model Head L) {n : Nat} (Γ : Ctx Head n) (t A : Tm Head n) : Prop :=
  ValidTy M Γ A ∧ ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m},
    EqSubst M Γ ξ σ σ' → ∀ {R}, Den M ξ (Presentation.subst σ A) R →
      R (Presentation.subst σ t) (Presentation.subst σ' t)

/-- Two valid terms that are validly equal. -/
def ValidEq (M : Model Head L) {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) : Prop :=
  ValidTm M Γ t A ∧ ValidTm M Γ u A ∧ ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m},
    EqSubst M Γ ξ σ σ' → ∀ {R}, Den M ξ (Presentation.subst σ A) R →
      R (Presentation.subst σ t) (Presentation.subst σ' u)

/-- A valid type whose denotation is included in that of another. -/
def ValidLe (M : Model Head L) {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ValidTy M Γ A ∧ ValidTy M Γ B ∧ ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m},
    EqSubst M Γ ξ σ σ' → ∀ {R R'}, Den M ξ (Presentation.subst σ A) R →
      Den M ξ (Presentation.subst σ B) R' → ∀ {a b}, R a b → R' a b

/-- What a statement means in the model. -/
def StatementValid (M : Model Head L) : Statement Head → Prop
  | .typing Γ t A => ValidCtx M Γ → ValidTm M Γ t A
  | .equality Γ a b A => ValidCtx M Γ → ValidEq M Γ a b A
  | .sub Γ A B => ValidCtx M Γ → ValidLe M Γ A B

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
