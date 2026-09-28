import Mettapedia.Languages.Agda.Adequacy.StaticObservationViews

/-!
# Evidence retained by static reflection

An interpretation records successful observation equations and an actual
derivation in the independently authored calculus. The indexed motive is
conditional only on observation of the ambient raw context. Context formation
itself returns its observed context and its formation derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Reflection

open Structural.Statics

theorem observed_unique {α : Type} {input : Option α} {a b : α}
    (first : input = some a) (second : input = some b) : a = b :=
  Option.some.inj (first.symm.trans second)

structure Context {n : Nat} (Γ : RawContext n) where
  value : StaticSpecification.RawContext n
  observed : Observation.context Γ = some value
  proof : StaticSpecification.FormCtx value

structure Formation {n : Nat} (Δ : StaticSpecification.RawContext n) (A : RawTy n) where
  value : StaticSpecification.Ty n
  observed : Observation.type A = some value
  proof : StaticSpecification.FormTy Δ value

structure Typing {n : Nat} (Δ : StaticSpecification.RawContext n) (t : RawTm n) (A : RawTy n) where
  value : StaticSpecification.Term n
  typeValue : StaticSpecification.Ty n
  observed : Observation.term t = some value
  typeObserved : Observation.type A = some typeValue
  proof : StaticSpecification.Typing Δ value typeValue

structure TypeEquality {n : Nat} (Δ : StaticSpecification.RawContext n) (A B : RawTy n) where
  left : StaticSpecification.Ty n
  right : StaticSpecification.Ty n
  leftObserved : Observation.type A = some left
  rightObserved : Observation.type B = some right
  proof : StaticSpecification.TypeEq Δ left right

structure TermEquality {n : Nat} (Δ : StaticSpecification.RawContext n)
    (t u : RawTm n) (A : RawTy n) where
  left : StaticSpecification.Term n
  right : StaticSpecification.Term n
  typeValue : StaticSpecification.Ty n
  leftObserved : Observation.term t = some left
  rightObserved : Observation.term u = some right
  typeObserved : Observation.type A = some typeValue
  proof : StaticSpecification.TermEq Δ left right typeValue

def Context.at {n : Nat} {Γ : RawContext n} (c : Context Γ)
    {Δ : StaticSpecification.RawContext n} (observed : Observation.context Γ = some Δ) :
    StaticSpecification.FormCtx Δ := (observed_unique c.observed observed) ▸ c.proof

def Formation.at {n : Nat} {Δ : StaticSpecification.RawContext n} {A : RawTy n}
    (c : Formation Δ A) {a : StaticSpecification.Ty n} (observed : Observation.type A = some a) :
    StaticSpecification.FormTy Δ a := (observed_unique c.observed observed) ▸ c.proof

def Typing.atType {n : Nat} {Δ : StaticSpecification.RawContext n} {t : RawTm n} {A : RawTy n}
    (c : Typing Δ t A) {a : StaticSpecification.Ty n} (observed : Observation.type A = some a) :
    StaticSpecification.Typing Δ c.value a := (observed_unique c.typeObserved observed) ▸ c.proof

def Typing.at {n : Nat} {Δ : StaticSpecification.RawContext n} {t : RawTm n} {A : RawTy n}
    (c : Typing Δ t A) {f : StaticSpecification.Term n} {a : StaticSpecification.Ty n}
    (termObserved : Observation.term t = some f) (typeObserved : Observation.type A = some a) :
    StaticSpecification.Typing Δ f a :=
  (observed_unique c.observed termObserved) ▸ c.atType typeObserved

def TypeEquality.at {n : Nat} {Δ : StaticSpecification.RawContext n} {A B : RawTy n}
    (c : TypeEquality Δ A B) {a b : StaticSpecification.Ty n}
    (first : Observation.type A = some a) (second : Observation.type B = some b) :
    StaticSpecification.TypeEq Δ a b :=
  (observed_unique c.leftObserved first) ▸ (observed_unique c.rightObserved second) ▸ c.proof

def TermEquality.atType {n : Nat} {Δ : StaticSpecification.RawContext n} {t u : RawTm n} {A : RawTy n}
    (c : TermEquality Δ t u A) {a : StaticSpecification.Ty n} (observed : Observation.type A = some a) :
    StaticSpecification.TermEq Δ c.left c.right a :=
  (observed_unique c.typeObserved observed) ▸ c.proof

def TermEquality.at {n : Nat} {Δ : StaticSpecification.RawContext n} {t u : RawTm n} {A : RawTy n}
    (c : TermEquality Δ t u A) {f g : StaticSpecification.Term n} {a : StaticSpecification.Ty n}
    (first : Observation.term t = some f) (second : Observation.term u = some g)
    (typeObserved : Observation.type A = some a) : StaticSpecification.TermEq Δ f g a :=
  (observed_unique c.leftObserved first) ▸ (observed_unique c.rightObserved second) ▸ c.atType typeObserved

def Interpretation : Judgment → Type
  | .context ⟨_, Γ⟩ => Context Γ
  | .type ⟨_, Γ⟩ A => ∀ Δ, Observation.context Γ = some Δ → Formation Δ A
  | .term ⟨_, Γ⟩ A t => ∀ Δ, Observation.context Γ = some Δ → Typing Δ t.code A
  | .typeEquality ⟨_, Γ⟩ A B => ∀ Δ, Observation.context Γ = some Δ → TypeEquality Δ A B
  | .termEquality ⟨_, Γ⟩ A t u => ∀ Δ, Observation.context Γ = some Δ → TermEquality Δ t.code u.code A
  | .substitution _ _ _ => Empty

end Mettapedia.Languages.Agda.StaticAdequacy.Reflection
