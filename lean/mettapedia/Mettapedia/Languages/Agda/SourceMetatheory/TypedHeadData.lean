import Mettapedia.Languages.Agda.SourceMetatheory.World

namespace Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead
open Mettapedia.Languages.Agda.SourceMetatheory.Kripke

def typedRedTrans {Γ : RawContext n} {t u v : Term n} {A : Ty n}
    (first : TypedRed Γ t u A) (second : TypedRed Γ u v A) : TypedRed Γ t v A :=
  match first with
  | .refl _ => second
  | .step next rest => .step next (typedRedTrans rest second)

def typedRedConvert {Γ : RawContext n} {t u : Term n} {A B : Ty n}
    (red : TypedRed Γ t u A) (eq : TypeEq Γ A B) : TypedRed Γ t u B :=
  match red with
  | .refl typed => .refl (.conv typed eq)
  | .step next rest => .step (.conv next eq) (typedRedConvert rest eq)

@[simp] theorem typeTerm_rename (A : Ty n) (ρ : Renaming n m) :
    (A.rename ρ).term = A.term.rename ρ := by cases A; rfl

@[simp] theorem typeTerm_subst (A : Ty n) (σ : Substitution n m) :
    (A.subst σ).term = A.term.subst σ := by cases A; rfl

/-- Exact annotations are retained; no cumulative retyping is introduced. -/
structure TypeRed (Γ : RawContext n) (A B : Ty n) where
  level : A.level = B.level
  steps : TypedRed Γ A.term B.term (Ty.universe A.level)

def TypeRed.equal {Γ : RawContext n} {A B : Ty n} (d : TypeRed Γ A B) : TypeEq Γ A B := by
  cases A with
  | el k a =>
      cases B with
      | el l b =>
          rcases d with ⟨levels, steps⟩
          change k = l at levels
          cases levels
          exact .atSort steps.equal

def TypeRed.refl {Γ : RawContext n} {A : Ty n} (formed : FormTy Γ A) : TypeRed Γ A A := by
  cases formed with
  | ofTyping typed => exact ⟨rfl, .refl typed⟩

def TypeRed.rename {Γ : RawContext n} {Δ : RawContext m} {ρ : Renaming n m}
    (world : World Γ Δ ρ) {A B : Ty n} (red : TypeRed Γ A B) :
    TypeRed Δ (A.rename ρ) (B.rename ρ) :=
  ⟨by simpa only [Ty.level_rename] using red.level,
    by simpa only [typeTerm_rename, Ty.level_rename, Ty.universe_rename] using
      world.reduction red.steps⟩

def TypeRed.substitute {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (substitution : SubDeriv Γ Δ σ) {A B : Ty n} (red : TypeRed Γ A B) :
    TypeRed Δ (A.subst σ) (B.subst σ) :=
  ⟨by simpa only [Ty.level_subst] using red.level,
    by simpa only [typeTerm_subst, Ty.level_subst, Ty.universe_subst] using
      red.steps.substitute substitution⟩

def TypeRed.trans {Γ : RawContext n} {A B C : Ty n}
    (first : TypeRed Γ A B) (second : TypeRed Γ B C) : TypeRed Γ A C :=
  ⟨first.level.trans second.level, typedRedTrans first.steps (first.level ▸ second.steps)⟩

inductive TypeHead : Term n → Type
  | neutral {t : Term n} : Neutral t → TypeHead t
  | sort (k : Nat) : TypeHead (.sort k)
  | pi (A : Ty n) (B : TyAbs n) : TypeHead (.pi A B)

def TypeHead.whnf {t : Term n} (head : TypeHead t) : Whnf t :=
  match head with
  | .neutral proof => .neutral proof
  | .sort k => .sort k
  | .pi A B => .pi A B

def TypeHead.rename {t : Term n} (head : TypeHead t) (ρ : Renaming n m) :
    TypeHead (t.rename ρ) :=
  match head with
  | .neutral proof => .neutral (proof.rename ρ)
  | .sort k => .sort k
  | .pi A B => .pi (A.rename ρ) (B.rename ρ)

inductive FunctionHead : Term n → Type
  | neutral {t : Term n} : Neutral t → FunctionHead t
  | lam (body : Abs n) : FunctionHead (.lam body)

def FunctionHead.whnf {t : Term n} (head : FunctionHead t) : Whnf t :=
  match head with
  | .neutral proof => .neutral proof
  | .lam body => .lam body

def FunctionHead.rename {t : Term n} (head : FunctionHead t) (ρ : Renaming n m) :
    FunctionHead (t.rename ρ) :=
  match head with
  | .neutral proof => .neutral (proof.rename ρ)
  | .lam body => .lam (body.rename ρ)

end Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData
