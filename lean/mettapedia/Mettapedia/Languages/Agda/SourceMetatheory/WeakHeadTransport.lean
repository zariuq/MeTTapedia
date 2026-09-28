import Mettapedia.Languages.Agda.SourceMetatheory.WeakHead

/-!
Renaming and substitution for explicit weak-head contraction evidence.
These functions map the premises of an already typed contraction. They do not
recover a typed contraction from an arbitrary raw step and a typing derivation.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.WeakHead
open Mettapedia.Languages.Agda.StaticSpecification

def Step.rename {t u : Term n} (d : Step t u) (ρ : Renaming n m) :
    Step (t.rename ρ) (u.rename ρ) :=
  match d with
  | .beta body argument => by
      simpa only [Term.app_rename, Term.rename, Abs.instantiate_rename] using
        Step.beta (body.rename ρ) (argument.rename ρ)
  | .head step => by simpa only [Term.app_rename] using Step.head (step.rename ρ)

def Step.substitute {t u : Term n} (d : Step t u) (σ : Substitution n m) :
    Step (t.subst σ) (u.subst σ) :=
  match d with
  | .beta body argument => by
      simpa only [Term.app_subst, Term.subst, Abs.instantiate_subst] using
        Step.beta (body.subst σ) (argument.subst σ)
  | .head step => by simpa only [Term.app_subst] using Step.head (step.substitute σ)

def Neutral.rename {t : Term n} (d : Neutral t) (ρ : Renaming n m) : Neutral (t.rename ρ) :=
  match d with
  | .var i => .var (ρ i)
  | .app head => by simpa only [Term.app_rename] using Neutral.app (head.rename ρ)

def Whnf.rename {t : Term n} (d : Whnf t) (ρ : Renaming n m) : Whnf (t.rename ρ) :=
  match d with
  | .neutral head => .neutral (head.rename ρ)
  | .lam body => .lam (body.rename ρ)
  | .pi A B => .pi (A.rename ρ) (B.rename ρ)
  | .sort k => .sort k

def Red.rename {t u : Term n} (d : Red t u) (ρ : Renaming n m) :
    Red (t.rename ρ) (u.rename ρ) :=
  match d with
  | .refl _ => .refl _
  | .step first rest => .step (first.rename ρ) (rest.rename ρ)

def Red.substitute {t u : Term n} (d : Red t u) (σ : Substitution n m) :
    Red (t.subst σ) (u.subst σ) :=
  match d with
  | .refl _ => .refl _
  | .step first rest => .step (first.substitute σ) (rest.substitute σ)

def TypedStep.rename {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedStep Γ t u A) {Δ : RawContext m} (ρ : Renaming n m)
    (respects : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
    TypedStep Δ (t.rename ρ) (u.rename ρ) (A.rename ρ) :=
  match d with
  | .beta (A := A) (B := B) (body := body) domain codomain typed argument => by
      have da := domain.rename ρ respects formed
      have db := codomain.rename (Renaming.lift ρ) (respects.lift A) (.snoc formed da)
      have dt := typed.rename (Renaming.lift ρ) (respects.lift A) (.snoc formed da)
      simpa only [Term.app_rename, Term.rename, Abs.instantiate_rename,
        TyAbs.instantiate_rename] using
        TypedStep.beta (B := B.rename ρ) (body := body.rename ρ) da
          (by simpa only [TyAbs.open_rename] using db)
          (by simpa only [Abs.open_rename, TyAbs.open_rename] using dt)
          (argument.rename ρ respects formed)
  | .head (B := B) step argument => by
      simpa only [Term.app_rename, TyAbs.instantiate_rename] using
        TypedStep.head (B := B.rename ρ)
          (by simpa only [Ty.pi_rename] using step.rename ρ respects formed)
          (argument.rename ρ respects formed)
  | .conv step eq => .conv (step.rename ρ respects formed) (eq.rename ρ respects formed)
termination_by structural d

def TypedStep.substitute {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedStep Γ t u A) {Δ : RawContext m} {σ : Substitution n m}
    (substitution : SubDeriv Γ Δ σ) : TypedStep Δ (t.subst σ) (u.subst σ) (A.subst σ) :=
  match d with
  | .beta (B := B) (body := body) domain codomain typed argument => by
      have da := domain.substitute substitution
      have db := codomain.substitute (substitution.lift domain da)
      have dt := typed.substitute (substitution.lift domain da)
      simpa only [Term.app_subst, Term.subst, Abs.instantiate_subst,
        TyAbs.instantiate_subst] using
        TypedStep.beta (B := B.subst σ) (body := body.subst σ) da
          (by simpa only [TyAbs.open_subst] using db)
          (by simpa only [Abs.open_subst, TyAbs.open_subst] using dt)
          (argument.substitute substitution)
  | .head (B := B) step argument => by
      simpa only [Term.app_subst, TyAbs.instantiate_subst] using
        TypedStep.head (B := B.subst σ)
          (by simpa only [Ty.pi_subst] using step.substitute substitution)
          (argument.substitute substitution)
  | .conv step eq => .conv (step.substitute substitution) (eq.substitute substitution)
termination_by structural d

def TypedRed.rename {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedRed Γ t u A) {Δ : RawContext m} (ρ : Renaming n m)
    (respects : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
    TypedRed Δ (t.rename ρ) (u.rename ρ) (A.rename ρ) :=
  match d with
  | .refl typed => .refl (typed.rename ρ respects formed)
  | .step first rest => .step (first.rename ρ respects formed) (rest.rename ρ respects formed)

def TypedRed.substitute {Γ : RawContext n} {t u : Term n} {A : Ty n}
    (d : TypedRed Γ t u A) {Δ : RawContext m} {σ : Substitution n m}
    (substitution : SubDeriv Γ Δ σ) : TypedRed Δ (t.subst σ) (u.subst σ) (A.subst σ) :=
  match d with
  | .refl typed => .refl (typed.substitute substitution)
  | .step first rest => .step (first.substitute substitution) (rest.substitute substitution)

end Mettapedia.Languages.Agda.SourceMetatheory.WeakHead
