import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

/-- Typed applicative structures with explicit lambda witnesses. -/
structure ApplicativeStructure (Base : Type u) (Const : Ty Base → Type v) where
  Carrier : Ty Base → Type w
  const : {τ : Ty Base} → Const τ → Carrier τ
  app : {σ τ : Ty Base} → Carrier (σ ⇒ τ) → Carrier σ → Carrier τ
  lam : {σ τ : Ty Base} → (Carrier σ → Carrier τ) → Carrier (σ ⇒ τ)
  beta : ∀ {σ τ : Ty Base} (f : Carrier σ → Carrier τ) (x : Carrier σ),
    app (lam f) x = f x
  eta : ∀ {σ τ : Ty Base} (f : Carrier (σ ⇒ τ)),
    lam (fun x => app f x) = f

namespace ApplicativeStructure

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Environments for open terms. -/
abbrev Env (M : ApplicativeStructure Base Const) (Γ : Ctx Base) :=
  ∀ {τ : Ty Base}, Var Γ τ → M.Carrier τ

namespace Env

/-- Extend an environment with one fresh variable. -/
def extend (M : ApplicativeStructure Base Const)
    (ρ : Env M Γ) (x : M.Carrier σ) : Env M (σ :: Γ)
  | _, .vz => x
  | _, .vs v => ρ v

@[simp] theorem extend_vz (M : ApplicativeStructure Base Const)
    (ρ : Env M Γ) (x : M.Carrier σ) :
    Env.extend M ρ x (.vz : Var (σ :: Γ) σ) = x := rfl

@[simp] theorem extend_vs (M : ApplicativeStructure Base Const)
    (ρ : Env M Γ) (x : M.Carrier σ) (v : Var Γ τ) :
    Env.extend M ρ x (.vs v) = ρ v := rfl

end Env

end ApplicativeStructure

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
