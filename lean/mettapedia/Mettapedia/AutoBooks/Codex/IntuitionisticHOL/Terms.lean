import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Types
import Mettapedia.Logic.HOL.Syntax.Subst

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

export Mettapedia.Logic.HOL
  (Var Term Formula ClosedFormula Sentence Rename Subst rename subst weaken instantiate)

/-- Beta-eta convertibility for typed HOL terms. -/
inductive BetaEtaEq : Term Const Γ τ → Term Const Γ τ → Prop where
  | refl (t : Term Const Γ τ) : BetaEtaEq t t
  | symm : BetaEtaEq t u → BetaEtaEq u t
  | trans : BetaEtaEq t u → BetaEtaEq u v → BetaEtaEq t v
  | app : BetaEtaEq f f' → BetaEtaEq t t' → BetaEtaEq (.app f t) (.app f' t')
  | lam : BetaEtaEq t u → BetaEtaEq (.lam t) (.lam u)
  | and : BetaEtaEq φ φ' → BetaEtaEq ψ ψ' → BetaEtaEq (.and φ ψ) (.and φ' ψ')
  | or : BetaEtaEq φ φ' → BetaEtaEq ψ ψ' → BetaEtaEq (.or φ ψ) (.or φ' ψ')
  | imp : BetaEtaEq φ φ' → BetaEtaEq ψ ψ' → BetaEtaEq (.imp φ ψ) (.imp φ' ψ')
  | not : BetaEtaEq φ φ' → BetaEtaEq (.not φ) (.not φ')
  | eq : BetaEtaEq t t' → BetaEtaEq u u' → BetaEtaEq (.eq t u) (.eq t' u')
  | all : BetaEtaEq φ φ' → BetaEtaEq (.all φ) (.all φ')
  | ex : BetaEtaEq φ φ' → BetaEtaEq (.ex φ) (.ex φ')
  | beta (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
      BetaEtaEq (.app (.lam u) t) (instantiate (Base := Base) t u)
  | eta (f : Term Const Γ (σ ⇒ τ)) :
      BetaEtaEq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f

/-- Pointwise beta-eta convertibility for antecedent lists. -/
inductive AntecedentsBetaEtaEq :
    List (Formula Const Γ) → List (Formula Const Γ) → Prop where
  | nil : AntecedentsBetaEtaEq [] []
  | cons : BetaEtaEq φ ψ →
      AntecedentsBetaEtaEq Δ Δ' →
      AntecedentsBetaEtaEq (φ :: Δ) (ψ :: Δ')

namespace AntecedentsBetaEtaEq

@[refl] theorem refl (Δ : List (Formula Const Γ)) : AntecedentsBetaEtaEq Δ Δ := by
  induction Δ with
  | nil => exact .nil
  | cons φ Δ ih => exact .cons (BetaEtaEq.refl φ) ih

end AntecedentsBetaEtaEq

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
