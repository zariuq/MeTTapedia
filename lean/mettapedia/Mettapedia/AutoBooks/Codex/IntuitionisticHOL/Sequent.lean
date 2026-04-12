import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Antecedent weakening along one context extension. -/
def weakenAntecedents (σ : Ty Base) (Δ : List (Formula Const Γ)) :
    List (Formula Const (σ :: Γ)) :=
  Δ.map (weaken (Base := Base) (σ := σ))

/-- Paper-facing sequent package. -/
structure Sequent (Const : Ty Base → Type v) (Γ : Ctx Base) where
  antecedents : List (Formula Const Γ)
  succedent : Formula Const Γ

/-- Cut-free sequent calculus for the initial soundness layer. -/
inductive Derivable (Const : Ty Base → Type v) :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop where
  | ax {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      φ ∈ Δ → Derivable Const Δ φ
  | topR {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
      Derivable Const Δ .top
  | botL {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
      Derivable Const (.bot :: Δ) φ
  | andL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivable Const (φ :: ψ :: Δ) χ →
      Derivable Const (.and φ ψ :: Δ) χ
  | andR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const Δ φ →
      Derivable Const Δ ψ →
      Derivable Const Δ (.and φ ψ)
  | orL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivable Const (φ :: Δ) χ →
      Derivable Const (ψ :: Δ) χ →
      Derivable Const (.or φ ψ :: Δ) χ
  | orR₁ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const Δ φ →
      Derivable Const Δ (.or φ ψ)
  | orR₂ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const Δ ψ →
      Derivable Const Δ (.or φ ψ)
  | impL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ χ : Formula Const Γ} :
      Derivable Const Δ φ →
      Derivable Const (ψ :: Δ) χ →
      Derivable Const (.imp φ ψ :: Δ) χ
  | impR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} :
      Derivable Const (φ :: Δ) ψ →
      Derivable Const Δ (.imp φ ψ)
  | allL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
      (t : Term Const Γ σ) :
      Derivable Const (instantiate (Base := Base) t φ :: Δ) χ →
      Derivable Const (.all φ :: Δ) χ
  | allR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} :
      Derivable Const (weakenAntecedents (Base := Base) (Const := Const) σ Δ) φ →
      Derivable Const Δ (.all φ)
  | exL {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {χ : Formula Const Γ} :
      Derivable Const
        (φ :: weakenAntecedents (Base := Base) (Const := Const) σ Δ)
        (weaken (Base := Base) (σ := σ) χ) →
      Derivable Const (.ex φ :: Δ) χ
  | exR {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
      {σ : Ty Base} {φ : Formula Const (σ :: Γ)}
      (t : Term Const Γ σ) :
      Derivable Const Δ (instantiate (Base := Base) t φ) →
      Derivable Const Δ (.ex φ)
  | lam {Γ : Ctx Base}
      {Δ Δ' : List (Formula Const Γ)}
      {φ φ' : Formula Const Γ} :
      AntecedentsBetaEtaEq (Base := Base) (Const := Const) Δ Δ' →
      BetaEtaEq (Base := Base) (Const := Const) φ φ' →
      Derivable Const Δ' φ' →
      Derivable Const Δ φ

namespace Derivable

/-- Closed theorems are derivations from an empty antecedent. -/
abbrev Theorem (Const : Ty Base → Type v) (φ : ClosedFormula Const) : Prop :=
  Derivable Const ([] : List (ClosedFormula Const)) φ

end Derivable

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
