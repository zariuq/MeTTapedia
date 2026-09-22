import Mettapedia.Logic.HOL.Syntax.Type

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u}

/-- Typed de Bruijn variables. -/
inductive Var : Ctx Base → Ty Base → Type u where
  | vz : Var (τ :: Γ) τ
  | vs : Var Γ τ → Var (σ :: Γ) τ
deriving DecidableEq, Repr

/-- Intrinsically typed HOL terms. -/
inductive Term (Const : Ty Base → Type v) : Ctx Base → Ty Base → Type (max u v) where
  | var : Var Γ τ → Term Const Γ τ
  | const : Const τ → Term Const Γ τ
  | app : Term Const Γ (σ ⇒ τ) → Term Const Γ σ → Term Const Γ τ
  | lam : Term Const (σ :: Γ) τ → Term Const Γ (σ ⇒ τ)
  | top : Term Const Γ propTy
  | bot : Term Const Γ propTy
  | and : Term Const Γ propTy → Term Const Γ propTy → Term Const Γ propTy
  | or : Term Const Γ propTy → Term Const Γ propTy → Term Const Γ propTy
  | imp : Term Const Γ propTy → Term Const Γ propTy → Term Const Γ propTy
  | not : Term Const Γ propTy → Term Const Γ propTy
  | eq : Term Const Γ τ → Term Const Γ τ → Term Const Γ propTy
  | all : Term Const (σ :: Γ) propTy → Term Const Γ propTy
  | ex : Term Const (σ :: Γ) propTy → Term Const Γ propTy

/-- Formulas in context `Γ`. -/
abbrev Formula (Const : Ty Base → Type v) (Γ : Ctx Base) := Term Const Γ propTy

/-- Closed HOL formulas. -/
abbrev ClosedFormula (Const : Ty Base → Type v) := Formula Const []

/-- Sentences as a naming alias for closed formulas. -/
abbrev Sentence (Const : Ty Base → Type v) := ClosedFormula Const

namespace Var

/-- Convert `Fin n` to a typed variable in a repeated-type context. -/
def ofFinRepeat (τ : Ty Base) : (n : Nat) → Fin n → Var (List.replicate n τ) τ
  | 0, i => nomatch i
  | _ + 1, ⟨0, _⟩ => Var.vz
  | _ + 1, ⟨Nat.succ k, hk⟩ =>
      Var.vs (ofFinRepeat τ _ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

end Var

namespace Term

variable {Const : Ty Base → Type v}

/-- Number of term-constructor nodes. Type annotations and the representation
sizes of constants and variable indices are not charged by this measure. -/
def nodeCount : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Nat
  | _, _, .var _ | _, _, .const _ | _, _, .top | _, _, .bot => 1
  | _, _, .app f a => 1 + nodeCount f + nodeCount a
  | _, _, .lam b | _, _, .all b | _, _, .ex b => 1 + nodeCount b
  | _, _, .and p q | _, _, .or p q | _, _, .imp p q | _, _, .eq p q =>
      1 + nodeCount p + nodeCount q
  | _, _, .not p => 1 + nodeCount p

/-- Convenience constructor for implication. -/
abbrev implies (φ ψ : Formula Const Γ) : Formula Const Γ := Term.imp φ ψ

/-- Convenience constructor for conjunction. -/
abbrev conj (φ ψ : Formula Const Γ) : Formula Const Γ := Term.and φ ψ

/-- Convenience constructor for disjunction. -/
abbrev disj (φ ψ : Formula Const Γ) : Formula Const Γ := Term.or φ ψ

/-- Convenience constructor for negation. -/
abbrev neg (φ : Formula Const Γ) : Formula Const Γ := Term.not φ

end Term

end Mettapedia.Logic.HOL
