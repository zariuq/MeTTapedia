import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.Lindenbaum
import Mettapedia.Logic.HOL.Syntax.Closed

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Fresh Codex-side paper layer for Henkin (1950).

Design choice:
- reuse the trusted HOL metalayer for typed terms, contexts, substitutions,
  and closed-theory notions;
- expose Henkin's paper-specific surface as a thin front-end with its own
  base sort and description operator.
-/

universe u

/-- Henkin's paper uses one non-propositional base type: individuals `ι`. -/
inductive Atom : Type
  | ind
  deriving DecidableEq, Repr

/-- Simple types for the Henkin (1950) presentation. -/
abbrev HTy : Type := Ty Atom

/-- The distinguished propositional type `o`. -/
abbrev o : HTy := propTy

/-- The individual type `ι`. -/
abbrev ι : HTy := .base .ind

/-- Predicates on a type `α`. -/
abbrev Pred (α : HTy) : HTy := α ⇒ o

/-- Henkin's definite-description constant `ι_{α(oα)}` for each simple type `α`. -/
inductive Primitive : HTy → Type
  | iota (α : HTy) : Primitive (Pred α ⇒ α)
  deriving DecidableEq, Repr

/-- Paper-facing typed variables. -/
abbrev Var (Γ : Ctx Atom) (τ : HTy) : Type := Mettapedia.Logic.HOL.Var Γ τ

/-- Paper-facing typed terms. -/
abbrev Term (Γ : Ctx Atom) (τ : HTy) : Type := Mettapedia.Logic.HOL.Term Primitive Γ τ

/-- Paper-facing formulas. -/
abbrev Formula (Γ : Ctx Atom) : Type := Mettapedia.Logic.HOL.Formula Primitive Γ

/-- Closed Henkin terms. -/
abbrev ClosedTerm (τ : HTy) : Type := Mettapedia.Logic.HOL.ClosedTerm Primitive τ

/-- Closed Henkin formulas. -/
abbrev Sentence : Type := Mettapedia.Logic.HOL.ClosedFormula Primitive

/-- Finite closed theories. -/
abbrev ClosedTheory : Type := Mettapedia.Logic.HOL.ClosedTheory Primitive

/-- Arbitrary closed theories as sets. -/
abbrev ClosedTheorySet : Type := Mettapedia.Logic.HOL.ClosedTheorySet Primitive

/-- Closed-theory derivability in the trusted HOL core. -/
abbrev Provable (Δ : ClosedTheory) (φ : Sentence) : Prop :=
  Mettapedia.Logic.HOL.ClosedTheory.Provable (Const := Primitive) Δ φ

/-- Set-based finite derivability in the trusted HOL core. -/
abbrev SetProvable (T : ClosedTheorySet) (φ : Sentence) : Prop :=
  Mettapedia.Logic.HOL.ClosedTheorySet.Provable (Const := Primitive) T φ

/-- Paper-facing alias for closed-theory consistency. -/
abbrev Consistent (T : ClosedTheorySet) : Prop :=
  Mettapedia.Logic.HOL.ClosedTheorySet.Consistent (Const := Primitive) T

/-- The innermost variable in a one-variable context. -/
def var0 (α : HTy) : Term [α] α := .var .vz

/-- Application of Henkin's definite-description operator. -/
def iotaTerm {Γ : Ctx Atom} {α : HTy} (p : Term Γ (Pred α)) : Term Γ α :=
  .app (.const (.iota α)) p

/-- Paper-facing implication. -/
def imp {Γ : Ctx Atom} (φ ψ : Formula Γ) : Formula Γ := .imp φ ψ

/-- Paper-facing conjunction. -/
def and {Γ : Ctx Atom} (φ ψ : Formula Γ) : Formula Γ := .and φ ψ

/-- Paper-facing disjunction. -/
def or {Γ : Ctx Atom} (φ ψ : Formula Γ) : Formula Γ := .or φ ψ

/-- Paper-facing negation. -/
def not {Γ : Ctx Atom} (φ : Formula Γ) : Formula Γ := .not φ

/-- Paper-facing equality. -/
def eq {Γ : Ctx Atom} {α : HTy} (t u : Term Γ α) : Formula Γ := .eq t u

/-- Universal closure of a one-variable formula. -/
def forall_ {α : HTy} (φ : Formula [α]) : Sentence := .all φ

/-- Existential closure of a one-variable formula. -/
def exists_ {α : HTy} (φ : Formula [α]) : Sentence := .ex φ

end Mettapedia.AutoBooks.Codex.Henkin1950
