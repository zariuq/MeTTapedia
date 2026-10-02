import Mathlib.Logic.Function.Basic

/-!
# A simply typed calculus over booleans, with products and propositions

Types are booleans, propositions, binary products and functions.  Terms are
intrinsically typed with de Bruijn variables.  Booleans have the constructors
`tt`, `ff` and the eliminator `ite`; products have `pair` with the projections
`fst`, `snd`; functions have `lam` and `app`.  The proposition sort follows the
propositional fragment of observational type theory: `top`, `bot`, conjunction,
implication, quantification over booleans, and the atomic proposition
`isTrue b` for a boolean `b`.  No term eliminates a proposition into data.

This module gives the syntax, renaming and simultaneous substitution, and the
erasure of a term to its untyped `Code`, which a code observer can inspect.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-- Simple types: booleans, propositions, binary products and functions. -/
inductive Ty where
  | bool : Ty
  | prop : Ty
  | prod (left right : Ty) : Ty
  | arr (domain codomain : Ty) : Ty
  deriving DecidableEq, Repr

/-- Typing contexts, newest variable first. -/
abbrev Ctx := List Ty

/-- Typed de Bruijn variables. -/
inductive Var : Ctx → Ty → Type where
  | zero {Γ : Ctx} {A : Ty} : Var (A :: Γ) A
  | succ {Γ : Ctx} {A B : Ty} : Var Γ A → Var (B :: Γ) A

/-- Intrinsically typed terms. -/
inductive Tm : Ctx → Ty → Type where
  | var {Γ : Ctx} {A : Ty} : Var Γ A → Tm Γ A
  | tt {Γ : Ctx} : Tm Γ .bool
  | ff {Γ : Ctx} : Tm Γ .bool
  | ite {Γ : Ctx} {A : Ty} : Tm Γ .bool → Tm Γ A → Tm Γ A → Tm Γ A
  | pair {Γ : Ctx} {A B : Ty} : Tm Γ A → Tm Γ B → Tm Γ (.prod A B)
  | fst {Γ : Ctx} {A B : Ty} : Tm Γ (.prod A B) → Tm Γ A
  | snd {Γ : Ctx} {A B : Ty} : Tm Γ (.prod A B) → Tm Γ B
  | lam {Γ : Ctx} {A B : Ty} : Tm (A :: Γ) B → Tm Γ (.arr A B)
  | app {Γ : Ctx} {A B : Ty} : Tm Γ (.arr A B) → Tm Γ A → Tm Γ B
  | top {Γ : Ctx} : Tm Γ .prop
  | bot {Γ : Ctx} : Tm Γ .prop
  | and {Γ : Ctx} : Tm Γ .prop → Tm Γ .prop → Tm Γ .prop
  | imp {Γ : Ctx} : Tm Γ .prop → Tm Γ .prop → Tm Γ .prop
  | isTrue {Γ : Ctx} : Tm Γ .bool → Tm Γ .prop
  | allBool {Γ : Ctx} : Tm (.bool :: Γ) .prop → Tm Γ .prop

/-- Closed terms. -/
abbrev Closed (A : Ty) : Type := Tm [] A

/-! ## Renaming -/

/-- Renamings between contexts. -/
abbrev Ren (Γ Δ : Ctx) : Type := ∀ ⦃A : Ty⦄, Var Γ A → Var Δ A

/-- Extend a renaming under a binder. -/
def Ren.lift {Γ Δ : Ctx} {B : Ty} (ρ : Ren Γ Δ) : Ren (B :: Γ) (B :: Δ) :=
  fun _ v => match v with
    | .zero => .zero
    | .succ w => .succ (ρ w)

/-- Weakening by one variable. -/
def Ren.weaken {Γ : Ctx} {B : Ty} : Ren Γ (B :: Γ) :=
  fun _ v => .succ v

/-- The empty context renames into every context. -/
def Ren.ofEmpty {Γ : Ctx} : Ren [] Γ :=
  fun _ v => nomatch v

/-- Apply a renaming to a term. -/
def Tm.rename : {Γ Δ : Ctx} → Ren Γ Δ → {A : Ty} → Tm Γ A → Tm Δ A
  | _, _, ρ, _, .var v => .var (ρ v)
  | _, _, _, _, .tt => .tt
  | _, _, _, _, .ff => .ff
  | _, _, ρ, _, .ite c t e => .ite (c.rename ρ) (t.rename ρ) (e.rename ρ)
  | _, _, ρ, _, .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | _, _, ρ, _, .fst p => .fst (p.rename ρ)
  | _, _, ρ, _, .snd p => .snd (p.rename ρ)
  | _, _, ρ, _, .lam b => .lam (b.rename ρ.lift)
  | _, _, ρ, _, .app f a => .app (f.rename ρ) (a.rename ρ)
  | _, _, _, _, .top => .top
  | _, _, _, _, .bot => .bot
  | _, _, ρ, _, .and p q => .and (p.rename ρ) (q.rename ρ)
  | _, _, ρ, _, .imp p q => .imp (p.rename ρ) (q.rename ρ)
  | _, _, ρ, _, .isTrue b => .isTrue (b.rename ρ)
  | _, _, ρ, _, .allBool b => .allBool (b.rename ρ.lift)

/-- A closed term, weakened into any context. -/
def Tm.weaken {Γ : Ctx} {A : Ty} (t : Closed A) : Tm Γ A :=
  t.rename Ren.ofEmpty

/-! ## Simultaneous substitution -/

/-- Substitutions from `Γ` into terms over `Δ`. -/
abbrev Sub (Γ Δ : Ctx) : Type := ∀ ⦃A : Ty⦄, Var Γ A → Tm Δ A

/-- Extend a substitution under a binder. -/
def Sub.lift {Γ Δ : Ctx} {B : Ty} (σ : Sub Γ Δ) : Sub (B :: Γ) (B :: Δ) :=
  fun _ v => match v with
    | .zero => .var .zero
    | .succ w => (σ w).rename Ren.weaken

/-- Substitute a term for the newest variable, and `σ` for the others. -/
def Sub.cons {Γ Δ : Ctx} {A : Ty} (a : Tm Δ A) (σ : Sub Γ Δ) : Sub (A :: Γ) Δ :=
  fun _ v => match v with
    | .zero => a
    | .succ w => σ w

/-- The substitution out of the empty context. -/
def Sub.ofEmpty {Δ : Ctx} : Sub [] Δ :=
  fun _ v => nomatch v

/-- Apply a substitution to a term. -/
def Tm.subst : {Γ Δ : Ctx} → Sub Γ Δ → {A : Ty} → Tm Γ A → Tm Δ A
  | _, _, σ, _, .var v => σ v
  | _, _, _, _, .tt => .tt
  | _, _, _, _, .ff => .ff
  | _, _, σ, _, .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)
  | _, _, σ, _, .pair a b => .pair (a.subst σ) (b.subst σ)
  | _, _, σ, _, .fst p => .fst (p.subst σ)
  | _, _, σ, _, .snd p => .snd (p.subst σ)
  | _, _, σ, _, .lam b => .lam (b.subst σ.lift)
  | _, _, σ, _, .app f a => .app (f.subst σ) (a.subst σ)
  | _, _, _, _, .top => .top
  | _, _, _, _, .bot => .bot
  | _, _, σ, _, .and p q => .and (p.subst σ) (q.subst σ)
  | _, _, σ, _, .imp p q => .imp (p.subst σ) (q.subst σ)
  | _, _, σ, _, .isTrue b => .isTrue (b.subst σ)
  | _, _, σ, _, .allBool b => .allBool (b.subst σ.lift)

/-- Plug a closed term into a term with one free variable. -/
def Tm.fill {A B : Ty} (body : Tm [A] B) (argument : Closed A) : Closed B :=
  body.subst (Sub.cons argument Sub.ofEmpty)

/-- The boolean constant of a Lean boolean. -/
def Tm.ofBool {Γ : Ctx} : Bool → Tm Γ .bool
  | true => .tt
  | false => .ff

/-! ## Codes: the untyped syntax a code observer reads -/

/-- Untyped syntax with the domain of every abstraction recorded. -/
inductive Code where
  | var (index : Nat)
  | tt
  | ff
  | ite (condition onTrue onFalse : Code)
  | pair (left right : Code)
  | fst (pair : Code)
  | snd (pair : Code)
  | lam (domain : Ty) (body : Code)
  | app (function argument : Code)
  | top
  | bot
  | and (left right : Code)
  | imp (left right : Code)
  | isTrue (boolean : Code)
  | allBool (body : Code)
  deriving DecidableEq, Repr

/-- The de Bruijn index of a variable. -/
def Var.index : {Γ : Ctx} → {A : Ty} → Var Γ A → Nat
  | _, _, .zero => 0
  | _, _, .succ v => v.index + 1

/-- Erase a term to its code. -/
def Tm.code : {Γ : Ctx} → {A : Ty} → Tm Γ A → Code
  | _, _, .var v => .var v.index
  | _, _, .tt => .tt
  | _, _, .ff => .ff
  | _, _, .ite c t e => .ite c.code t.code e.code
  | _, _, .pair a b => .pair a.code b.code
  | _, _, .fst p => .fst p.code
  | _, _, .snd p => .snd p.code
  | _, _, @Tm.lam _ A _ b => .lam A b.code
  | _, _, .app f a => .app f.code a.code
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q => .and p.code q.code
  | _, _, .imp p q => .imp p.code q.code
  | _, _, .isTrue b => .isTrue b.code
  | _, _, .allBool b => .allBool b.code

end Mettapedia.TypeTheory.Calculi.BooleanSTLC
