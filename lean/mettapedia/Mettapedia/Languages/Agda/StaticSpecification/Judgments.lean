import Mettapedia.Languages.Agda.StaticSpecification.Context

/-!
# Declarative finite-Set Pi judgments with retained derivations

The universe hierarchy and annotated Pi formation follow Cockx's Agda Core
`Syntax.agda`/`Typing.agda`, commit `2fb9574e78326ec532dcb2af8272631c765e947d`:
`sortType`, `piSort`, `TyType`, `TyPi`, `TyLam`, `TyAppE`, and `TyArg`.
Context formation and typed equality follow the Pi fragment of `logrel-mltt`,
`Definition.Typed`, commit `9d6e290064962a1987c9e1a131c2fb967d6ef928`.
Its single universe is replaced here by Cockx's predicative finite hierarchy.
All annotation levels are checked; there is no cumulativity rule.

Function eta is the typed extensionality rule `η-eq` of that reference, also
reflected by the `Pi`/`equalFun` branch of Agda 2.8.0.2
`TypeChecking.Conversion`, commit `cccf42fa88eae25ccbe2623f489021d2075f6f73`.
It requires both functions to have the stated Pi type and their weakened
applications to agree at the opened codomain. No untyped eta equation, evaluator,
decidability, completeness, or full Agda adequacy is asserted.

These are Type-valued finite derivation trees. Structural substitution is an
operation on the raw syntax, not a typing or conversion inference rule.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

mutual
  inductive FormCtx : {n : Nat} → RawContext n → Type
    /-- `logrel-mltt` context rule `ε`. -/
    | nil : FormCtx .nil
    /-- `logrel-mltt` context extension, retaining the type formation tree. -/
    | snoc {Γ : RawContext n} {a : Ty n} : FormCtx Γ → FormTy Γ a → FormCtx (Γ.snoc a)

  inductive FormTy : {n : Nat} → RawContext n → Ty n → Type
    /-- `univ`, with the `El` annotation checked in its declared finite Set. -/
    | ofTyping {Γ : RawContext n} {k : Nat} {a : Term n} :
        Typing Γ a (Ty.universe k) → FormTy Γ (.el k a)

  inductive Typing : {n : Nat} → RawContext n → Term n → Ty n → Type
    /-- `TyType`: Set k itself inhabits Set (k + 1). -/
    | sort {Γ : RawContext n} (k : Nat) :
        FormCtx Γ → Typing Γ (.sort k) (Ty.universe (k + 1))
    /-- `var`, using the fully weakened telescope lookup. -/
    | var {Γ : RawContext n} (i : Fin n) :
        FormCtx Γ → Typing Γ (.var i) (Γ.lookup i)
    /-- `TyPi` and `piSort`; the codomain is formed in the extended context. -/
    | pi {Γ : RawContext n} {a : Ty n} {b : TyAbs n} :
        FormTy Γ a → FormTy (Γ.snoc a) b.open →
        Typing Γ (.pi a b) (Ty.universe (max a.level b.level))
    /-- `lamⱼ`, with explicit domain/codomain formation premises. -/
    | lam {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {body : Abs n} :
        FormTy Γ a → FormTy (Γ.snoc a) b.open →
        Typing (Γ.snoc a) body.open b.open → Typing Γ (.lam body) (Ty.pi a b)
    /-- `TyAppE`/`TyArg`, restricted to ordinary relevant argument elimination. -/
    | app {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {f u : Term n} :
        Typing Γ f (Ty.pi a b) → Typing Γ u a →
        Typing Γ (f.app u) (b.instantiate u)
    /-- Typed `conv`; the source and target types have the same checked sort. -/
    | conv {Γ : RawContext n} {t : Term n} {a b : Ty n} :
        Typing Γ t a → TypeEq Γ a b → Typing Γ t b

  inductive TypeEq : {n : Nat} → RawContext n → Ty n → Ty n → Type
    /-- `univ` for type equality, at one fixed finite Set level. -/
    | atSort {Γ : RawContext n} {k : Nat} {a b : Term n} :
        TermEq Γ a b (Ty.universe k) → TypeEq Γ (.el k a) (.el k b)

  inductive TermEq : {n : Nat} → RawContext n → Term n → Term n → Ty n → Type
    /-- Typed reflexivity, symmetry, and transitivity from `Definition.Typed`. -/
    | refl {Γ : RawContext n} {t : Term n} {a : Ty n} :
        Typing Γ t a → TermEq Γ t t a
    | symm {Γ : RawContext n} {t u : Term n} {a : Ty n} :
        TermEq Γ t u a → TermEq Γ u t a
    | trans {Γ : RawContext n} {t u v : Term n} {a : Ty n} :
        TermEq Γ t u a → TermEq Γ u v a → TermEq Γ t v a
    /-- Typed equality conversion from `Definition.Typed`. -/
    | conv {Γ : RawContext n} {t u : Term n} {a b : Ty n} :
        TermEq Γ t u a → TypeEq Γ a b → TermEq Γ t u b
    /-- `Π-cong`: compare codomains under the source domain. -/
    | piCong {Γ : RawContext n} {a a' : Ty n} {b b' : TyAbs n} :
        FormTy Γ a → TypeEq Γ a a' → TypeEq (Γ.snoc a) b.open b'.open →
        TermEq Γ (.pi a b) (.pi a' b') (Ty.universe (max a.level b.level))
    /-- `app-cong`; its result type uses the left argument, as in the source. -/
    | appCong {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {f g u v : Term n} :
        TermEq Γ f g (Ty.pi a b) → TermEq Γ u v a →
        TermEq Γ (f.app u) (g.app v) (b.instantiate u)
    /-- Typed `β-red`; both binding and non-binding abstractions are opened. -/
    | beta {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {body : Abs n} {u : Term n} :
        FormTy Γ a → FormTy (Γ.snoc a) b.open →
        Typing (Γ.snoc a) body.open b.open → Typing Γ u a →
        TermEq Γ ((Term.lam body).app u) (body.instantiate u) (b.instantiate u)
    /-- Typed function `η-eq`, with the actual extended-context comparison. -/
    | eta {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {f g : Term n} :
        FormTy Γ a → FormTy (Γ.snoc a) b.open →
        Typing Γ f (Ty.pi a b) → Typing Γ g (Ty.pi a b) →
        TermEq (Γ.snoc a) (f.weaken.app (.var 0)) (g.weaken.app (.var 0)) b.open →
        TermEq Γ f g (Ty.pi a b)
end

def FormTy.universe {Γ : RawContext n} (formed : FormCtx Γ) (k : Nat) :
    FormTy Γ (Ty.universe k) := .ofTyping (.sort k formed)

def FormTy.pi {Γ : RawContext n} {a : Ty n} {b : TyAbs n}
    (domain : FormTy Γ a) (codomain : FormTy (Γ.snoc a) b.open) :
    FormTy Γ (Ty.pi a b) := .ofTyping (.pi domain codomain)

def TypeEq.refl {Γ : RawContext n} {a : Ty n} (formed : FormTy Γ a) : TypeEq Γ a a :=
  match formed with | .ofTyping d => .atSort (.refl d)

def TypeEq.symm {Γ : RawContext n} {a b : Ty n} (d : TypeEq Γ a b) : TypeEq Γ b a :=
  match d with | .atSort e => .atSort (.symm e)

def TypeEq.trans {Γ : RawContext n} {a b c : Ty n}
    (d : TypeEq Γ a b) (e : TypeEq Γ b c) : TypeEq Γ a c :=
  match d, e with | .atSort d, .atSort e => .atSort (.trans d e)

/-- Consecutive ordinary eliminations, with the intermediate types retained. -/
inductive SpineTyping {n : Nat} (Γ : RawContext n) :
    Term n → Ty n → Spine n → Ty n → Type
  | nil {f : Term n} {a : Ty n} : Typing Γ f a → SpineTyping Γ f a [] a
  | cons {f u : Term n} {a : Ty n} {b : TyAbs n} {es : Spine n} {c : Ty n} :
      Typing Γ f (Ty.pi a b) → Typing Γ u a →
      SpineTyping Γ (f.app u) (b.instantiate u) es c →
      SpineTyping Γ f (Ty.pi a b) (.apply u :: es) c

def SpineTyping.typing {Γ : RawContext n} {f : Term n} {a b : Ty n} {es : Spine n}
    (d : SpineTyping Γ f a es b) : Typing Γ (f.applySpine es) b :=
  match d with
  | .nil h => h
  | .cons _ _ rest => rest.typing

end Mettapedia.Languages.Agda.StaticSpecification
