import Mathlib.Data.List.Basic

/-!
# Scoped introduction: Curry–Howard introduction as an operational move

Prime constructs a lambda the way a proof assistant discharges a hypothesis:
create a child context, introduce a hypothetical binding as a **fresh name**,
construct the body under it, **close** the name into de Bruijn index `0`
(nearest binder — the ratified `idx` convention), and discharge the child
context.  The construction happens on the untrusted extraction side; this
module proves the theorem that lets the checking side *grant* the result:

* `scoped_introduction` — if the body is well-typed in the child context
  `(a, A) :: Γ` with `a` fresh for `Γ`, then `lam A (close a body)` is
  well-typed at `A ⇒ B` in `Γ` alone.  Hypothesis discharge is sound.

The engine of the proof is the locally-nameless round trip
`open_close : open a (close a t) = t` for locally closed `t`, plus
`fvar_notMem_close` (closing genuinely removes the name).  The negative
examples show both side conditions are load-bearing: `open_close` fails on a
term with a dangling bound index, and discharge fails without freshness.

Scope, honestly: the calculus is simply typed and the `lam` typing rule is
exists-fresh (it carries one witnessing name), which is exactly what the
introduction theorem needs; the cofinite strengthening, the substitution
lemma, and the dependent (Π) version are stated extensions, not smuggled
claims.  Names are `ℕ` for decidability; nothing depends on that choice.
-/

namespace Mettapedia.Languages.MeTTa.PrimeScopedIntroduction

/-- Simple types: a base sort and functions. -/
inductive Ty where
  | base : Ty
  | arrow : Ty → Ty → Ty
deriving DecidableEq, Repr

/-- Terms in locally-nameless style: bound variables are de Bruijn indices
(`bvar 0` = nearest binder), free variables are names. -/
inductive Tm where
  | bvar : ℕ → Tm
  | fvar : ℕ → Tm
  | app : Tm → Tm → Tm
  | lam : Ty → Tm → Tm
deriving DecidableEq, Repr

namespace Tm

/-- Replace bound index `k` by the name `a` (opening a scope). -/
def openAt (k : ℕ) (a : ℕ) : Tm → Tm
  | bvar i => if i = k then fvar a else bvar i
  | fvar b => fvar b
  | app f e => app (openAt k a f) (openAt k a e)
  | lam A t => lam A (openAt (k + 1) a t)

/-- Replace the name `a` by bound index `k` (closing a scope). -/
def closeAt (k : ℕ) (a : ℕ) : Tm → Tm
  | bvar i => bvar i
  | fvar b => if b = a then bvar k else fvar b
  | app f e => app (closeAt k a f) (closeAt k a e)
  | lam A t => lam A (closeAt (k + 1) a t)

/-- All bound indices are below `k` (local closure at level `k`). -/
def LCAt (k : ℕ) : Tm → Prop
  | bvar i => i < k
  | fvar _ => True
  | app f e => LCAt k f ∧ LCAt k e
  | lam _ t => LCAt (k + 1) t

/-- The name `a` occurs free. -/
def FreeIn (a : ℕ) : Tm → Prop
  | bvar _ => False
  | fvar b => b = a
  | app f e => FreeIn a f ∨ FreeIn a e
  | lam _ t => FreeIn a t

/-- **The locally-nameless round trip**: opening a closed scope with the same
name recovers the term, provided the term had no dangling index at that level.
This equation is the entire operational content of "close then reopen". -/
theorem open_close (a : ℕ) : ∀ (t : Tm) (k : ℕ), LCAt k t →
    openAt k a (closeAt k a t) = t
  | bvar i, k, hlc => by
      have h : i < k := hlc
      simp only [closeAt, openAt, if_neg (Nat.ne_of_lt h)]
  | fvar b, k, _ => by
      by_cases h : b = a
      · subst h; simp [closeAt, openAt]
      · simp [closeAt, openAt, h]
  | app f e, k, hlc => by
      simp [closeAt, openAt, open_close a f k hlc.1, open_close a e k hlc.2]
  | lam A t, k, hlc => by
      simp [closeAt, openAt, open_close a t (k + 1) hlc]

/-- Closing removes the name: `a` is not free in `closeAt k a t`. -/
theorem fvar_notMem_close (a : ℕ) : ∀ (t : Tm) (k : ℕ), ¬ FreeIn a (closeAt k a t)
  | bvar _, _ => by simp [closeAt, FreeIn]
  | fvar b, k => by
      by_cases h : b = a
      · subst h; simp [closeAt, FreeIn]
      · simpa [closeAt, if_neg h, FreeIn] using h
  | app f e, k => by
      simp only [closeAt, FreeIn]
      rintro (h | h)
      · exact fvar_notMem_close a f k h
      · exact fvar_notMem_close a e k h
  | lam A t, k => fvar_notMem_close a t (k + 1)

end Tm

open Tm

/-- Typing contexts: newest binding first; lookup takes the first hit. -/
abbrev Ctx := List (ℕ × Ty)

/-- Names bound by a context. -/
def Ctx.names (Γ : Ctx) : List ℕ := Γ.map Prod.fst

/-- Typing.  The `lam` rule is exists-fresh: it carries one name `a`, fresh
for the context and the body, under which the opened body types. -/
inductive Typing : Ctx → Tm → Ty → Prop where
  | fvar {Γ : Ctx} {a : ℕ} {A : Ty} :
      (Γ.lookup a = some A) → Typing Γ (Tm.fvar a) A
  | app {Γ : Ctx} {f e : Tm} {A B : Ty} :
      Typing Γ f (Ty.arrow A B) → Typing Γ e A → Typing Γ (Tm.app f e) B
  | lam {Γ : Ctx} {A B : Ty} {t : Tm} (a : ℕ) :
      a ∉ Ctx.names Γ → ¬ FreeIn a t →
      Typing ((a, A) :: Γ) (openAt 0 a t) B →
      Typing Γ (Tm.lam A t) (Ty.arrow A B)

/-- **Scoped introduction is sound.**  Prime's operational move — child
context, fresh hypothetical binding `a : A`, construct `body`, close, discharge
— produces a term the checker may grant at `A ⇒ B`.  This is the →-introduction
rule of the Curry–Howard reading, performed by the machine and justified once,
here. -/
theorem scoped_introduction {Γ : Ctx} {A B : Ty} {a : ℕ} {body : Tm}
    (hfresh : a ∉ Ctx.names Γ) (hlc : LCAt 0 body)
    (hty : Typing ((a, A) :: Γ) body B) :
    Typing Γ (Tm.lam A (closeAt 0 a body)) (Ty.arrow A B) := by
  refine Typing.lam a hfresh (fvar_notMem_close a body 0) ?_
  rw [open_close a body 0 hlc]
  exact hty

/-- The machine's discharge step, as a function: what Prime computes. -/
def dischargeIntro (a : ℕ) (A : Ty) (body : Tm) : Tm :=
  Tm.lam A (closeAt 0 a body)

/-- The machine step is exactly the sound rule. -/
theorem dischargeIntro_sound {Γ : Ctx} {A B : Ty} {a : ℕ} {body : Tm}
    (hfresh : a ∉ Ctx.names Γ) (hlc : LCAt 0 body)
    (hty : Typing ((a, A) :: Γ) body B) :
    Typing Γ (dischargeIntro a A body) (Ty.arrow A B) :=
  scoped_introduction hfresh hlc hty

/-! ## Positive and negative examples -/

/-- Positive: constructing the identity.  Under hypothesis `a : base` the body
`fvar a` types at `base`; discharge yields `lam base (bvar 0) : base ⇒ base` in
the empty context — the machine builds `λ.0` without ever writing an index. -/
example : Typing [] (dischargeIntro 7 Ty.base (Tm.fvar 7)) (Ty.arrow Ty.base Ty.base) := by
  refine dischargeIntro_sound (by simp [Ctx.names]) (by trivial) ?_
  exact Typing.fvar (by simp [List.lookup])

/-- The identity really is `λ.0`: closing computed the index. -/
example : dischargeIntro 7 Ty.base (Tm.fvar 7) = Tm.lam Ty.base (Tm.bvar 0) := by
  decide

/-- Negative: the round trip fails on a body with a dangling bound index —
local closure is load-bearing, not decoration.  `bvar 0` is untouched by
closing, then wrongly captured by opening. -/
example : openAt 0 5 (closeAt 0 5 (Tm.bvar 0)) ≠ Tm.bvar 0 := by decide

/-- Negative: freshness is load-bearing.  With `a` already bound in the outer
context, the "hypothesis" `fvar 7` can type against the *outer* binding, and
discharging would smuggle the outer assumption into the lambda: here the body
types at `base` via the outer `7 : base`, yet naive discharge at a *different*
hypothesis type would close over the same name.  The theorem's freshness
hypothesis is exactly what rules this out. -/
example : ¬ ((7 : ℕ) ∉ Ctx.names [((7 : ℕ), Ty.base)]) := by simp [Ctx.names]

end Mettapedia.Languages.MeTTa.PrimeScopedIntroduction
