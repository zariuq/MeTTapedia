import Mettapedia.Logic.HOL.Syntax.ConstMap

/-!
# Fresh parameter constants (Henkin witnesses / diagram constants)

To prove completeness via a canonical term model we must introduce *fresh*
witness constants for existential statements (the Henkin construction) and,
dually, fresh counterexample constants for failed universals.  This file adds,
to any constant family `Const`, a countable family of fresh parameter constants
**at every type** — including empty base types, which is what makes the
canonical model's domains nonempty over an empty original signature (the
standard `∃x:b.⊤` conservativity subtlety).

`WithParams Const σ := Const σ ⊕ Nat`.  The left injection `inj` embeds the
original signature; `param σ n` is the `n`-th fresh constant at type `σ`.

The load-bearing fact is `noConstOccurrence_param_of_inj`: an image
`mapConst inj t` of an original-signature term contains **no** fresh parameter.
It needs **no** `DecidableEq` assumption on the base signature (the two `Sum`
injections are syntactically distinct).  Generality note: `WithParams` is rich
enough to host the elementary diagram of any countable structure (use `param`
to name its elements), so the canonical term model can be built over a given
countable `M`.
-/

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u}

/-- Extend a constant family with `Nat`-many fresh parameter constants **at every
type** `σ`.  Left = original constants, right = fresh parameters. -/
@[reducible] def WithParams (Const : Ty Base → Type v) (σ : Ty Base) : Type v := Const σ ⊕ Nat

namespace WithParams

variable {Const : Ty Base → Type v}

/-- Embed an original constant. -/
@[reducible] def inj {σ : Ty Base} (c : Const σ) : WithParams Const σ := Sum.inl c

/-- The `n`-th fresh parameter constant at type `σ`. -/
@[reducible] def param (σ : Ty Base) (n : Nat) : WithParams Const σ := Sum.inr n

@[simp] theorem inj_ne_param {σ : Ty Base} (c : Const σ) (n : Nat) :
    (inj c : WithParams Const σ) ≠ param σ n := by
  simp [inj, param]

@[simp] theorem param_ne_inj {σ : Ty Base} (c : Const σ) (n : Nat) :
    (param σ n : WithParams Const σ) ≠ inj c :=
  fun h => inj_ne_param c n h.symm

theorem param_inj {σ : Ty Base} {m n : Nat}
    (h : (param σ m : WithParams Const σ) = param σ n) : m = n := by
  simpa only [param, Sum.inr.injEq] using h

instance [∀ τ, DecidableEq (Const τ)] {σ : Ty Base} : DecidableEq (WithParams Const σ) := by
  unfold WithParams; infer_instance

/-- The image of an original-signature term under `inj` contains no fresh
parameter constant — uniformly, with no decidability assumption. -/
theorem noConstOccurrence_param_of_inj {σ : Ty Base} (n : Nat) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
      NoConstOccurrence (param σ n) (mapConst (fun {_} c => inj c) t) := by
  intro Γ τ t
  induction t with
  | var v => exact NoConstOccurrence.var
  | @const τ₁ Γ₁ c =>
      by_cases h : σ = τ₁
      · subst h
        exact NoConstOccurrence.const_same_ne (inj c) (inj_ne_param c n)
      · exact NoConstOccurrence.const_diff_type h (inj c)
  | app g t hg ht => exact NoConstOccurrence.app hg ht
  | lam t ih => exact NoConstOccurrence.lam ih
  | top => exact NoConstOccurrence.top
  | bot => exact NoConstOccurrence.bot
  | and φ ψ hφ hψ => exact NoConstOccurrence.and hφ hψ
  | or φ ψ hφ hψ => exact NoConstOccurrence.or hφ hψ
  | imp φ ψ hφ hψ => exact NoConstOccurrence.imp hφ hψ
  | not φ hφ => exact NoConstOccurrence.not hφ
  | eq t u ht hu => exact NoConstOccurrence.eq ht hu
  | all φ hφ => exact NoConstOccurrence.all hφ
  | ex φ hφ => exact NoConstOccurrence.ex hφ

/-- A strict upper bound on the parameter indices occurring in a term: `0` if no
parameter occurs, else `1 + (largest index)`.  Used to pick a *fresh* witness
parameter when saturating: any `param σ k` with `maxParam t ≤ k` is absent from
`t`. -/
def maxParam {Γ : Ctx Base} {τ : Ty Base} : Term (WithParams Const) Γ τ → Nat
  | .var _ => 0
  | .const d => Sum.elim (fun _ => 0) (fun k => k + 1) d
  | .app f t => max (maxParam f) (maxParam t)
  | .lam t => maxParam t
  | .top => 0
  | .bot => 0
  | .and a b => max (maxParam a) (maxParam b)
  | .or a b => max (maxParam a) (maxParam b)
  | .imp a b => max (maxParam a) (maxParam b)
  | .not a => maxParam a
  | .eq a b => max (maxParam a) (maxParam b)
  | .all a => maxParam a
  | .ex a => maxParam a

/-- Any parameter index at or above `maxParam t` names a constant absent from
`t`: the freshness criterion for Henkin witnessing. -/
theorem noConstOccurrence_param_of_ge {σ : Ty Base} (k : Nat) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term (WithParams Const) Γ τ),
      maxParam (Const := Const) t ≤ k → NoConstOccurrence (param σ k) t
  | _, _, .var _, _ => NoConstOccurrence.var
  | _, τ', .const d, h => by
      cases d with
      | inl c =>
          by_cases hτ : σ = τ'
          · subst hτ
            exact NoConstOccurrence.const_same_ne (inj c) (inj_ne_param c k)
          · exact NoConstOccurrence.const_diff_type hτ (inj c)
      | inr j =>
          simp only [maxParam, Sum.elim_inr] at h
          by_cases hτ : σ = τ'
          · subst hτ
            refine NoConstOccurrence.const_same_ne (param σ j) (fun he => ?_)
            have hjk : j = k := param_inj he
            omega
          · exact NoConstOccurrence.const_diff_type hτ (param τ' j)
  | _, _, .app f t, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.app
        (noConstOccurrence_param_of_ge k f (by omega))
        (noConstOccurrence_param_of_ge k t (by omega))
  | _, _, .lam t, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.lam (noConstOccurrence_param_of_ge k t h)
  | _, _, .top, _ => NoConstOccurrence.top
  | _, _, .bot, _ => NoConstOccurrence.bot
  | _, _, .and a b, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.and
        (noConstOccurrence_param_of_ge k a (by omega))
        (noConstOccurrence_param_of_ge k b (by omega))
  | _, _, .or a b, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.or
        (noConstOccurrence_param_of_ge k a (by omega))
        (noConstOccurrence_param_of_ge k b (by omega))
  | _, _, .imp a b, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.imp
        (noConstOccurrence_param_of_ge k a (by omega))
        (noConstOccurrence_param_of_ge k b (by omega))
  | _, _, .not a, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.not (noConstOccurrence_param_of_ge k a h)
  | _, _, .eq a b, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.eq
        (noConstOccurrence_param_of_ge k a (by omega))
        (noConstOccurrence_param_of_ge k b (by omega))
  | _, _, .all a, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.all (noConstOccurrence_param_of_ge k a h)
  | _, _, .ex a, h => by
      simp only [maxParam] at h
      exact NoConstOccurrence.ex (noConstOccurrence_param_of_ge k a h)

end WithParams

end Mettapedia.Logic.HOL
