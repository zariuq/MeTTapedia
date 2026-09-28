import Mettapedia.GSLT.LanguageDef.AffineExpressionGSLT
import Mettapedia.GSLT.Core.CertifiedPlanning

/-!
# An admitted affine artifact in the shared realization interface

The compiler produces executable coefficient syntax and an exact source DSL
charge. Admission failure remains distinct from a computed integer, including
zero. The certificate observes every environment and initial accumulator,
rather than one benchmark instance. Numeric representation is a separate
boundary: the checked evaluator below exposes intermediate overflow.
-/

namespace Mettapedia.GSLT.AffineExpression

structure Program (n : Nat) where
  body : Form n
  sourceCharge : Nat
  deriving Repr

def compileAccepted (e : Expr n) (h : (compile e).isSome = true) : Program n :=
  ⟨(compile e).get h, e.work⟩

/-- Exact values and source rewrite charge, under all possible inputs. -/
def realization : PartialRealization Expr Program
    (fun n => (Fin n → Int) → Int → Int × Nat) where
  accepts := fun _ e => (compile e).isSome
  compile := fun _ e h => compileAccepted e h
  observeSource := fun _ e env state => (e.eval env state, e.work)
  observeArtifact := fun _ p env state => (p.body.apply env state, p.sourceCharge)
  adequate := by
    intro n e h
    funext env state
    apply Prod.ext
    · exact compile_sound e _ (Option.some_get h).symm env state
    · rfl

/-- Bounds are parameters, not a claim that all integers use one machine
width. Rejecting is a numeric representation refusal, not logical failure. -/
def checked (lo hi v : Int) : Option Int :=
  if lo ≤ v ∧ v ≤ hi then some v else none

theorem checked_some {lo hi v out : Int} (h : checked lo hi v = some out) :
    out = v ∧ lo ≤ out ∧ out ≤ hi := by
  unfold checked at h
  split at h
  · cases h
    exact ⟨rfl, ‹lo ≤ v ∧ v ≤ hi›⟩
  · contradiction

/-- Evaluate in source order, checking *every* primitive result. -/
def Expr.evalChecked (lo hi : Int) (env : Fin n → Int) (state : Int) :
    Expr n → Option Int
  | .lit k => checked lo hi k
  | .input i => checked lo hi (env i)
  | .acc => checked lo hi state
  | .bin op l r => do
      let x ← l.evalChecked lo hi env state
      let y ← r.evalChecked lo hi env state
      checked lo hi (op.eval x y)

theorem checked_eval_sound (e : Expr n) (lo hi : Int) (env : Fin n → Int)
    (state out : Int) (h : e.evalChecked lo hi env state = some out) :
    out = e.eval env state ∧ lo ≤ out ∧ out ≤ hi := by
  induction e generalizing out with
  | lit | input | acc => exact checked_some h
  | bin op l r ihl ihr =>
      cases hl : l.evalChecked lo hi env state with
      | none => simp [Expr.evalChecked, hl] at h
      | some x =>
          cases hr : r.evalChecked lo hi env state with
          | none => simp [Expr.evalChecked, hl, hr] at h
          | some y =>
              have hh : checked lo hi (op.eval x y) = some out := by
                simpa [Expr.evalChecked, hl, hr] using h
              obtain ⟨hout, hlo, hhi⟩ := checked_some hh
              exact ⟨by rw [hout, (ihl x hl).1, (ihr y hr).1]; rfl, hlo, hhi⟩

end Mettapedia.GSLT.AffineExpression
