import Mettapedia.Logic.HOL.Embedding.ConversionPrice
import Mettapedia.Logic.HOL.Syntax.Subst

/-! Simultaneous substitution across the HOL embedding. An environment on
raw indices need only represent the variables actually in the source context.
The target action also operates on dependent types and binder annotations. -/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ Ξ : Ctx Base} {τ α : Ty Base}

namespace Expr

def liftImages (images : Nat → Expr Base Const) : Nat → Expr Base Const
  | 0 => .bvar 0
  | i + 1 => shiftAt 0 (images i)

/-- Simultaneous, capture-avoiding substitution into target syntax. -/
def substitute (images : Nat → Expr Base Const) : Expr Base Const → Expr Base Const
  | .bvar i => images i
  | .pi A B => .pi (substitute images A) (substitute (liftImages images) B)
  | .lam A b => .lam (substitute images A) (substitute (liftImages images) b)
  | .all A b => .all (substitute images A) (substitute (liftImages images) b)
  | .ex A b => .ex (substitute images A) (substitute (liftImages images) b)
  | .app f a => .app (substitute images f) (substitute images a)
  | .and p q => .and (substitute images p) (substitute images q)
  | .or p q => .or (substitute images p) (substitute images q)
  | .imp p q => .imp (substitute images p) (substitute images q)
  | .eq p q => .eq (substitute images p) (substitute images q)
  | .not p => .not (substitute images p)
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .const t c => .const t c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot

end Expr

theorem substitute_type (images : Nat → Expr Base Const) (t : Ty Base) :
    Expr.substitute images (tyToExpr t) = tyToExpr t := by
  induction t generalizing images <;> simp [tyToExpr, Expr.substitute, *]

private def InsertsAt (ρ : Rename Base Γ Δ) (k : Nat) : Prop :=
  ∀ {t} (v : Var Γ t), varIdx (ρ v) = if varIdx v < k then varIdx v else varIdx v + 1

private theorem lift_inserts {ρ : Rename Base Γ Δ} {k : Nat} (h : InsertsAt ρ k) :
    InsertsAt (Rename.lift (σ := α) ρ) (k + 1) := by
  intro t v
  cases v with
  | vz => simp [Rename.lift, varIdx]
  | vs v =>
    simp only [Rename.lift, varIdx, Nat.add_lt_add_iff_right, h v]
    split <;> rfl

private theorem translate_shift (t : Term Const Γ τ) (ρ : Rename Base Γ Δ) (k : Nat)
    (h : InsertsAt ρ k) : termToExpr (rename ρ t) = Expr.shiftAt k (termToExpr t) := by
  induction t generalizing Δ k <;>
    simp only [rename, termToExpr, Expr.shiftAt, shiftAt_tyToExpr] <;>
    first | rfl | (rw [h]; split <;> rfl) | (congr 1 <;> solve_by_elim [lift_inserts])

theorem translate_weaken (t : Term Const Γ τ) :
    termToExpr (weaken (σ := α) t) = Expr.shiftAt 0 (termToExpr t) :=
  translate_shift t Rename.weaken 0 (by intro t v; simp [Rename.weaken, varIdx])

/-- The typed and raw variables agree at each declared position. -/
def Represents (σ : Subst Const Γ Δ) (images : Nat → Expr Base Const) : Prop :=
  ∀ {t} (v : Var Γ t), termToExpr (σ v) = images (varIdx v)

private theorem lift_represents {σ : Subst Const Γ Δ} {images : Nat → Expr Base Const}
    (h : Represents σ images) : Represents (Subst.lift (σ := α) σ) (Expr.liftImages images) := by
  intro t v
  cases v with
  | vz => rfl
  | vs v => exact (translate_weaken (α := α) (σ v)).trans (congrArg (Expr.shiftAt 0) (h v))

theorem translate_substitution (t : Term Const Γ τ) (σ : Subst Const Γ Δ)
    (images : Nat → Expr Base Const) (h : Represents σ images) :
    termToExpr (subst σ t) = Expr.substitute images (termToExpr t) := by
  induction t generalizing Δ images <;>
    simp only [subst, termToExpr, Expr.substitute, substitute_type] <;>
    first | rfl | exact h _ | (congr 1 <;> solve_by_elim [lift_represents])

/-- Canonical images, independent of any proof or choice of variable names. -/
def imagesOf : {Γ : Ctx Base} → Subst Const Γ Δ → Nat → Expr Base Const
  | [], _, i => .bvar i
  | _ :: _, σ, 0 => termToExpr (σ .vz)
  | _ :: _, σ, i + 1 => imagesOf (fun v => σ (.vs v)) i

theorem imagesOf_represents (σ : Subst Const Γ Δ) : Represents σ (imagesOf σ) := by
  intro t v
  induction v with
  | vz => rfl
  | vs v ih => exact ih (fun x => σ (.vs x))

theorem substitution_natural (t : Term Const Γ τ) (σ : Subst Const Γ Δ) :
    termToExpr (subst σ t) = Expr.substitute (imagesOf σ) (termToExpr t) :=
  translate_substitution t σ _ (imagesOf_represents σ)

theorem substitution_composes (t : Term Const Γ τ) (σ : Subst Const Γ Δ) (δ : Subst Const Δ Ξ) :
    Expr.substitute (imagesOf δ) (Expr.substitute (imagesOf σ) (termToExpr t)) =
      Expr.substitute (imagesOf (Subst.comp δ σ)) (termToExpr t) := by
  rw [← substitution_natural, ← substitution_natural, ← substitution_natural, subst_comp]

/-- Specialize a parallel environment to the substitution used by the
dependent core's existing β rule. -/
private def singleImage (k : Nat) (s : Expr Base Const) (i : Nat) : Expr Base Const :=
  Expr.substAt k s (.bvar i)

private theorem lift_single (k : Nat) (s : Expr Base Const) :
    Expr.liftImages (singleImage k s) = singleImage (k + 1) s := by
  funext i
  cases i with
  | zero => simp [singleImage, Expr.liftImages, Expr.substAt]
  | succ i =>
    rcases Nat.lt_trichotomy i k with h | rfl | h
    · simp [singleImage, Expr.liftImages, Expr.substAt, Expr.shiftAt, h]
    · simp [singleImage, Expr.liftImages, Expr.substAt, Expr.shiftN]
    · have diff : i - 1 + 1 = i := by omega
      have less : ¬ i < k := by omega
      have different : i ≠ k := by omega
      simp [singleImage, Expr.liftImages, Expr.substAt, Expr.shiftAt, less, different, diff]

private theorem single_substitute (t s : Expr Base Const) (k : Nat) :
    Expr.substitute (singleImage k s) t = Expr.substAt k s t := by
  induction t generalizing k <;> simp only [Expr.substitute, lift_single, Expr.substAt, *] <;> rfl

theorem translate_beta (body : Term Const (α :: Γ) τ) (arg : Term Const Γ α) :
    Conv (termToExpr (.app (.lam body) arg)) (termToExpr (instantiate arg body)) := by
  have represented : Represents (Subst.single arg) (singleImage 0 (termToExpr arg)) := by
    intro t v
    cases v <;> simp [termToExpr, Subst.single, singleImage, Expr.substAt, varIdx, Expr.shiftN]
  rw [instantiate, translate_substitution body _ _ represented, single_substitute]
  exact Conv.beta _ _ _

end Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
