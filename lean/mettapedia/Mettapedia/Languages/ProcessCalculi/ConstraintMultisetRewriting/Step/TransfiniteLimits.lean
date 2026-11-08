import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalStep

/-!
# ω-limits of transforms of infinite trees

A transform `Φ` acts on whole trees. Its finite observations are agreements below a depth
(`AgreeBelow d s t`: the same label at every path shorter than `d`).

* **Strong convergence** (`ConvergesTo`): a run of trees converges to `t` when at every depth it is
  eventually equal to `t` below that depth. Limits are unique (`ConvergesTo.unique`).
* **A productive transform** (`Productive`) adds one level of agreement: inputs agreeing below `d`
  give outputs agreeing below `d + 1`. For a productive transform, from every start, the run of
  iterates converges (`Productive.converges`) to a fixed point (`Productive.limit_fixed`), and the
  fixed point is unique (`Productive.fixed_unique`): `Productive.existsUnique_fixed`. This is the
  contraction principle for the depth ultrametric, with the limit read path by path.

**The rational step on `X = f(X)`.** The firing `tellLoop` tells `X = f(X)`, and its run ends in
knowledge solved by `X := f(f(f(…)))` (`RationalStep.tellLoop_run`). Its unfolding run substitutes
`X := f(X)` again and again from `X`: `X, f(X), f(f(X)), …` (`unfoldRun`, `unfoldRun_eq_iterate`).
The guarded transform `t ↦ f(t)` is productive (`productive_guard`), so the unfolding run converges
path-wise to `f(f(f(…)))`, the unique tree solving `X = f(X)` (`unfoldRun_converges`,
`tellLoop_unfolding_limit`).

**Controls.**
* A run that is not productive need not converge: the transform that flips the root between two
  constants is not productive, and none of its runs converges (`not_convergesTo_rootFlip`,
  `not_productive_rootFlip`).
* An unguarded equation `X = X` has more than one solution (`unguarded_not_unique`).

Each iterate of the unfolding run is a finite tree; the limit is not assembled from them. It is the
unique fixed point of a transform of whole trees, and the iterates are its observations below
growing depths.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Transfinite

open Mettapedia.Logic.LP
open Raw (node bot)

variable {σ : LPSignature}

/-! ## Convergence by stabilization at every depth -/

/-- Two trees **agree below depth `d`**: the same label at every path shorter than `d`. -/
def AgreeBelow (d : ℕ) (s t : Raw σ) : Prop := ∀ p : List ℕ, p.length < d → s p = t p

theorem agreeBelow_zero (s t : Raw σ) : AgreeBelow 0 s t :=
  fun _ short => absurd short (Nat.not_lt_zero _)

theorem eq_of_agreeBelow {s t : Raw σ} (agree : ∀ d, AgreeBelow d s t) : s = t :=
  funext fun p => agree (p.length + 1) p (Nat.lt_succ_self _)

/-- **Strong convergence**: at every depth the run is eventually equal to `t` below that depth. -/
def ConvergesTo (run : ℕ → Raw σ) (t : Raw σ) : Prop :=
  ∀ d, ∃ N, ∀ n, N ≤ n → AgreeBelow d (run n) t

/-- **Limits are unique.** -/
theorem ConvergesTo.unique {run : ℕ → Raw σ} {s t : Raw σ} (hs : ConvergesTo run s)
    (ht : ConvergesTo run t) : s = t := by
  refine eq_of_agreeBelow fun d p short => ?_
  obtain ⟨N, hN⟩ := hs d
  obtain ⟨M, hM⟩ := ht d
  exact (hN (max N M) (le_max_left _ _) p short).symm.trans (hM (max N M) (le_max_right _ _) p short)

/-! ## Productive transforms -/

/-- **A productive transform**: inputs agreeing below `d` give outputs agreeing below `d + 1`. -/
def Productive (Φ : Raw σ → Raw σ) : Prop :=
  ∀ d s t, AgreeBelow d s t → AgreeBelow (d + 1) (Φ s) (Φ t)

/-- The limit of the run of `Φ` from `t₀`, read at a path of length `ℓ` from the `ℓ + 1`-th
iterate. -/
def limit (Φ : Raw σ → Raw σ) (t₀ : Raw σ) : Raw σ := fun p => (Φ^[p.length + 1] t₀) p

namespace Productive

variable {Φ : Raw σ → Raw σ} (productive : Productive Φ)
include productive

theorem iterate_agree (n : ℕ) (s t : Raw σ) : AgreeBelow n (Φ^[n] s) (Φ^[n] t) := by
  induction n with
  | zero => exact agreeBelow_zero _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact productive n _ _ ih

theorem iterate_agree_le (t₀ : Raw σ) {m n : ℕ} (le : m ≤ n) :
    AgreeBelow m (Φ^[m] t₀) (Φ^[n] t₀) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Function.iterate_add_apply]
  exact productive.iterate_agree m t₀ _

theorem limit_agree (t₀ : Raw σ) (n : ℕ) : AgreeBelow n (limit Φ t₀) (Φ^[n] t₀) :=
  fun p short => productive.iterate_agree_le t₀ short p (Nat.lt_succ_self _)

/-- **The run of iterates converges** to the limit. -/
theorem converges (t₀ : Raw σ) : ConvergesTo (fun n => Φ^[n] t₀) (limit Φ t₀) :=
  fun d => ⟨d, fun n le p short => (productive.limit_agree t₀ n p (lt_of_lt_of_le short le)).symm⟩

/-- **The limit is a fixed point.** -/
theorem limit_fixed (t₀ : Raw σ) : Φ (limit Φ t₀) = limit Φ t₀ := by
  funext p
  have step := productive _ _ _ (productive.limit_agree t₀ p.length) p (Nat.lt_succ_self _)
  rw [← Function.iterate_succ_apply' Φ p.length t₀] at step
  exact step

/-- **The fixed point is unique.** -/
theorem fixed_unique {a b : Raw σ} (ha : Φ a = a) (hb : Φ b = b) : a = b :=
  eq_of_agreeBelow fun n => by
    have := productive.iterate_agree n a b
    rwa [Function.iterate_fixed ha, Function.iterate_fixed hb] at this

/-- **A productive transform has exactly one fixed point, and every run of it converges there.** -/
theorem existsUnique_fixed (t₀ : Raw σ) :
    ∃! a, Φ a = a ∧ ∀ t : Raw σ, ConvergesTo (fun n => Φ^[n] t) a :=
  ⟨limit Φ t₀, ⟨productive.limit_fixed t₀, fun t =>
      (productive.fixed_unique (productive.limit_fixed t) (productive.limit_fixed t₀)) ▸
        productive.converges t⟩,
    fun _ ⟨fixed, _⟩ => productive.fixed_unique fixed (productive.limit_fixed t₀)⟩

end Productive

/-- **A guard makes a transform productive**: `t ↦ h(t, …, t)`. -/
theorem productive_guard (h : Head σ) : Productive fun t : Raw σ => node h fun _ => t := by
  intro d s t agree p short
  cases p with
  | nil => rfl
  | cons i q =>
    show (if i < h.arity then s q else none) = if i < h.arity then t q else none
    rw [agree q (by simpa using short)]

/-! ## The unfolding run of `X = f(X)` -/

section Loop

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Controls

/-- The substitution `X := f(X)`, every other variable kept. -/
def unfoldX : ctlSig.vars → Raw ctlSig :=
  fun v => if v = 0 then node (.fn Sym.f) (fun _ => Raw.leaf 0) else Raw.leaf v

/-- **The unfolding run**: substitute `X := f(X)` `n` times into `X`. -/
def unfoldRun (n : ℕ) : Raw ctlSig := (Raw.subst unfoldX)^[n] (Raw.leaf 0)

/-- The guarded transform of `X = f(X)`. -/
def guardF (t : Raw ctlSig) : Raw ctlSig := node (.fn Sym.f) fun _ => t

theorem productive_guardF : Productive guardF :=
  productive_guard _

theorem subst_guardF (t : Raw ctlSig) : Raw.subst unfoldX (guardF t) = guardF (Raw.subst unfoldX t) :=
  Raw.subst_node _ (fun v same => by cases same) _

theorem subst_iterate_guardF (n : ℕ) (t : Raw ctlSig) :
    Raw.subst unfoldX (guardF^[n] t) = guardF^[n] (Raw.subst unfoldX t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', subst_guardF, ih, Function.iterate_succ_apply']

theorem subst_unfoldX_leaf : Raw.subst unfoldX (Raw.leaf 0) = guardF (Raw.leaf 0) := by
  rw [Raw.subst_leaf]
  rfl

/-- **The unfolding run is the run of the guarded transform from `X`.** -/
theorem unfoldRun_eq_iterate (n : ℕ) : unfoldRun n = guardF^[n] (Raw.leaf 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unfoldRun, Function.iterate_succ_apply', ← unfoldRun, ih, subst_iterate_guardF,
      subst_unfoldX_leaf, ← Function.iterate_succ_apply]

/-- **The unfolding run converges path-wise to `f(f(f(…)))`.** -/
theorem unfoldRun_converges : ConvergesTo unfoldRun (loop .f).1 := by
  have lim : limit guardF (Raw.leaf 0) = (loop .f).1 :=
    productive_guardF.fixed_unique (productive_guardF.limit_fixed _) (loop_eq .f).symm
  have run := productive_guardF.converges (Raw.leaf 0)
  rw [lim] at run
  rw [show unfoldRun = fun n => guardF^[n] (Raw.leaf 0) from funext unfoldRun_eq_iterate]
  exact run

/-- **The run of the rational step on `X = f(X)`, and its limit.** The one firing `tellLoop` tells
`X = f(X)` and ends in knowledge solved by `X := f(f(f(…)))`; the unfolding run of that equation
converges path-wise to the same tree; and it is the only tree solving the equation. -/
theorem tellLoop_unfolding_limit {O : Type*} [DecidableEq O] (label : O → RTree ctlSig)
    (present : Finset O) :
    (∃ run : (rationalStep ctlSig label).Run ⟨[], present⟩,
        run.word.length = 1 ∧ (rationalAction ctlSig).Models (fun _ => loop .f) run.last.equations) ∧
      ConvergesTo unfoldRun (loop .f).1 ∧
      ∀ a : Raw ctlSig, a = node (.fn Sym.f) (fun _ => a) → a = (loop .f).1 :=
  ⟨tellLoop_run label present, unfoldRun_converges,
    fun _ fixed => productive_guardF.fixed_unique fixed.symm (loop_eq .f).symm⟩

/-! ## Controls -/

/-- A constant leaf. -/
def constLeaf (b : Bool) : Raw ctlSig := node (.const b) fun _ => bot

/-- Flip the root between the constants `true` and `false`. -/
def rootFlip (t : Raw ctlSig) : Raw ctlSig :=
  match t [] with
  | some (.const true) => constLeaf false
  | _ => constLeaf true

theorem rootFlip_cases (t : Raw ctlSig) : rootFlip t = constLeaf false ∨ rootFlip t = constLeaf true := by
  unfold rootFlip
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem constLeaf_root_ne : constLeaf true [] ≠ constLeaf false [] := by
  simp [constLeaf]

/-- Consecutive iterates of the flip, after the first, differ at the root. -/
theorem rootFlip_iterate_root_ne (t : Raw ctlSig) (n : ℕ) :
    rootFlip^[n + 2] t [] ≠ rootFlip^[n + 1] t [] := by
  rw [Function.iterate_succ_apply' rootFlip (n + 1)]
  rw [Function.iterate_succ_apply']
  rcases rootFlip_cases (rootFlip^[n] t) with same | same <;> rw [same]
  · exact constLeaf_root_ne
  · exact fun h => constLeaf_root_ne h.symm

/-- **No run of the flip converges.** -/
theorem not_convergesTo_rootFlip (t₀ t : Raw ctlSig) :
    ¬ ConvergesTo (fun n => rootFlip^[n] t₀) t := fun converges => by
  obtain ⟨N, stable⟩ := converges 1
  have first := stable (N + 1) (by omega) [] (by simp)
  have second := stable (N + 2) (by omega) [] (by simp)
  exact rootFlip_iterate_root_ne t₀ N (second.trans first.symm)

/-- **The flip is not productive.** -/
theorem not_productive_rootFlip : ¬ Productive rootFlip := fun productive =>
  not_convergesTo_rootFlip bot _ (productive.converges bot)

/-- **An unguarded equation `X = X` has more than one solution**, and the identity is not
productive. -/
theorem unguarded_not_unique :
    id (constLeaf true) = constLeaf true ∧ id (constLeaf false) = constLeaf false ∧
      constLeaf true ≠ constLeaf false ∧ ¬ Productive (id : Raw ctlSig → Raw ctlSig) :=
  ⟨rfl, rfl, fun same => constLeaf_root_ne (congrFun same []), fun productive =>
    constLeaf_root_ne (productive 0 _ _ (agreeBelow_zero (constLeaf true) (constLeaf false)) []
      (by simp))⟩

end Loop

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational.Transfinite

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Transfinite.eq_of_agreeBelow
#print axioms Rational.Transfinite.ConvergesTo.unique
#print axioms Rational.Transfinite.Productive.converges
#print axioms Rational.Transfinite.Productive.limit_fixed
#print axioms Rational.Transfinite.Productive.fixed_unique
#print axioms Rational.Transfinite.Productive.existsUnique_fixed
#print axioms Rational.Transfinite.productive_guard
#print axioms Rational.Transfinite.unfoldRun_eq_iterate
#print axioms Rational.Transfinite.unfoldRun_converges
#print axioms Rational.Transfinite.tellLoop_unfolding_limit
#print axioms Rational.Transfinite.not_convergesTo_rootFlip
#print axioms Rational.Transfinite.not_productive_rootFlip
#print axioms Rational.Transfinite.unguarded_not_unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
