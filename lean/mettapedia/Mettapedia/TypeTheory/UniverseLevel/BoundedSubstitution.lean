import Mettapedia.TypeTheory.UniverseLevel.Bounded

/-!
# Level expressions under substitution, and bounds extended by a variable

Facts about substituting level expressions under a bound level variable and about bounds
extended by one variable: which variables a substituted expression has, when two
substitutions agree, how the supremum over a bounded variable commutes with a substitution,
the bounds extended by one variable, and the substitution that closes the bounded variables
at a valuation. A comparison of level expressions under bounds holds exactly when it holds at
every closing instance (`LevelBounds.leUnder_iff_forall_closing`,
`LevelBounds.eqUnder_iff_forall_closing`).

A substitution *avoids* a name when the name occurs in the image of no other variable. The
substitution `keep x σ` is `σ` under a binder of `x`: it leaves `x` alone.

The declarations extend the namespaces of level expressions and of bounds.

Positive example: over the natural numbers, the supremum of `x + 1` over `x < 3` commutes
with the substitution `y ↦ y + 1`, which avoids `x`. Negative example: the substitution
`y ↦ x` does not avoid `x`, and the supremum of `max x y` over `x < 3` does not commute with
it: the supremum is `max 2 y`, which the substitution sends to `max 2 x`, while substituting
under the binder captures `x` and gives the supremum `2`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

open LevelOrder PredLevelOrder

variable {L : Type}

namespace LevelExpr

/-! ## Variables of a substituted expression -/

/-- Substitutions that agree on the variables of an expression give the same result. -/
theorem subst_congr {σ τ : Nat → LevelExpr L} :
    ∀ {e : LevelExpr L}, (∀ i, e.occurs i = true → σ i = τ i) → e.subst σ = e.subst τ
  | .const _, _ => rfl
  | .param i, h => h i (by simp [LevelExpr.occurs])
  | .succ e, h => congrArg LevelExpr.succ (subst_congr (e := e) h)
  | .max e₁ e₂, h =>
    congrArg₂ LevelExpr.max
      (subst_congr fun i hi => h i (by simp [LevelExpr.occurs, hi]))
      (subst_congr fun i hi => h i (by simp [LevelExpr.occurs, hi]))

/-- A substitution that fixes the variables of an expression fixes the expression. -/
theorem subst_eq_self {σ : Nat → LevelExpr L} {e : LevelExpr L}
    (h : ∀ i, e.occurs i = true → σ i = .param i) : e.subst σ = e :=
  (subst_congr h).trans (LevelExpr.subst_param e)

/-- The variables of a substituted expression are the variables of the images of its
variables. -/
theorem occurs_subst {σ : Nat → LevelExpr L} {y : Nat} :
    ∀ {e : LevelExpr L},
      (e.subst σ).occurs y = true ↔ ∃ i, e.occurs i = true ∧ (σ i).occurs y = true
  | .const _ => ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => nomatch h⟩
  | .param j =>
    ⟨fun h => ⟨j, by simp [LevelExpr.occurs], h⟩, fun ⟨i, hi, h⟩ => by
      have hji : j = i := by simpa [LevelExpr.occurs] using hi
      subst hji
      exact h⟩
  | .succ e => occurs_subst (e := e)
  | .max e₁ e₂ => by
    show ((e₁.subst σ).occurs y || (e₂.subst σ).occurs y) = true ↔
      ∃ i, (e₁.occurs i || e₂.occurs i) = true ∧ (σ i).occurs y = true
    rw [Bool.or_eq_true, occurs_subst (e := e₁), occurs_subst (e := e₂)]
    constructor
    · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
      · exact ⟨i, by rw [hi]; rfl, h⟩
      · exact ⟨i, by rw [hi, Bool.or_true], h⟩
    · rintro ⟨i, hi, h⟩
      rcases Bool.or_eq_true _ _ |>.mp hi with hi | hi
      · exact .inl ⟨i, hi, h⟩
      · exact .inr ⟨i, hi, h⟩

/-- The value of an expression depends only on the values of its variables. -/
theorem eval_congr [LevelOrder L] {v w : Nat → L} :
    ∀ {e : LevelExpr L}, (∀ i, e.occurs i = true → v i = w i) → e.eval v = e.eval w
  | .const _, _ => rfl
  | .param i, h => h i (by simp [LevelExpr.occurs])
  | .succ e, h => congrArg LevelOrder.succ (eval_congr (e := e) h)
  | .max e₁ e₂, h =>
    congrArg₂ Max.max
      (eval_congr fun i hi => h i (by simp [LevelExpr.occurs, hi]))
      (eval_congr fun i hi => h i (by simp [LevelExpr.occurs, hi]))

/-- Updating a variable to the value it has changes nothing. -/
theorem update_eq_self (ν : Nat → L) (x : Nat) : Function.update ν x (ν x) = ν := by
  funext i
  by_cases h : i = x
  · subst h
    rw [Function.update_self]
  · rw [Function.update_of_ne h]

/-- An expression that stays below a closed level at every valuation has no variable. -/
theorem occurs_eq_false_of_forall_lt [LevelOrder L] {e : LevelExpr L} {c : L}
    (h : ∀ v : Nat → L, e.eval v < c) (y : Nat) : e.occurs y = false := by
  cases hy : e.occurs y with
  | false => rfl
  | true =>
    exact absurd (lt_of_le_of_lt (LevelExpr.le_eval_of_occurs (fun _ => c) hy) (h fun _ => c))
      (lt_irrefl c)

/-! ## Substitutions that avoid a name -/

/-- The substitution `σ` avoids the name `y`: `y` occurs in the image of no other
variable. Substituting by `σ` under a binder named `y` then captures nothing. -/
def Avoids (σ : Nat → LevelExpr L) (y : Nat) : Prop :=
  ∀ i, i ≠ y → (σ i).occurs y = false

/-- The substitution `σ` under a binder of the variable `x`: it keeps `x`. -/
def keep (x : Nat) (σ : Nat → LevelExpr L) : Nat → LevelExpr L :=
  fun i => if i = x then .param x else σ i

/-- The kept variable is sent to itself. -/
@[simp] theorem keep_self (x : Nat) (σ : Nat → LevelExpr L) : keep x σ x = .param x :=
  if_pos rfl

/-- Another variable is sent to its image. -/
theorem keep_of_ne {x i : Nat} (h : i ≠ x) (σ : Nat → LevelExpr L) : keep x σ i = σ i :=
  if_neg h

/-- Keeping a variable of the identity substitution is the identity substitution. -/
theorem keep_param (x : Nat) : keep x (LevelExpr.param : Nat → LevelExpr L) = .param := by
  funext i
  by_cases h : i = x
  · subst h
    exact keep_self i _
  · exact keep_of_ne h _

/-- A substitution that avoids a name still avoids it under a binder. -/
theorem Avoids.keep {σ : Nat → LevelExpr L} {y : Nat} (h : Avoids σ y) (x : Nat) :
    Avoids (keep x σ) y := by
  intro i hi
  by_cases hix : i = x
  · subst hix
    rw [keep_self]
    simpa [LevelExpr.occurs] using hi
  · rw [keep_of_ne hix]
    exact h i hi

/-- Instantiating one variable avoids every name that does not occur in the instance. -/
theorem avoids_instantiate {x y : Nat} {a : LevelExpr L} (h : a.occurs y = false) :
    Avoids (LevelExpr.instantiate x a) y := by
  intro i hi
  unfold LevelExpr.instantiate
  by_cases hix : i = x
  · rw [if_pos hix]
    exact h
  · rw [if_neg hix]
    simpa [LevelExpr.occurs] using hi

/-- A name that does not occur in an expression and is avoided by a substitution does not
occur in the substituted expression. -/
theorem occurs_subst_eq_false {σ : Nat → LevelExpr L} {y : Nat} {e : LevelExpr L}
    (he : e.occurs y = false) (hσ : Avoids σ y) : (e.subst σ).occurs y = false := by
  cases h : (e.subst σ).occurs y with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hy⟩ := occurs_subst.mp h
    by_cases hiy : i = y
    · subst hiy
      rw [he] at hi
      exact nomatch hi
    · rw [hσ i hiy] at hy
      exact nomatch hy

/-- At each variable, keeping `x` and then instantiating it gives the instance at `x` and the
substitution elsewhere, when the kept substitution avoids `x`. -/
theorem keep_subst_instantiate {σ : Nat → LevelExpr L} {x : Nat} (hσ : Avoids σ x)
    (a : LevelExpr L) (i : Nat) :
    (keep x σ i).subst (instantiate x a) = if i = x then a else σ i := by
  by_cases hix : i = x
  · subst hix
    simp [keep, LevelExpr.subst, instantiate]
  · rw [keep_of_ne hix, if_neg hix]
    refine subst_eq_self fun j hj => ?_
    have hjx : j ≠ x := fun hjx => by
      subst hjx
      rw [hσ i hix] at hj
      exact nomatch hj
    simp [instantiate, hjx]

/-- At each variable, instantiating `x` and then substituting gives the substituted instance
at `x` and the substitution elsewhere. -/
theorem instantiate_subst (σ : Nat → LevelExpr L) (x : Nat) (a : LevelExpr L) (i : Nat) :
    (instantiate x a i).subst σ = if i = x then a.subst σ else σ i := by
  by_cases hix : i = x
  · simp [instantiate, hix]
  · simp [instantiate, hix, LevelExpr.subst]

/-- Keeping a variable and then instantiating it is one substitution, when the kept
substitution avoids the variable. -/
theorem subst_keep_instantiate {σ : Nat → LevelExpr L} {x : Nat} (hσ : Avoids σ x)
    (a : LevelExpr L) (e : LevelExpr L) :
    (e.subst (keep x σ)).subst (instantiate x a) =
      e.subst (fun i => if i = x then a else σ i) := by
  rw [LevelExpr.subst_subst]
  exact congrArg (fun τ => e.subst τ) (funext (keep_subst_instantiate hσ a))

/-- Instantiating a variable and then substituting is one substitution. -/
theorem subst_instantiate_subst (σ : Nat → LevelExpr L) (x : Nat) (a : LevelExpr L)
    (e : LevelExpr L) :
    (e.subst (instantiate x a)).subst σ =
      e.subst (fun i => if i = x then a.subst σ else σ i) := by
  rw [LevelExpr.subst_subst]
  exact congrArg (fun τ => e.subst τ) (funext (instantiate_subst σ x a))

/-- Instantiation commutes with a substitution that avoids the instantiated variable. -/
theorem subst_instantiate_comm {σ : Nat → LevelExpr L} {x : Nat} (hσ : Avoids σ x)
    (a : LevelExpr L) (e : LevelExpr L) :
    (e.subst (LevelExpr.instantiate x a)).subst σ =
      (e.subst (keep x σ)).subst (LevelExpr.instantiate x (a.subst σ)) := by
  rw [subst_instantiate_subst, subst_keep_instantiate hσ]

/-! ## The supremum over a bounded variable under a substitution -/

/-- A substitution that avoids a variable preserves its occurrence under the binder. -/
theorem occurs_subst_keep {σ : Nat → LevelExpr L} {x : Nat} (hσ : Avoids σ x)
    (e : LevelExpr L) : (e.subst (keep x σ)).occurs x = e.occurs x := by
  cases he : e.occurs x with
  | false => exact occurs_subst_eq_false he (hσ.keep x)
  | true => exact occurs_subst.mpr ⟨x, he, by simp [LevelExpr.occurs]⟩

/-- The instantiated variable does not occur in an instance at a closed level. -/
theorem occurs_subst_instantiate_const (x : Nat) (a : L) (e : LevelExpr L) :
    (e.subst (instantiate x (.const a))).occurs x = false := by
  cases h : (e.subst (instantiate x (.const a))).occurs x with
  | false => rfl
  | true =>
    obtain ⟨i, _, hy⟩ := occurs_subst.mp h
    by_cases hix : i = x
    · simp [instantiate, hix, LevelExpr.occurs] at hy
    · simp [instantiate, hix, LevelExpr.occurs] at hy

/-- Renaming a variable to a variable that does not occur, and then instantiating the new
variable, is instantiating the old one. -/
theorem subst_instantiate_param_instantiate {e : LevelExpr L} {y : Nat}
    (hy : e.occurs y = false) (x : Nat) (a : LevelExpr L) :
    (e.subst (instantiate x (.param y))).subst (instantiate y a) = e.subst (instantiate x a) := by
  rw [LevelExpr.subst_subst]
  refine subst_congr fun i hi => ?_
  by_cases hix : i = x
  · simp [instantiate, hix, LevelExpr.subst]
  · have hiy : i ≠ y := fun hiy => by
      subst hiy
      rw [hy] at hi
      exact nomatch hi
    simp [instantiate, hix, hiy, LevelExpr.subst]

/-- The value of an expression renamed to a variable that does not occur, at a value of the
new variable, is the value of the expression at that value of the old variable. -/
theorem eval_subst_instantiate_param [LevelOrder L] {e : LevelExpr L} {y : Nat}
    (hy : e.occurs y = false) (x : Nat) (v : Nat → L) (a : L) :
    (e.subst (instantiate x (.param y))).eval (Function.update v y a) =
      e.eval (Function.update v x a) := by
  rw [LevelExpr.eval_subst]
  refine eval_congr fun i hi => ?_
  by_cases hix : i = x
  · subst hix
    simp [instantiate, LevelExpr.eval]
  · have hiy : i ≠ y := fun hiy => by
      subst hiy
      rw [hy] at hi
      exact nomatch hi
    simp [instantiate, hix, LevelExpr.eval, Function.update_of_ne hiy]

section BoundedSup

variable [PredLevelOrder L]

/-- **The supremum does not depend on the name of the bound variable.** -/
theorem eval_boundedSup_rename {x y : Nat} {c : L} (hc : bot < c) {e : LevelExpr L}
    (hy : e.occurs y = false) (v : Nat → L) :
    (boundedSup y c (e.subst (instantiate x (.param y)))).eval v = (boundedSup x c e).eval v := by
  apply le_antisymm
  · refine boundedSup_least hc _ v fun a ha => ?_
    rw [eval_subst_instantiate_param hy]
    exact boundedSup_upper e v ha
  · refine boundedSup_least hc e v fun a ha => ?_
    rw [← eval_subst_instantiate_param hy x v a]
    exact boundedSup_upper _ v ha

/-- **The supremum over a bounded variable commutes with a substitution that avoids the
variable.** -/
theorem boundedSup_subst {σ : Nat → LevelExpr L} {x : Nat} (hσ : Avoids σ x) (c : L)
    (e : LevelExpr L) :
    (LevelExpr.boundedSup x c e).subst σ = LevelExpr.boundedSup x c (e.subst (keep x σ)) := by
  unfold LevelExpr.boundedSup
  rw [occurs_subst_keep hσ]
  cases pred? c with
  | some p => exact subst_instantiate_comm hσ (.const p) e
  | none =>
    cases e.occurs x with
    | true =>
      show LevelExpr.max ((e.subst (LevelExpr.instantiate x (.const bot))).subst σ) (.const c) = _
      rw [subst_instantiate_comm hσ]
      rfl
    | false => exact subst_instantiate_comm hσ (.const bot) e

/-- The bound variable does not occur in the supremum. -/
theorem occurs_boundedSup (x : Nat) (c : L) (e : LevelExpr L) :
    (LevelExpr.boundedSup x c e).occurs x = false := by
  unfold LevelExpr.boundedSup
  cases pred? c with
  | some p => exact occurs_subst_instantiate_const x p e
  | none =>
    cases e.occurs x with
    | true =>
      show ((e.subst (LevelExpr.instantiate x (.const bot))).occurs x || false) = false
      rw [occurs_subst_instantiate_const x bot e]
      rfl
    | false => exact occurs_subst_instantiate_const x bot e

end BoundedSup

end LevelExpr

/-! ## Bounds extended by a variable -/

namespace LevelBounds

open LevelExpr (Avoids keep keep_self keep_of_ne)

/-- The bounds `Δ` with the variable `x` bounded by `c`. -/
def bind (Δ : LevelBounds L) (x : Nat) (c : L) : LevelBounds L :=
  fun i => if i = x then some c else Δ i

/-- The new variable has the new bound. -/
@[simp] theorem bind_self (Δ : LevelBounds L) (x : Nat) (c : L) : Δ.bind x c x = some c :=
  if_pos rfl

/-- Another variable keeps its bound. -/
theorem bind_of_ne (Δ : LevelBounds L) {x i : Nat} (h : i ≠ x) (c : L) :
    Δ.bind x c i = Δ i :=
  if_neg h

/-- A variable that the extended bounds do not bound was not bounded. -/
theorem eq_none_of_bind {Δ : LevelBounds L} {x y : Nat} {c : L} (h : Δ.bind x c y = none) :
    Δ y = none := by
  by_cases hyx : y = x
  · subst hyx
    rw [bind_self] at h
    exact nomatch h
  · rwa [bind_of_ne Δ hyx] at h

/-- The substitution that closes the bounded variables at a valuation and keeps the
others. -/
def closing (Δ : LevelBounds L) (ρ : Nat → L) : Nat → LevelExpr L :=
  fun i => match Δ i with
    | some _ => .const (ρ i)
    | none => .param i

/-- Without bounds, closing is the identity substitution. -/
theorem closing_unbounded (ρ : Nat → L) : closing (unbounded L) ρ = .param := rfl

/-- The closing substitution avoids every name. -/
theorem avoids_closing (Δ : LevelBounds L) (ρ : Nat → L) (y : Nat) :
    Avoids (closing Δ ρ) y := by
  intro i hi
  unfold closing
  cases Δ i with
  | some _ => rfl
  | none => simpa [LevelExpr.occurs] using hi

/-- Closing the extended bounds closes the new variable and the old bounded variables. -/
theorem closing_bind (Δ : LevelBounds L) (ρ : Nat → L) (x : Nat) (c d : L) :
    closing (Δ.bind x c) (Function.update ρ x d) =
      fun i => if i = x then .const d else closing Δ ρ i := by
  funext i
  unfold closing
  by_cases hix : i = x
  · subst hix
    rw [bind_self, Function.update_self, if_pos rfl]
  · rw [bind_of_ne Δ hix, Function.update_of_ne hix, if_neg hix]

/-- Closing a level expression under the extended bounds is closing it under the binder and
instantiating the bound variable. -/
theorem subst_closing_bind (Δ : LevelBounds L) (ρ : Nat → L) (x : Nat) (c d : L)
    (e : LevelExpr L) :
    e.subst (closing (Δ.bind x c) (Function.update ρ x d)) =
      (e.subst (keep x (closing Δ ρ))).subst (LevelExpr.instantiate x (.const d)) := by
  rw [closing_bind, LevelExpr.subst_keep_instantiate (avoids_closing Δ ρ x)]

variable [LevelOrder L]

/-- Positive bounds extended by a positive bound are positive. -/
theorem Positive.bind {Δ : LevelBounds L} (pos : Δ.Positive) (x : Nat) {c : L}
    (hc : bot < c) : (Δ.bind x c).Positive := by
  intro i b h
  by_cases hix : i = x
  · subst hix
    rw [bind_self] at h
    exact Option.some.inj h ▸ hc
  · rw [bind_of_ne Δ hix] at h
    exact pos i b h

/-- A valid valuation, with the new variable at a value below its bound, is valid for the
extended bounds. -/
theorem Valid.bind {Δ : LevelBounds L} {ν : Nat → L} (valid : Δ.Valid ν) (x : Nat) {c d : L}
    (hd : d < c) : (Δ.bind x c).Valid (Function.update ν x d) := by
  intro i b h
  by_cases hix : i = x
  · subst hix
    rw [bind_self] at h
    rw [Function.update_self]
    exact Option.some.inj h ▸ hd
  · rw [bind_of_ne Δ hix] at h
    rw [Function.update_of_ne hix]
    exact valid i b h

/-- A valuation valid for the extended bounds puts the new variable below its bound. -/
theorem Valid.lt_of_bind {Δ : LevelBounds L} {ν : Nat → L} {x : Nat} {c : L}
    (valid : (Δ.bind x c).Valid ν) : ν x < c :=
  valid x c (bind_self Δ x c)

/-- A valuation valid for the extended bounds is valid for the bounds, when the new variable
was not bounded. -/
theorem Valid.of_bind {Δ : LevelBounds L} {ν : Nat → L} {x : Nat} {c : L}
    (hx : Δ x = none) (valid : (Δ.bind x c).Valid ν) : Δ.Valid ν := by
  intro i b h
  have hix : i ≠ x := fun hix => by
    subst hix
    rw [hx] at h
    exact nomatch h
  exact valid i b ((bind_of_ne Δ hix c).trans h)

/-- An admissible substitution stays admissible under a binder of a variable that the
target bounds do not bound. -/
theorem Admissible.keep {Δ' Δ : LevelBounds L} {σ : Nat → LevelExpr L}
    (admissible : Admissible Δ' Δ σ) {x : Nat} (hx : Δ' x = none) (c : L) :
    Admissible (Δ'.bind x c) (Δ.bind x c) (keep x σ) := by
  intro i b h
  by_cases hix : i = x
  · subst hix
    rw [bind_self] at h
    rw [keep_self]
    exact Option.some.inj h ▸ succ_le_of_lt_bound (bind_self Δ' i c)
  · rw [bind_of_ne Δ hix] at h
    rw [keep_of_ne hix]
    exact fun ν valid => admissible i b h ν (valid.of_bind hx)

/-- Instantiating the new variable by an expression below its bound is admissible from the
bounds to the extended bounds. -/
theorem admissible_instantiate_bind {Δ : LevelBounds L} {x : Nat} {c : L} {a : LevelExpr L}
    (below : LeUnder Δ (.succ a) (.const c)) :
    Admissible Δ (Δ.bind x c) (LevelExpr.instantiate x a) := by
  intro i b h
  by_cases hix : i = x
  · subst hix
    rw [bind_self] at h
    simpa [LevelExpr.instantiate] using Option.some.inj h ▸ below
  · rw [bind_of_ne Δ hix] at h
    simpa [LevelExpr.instantiate, hix] using succ_le_of_lt_bound h

/-- Under positive bounds, an expression that stays below a closed level has only bounded
variables. -/
theorem bounded_of_occurs {Δ : LevelBounds L} (pos : Δ.Positive) {e : LevelExpr L} {c : L}
    (below : LeUnder Δ (.succ e) (.const c)) {y : Nat} (hy : e.occurs y = true) :
    Δ y ≠ none := by
  intro hnone
  have valid : Δ.Valid fun j => if j = y then c else bot :=
    pos.valid_single fun b hb => by rw [hnone] at hb; exact nomatch hb
  have h₁ : c ≤ e.eval fun j => if j = y then c else bot := by
    have := LevelExpr.le_eval_of_occurs (fun j => if j = y then c else bot) hy
    rwa [if_pos rfl] at this
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h₁ (lt_succ _)) (below _ valid)) (lt_irrefl c)

/-! ## Closing the bounded variables -/

/-- Evaluating the closing substitution of a valid valuation gives a valid valuation. -/
theorem Valid.eval_closing {Δ : LevelBounds L} {ρ : Nat → L} (valid : Δ.Valid ρ)
    (v : Nat → L) : Δ.Valid fun i => (closing Δ ρ i).eval v := by
  intro i b h
  show LevelExpr.eval v (closing Δ ρ i) < b
  unfold closing
  rw [h]
  exact valid i b h

/-- At the valuation it closes, the closing substitution does not change a value. -/
theorem eval_subst_closing (Δ : LevelBounds L) (ν : Nat → L) (e : LevelExpr L) :
    (e.subst (closing Δ ν)).eval ν = e.eval ν := by
  rw [LevelExpr.eval_subst]
  congr 1
  funext i
  unfold closing
  cases Δ i <;> rfl

/-- Under the extended bounds, closing the instance of an expression at the least level of a
variable that was not bounded is closing the expression and evaluating the variable at the
least level. -/
theorem eval_instantiate_bot_closing_bind {Δ : LevelBounds L} {x : Nat} (hx : Δ x = none)
    (ρ : Nat → L) (c d : L) (e : LevelExpr L) (v : Nat → L) :
    ((e.subst (LevelExpr.instantiate x (.const bot))).subst
        (closing (Δ.bind x c) (Function.update ρ x d))).eval v =
      (e.subst (closing Δ ρ)).eval (Function.update v x bot) := by
  rw [LevelExpr.subst_subst, LevelExpr.eval_subst, LevelExpr.eval_subst]
  congr 1
  funext i
  by_cases hix : i = x
  · subst hix
    have hi : closing Δ ρ i = .param i := by
      unfold closing
      rw [hx]
    rw [hi]
    simp [LevelExpr.instantiate, LevelExpr.subst, LevelExpr.eval]
  · rw [LevelExpr.eval_update_of_not_occurs v bot (avoids_closing Δ ρ x i hix), closing_bind]
    simp [LevelExpr.instantiate, hix, LevelExpr.subst]

/-- **Comparison under bounds is comparison at every closed instance.** -/
theorem leUnder_iff_forall_closing {Δ : LevelBounds L} {e₁ e₂ : LevelExpr L} :
    LeUnder Δ e₁ e₂ ↔ ∀ ρ : Nat → L, Δ.Valid ρ → ∀ v : Nat → L,
      (e₁.subst (closing Δ ρ)).eval v ≤ (e₂.subst (closing Δ ρ)).eval v := by
  constructor
  · intro h ρ valid v
    rw [LevelExpr.eval_subst, LevelExpr.eval_subst]
    exact h _ (valid.eval_closing v)
  · intro h ν valid
    have := h ν valid ν
    rwa [eval_subst_closing, eval_subst_closing] at this

/-- Equality under bounds is equality at every closed instance. -/
theorem eqUnder_iff_forall_closing {Δ : LevelBounds L} {e₁ e₂ : LevelExpr L} :
    EqUnder Δ e₁ e₂ ↔ ∀ ρ : Nat → L, Δ.Valid ρ → ∀ v : Nat → L,
      (e₁.subst (closing Δ ρ)).eval v = (e₂.subst (closing Δ ρ)).eval v := by
  constructor
  · intro h ρ valid v
    rw [LevelExpr.eval_subst, LevelExpr.eval_subst]
    exact h _ (valid.eval_closing v)
  · intro h ν valid
    have := h ν valid ν
    rwa [eval_subst_closing, eval_subst_closing] at this

/-- An expression stays below a closed level under the bounds exactly when every closed
instance does, at every valuation. -/
theorem succ_leUnder_const_iff_forall_closing {Δ : LevelBounds L} {e : LevelExpr L} {c : L} :
    LeUnder Δ (.succ e) (.const c) ↔ ∀ ρ : Nat → L, Δ.Valid ρ → ∀ v : Nat → L,
      (e.subst (closing Δ ρ)).eval v < c := by
  rw [leUnder_iff_forall_closing]
  exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => succ_le_iff

end LevelBounds

/-! ## The supremum over a bounded variable under bounds -/

namespace LevelBounds

section Principal

variable [PredLevelOrder L]

/-- Under the extended bounds, an expression lies below its supremum over the new
variable. -/
theorem leUnder_boundedSup (Δ : LevelBounds L) (x : Nat) (c : L) (e : LevelExpr L) :
    LeUnder (Δ.bind x c) e (LevelExpr.boundedSup x c e) := by
  intro ν valid
  have h := LevelExpr.boundedSup_upper e ν (x := x) valid.lt_of_bind
  rwa [LevelExpr.update_eq_self] at h

/-- The supremum over the new variable is the least expression without that variable above
the expression under the extended bounds. -/
theorem boundedSup_leUnder {Δ : LevelBounds L} {x : Nat} {c : L} (hc : bot < c)
    {e u : LevelExpr L} (hu : u.occurs x = false) (h : LeUnder (Δ.bind x c) e u) :
    LeUnder Δ (LevelExpr.boundedSup x c e) u := by
  intro ν valid
  refine LevelExpr.boundedSup_least hc e ν fun a ha => ?_
  have := h _ (valid.bind x ha)
  rwa [LevelExpr.eval_update_of_not_occurs ν a hu] at this

end Principal

end LevelBounds

/-! ## Examples over the natural numbers -/

section Examples

open LevelExpr

/-- The substitution `y ↦ y + 1` avoids the variable `0`, and the supremum of `x + 1` over
`x < 3` commutes with it. -/
example : (LevelExpr.boundedSup 0 (3 : Nat) (.succ (.param 0))).subst
      (fun i => .succ (.param i)) =
    LevelExpr.boundedSup 0 3 ((LevelExpr.succ (.param 0)).subst
      (keep 0 fun i => .succ (.param i))) :=
  boundedSup_subst (fun _ hi => by simpa [LevelExpr.occurs] using hi) 3 _

/-- The substitution `1 ↦ x₀` does not avoid the variable `0`. -/
example : ¬ Avoids (LevelExpr.instantiate 1 (.param 0 : LevelExpr Nat)) 0 := fun h =>
  absurd (h 1 (by decide)) (by decide)

/-- The supremum of `max x₀ x₁` over `x₀ < 3` does not commute with that substitution: the
supremum `max 2 x₁` becomes `max 2 x₀`, while substituting under the binder captures `x₀`
and gives `2`. The two sides differ at the valuation `x₀ = 5`. -/
example :
    ((LevelExpr.boundedSup 0 (3 : Nat) (.max (.param 0) (.param 1))).subst
        (LevelExpr.instantiate 1 (.param 0))).eval (fun _ => 5) ≠
      (LevelExpr.boundedSup 0 (3 : Nat) ((LevelExpr.max (.param 0) (.param 1)).subst
        (keep 0 (LevelExpr.instantiate 1 (.param 0))))).eval (fun _ => 5) := by
  decide

end Examples

end Mettapedia.TypeTheory.UniverseLevel
