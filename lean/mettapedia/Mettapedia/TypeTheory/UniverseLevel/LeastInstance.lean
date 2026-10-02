import Mettapedia.TypeTheory.UniverseLevel.Bounded

/-!
# Least instances of level parameters

A declaration with level parameters is used at an instance of them. Where the instance is not
written it is found from the use: every comparison of levels that the use needs is a
constraint on the parameters, and the instance is the least assignment that satisfies the
constraints. This module states the search and proves its steps.

The values of levels form a join-semilattice with a monotone successor (`LevelValues`): the
levels of a level order, or the monotone functions of the valuation of the parameters that
are not being solved. A step *raises* the solved parameters of an expression so that the
expression reaches a bound (`raise`):

* a solved parameter is raised to its join with the bound;
* under a successor the bound is replaced by the least value whose successor reaches it,
  where one exists (`IsUnderSucc`);
* under a maximum with solved parameters on one side only, nothing is raised when the other
  side reaches the bound, and otherwise the bound goes to the side with the parameters. This
  needs a bound that lies under a join only when it lies under one of the two (`JoinPrime`):
  every level of a level order, and every constant among the monotone functions.

Where the step is defined its result is the least assignment above the given one at which the
expression reaches the bound (`raise_extends`, `raise_reaches`, `raise_forced`). A search that
only makes such steps stays below every solution (`Below.step`), and its verdicts are exact:

* a comparison whose right side has no solved parameter and which fails at the assignment
  the search has reached holds at no solution (`Below.no_solution_of_le`);
* an equation one side of which has no solved parameter is decided by one raise and one test
  (`Below.no_solution_of_eq_left`, `Below.no_solution_of_eq_right`);
* an assignment the search reaches at which every constraint holds is the least solution
  (`Below.least`).

A maximum with solved parameters on both sides has no least raise
(`not_exists_least_raise_max`), and there the step is not defined.

Positive examples: three uses that bound one parameter by `1`, fix it at `5` and bound it by
`5` have the least instance `5` in every order of the uses; a bound that reaches a parameter
through another one arrives in a second pass; below `ε₀`, the least level whose successor
reaches `ω` is `ω`. Negative examples: a parameter bounded below by `7` and fixed at `5` has
no instance; `ω` is the successor of no level; `l + 1 ≤ l` holds at no level; and a step for
an equation that is not among the constraints can lose every solution
(`trial_step_loses_solution`), so a search tries no comparison that the judgment can do
without.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

/-- Values of levels: a join-semilattice with a monotone successor. -/
class LevelValues (V : Type) extends SemilatticeSup V where
  /-- The successor of a value. -/
  next : V → V
  next_mono : ∀ {a b : V}, a ≤ b → next a ≤ next b

/-- The levels of a level order are values of levels. -/
instance instLevelValuesOfLevelOrder {L : Type} [LevelOrder L] : LevelValues L where
  toSemilatticeSup := inferInstance
  next := LevelOrder.succ
  next_mono := LevelOrder.succ_le_succ

namespace LeastInstance

variable {V : Type}

/-! ## Expressions at assignments of values -/

/-- Whether a parameter that is being solved occurs in an expression. -/
def mentions (S : Nat → Bool) : LevelExpr V → Bool
  | .const _ => false
  | .param i => S i
  | .succ e => mentions S e
  | .max a b => mentions S a || mentions S b

section Values

variable [LevelValues V]

/-- The value of an expression at an assignment of values to the parameters. -/
def value (σ : Nat → V) : LevelExpr V → V
  | .const c => c
  | .param i => σ i
  | .succ e => LevelValues.next (value σ e)
  | .max a b => value σ a ⊔ value σ b

/-- The value is monotone in the assignment. -/
theorem value_mono {σ τ : Nat → V} (h : ∀ i, σ i ≤ τ i) :
    ∀ e : LevelExpr V, value σ e ≤ value τ e
  | .const _ => le_refl _
  | .param i => h i
  | .succ e => LevelValues.next_mono (value_mono h e)
  | .max a b => sup_le_sup (value_mono h a) (value_mono h b)

/-- An expression without solved parameters has one value at all assignments that agree on
the other parameters. -/
theorem value_congr {S : Nat → Bool} {σ τ : Nat → V} (agree : ∀ i, S i = false → τ i = σ i) :
    ∀ e : LevelExpr V, mentions S e = false → value τ e = value σ e
  | .const _, _ => rfl
  | .param i, h => agree i h
  | .succ e, h => congrArg LevelValues.next (value_congr agree e h)
  | .max a b, h => by
    have parts : mentions S a = false ∧ mentions S b = false := Bool.or_eq_false_iff.mp h
    show value τ a ⊔ value τ b = value σ a ⊔ value σ b
    rw [value_congr agree a parts.1, value_congr agree b parts.2]

/-- One assignment extends another on the solved parameters: it is above it, and equal to it
at the other parameters. -/
structure Extends (S : Nat → Bool) (σ τ : Nat → V) : Prop where
  le : ∀ i, σ i ≤ τ i
  agree : ∀ i, S i = false → τ i = σ i

theorem Extends.refl (S : Nat → Bool) (σ : Nat → V) : Extends S σ σ :=
  ⟨fun _ => le_refl _, fun _ _ => rfl⟩

theorem Extends.trans {S : Nat → Bool} {σ τ υ : Nat → V} (first : Extends S σ τ)
    (second : Extends S τ υ) : Extends S σ υ :=
  ⟨fun i => le_trans (first.le i) (second.le i),
    fun i h => (second.agree i h).trans (first.agree i h)⟩

/-- Two assignments that extend each other are equal. -/
theorem Extends.antisymm {S : Nat → Bool} {σ τ : Nat → V} (first : Extends S σ τ)
    (second : Extends S τ σ) : σ = τ :=
  funext fun i => le_antisymm (first.le i) (second.le i)

/-! ## Bounds -/

/-- `u` is the least value whose successor reaches `c`. -/
def IsUnderSucc (c u : V) : Prop := ∀ x : V, c ≤ LevelValues.next x ↔ u ≤ x

/-- A value that lies under a join only when it lies under one of the two. -/
def JoinPrime (c : V) : Prop := ∀ a x : V, c ≤ a ⊔ x → c ≤ a ∨ c ≤ x

/-- The values under two successors: the join of the values under each. -/
theorem IsUnderSucc.sup {c c' u u' : V} (first : IsUnderSucc c u) (second : IsUnderSucc c' u') :
    IsUnderSucc (c ⊔ c') (u ⊔ u') := fun x =>
  ⟨fun h => sup_le ((first x).mp (le_trans le_sup_left h))
      ((second x).mp (le_trans le_sup_right h)),
    fun h => sup_le ((first x).mpr (le_trans le_sup_left h))
      ((second x).mpr (le_trans le_sup_right h))⟩

/-- What a search computes about bounds: the least value whose successor reaches a bound,
where it knows one; whether a bound is join-prime; and the order of two values, where it
decides it. Each answer is correct; none is required. -/
structure Bounds (V : Type) [LevelValues V] where
  under : V → Option V
  prime : V → Bool
  le : V → V → Option Bool
  under_spec : ∀ {c u : V}, under c = some u → IsUnderSucc c u
  prime_spec : ∀ {c : V}, prime c = true → JoinPrime c
  le_true : ∀ {a b : V}, le a b = some true → a ≤ b
  le_false : ∀ {a b : V}, le a b = some false → ¬ a ≤ b

/-! ## Raising the solved parameters of an expression to a bound -/

/-- Raise the solved parameters of an expression so that it reaches the bound `c`. `none`
where the search knows no least raise. -/
def raise (B : Bounds V) (S : Nat → Bool) : LevelExpr V → V → (Nat → V) → Option (Nat → V)
  | .const _, _, σ => some σ
  | .param i, c, σ => some (if S i then Function.update σ i (σ i ⊔ c) else σ)
  | .succ e, c, σ =>
    if mentions S e then
      match B.under c with
      | some u => raise B S e u σ
      | none => none
    else some σ
  | .max a b, c, σ =>
    match mentions S a, mentions S b with
    | false, false => some σ
    | true, true => none
    | true, false =>
      if B.prime c then
        match B.le c (value σ b) with
        | some true => some σ
        | some false => raise B S a c σ
        | none => none
      else none
    | false, true =>
      if B.prime c then
        match B.le c (value σ a) with
        | some true => some σ
        | some false => raise B S b c σ
        | none => none
      else none

variable {B : Bounds V} {S : Nat → Bool}

/-- Nothing is raised in an expression without solved parameters. -/
theorem raise_of_not_mentions :
    ∀ (e : LevelExpr V) (c : V) (σ : Nat → V), mentions S e = false → raise B S e c σ = some σ
  | .const _, _, _, _ => rfl
  | .param i, c, σ, h => by
    have unsolved : S i = false := h
    simp only [raise, unsolved, Bool.false_eq_true, if_false]
  | .succ e, c, σ, h => by
    have inner : mentions S e = false := h
    simp only [raise, inner, Bool.false_eq_true, if_false]
  | .max a b, c, σ, h => by
    have parts : mentions S a = false ∧ mentions S b = false := Bool.or_eq_false_iff.mp h
    simp only [raise, parts.1, parts.2]

/-- **A raise extends the assignment.** -/
theorem raise_extends :
    ∀ (e : LevelExpr V) (c : V) (σ σ' : Nat → V), raise B S e c σ = some σ' → Extends S σ σ'
  | .const _, _, σ, σ', h => by
    cases h
    exact Extends.refl S σ
  | .param i, c, σ, σ', h => by
    simp only [raise, Option.some.injEq] at h
    subst h
    by_cases solved : S i = true
    · rw [if_pos solved]
      refine ⟨fun j => ?_, fun j unsolved => ?_⟩
      · by_cases same : j = i
        · subst same
          rw [Function.update_self]
          exact le_sup_left
        · rw [Function.update_of_ne same]
      · have other : j ≠ i := fun same => by
          rw [same, solved] at unsolved
          exact absurd unsolved (by decide)
        rw [Function.update_of_ne other]
    · rw [if_neg solved]
      exact Extends.refl S σ
  | .succ e, c, σ, σ', h => by
    by_cases inner : mentions S e = true
    · simp only [raise, inner, if_true] at h
      cases under : B.under c with
      | none =>
        rw [under] at h
        exact nomatch h
      | some u =>
        rw [under] at h
        exact raise_extends e u σ σ' h
    · simp only [raise, inner, Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      exact Extends.refl S σ
  | .max a b, c, σ, σ', h => by
    cases left : mentions S a <;> cases right : mentions S b <;>
      simp only [raise, left, right] at h
    · cases h
      exact Extends.refl S σ
    · by_cases prime : B.prime c = true
      · rw [if_pos prime] at h
        cases decided : B.le c (value σ a) with
        | none =>
          rw [decided] at h
          exact nomatch h
        | some answer =>
          rw [decided] at h
          cases answer with
          | true =>
            cases h
            exact Extends.refl S σ
          | false => exact raise_extends b c σ σ' h
      · rw [if_neg prime] at h
        exact nomatch h
    · by_cases prime : B.prime c = true
      · rw [if_pos prime] at h
        cases decided : B.le c (value σ b) with
        | none =>
          rw [decided] at h
          exact nomatch h
        | some answer =>
          rw [decided] at h
          cases answer with
          | true =>
            cases h
            exact Extends.refl S σ
          | false => exact raise_extends a c σ σ' h
      · rw [if_neg prime] at h
        exact nomatch h
    · exact nomatch h

/-- **After a raise an expression with a solved parameter reaches the bound.** -/
theorem raise_reaches :
    ∀ (e : LevelExpr V) (c : V) (σ σ' : Nat → V), raise B S e c σ = some σ' →
      mentions S e = true → c ≤ value σ' e
  | .const _, _, _, _, _, solved => nomatch solved
  | .param i, c, σ, σ', h, solved => by
    have solved' : S i = true := solved
    simp only [raise, solved', if_true, Option.some.injEq] at h
    subst h
    show c ≤ Function.update σ i (σ i ⊔ c) i
    rw [Function.update_self]
    exact le_sup_right
  | .succ e, c, σ, σ', h, solved => by
    have inner : mentions S e = true := solved
    simp only [raise, inner, if_true] at h
    cases under : B.under c with
    | none =>
      rw [under] at h
      exact nomatch h
    | some u =>
      rw [under] at h
      exact (B.under_spec under _).mpr (raise_reaches e u σ σ' h inner)
  | .max a b, c, σ, σ', h, solved => by
    cases left : mentions S a <;> cases right : mentions S b <;>
      simp only [raise, left, right] at h
    · have none_ : mentions S (.max a b) = false := by
        show (mentions S a || mentions S b) = false
        rw [left, right]
        rfl
      rw [none_] at solved
      exact nomatch solved
    · by_cases prime : B.prime c = true
      · rw [if_pos prime] at h
        cases decided : B.le c (value σ a) with
        | none =>
          rw [decided] at h
          exact nomatch h
        | some answer =>
          rw [decided] at h
          cases answer with
          | true =>
            cases h
            exact le_trans (B.le_true decided) le_sup_left
          | false => exact le_trans (raise_reaches b c σ σ' h right) le_sup_right
      · rw [if_neg prime] at h
        exact nomatch h
    · by_cases prime : B.prime c = true
      · rw [if_pos prime] at h
        cases decided : B.le c (value σ b) with
        | none =>
          rw [decided] at h
          exact nomatch h
        | some answer =>
          rw [decided] at h
          cases answer with
          | true =>
            cases h
            exact le_trans (B.le_true decided) le_sup_right
          | false => exact le_trans (raise_reaches a c σ σ' h left) le_sup_left
      · rw [if_neg prime] at h
        exact nomatch h
    · exact nomatch h

/-- **A raise is forced: every assignment above the given one at which the expression
reaches the bound is above the raised one.** -/
theorem raise_forced :
    ∀ (e : LevelExpr V) (c : V) (σ σ' : Nat → V), raise B S e c σ = some σ' →
      ∀ τ : Nat → V, Extends S σ τ → c ≤ value τ e → Extends S σ' τ
  | .const _, _, σ, σ', h, τ, above, _ => by
    cases h
    exact above
  | .param i, c, σ, σ', h, τ, above, reach => by
    simp only [raise, Option.some.injEq] at h
    subst h
    by_cases solved : S i = true
    · rw [if_pos solved]
      refine ⟨fun j => ?_, fun j unsolved => ?_⟩
      · by_cases same : j = i
        · subst same
          rw [Function.update_self]
          exact sup_le (above.le j) reach
        · rw [Function.update_of_ne same]
          exact above.le j
      · have other : j ≠ i := fun same => by
          rw [same, solved] at unsolved
          exact absurd unsolved (by decide)
        rw [Function.update_of_ne other]
        exact above.agree j unsolved
    · rw [if_neg solved]
      exact above
  | .succ e, c, σ, σ', h, τ, above, reach => by
    by_cases inner : mentions S e = true
    · simp only [raise, inner, if_true] at h
      cases under : B.under c with
      | none =>
        rw [under] at h
        exact nomatch h
      | some u =>
        rw [under] at h
        exact raise_forced e u σ σ' h τ above ((B.under_spec under _).mp reach)
    · simp only [raise, inner, Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      exact above
  | .max a b, c, σ, σ', h, τ, above, reach => by
    have reach' : c ≤ value τ a ⊔ value τ b := reach
    cases left : mentions S a <;> cases right : mentions S b <;>
      simp only [raise, left, right] at h
    · cases h
      exact above
    · by_cases prime : B.prime c = true
      · rw [if_pos prime] at h
        cases decided : B.le c (value σ a) with
        | none =>
          rw [decided] at h
          exact nomatch h
        | some answer =>
          rw [decided] at h
          cases answer with
          | true =>
            cases h
            exact above
          | false =>
            rw [value_congr above.agree a left] at reach'
            rcases B.prime_spec prime _ _ reach' with other | here
            · exact absurd other (B.le_false decided)
            · exact raise_forced b c σ σ' h τ above here
      · rw [if_neg prime] at h
        exact nomatch h
    · by_cases prime : B.prime c = true
      · rw [if_pos prime] at h
        cases decided : B.le c (value σ b) with
        | none =>
          rw [decided] at h
          exact nomatch h
        | some answer =>
          rw [decided] at h
          cases answer with
          | true =>
            cases h
            exact above
          | false =>
            rw [value_congr above.agree b right] at reach'
            rcases B.prime_spec prime _ _ reach' with here | other
            · exact raise_forced a c σ σ' h τ above here
            · exact absurd other (B.le_false decided)
      · rw [if_neg prime] at h
        exact nomatch h
    · exact nomatch h

/-- **An equation with a bound is decided by one raise and one test.** When the raised
assignment does not give the expression the value of the bound, no assignment above the given
one does. -/
theorem no_equal_of_raise {e : LevelExpr V} {c : V} {σ σ' : Nat → V}
    (raised : raise B S e c σ = some σ') (differs : value σ' e ≠ c) :
    ∀ τ : Nat → V, Extends S σ τ → value τ e ≠ c := by
  intro τ above equal
  have below : Extends S σ' τ := raise_forced e c σ σ' raised τ above (le_of_eq equal.symm)
  have upper : value σ' e ≤ c := equal ▸ value_mono below.le e
  cases solved : mentions S e with
  | true => exact differs (le_antisymm upper (raise_reaches e c σ σ' raised solved))
  | false =>
    rw [raise_of_not_mentions e c σ solved] at raised
    cases raised
    exact differs ((value_congr above.agree e solved).symm.trans equal)

/-- An upper bound that fails at an assignment fails at every assignment above it. -/
theorem not_le_of_extends {e : LevelExpr V} {c : V} {σ τ : Nat → V} (above : Extends S σ τ)
    (fails : ¬ value σ e ≤ c) : ¬ value τ e ≤ c :=
  fun h => fails (le_trans (value_mono above.le e) h)

/-! ## Constraints and the search -/

/-- A constraint between two level expressions. -/
inductive Constraint (V : Type) where
  | le (a b : LevelExpr V)
  | eq (a b : LevelExpr V)

/-- A constraint holds at an assignment. -/
def Constraint.Holds (σ : Nat → V) : Constraint V → Prop
  | .le a b => value σ a ≤ value σ b
  | .eq a b => value σ a = value σ b

/-- The step of the search at a constraint: the right side is raised to the value of the left
side; for an equation the left side is then raised to the value of the right side. -/
def Constraint.step (B : Bounds V) (S : Nat → Bool) : Constraint V → (Nat → V) → Option (Nat → V)
  | .le a b, σ => raise B S b (value σ a) σ
  | .eq a b, σ =>
    match raise B S b (value σ a) σ with
    | some σ' => raise B S a (value σ' b) σ'
    | none => none

/-- An assignment solves a list of constraints from a start: it extends the start and every
constraint holds at it. -/
def Solves (S : Nat → Bool) (Cs : List (Constraint V)) (σ₀ τ : Nat → V) : Prop :=
  Extends S σ₀ τ ∧ ∀ C ∈ Cs, C.Holds τ

/-- The state of a search: an assignment that extends the start and that every solution
extends. -/
structure Below (S : Nat → Bool) (Cs : List (Constraint V)) (σ₀ σ : Nat → V) : Prop where
  start : Extends S σ₀ σ
  below : ∀ τ : Nat → V, Solves S Cs σ₀ τ → Extends S σ τ

/-- The start is a state of the search. -/
theorem Below.refl (S : Nat → Bool) (Cs : List (Constraint V)) (σ₀ : Nat → V) :
    Below S Cs σ₀ σ₀ :=
  ⟨Extends.refl S σ₀, fun _ solves => solves.1⟩

/-- **A step keeps the search below every solution.** -/
theorem Below.step {Cs : List (Constraint V)} {σ₀ σ σ' : Nat → V} (state : Below S Cs σ₀ σ)
    {C : Constraint V} (mem : C ∈ Cs) (stepped : C.step B S σ = some σ') :
    Below S Cs σ₀ σ' := by
  cases C with
  | le a b =>
    refine ⟨state.start.trans (raise_extends b _ σ σ' stepped), fun τ solves => ?_⟩
    have above : Extends S σ τ := state.below τ solves
    have holds : value τ a ≤ value τ b := solves.2 _ mem
    exact raise_forced b _ σ σ' stepped τ above (le_trans (value_mono above.le a) holds)
  | eq a b =>
    have unfolded : (match raise B S b (value σ a) σ with
        | some σ₁ => raise B S a (value σ₁ b) σ₁
        | none => none) = some σ' := stepped
    cases first : raise B S b (value σ a) σ with
    | none =>
      rw [first] at unfolded
      exact nomatch unfolded
    | some σ₁ =>
      rw [first] at unfolded
      refine ⟨state.start.trans ((raise_extends b _ σ σ₁ first).trans
        (raise_extends a _ σ₁ σ' unfolded)), fun τ solves => ?_⟩
      have above : Extends S σ τ := state.below τ solves
      have holds : value τ a = value τ b := solves.2 _ mem
      have middle : Extends S σ₁ τ :=
        raise_forced b _ σ σ₁ first τ above (holds ▸ value_mono above.le a)
      exact raise_forced a _ σ₁ σ' unfolded τ middle (holds ▸ value_mono middle.le b)

/-- **A state at which every constraint holds is the least solution.** -/
theorem Below.least {Cs : List (Constraint V)} {σ₀ σ : Nat → V} (state : Below S Cs σ₀ σ)
    (holds : ∀ C ∈ Cs, C.Holds σ) :
    Solves S Cs σ₀ σ ∧ ∀ τ : Nat → V, Solves S Cs σ₀ τ → Extends S σ τ :=
  ⟨⟨state.start, holds⟩, state.below⟩

/-- **A failing upper bound refutes.** A comparison whose right side has no solved parameter
and which fails at a state of the search holds at no solution. -/
theorem Below.no_solution_of_le {Cs : List (Constraint V)} {σ₀ σ : Nat → V}
    (state : Below S Cs σ₀ σ) {a b : LevelExpr V} (mem : Constraint.le a b ∈ Cs)
    (closed : mentions S b = false) (fails : ¬ value σ a ≤ value σ b) :
    ∀ τ : Nat → V, ¬ Solves S Cs σ₀ τ := by
  intro τ solves
  have above : Extends S σ τ := state.below τ solves
  have holds : value τ a ≤ value τ b := solves.2 _ mem
  rw [value_congr above.agree b closed] at holds
  exact fails (le_trans (value_mono above.le a) holds)

/-- **An equation whose left side has no solved parameter is decided by one raise and one
test.** -/
theorem Below.no_solution_of_eq_left {Cs : List (Constraint V)} {σ₀ σ σ' : Nat → V}
    (state : Below S Cs σ₀ σ) {a b : LevelExpr V} (mem : Constraint.eq a b ∈ Cs)
    (closed : mentions S a = false) (raised : raise B S b (value σ a) σ = some σ')
    (differs : value σ' b ≠ value σ a) : ∀ τ : Nat → V, ¬ Solves S Cs σ₀ τ := by
  intro τ solves
  have above : Extends S σ τ := state.below τ solves
  have holds : value τ a = value τ b := solves.2 _ mem
  rw [value_congr above.agree a closed] at holds
  exact no_equal_of_raise raised differs τ above holds.symm

/-- The same with the right side closed. -/
theorem Below.no_solution_of_eq_right {Cs : List (Constraint V)} {σ₀ σ σ' : Nat → V}
    (state : Below S Cs σ₀ σ) {a b : LevelExpr V} (mem : Constraint.eq a b ∈ Cs)
    (closed : mentions S b = false) (raised : raise B S a (value σ b) σ = some σ')
    (differs : value σ' a ≠ value σ b) : ∀ τ : Nat → V, ¬ Solves S Cs σ₀ τ := by
  intro τ solves
  have above : Extends S σ τ := state.below τ solves
  have holds : value τ a = value τ b := solves.2 _ mem
  rw [value_congr above.agree b closed] at holds
  exact no_equal_of_raise raised differs τ above holds

/-- One pass of the search: the steps of the constraints in their order. -/
def pass (B : Bounds V) (S : Nat → Bool) : List (Constraint V) → (Nat → V) → Option (Nat → V)
  | [], σ => some σ
  | C :: Cs, σ =>
    match C.step B S σ with
    | some σ' => pass B S Cs σ'
    | none => none

/-- A number of passes. -/
def passes (B : Bounds V) (S : Nat → Bool) (Cs : List (Constraint V)) :
    Nat → (Nat → V) → Option (Nat → V)
  | 0, σ => some σ
  | n + 1, σ =>
    match pass B S Cs σ with
    | some σ' => passes B S Cs n σ'
    | none => none

/-- A pass over some of the constraints keeps the search below every solution. -/
theorem Below.pass {Cs : List (Constraint V)} {σ₀ : Nat → V} :
    ∀ (Ds : List (Constraint V)) (σ σ' : Nat → V), (∀ C ∈ Ds, C ∈ Cs) → Below S Cs σ₀ σ →
      pass B S Ds σ = some σ' → Below S Cs σ₀ σ'
  | [], σ, σ', _, state, h => by
    cases h
    exact state
  | C :: Ds, σ, σ', sub, state, h => by
    have unfolded : (match C.step B S σ with
        | some σ₁ => LeastInstance.pass B S Ds σ₁
        | none => none) = some σ' := h
    cases first : C.step B S σ with
    | none =>
      rw [first] at unfolded
      exact nomatch unfolded
    | some σ₁ =>
      rw [first] at unfolded
      exact Below.pass Ds σ₁ σ' (fun D mem => sub D (List.mem_cons_of_mem _ mem))
        (state.step (sub C List.mem_cons_self) first) unfolded

/-- **Any number of passes keeps the search below every solution.** -/
theorem Below.passes {Cs : List (Constraint V)} {σ₀ : Nat → V} :
    ∀ (n : Nat) (σ σ' : Nat → V), Below S Cs σ₀ σ → passes B S Cs n σ = some σ' →
      Below S Cs σ₀ σ'
  | 0, σ, σ', state, h => by
    cases h
    exact state
  | n + 1, σ, σ', state, h => by
    have unfolded : (match LeastInstance.pass B S Cs σ with
        | some σ₁ => LeastInstance.passes B S Cs n σ₁
        | none => none) = some σ' := h
    cases first : LeastInstance.pass B S Cs σ with
    | none =>
      rw [first] at unfolded
      exact nomatch unfolded
    | some σ₁ =>
      rw [first] at unfolded
      exact Below.passes n σ₁ σ' (Below.pass Cs σ σ₁ (fun _ mem => mem) state first) unfolded

end Values

/-! ## Closed levels -/

/-- Every level is join-prime: the order is linear. -/
theorem joinPrime_level {L : Type} [LevelOrder L] (c : L) : JoinPrime c := fun a x h => by
  rcases le_total a x with below | above
  · exact Or.inr (le_trans h (sup_le below (le_refl x)))
  · exact Or.inl (le_trans h (sup_le (le_refl a) above))

section Closed

variable {L : Type} [PredLevelOrder L]

open LevelOrder PredLevelOrder

/-- Over a level order the value of an expression is its evaluation. -/
theorem value_eq_eval (σ : Nat → L) : ∀ e : LevelExpr L, value σ e = LevelExpr.eval σ e
  | .const _ => rfl
  | .param _ => rfl
  | .succ e => congrArg LevelOrder.succ (value_eq_eval σ e)
  | .max a b => by
    show value σ a ⊔ value σ b = Max.max (LevelExpr.eval σ a) (LevelExpr.eval σ b)
    rw [value_eq_eval σ a, value_eq_eval σ b]

/-- The least level whose successor reaches a level. -/
theorem isUnderSucc_level (c : L) : IsUnderSucc c (underSucc c) := fun _ =>
  le_succ_iff_underSucc_le

/-- What the search computes about closed levels: everything. -/
def levelBounds : Bounds L where
  under c := some (underSucc c)
  prime _ := true
  le a b := some (decide (a ≤ b))
  under_spec := fun h => by
    cases h
    exact isUnderSucc_level _
  prime_spec := fun _ => joinPrime_level _
  le_true := fun h => of_decide_eq_true (Option.some.inj h)
  le_false := fun h => of_decide_eq_false (Option.some.inj h)

end Closed

/-! ## Values that depend on parameters that are not solved

A bound may mention level parameters of an enclosing declaration. Its value is then a
monotone function of their valuation. Constants are join-prime among these functions, and
the values under a successor are computed as for closed levels. -/

section Open

variable {L : Type} [LevelOrder L]

/-- Monotone functions of a valuation are values of levels, pointwise. -/
instance instLevelValuesOfValuations : LevelValues ((Nat → L) →o L) where
  toSemilatticeSup := inferInstance
  next f := ⟨fun ρ => LevelOrder.succ (f ρ), fun _ _ h => LevelOrder.succ_le_succ (f.monotone h)⟩
  next_mono := fun h ρ => LevelOrder.succ_le_succ (h ρ)

/-- **A constant is join-prime among the monotone functions of a valuation.** A constant that
is not below a function is not below it at the least valuation, where the other function
must reach it; and that function is monotone. -/
theorem joinPrime_const (c : L) : JoinPrime (OrderHom.const (Nat → L) c) := by
  intro a x h
  have least : ∀ ρ : Nat → L, (fun _ => LevelOrder.bot) ≤ ρ := fun ρ _ => LevelOrder.bot_le _
  rcases joinPrime_level c _ _ (h fun _ => LevelOrder.bot) with here | there
  · exact Or.inl fun ρ => le_trans here (a.monotone (least ρ))
  · exact Or.inr fun ρ => le_trans there (x.monotone (least ρ))

/-- The value under the successor of a successor. -/
theorem isUnderSucc_next (y : (Nat → L) →o L) : IsUnderSucc (LevelValues.next y) y := fun _ =>
  ⟨fun h ρ => LevelOrder.succ_le_succ_iff.mp (h ρ), fun h ρ => LevelOrder.succ_le_succ (h ρ)⟩

/-- The value under the successor of a constant. -/
theorem isUnderSucc_const {L : Type} [PredLevelOrder L] (c : L) :
    IsUnderSucc (OrderHom.const (Nat → L) c)
      (OrderHom.const (Nat → L) (PredLevelOrder.underSucc c)) := fun _ =>
  ⟨fun h ρ => PredLevelOrder.le_succ_iff_underSucc_le.mp (h ρ),
    fun h ρ => PredLevelOrder.le_succ_iff_underSucc_le.mpr (h ρ)⟩

end Open

/-! ## Examples over the natural numbers -/

section Examples

/-- The parameter `0` is solved. -/
def solveFirst : Nat → Bool := fun i => decide (i = 0)

/-- The parameters `0` and `1` are solved. -/
def solveTwo : Nat → Bool := fun i => decide (i < 2)

/-- Three uses of one parameter `l`: `1 ≤ l`, `l = 5`, `5 ≤ l`. -/
def smallFirst : List (Constraint Nat) :=
  [.le (.const 1) (.param 0), .eq (.const 5) (.param 0), .le (.const 5) (.param 0)]

/-- The same uses in another order. -/
def smallLast : List (Constraint Nat) :=
  [.le (.const 5) (.param 0), .eq (.const 5) (.param 0), .le (.const 1) (.param 0)]

/-- In both orders one pass reaches `5`. -/
example : (pass levelBounds solveFirst smallFirst fun _ => 0).map (fun σ => σ 0) = some 5 ∧
    (pass levelBounds solveFirst smallLast fun _ => 0).map (fun σ => σ 0) = some 5 := by
  decide

/-- **The instance does not depend on the order of the uses**: in the first order the
assignment of `5` is the least solution. -/
theorem smallFirst_least :
    ∃ σ : Nat → Nat, σ 0 = 5 ∧ Solves solveFirst smallFirst (fun _ => 0) σ ∧
      ∀ τ, Solves solveFirst smallFirst (fun _ => 0) τ → Extends solveFirst σ τ := by
  cases reached : pass levelBounds solveFirst smallFirst fun _ => 0 with
  | none => exact absurd reached (by decide)
  | some σ =>
    have value_ : σ 0 = 5 := by
      have : (pass levelBounds solveFirst smallFirst fun _ => 0).map (fun σ => σ 0) = some 5 := by
        decide
      rw [reached] at this
      exact Option.some.inj this
    have state : Below solveFirst smallFirst (fun _ => 0) σ :=
      Below.pass smallFirst _ σ (fun _ mem => mem) (Below.refl _ _ _) reached
    have holds : ∀ C ∈ smallFirst, C.Holds σ := by
      intro C mem
      simp only [smallFirst, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · show (1 : Nat) ≤ σ 0
        rw [value_]
        decide
      · show (5 : Nat) = σ 0
        exact value_.symm
      · show (5 : Nat) ≤ σ 0
        rw [value_]
    exact ⟨σ, value_, state.least holds⟩

/-- A parameter bounded below by `7` and fixed at `5`. -/
def conflicting : List (Constraint Nat) :=
  [.le (.const 7) (.param 0), .eq (.const 5) (.param 0)]

/-- Negative: **it has no instance**, found by one raise and one test. -/
theorem conflicting_no_solution :
    ∀ τ : Nat → Nat, ¬ Solves solveFirst conflicting (fun _ => 0) τ := by
  cases first : (Constraint.le (.const 7) (.param 0) : Constraint Nat).step levelBounds solveFirst
      fun _ => 0 with
  | none => exact absurd first (by decide)
  | some σ =>
    have seven : σ 0 = 7 := by
      have : ((Constraint.le (.const 7) (.param 0) : Constraint Nat).step levelBounds solveFirst
          fun _ => 0).map (fun σ => σ 0) = some 7 := by decide
      rw [first] at this
      exact Option.some.inj this
    have state : Below solveFirst conflicting (fun _ => 0) σ :=
      (Below.refl _ _ _).step List.mem_cons_self first
    refine state.no_solution_of_eq_left (B := levelBounds)
      (σ' := Function.update σ 0 (σ 0 ⊔ 5)) (a := .const 5) (b := .param 0)
      (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl ?_
    show Function.update σ 0 (σ 0 ⊔ 5) 0 ≠ 5
    rw [Function.update_self, seven]
    decide

/-- A bound that reaches the parameter `1` through the parameter `0`: `l₀ ≤ l₁`, `3 ≤ l₀`. -/
def chained : List (Constraint Nat) :=
  [.le (.param 0) (.param 1), .le (.const 3) (.param 0)]

/-- After one pass the first constraint fails; after two passes both hold at `3`. -/
example : (pass levelBounds solveTwo chained fun _ => 0).map (fun σ => (σ 0, σ 1)) = some (3, 0) ∧
    (passes levelBounds solveTwo chained 2 fun _ => 0).map (fun σ => (σ 0, σ 1)) = some (3, 3) := by
  decide

/-- Under a maximum with a solved parameter on one side, the bound goes to the parameter only
where the other side does not reach it. -/
example : (raise levelBounds solveFirst (.max (.const 4) (.param 0)) 3 fun _ => 0).map
      (fun σ => σ 0) = some 0 ∧
    (raise levelBounds solveFirst (.max (.const 4) (.param 0)) 6 fun _ => 0).map
      (fun σ => σ 0) = some 6 := by
  decide

/-- Under successors the bound goes down by as many steps. -/
example : (raise levelBounds solveFirst (.succ (.succ (.param 0))) 5 fun _ => 0).map
    (fun σ => σ 0) = some 3 := by
  decide

/-- Negative: with solved parameters on both sides of a maximum the step is not defined. -/
example : (raise levelBounds solveTwo (.max (.param 0) (.param 1)) 1 fun _ => 0).isNone := by
  decide

/-- Negative: **there is no least raise there.** Each of the two parameters alone reaches the
bound, and nothing below both does. -/
theorem not_exists_least_raise_max :
    ¬ ∃ σ : Nat → Nat, 1 ≤ value σ (.max (.param 0) (.param 1)) ∧
      ∀ τ : Nat → Nat, 1 ≤ value τ (.max (.param 0) (.param 1)) → ∀ i, σ i ≤ τ i := by
  rintro ⟨σ, reaches, least⟩
  have first := least (fun i => if i = 1 then 1 else 0) (by decide) 0
  have second := least (fun i => if i = 0 then 1 else 0) (by decide) 1
  have zero₀ : σ 0 = 0 := Nat.le_zero.mp first
  have zero₁ : σ 1 = 0 := Nat.le_zero.mp second
  have : (1 : Nat) ≤ σ 0 ⊔ σ 1 := reaches
  rw [zero₀, zero₁] at this
  exact absurd this (by decide)

/-- One use that fixes the parameter: `l = 3`. -/
def fixedAtThree : List (Constraint Nat) :=
  [.eq (.const 3) (.param 0)]

/-- An equation that is not among the uses: `l + 1 = 6`. A term whose type is the universe at
`l + 1` is compared with a term of the universe at `6`; the two terms need a common type, and
equal types are one way to have it, not the only one. -/
def equalTypesTrial : Constraint Nat :=
  .eq (.succ (.param 0)) (.const 6)

/-- Negative: **a step for a constraint that the judgment does not need can lose every
solution.** The use `l = 3` has the solution `3`. The step of `l + 1 = 6` raises `l` to `5`,
and no solution extends that: a search that made the step would refute a judgment that
holds. `Below.step` asks for a constraint of the judgment for this reason. -/
theorem trial_step_loses_solution :
    Solves solveFirst fixedAtThree (fun _ => 0) (fun i => if i = 0 then 3 else 0) ∧
      ∃ σ : Nat → Nat, equalTypesTrial.step levelBounds solveFirst (fun _ => 0) = some σ ∧
        σ 0 = 5 ∧
        ∀ τ, Solves solveFirst fixedAtThree (fun _ => 0) τ → ¬ Extends solveFirst σ τ := by
  refine ⟨⟨⟨fun i => Nat.zero_le _, fun i unsolved => ?_⟩, fun C mem => ?_⟩, ?_⟩
  · have other : i ≠ 0 := by
      rintro rfl
      exact absurd unsolved (by decide)
    show (if i = 0 then 3 else 0) = 0
    rw [if_neg other]
  · simp only [fixedAtThree, List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    rfl
  · cases stepped : equalTypesTrial.step levelBounds solveFirst fun _ => 0 with
    | none => exact absurd stepped (by decide)
    | some σ =>
      have five : σ 0 = 5 := by
        have : (equalTypesTrial.step levelBounds solveFirst fun _ => 0).map (fun σ => σ 0) =
            some 5 := by decide
        rw [stepped] at this
        exact Option.some.inj this
      refine ⟨σ, rfl, five, fun τ solves above => ?_⟩
      have three : (3 : Nat) = τ 0 := solves.2 _ List.mem_cons_self
      have reached := above.le 0
      rw [five, ← three] at reached
      exact absurd reached (by decide)

/-- Negative: `l + 1 ≤ l` holds at no assignment, and every pass raises `l`. -/
theorem succ_le_self_no_solution (σ₀ τ : Nat → Nat) :
    ¬ Solves solveFirst [.le (.succ (.param 0)) (.param 0)] σ₀ τ := fun solves =>
  absurd (solves.2 _ List.mem_cons_self) (Nat.not_succ_le_self (τ 0))

example : (passes levelBounds solveFirst [.le (.succ (.param 0)) (.param 0)] 3 fun _ => 0).map
    (fun σ => σ 0) = some 3 := by
  decide

end Examples

/-! ## Examples over the ordinal notations below ε₀ -/

section TransfiniteExamples

/-- The least level whose successor reaches `ω` is `ω`: the parameter under one successor is
raised to `ω`. -/
example : (raise levelBounds solveFirst (.succ (.param 0)) Level.omega fun _ => Level.zero).map
    (fun σ => σ 0) = some Level.omega := by
  decide

/-- Negative: **`ω` is the successor of no level**: the equation `ω = l + 1` has no instance,
by one raise and one test. -/
theorem omega_eq_succ_no_solution :
    ∀ τ : Nat → Level, ¬ Solves solveFirst
      [.eq (.const Level.omega) (.succ (.param 0))] (fun _ => Level.zero) τ := by
  cases raised : raise levelBounds solveFirst (.succ (.param 0))
      (value (fun _ => Level.zero) (.const Level.omega)) fun _ => Level.zero with
  | none => exact absurd raised (by decide)
  | some σ' =>
    have reached : σ' 0 = Level.omega := by
      have : (raise levelBounds solveFirst (.succ (.param 0))
          (value (fun _ => Level.zero) (.const Level.omega)) fun _ => Level.zero).map
          (fun σ => σ 0) = some Level.omega := by decide
      rw [raised] at this
      exact Option.some.inj this
    refine (Below.refl solveFirst _ _).no_solution_of_eq_left (a := .const Level.omega)
      (b := .succ (.param 0)) List.mem_cons_self rfl raised ?_
    show LevelOrder.succ (σ' 0) ≠ Level.omega
    rw [reached]
    decide

end TransfiniteExamples

end LeastInstance

end Mettapedia.TypeTheory.UniverseLevel
