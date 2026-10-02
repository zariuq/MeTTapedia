import Mettapedia.TypeTheory.UniverseLevel.Extension

/-!
# Initiality is needed for bounds

An embedding of level orders preserves and reflects an unbounded comparison.
Under bounds, the same statement asks the embedding to be an initial segment.
The embedding defined here is not an initial segment. On the level order of
order type `ω + ω` it fixes every finite level and sends `ω + n` to
`ω + n + 1`, so the limit `ω` is sent to the successor `ω + 1`.

The comparison `x + 2 ≤ ω` holds for every `x < ω`. After the embedding the
bound is `ω + 1`, the right-hand side is `ω + 1`, and the valuation `x = ω`
is still allowed, but `ω + 2` does not lie under `ω + 1`.

The unbounded theorem still applies to this embedding. This module does not
use the comparison of level notations with ordinals.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

/-- Levels of order type `ω + ω`. `fin n` is the finite level `n`. `plus n` is
the level `ω + n`. -/
inductive TwoCopy where
  | fin : Nat → TwoCopy
  | plus : Nat → TwoCopy
  deriving DecidableEq

namespace TwoCopy

open Ordering

/-- The level `ω`. -/
def w : TwoCopy := plus 0

/-- Comparison: every finite level lies below every level `ω + n`, and each copy is
ordered by the natural numbers. -/
def cmp : TwoCopy → TwoCopy → Ordering
  | fin m, fin n => compare m n
  | fin _, plus _ => .lt
  | plus _, fin _ => .gt
  | plus m, plus n => compare m n

theorem nat_compare_swap (m n : Nat) : (compare m n).swap = compare n m := by
  cases h : compare m n with
  | lt =>
    rw [Nat.compare_eq_gt.mpr (Nat.compare_eq_lt.mp h)]
    rfl
  | eq =>
    rw [Nat.compare_eq_eq.mpr (Nat.compare_eq_eq.mp h).symm]
    rfl
  | gt =>
    rw [Nat.compare_eq_lt.mpr (Nat.compare_eq_gt.mp h)]
    rfl

theorem cmp_swap : ∀ x y : TwoCopy, (cmp x y).swap = cmp y x
  | fin m, fin n => nat_compare_swap m n
  | fin _, plus _ => rfl
  | plus _, fin _ => rfl
  | plus m, plus n => nat_compare_swap m n

theorem cmp_self : ∀ x : TwoCopy, cmp x x = .eq
  | fin _ => Nat.compare_eq_eq.mpr rfl
  | plus _ => Nat.compare_eq_eq.mpr rfl

theorem eq_of_cmp_eq {x y : TwoCopy} (h : cmp x y = .eq) : x = y := by
  cases x with
  | fin m =>
    cases y with
    | fin n => exact congrArg fin (Nat.compare_eq_eq.mp h)
    | plus _ => exact nomatch h
  | plus m =>
    cases y with
    | fin _ => exact nomatch h
    | plus n => exact congrArg plus (Nat.compare_eq_eq.mp h)

theorem cmp_lt_trans {x y z : TwoCopy} (hxy : cmp x y = .lt) (hyz : cmp y z = .lt) :
    cmp x z = .lt := by
  cases x with
  | fin _ =>
    cases y with
    | fin _ =>
      cases z with
      | fin _ =>
        exact Nat.compare_eq_lt.mpr
          (Nat.lt_trans (Nat.compare_eq_lt.mp hxy) (Nat.compare_eq_lt.mp hyz))
      | plus _ => rfl
    | plus _ =>
      cases z with
      | fin _ => exact nomatch hyz
      | plus _ => rfl
  | plus _ =>
    cases y with
    | fin _ => exact nomatch hxy
    | plus _ =>
      cases z with
      | fin _ => exact nomatch hyz
      | plus _ =>
        exact Nat.compare_eq_lt.mpr
          (Nat.lt_trans (Nat.compare_eq_lt.mp hxy) (Nat.compare_eq_lt.mp hyz))

theorem compare_ne_gt_of_le {m n : Nat} (h : m ≤ n) : compare m n ≠ .gt := by
  cases hc : compare m n with
  | lt => exact nofun
  | eq => exact nofun
  | gt => exact absurd (Nat.compare_eq_gt.mp hc) (Nat.not_lt_of_ge h)

instance : LinearOrder TwoCopy where
  le x y := cmp x y ≠ .gt
  lt x y := cmp x y = .lt
  le_refl x := by
    show cmp x x ≠ .gt
    rw [cmp_self]
    exact nofun
  le_trans x y z hxy hyz := by
    intro hxz
    cases hxy_c : cmp x y with
    | gt => exact hxy hxy_c
    | eq =>
      rw [eq_of_cmp_eq hxy_c] at hxz
      exact hyz hxz
    | lt =>
      cases hyz_c : cmp y z with
      | gt => exact hyz hyz_c
      | eq =>
        rw [← eq_of_cmp_eq hyz_c] at hxz
        rw [hxy_c] at hxz
        exact nomatch hxz
      | lt =>
        rw [cmp_lt_trans hxy_c hyz_c] at hxz
        exact nomatch hxz
  lt_iff_le_not_ge x y := by
    show cmp x y = .lt ↔ cmp x y ≠ .gt ∧ ¬ cmp y x ≠ .gt
    cases h : cmp x y with
    | lt =>
      refine ⟨fun _ => ⟨nofun, ?_⟩, fun _ => rfl⟩
      intro hne
      have hswap : cmp y x = .gt := by
        rw [← cmp_swap x y, h]
        rfl
      exact hne hswap
    | eq =>
      refine ⟨(fun h' => nomatch h'), (fun hnot => ?_)⟩
      have hswap : cmp y x ≠ .gt := by
        rw [← cmp_swap x y, h]
        exact nofun
      exact False.elim (hnot.2 hswap)
    | gt =>
      refine ⟨(fun h' => nomatch h'), (fun hnot => False.elim (hnot.1 rfl))⟩
  le_antisymm x y hxy hyx := by
    cases h : cmp x y with
    | lt =>
      have hswap : cmp y x = .gt := by
        rw [← cmp_swap x y, h]
        rfl
      exact absurd hswap hyx
    | eq => exact eq_of_cmp_eq h
    | gt => exact absurd h hxy
  min x y := if cmp x y ≠ .gt then x else y
  max x y := if cmp x y ≠ .gt then y else x
  compare x y := cmp x y
  le_total x y := by
    cases h : cmp x y with
    | lt => exact Or.inl nofun
    | eq => exact Or.inl nofun
    | gt =>
      refine Or.inr ?_
      show cmp y x ≠ .gt
      rw [← cmp_swap x y, h]
      exact nofun
  toDecidableLE x y := inferInstanceAs (Decidable (cmp x y ≠ .gt))
  toDecidableEq := inferInstance
  toDecidableLT x y := inferInstanceAs (Decidable (cmp x y = .lt))
  min_def _ _ := rfl
  max_def _ _ := rfl
  compare_eq_compareOfLessAndEq x y := by
    show cmp x y = if cmp x y = .lt then .lt else if x = y then .eq else .gt
    cases h : cmp x y with
    | lt => rfl
    | eq => rw [if_pos (eq_of_cmp_eq h)]; rfl
    | gt =>
      have hne : x ≠ y := fun e => by
        subst e
        rw [cmp_self] at h
        exact nomatch h
      rw [if_neg hne]
      rfl

/-- The successor: one step up inside the same copy. -/
def succ : TwoCopy → TwoCopy
  | fin n => fin (n + 1)
  | plus n => plus (n + 1)

/-- The least level, `0`. -/
def bot : TwoCopy := fin 0

theorem acc_fin : ∀ n, Acc (fun a b : TwoCopy => a < b) (fin n)
  | 0 =>
    Acc.intro _ fun y hy => by
      cases y with
      | plus _ => exact nomatch hy
      | fin m => exact absurd (Nat.compare_eq_lt.mp hy) (Nat.not_lt_zero m)
  | n + 1 =>
    Acc.intro _ fun y hy => by
      cases y with
      | plus _ => exact nomatch hy
      | fin m =>
        have hmn : m ≤ n := Nat.le_of_lt_succ (Nat.compare_eq_lt.mp hy)
        match Nat.eq_or_lt_of_le hmn with
        | Or.inl heq =>
          cases heq
          exact acc_fin n
        | Or.inr hlt =>
          exact Acc.inv (acc_fin n) (Nat.compare_eq_lt.mpr hlt)

theorem acc_plus : ∀ n, Acc (fun a b : TwoCopy => a < b) (plus n)
  | 0 =>
    Acc.intro _ fun y hy => by
      cases y with
      | fin m => exact acc_fin m
      | plus m => exact absurd (Nat.compare_eq_lt.mp hy) (Nat.not_lt_zero m)
  | n + 1 =>
    Acc.intro _ fun y hy => by
      cases y with
      | fin m => exact acc_fin m
      | plus m =>
        have hmn : m ≤ n := Nat.le_of_lt_succ (Nat.compare_eq_lt.mp hy)
        match Nat.eq_or_lt_of_le hmn with
        | Or.inl heq =>
          cases heq
          exact acc_plus n
        | Or.inr hlt =>
          exact Acc.inv (acc_plus n) (Nat.compare_eq_lt.mpr hlt)

instance : LevelOrder TwoCopy where
  toLinearOrder := inferInstance
  wf := ⟨fun x => by
    cases x with
    | fin n => exact acc_fin n
    | plus n => exact acc_plus n⟩
  bot := bot
  bot_le := fun l => by
    cases l with
    | fin n => exact compare_ne_gt_of_le (Nat.zero_le n)
    | plus _ => exact nofun
  succ := succ
  lt_succ := fun l => by
    cases l with
    | fin n => exact Nat.compare_eq_lt.mpr (Nat.lt_succ_self n)
    | plus n => exact Nat.compare_eq_lt.mpr (Nat.lt_succ_self n)
  succ_le_of_lt := fun {a b} h => by
    cases a with
    | fin m =>
      cases b with
      | fin n => exact compare_ne_gt_of_le (Nat.succ_le_of_lt (Nat.compare_eq_lt.mp h))
      | plus _ => exact nofun
    | plus m =>
      cases b with
      | fin _ => exact nomatch h
      | plus n => exact compare_ne_gt_of_le (Nat.succ_le_of_lt (Nat.compare_eq_lt.mp h))

/-- Identity on the finite levels, and `ω + n ↦ ω + n + 1`. -/
def bumpFun : TwoCopy → TwoCopy
  | fin n => fin n
  | plus n => plus (n + 1)

theorem bumpFun_le_iff {a b : TwoCopy} : bumpFun a ≤ bumpFun b ↔ a ≤ b := by
  cases a with
  | fin m =>
    cases b with
    | fin n =>
      exact Iff.rfl
    | plus _ =>
      exact Iff.rfl
  | plus m =>
    cases b with
    | fin _ =>
      exact Iff.rfl
    | plus n =>
      show compare (m + 1) (n + 1) ≠ .gt ↔ compare m n ≠ .gt
      cases h : compare m n with
      | lt =>
        rw [Nat.compare_eq_lt.mpr (Nat.succ_lt_succ (Nat.compare_eq_lt.mp h))]
      | eq =>
        have hm : m = n := Nat.compare_eq_eq.mp h
        cases hm
        rw [Nat.compare_eq_eq.mpr rfl]
      | gt =>
        rw [Nat.compare_eq_gt.mpr (Nat.succ_lt_succ (Nat.compare_eq_gt.mp h))]

/-- The embedding that shifts the `ω` copy up by one. -/
def bump : LevelOrder.Embedding TwoCopy TwoCopy where
  toFun := bumpFun
  le_iff := bumpFun_le_iff
  map_bot := rfl
  map_succ := by
    intro a
    cases a with
    | fin _ => rfl
    | plus _ => rfl

/-- `ω` is a limit level. -/
theorem isLimit_w : LevelOrder.IsLimit w := by
  refine ⟨?_, fun p hp => ?_⟩
  · rfl
  · cases p with
    | fin _ => exact nomatch hp
    | plus n =>
      have hn : n + 1 = 0 := plus.inj hp
      exact Nat.succ_ne_zero n hn

/-- `bump` sends the limit `ω` to the successor `ω + 1`. -/
theorem bump_limit_to_succ : LevelOrder.IsLimit w ∧ bump w = LevelOrder.succ w :=
  ⟨isLimit_w, rfl⟩

/-- Nothing is sent to `ω`: the finite levels stay finite, and `ω + n` moves to
`ω + n + 1`. -/
theorem bump_ne_w (a : TwoCopy) : bump a ≠ w := by
  cases a with
  | fin _ =>
    intro h
    exact nomatch h
  | plus n =>
    intro h
    have hn : n + 1 = 0 := plus.inj h
    exact Nat.succ_ne_zero n hn

/-- `ω` lies strictly below `bump ω`. -/
theorem w_lt_bump_w : w < bump w := by
  show compare 0 1 = .lt
  exact Nat.compare_eq_lt.mpr Nat.zero_lt_one

/-- `bump` is not an initial segment: `ω` lies below `bump ω` and is not in the image. -/
theorem bump_not_initial : ¬ bump.Initial := by
  intro initial
  obtain ⟨a, ha⟩ := initial w w w_lt_bump_w
  exact bump_ne_w a ha

/-- The variable `0` ranges strictly below `ω`. -/
def belowW : LevelBounds TwoCopy := fun i => if i = 0 then some w else none

theorem belowW_zero : belowW 0 = some w := by
  rw [belowW, if_pos rfl]

/-- `x + 2`. -/
def exprTwo : LevelExpr TwoCopy := .succ (.succ (.param 0))

/-- The constant `ω`. -/
def exprW : LevelExpr TwoCopy := .const w

/-- Under `x < ω`, the level `x + 2` lies under `ω`. -/
theorem leUnder_two_w : LevelBounds.LeUnder belowW exprTwo exprW := by
  intro ν valid
  have hlt : ν 0 < w := valid 0 w belowW_zero
  cases hν : ν 0 with
  | plus k =>
    rw [hν] at hlt
    exact absurd (Nat.compare_eq_lt.mp hlt) (Nat.not_lt_zero k)
  | fin _ =>
    show succ (succ (ν 0)) ≤ w
    rw [hν]
    exact nofun

/-- The witness that breaks the mapped comparison: variable `0` is `ω`. -/
def witness (j : Nat) : TwoCopy := if j = 0 then w else bot

theorem witness_zero : witness 0 = w := by
  rw [witness, if_pos rfl]

/-- After `bump`, the bound on `0` is `ω + 1`. -/
theorem map_belowW_zero : LevelBounds.map bump belowW 0 = some (plus 1) := by
  show (belowW 0).map bump = some (plus 1)
  rw [belowW_zero]
  rfl

/-- `ω` is still strictly below the mapped bound `ω + 1`. -/
theorem w_lt_plus_one : w < plus 1 := by
  show compare 0 1 = .lt
  exact Nat.compare_eq_lt.mpr Nat.zero_lt_one

/-- The valuation at `ω` respects the mapped bounds. -/
theorem witness_valid : (LevelBounds.map bump belowW).Valid witness := by
  intro i c h
  cases hi : decide (i = 0) with
  | false =>
    have hne : i ≠ 0 := of_decide_eq_false hi
    have hnone : belowW i = none := by
      rw [belowW, if_neg hne]
    rw [LevelBounds.map, hnone] at h
    exact nomatch h
  | true =>
    have heq : i = 0 := of_decide_eq_true hi
    cases heq
    rw [LevelBounds.map, belowW_zero] at h
    obtain rfl : bump w = c := Option.some.inj h
    rw [witness_zero]
    exact w_lt_plus_one

/-- `ω + 2` does not lie under `ω + 1`. -/
theorem not_plus_two_le_plus_one : ¬ plus 2 ≤ plus 1 := by
  intro h
  exact h (Nat.compare_eq_gt.mpr (Nat.lt_succ_self 1))

/-- Mapping the bounds and the constants along `bump` breaks `x + 2 ≤ ω`.
The valuation `x = ω` lies under the new bound `ω + 1` and reverses the comparison. -/
theorem not_leUnder_bumped :
    ¬ LevelBounds.LeUnder (LevelBounds.map bump belowW) (exprTwo.map bump) (exprW.map bump) := by
  intro held
  have hle := held witness witness_valid
  have htwo : LevelExpr.eval witness (exprTwo.map bump) = plus 2 := by
    show succ (succ (witness 0)) = plus 2
    rw [witness_zero]
    rfl
  have hw : LevelExpr.eval witness (exprW.map bump) = plus 1 := by
    show bump w = plus 1
    rfl
  rw [htwo, hw] at hle
  exact not_plus_two_le_plus_one hle

/-- The unbounded comparison is still conservative along `bump`. -/
theorem bump_level_le_conservative (e₁ e₂ : LevelExpr TwoCopy) :
    (∀ v : Nat → TwoCopy,
        LevelExpr.eval v (e₁.map bump) ≤ LevelExpr.eval v (e₂.map bump)) ↔
      ∀ v : Nat → TwoCopy, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂ :=
  LevelNF.level_le_conservative bump e₁ e₂

end TwoCopy

end Mettapedia.TypeTheory.UniverseLevel
