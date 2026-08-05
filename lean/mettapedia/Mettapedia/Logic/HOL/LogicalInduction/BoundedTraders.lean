import Mettapedia.Logic.HOL.LogicalInduction.Criterion

/-!
# Bounded-Volume Traders Cannot Exploit

The budgeter soundness kernel for the logical-induction layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the inductor construction
tames an enumerated trader basis with a budgeter transform; its soundness
rests on the fact that a trader whose cumulative trading volume is bounded
can never become unboundedly rich, because each share's payoff-minus-price
lies in `[-1, 1]`.  This module proves that fact over the existing
`Criterion` vocabulary, strictly generalizing `silent_not_exploits`
(the silent trader is the volume-zero instance), and shows by a concrete
unit-buyer counterexample that the bounded-volume class genuinely excludes
real traders.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Model : Type w}
variable (satisfies : Model → ClosedFormulaCode Const → Prop)

/-- Total absolute size of an order: how many shares change hands. -/
noncomputable def orderVolume (o : MarketOrder Const) : Rat :=
  o.positions.sum (fun p => |p.2|)

@[simp] theorem orderVolume_empty :
    orderVolume (MarketOrder.empty (Const := Const)) = 0 := by
  simp [orderVolume, MarketOrder.empty]

theorem orderVolume_nonneg (o : MarketOrder Const) :
    0 ≤ orderVolume (Const := Const) o :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Cumulative traded volume through day `n - 1`. -/
noncomputable def volumeUpTo
    (P : BeliefProcess Const) (T : Trader Const) (n : Nat) : Rat :=
  (Finset.range n).sum (fun k => orderVolume (Const := Const) (T.orderAt P k))

/-- A trader budgeted by `V`: its lifetime volume never exceeds `V`. -/
def HasBoundedVolume
    (P : BeliefProcess Const) (T : Trader Const) (V : Rat) : Prop :=
  ∀ n : Nat, volumeUpTo (Const := Const) P T n ≤ V

theorem sharePayoff_nonneg (M : Model) (φ : ClosedFormulaCode Const) :
    0 ≤ sharePayoff (Const := Const) satisfies M φ := by
  simp only [sharePayoff]
  split <;> norm_num

theorem sharePayoff_le_one (M : Model) (φ : ClosedFormulaCode Const) :
    sharePayoff (Const := Const) satisfies M φ ≤ 1 := by
  simp only [sharePayoff]
  split <;> norm_num

/-- One share's payoff-minus-price sits in `[-1, 1]`. -/
theorem abs_payoff_sub_price_le_one
    (B : BeliefDay Const) (M : Model) (φ : ClosedFormulaCode Const) :
    |sharePayoff (Const := Const) satisfies M φ - ((B φ : Price01) : Rat)| ≤ 1 := by
  have hp0 := sharePayoff_nonneg (Const := Const) satisfies M φ
  have hp1 := sharePayoff_le_one (Const := Const) satisfies M φ
  have hq0 : (0 : Rat) ≤ ((B φ : Price01) : Rat) := (B φ).zero_le
  have hq1 : ((B φ : Price01) : Rat) ≤ 1 := (B φ).le_one
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The day-value of any order is dominated by its volume. -/
theorem abs_orderValueAt_le_orderVolume
    (B : BeliefDay Const) (M : Model) (o : MarketOrder Const) :
    |orderValueAt (Const := Const) satisfies B M o| ≤
      orderVolume (Const := Const) o := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul]
  calc |p.2| * |sharePayoff (Const := Const) satisfies M p.1 - ((B p.1 : Price01) : Rat)|
      ≤ |p.2| * 1 :=
        mul_le_mul_of_nonneg_left
          (abs_payoff_sub_price_le_one (Const := Const) satisfies B M p.1)
          (abs_nonneg _)
    _ = |p.2| := mul_one _

/-- Holdings value never exceeds cumulative volume. -/
theorem holdingsValueUpTo_le_volumeUpTo
    (P : BeliefProcess Const) (T : Trader Const) (n : Nat) (M : Model) :
    holdingsValueUpTo (Const := Const) satisfies P T n M ≤
      volumeUpTo (Const := Const) P T n :=
  Finset.sum_le_sum fun k _ =>
    (le_abs_self _).trans
      (abs_orderValueAt_le_orderVolume (Const := Const) satisfies (P k) M
        (T.orderAt P k))

/-- **Budgeter soundness, negative half**: a budgeted trader is never
unboundedly rich on plausible worlds. -/
theorem boundedVolume_not_unboundedAbove
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) (T : Trader Const) (V : Rat)
    (hV : HasBoundedVolume (Const := Const) P T V) :
    ¬ UnboundedAboveOnPlausible (Const := Const) satisfies D P T := by
  intro hunb
  rcases hunb (V + 1) with ⟨n, M, _hpl, hge⟩
  have hle := holdingsValueUpTo_le_volumeUpTo (Const := Const) satisfies P T n M
  have hvol := hV n
  linarith

/-- **Budgeter soundness**: bounded lifetime volume rules out exploitation. -/
theorem boundedVolume_not_exploits
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) (T : Trader Const) (V : Rat)
    (hV : HasBoundedVolume (Const := Const) P T V) :
    ¬ Exploits (Const := Const) satisfies D P T := by
  intro hex
  exact boundedVolume_not_unboundedAbove
    (Const := Const) satisfies D P T V hV hex.2

/-- The criterion holds outright for any admissibility notion that implies a
volume budget. -/
theorem criterion_of_admissible_budgeted
    (Admissible : Trader Const → Prop)
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const)
    (h : ∀ T : Trader Const, Admissible T →
      ∃ V : Rat, HasBoundedVolume (Const := Const) P T V) :
    LogicalInductionCriterion (Const := Const) satisfies Admissible D P := by
  intro T hT
  rcases h T hT with ⟨V, hV⟩
  exact boundedVolume_not_exploits (Const := Const) satisfies D P T V hV

/-! ## Positive instance: the silent trader has volume zero. -/

@[simp] theorem silent_volumeUpTo
    (P : BeliefProcess Const) (n : Nat) :
    volumeUpTo (Const := Const) P (Trader.silent (Const := Const)) n = 0 := by
  simp [volumeUpTo, Trader.orderAt, Trader.silent]

theorem silent_hasBoundedVolume (P : BeliefProcess Const) :
    HasBoundedVolume (Const := Const) P (Trader.silent (Const := Const)) 0 := by
  intro n
  simp

/-- `silent_not_exploits`, re-derived as the volume-zero instance. -/
theorem silent_not_exploits'
    (D : DeductiveProcess Const) (P : BeliefProcess Const) :
    ¬ Exploits (Const := Const) satisfies D P (Trader.silent (Const := Const)) :=
  boundedVolume_not_exploits (Const := Const) satisfies D P _ 0
    (silent_hasBoundedVolume (Const := Const) P)

/-! ## Negative instance: the unit buyer escapes every budget. -/

/-- Buys one share of a fixed formula every day, at any prices. -/
def Trader.unitBuyer (φ : ClosedFormulaCode Const) : Trader Const where
  act := fun _ _ => ⟨{(φ, 1)}⟩

@[simp] theorem unitBuyer_orderVolume
    (P : BeliefProcess Const) (φ : ClosedFormulaCode Const) (k : Nat) :
    orderVolume (Const := Const)
      ((Trader.unitBuyer (Const := Const) φ).orderAt P k) = 1 := by
  simp [orderVolume, Trader.orderAt, Trader.unitBuyer]

theorem unitBuyer_volumeUpTo
    (P : BeliefProcess Const) (φ : ClosedFormulaCode Const) (n : Nat) :
    volumeUpTo (Const := Const) P (Trader.unitBuyer (Const := Const) φ) n =
      (n : Rat) := by
  simp [volumeUpTo]

/-- No finite budget contains the unit buyer: `HasBoundedVolume` genuinely
excludes real traders, so the budgeted class is nontrivial in both
directions. -/
theorem unitBuyer_not_hasBoundedVolume
    (P : BeliefProcess Const) (φ : ClosedFormulaCode Const) (V : Rat) :
    ¬ HasBoundedVolume (Const := Const) P
        (Trader.unitBuyer (Const := Const) φ) V := by
  intro hV
  rcases exists_nat_gt V with ⟨n, hn⟩
  have h := hV n
  rw [unitBuyer_volumeUpTo (Const := Const) P φ n] at h
  exact absurd (lt_of_lt_of_le hn h) (lt_irrefl _)

end Mettapedia.Logic.HOL.LogicalInduction
