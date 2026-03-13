import Mettapedia.Logic.HOL.LogicalInduction.Market
/-!
# Logical Induction Criterion Over HOL Formulas

This module packages a market-style exploitability criterion for the
logical-induction-ready HOL belief layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), the central idea is that a
belief process should not admit systematic exploitation relative to a deductive
process.  This file implements that criterion at the level of definitions and
toy theoremic infrastructure over closed HOL formulas, parameterized by an
explicit model type and satisfaction relation.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Model : Type w}
variable (satisfies : Model → ClosedFormulaCode Const → Prop)

/-- The semantic payoff of one share of a closed HOL formula at a model. -/
noncomputable def sharePayoff
    (M : Model) (φ : ClosedFormulaCode Const) : Rat := by
  classical
  exact if satisfies M φ then 1 else 0

/-- Net value of a finite market order at one model and one price day. -/
noncomputable def orderValueAt
    (B : BeliefDay Const)
    (M : Model)
    (o : MarketOrder Const) : Rat :=
  o.positions.sum
    (fun p => p.2 * (sharePayoff (Const := Const) satisfies M p.1 - ((B p.1 : Price01) : Rat)))

/-- All theorem-stream formulas visible by day `n` hold in the model. -/
def PlausibleAt
    (D : DeductiveProcess Const) (n : Nat)
    (M : Model) : Prop :=
  ∀ {φ : ClosedFormulaCode Const}, φ ∈ D.days n → satisfies M φ

/-- Net holdings value after trading through day `n - 1`. -/
noncomputable def holdingsValueUpTo
    (P : BeliefProcess Const)
    (T : Trader Const)
    (n : Nat)
    (M : Model) : Rat :=
  (Finset.range n).sum
    (fun k => orderValueAt (Const := Const) satisfies (B := P k) M (T.orderAt P k))

/-- Exploiters keep plausible net worth bounded below while becoming
arbitrarily rich on some plausible world at some day. -/
def BoundedBelowOnPlausible
    (D : DeductiveProcess Const) (P : BeliefProcess Const) (T : Trader Const) : Prop :=
  ∃ b : Rat,
    ∀ n : Nat, ∀ M : Model,
      PlausibleAt (Const := Const) satisfies D n M →
        b ≤ holdingsValueUpTo (Const := Const) satisfies P T n M

def UnboundedAboveOnPlausible
    (D : DeductiveProcess Const) (P : BeliefProcess Const) (T : Trader Const) : Prop :=
  ∀ B : Rat, ∃ n : Nat, ∃ M : Model,
    PlausibleAt (Const := Const) satisfies D n M ∧
      B ≤ holdingsValueUpTo (Const := Const) satisfies P T n M

def Exploits
    (D : DeductiveProcess Const) (P : BeliefProcess Const) (T : Trader Const) : Prop :=
  BoundedBelowOnPlausible (Const := Const) satisfies D P T ∧
    UnboundedAboveOnPlausible (Const := Const) satisfies D P T

/-- Criterion schema: no admissible trader exploits the belief process relative
to the deductive process.  This keeps trader admissibility abstract in v1. -/
def LogicalInductionCriterion
    (Admissible : Trader Const → Prop)
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) : Prop :=
  ∀ T : Trader Const, Admissible T → ¬ Exploits (Const := Const) satisfies D P T

@[simp] theorem orderValueAt_empty
    (B : BeliefDay Const)
    (M : Model) :
    orderValueAt (Const := Const) satisfies B M (MarketOrder.empty (Const := Const)) = 0 := by
  simp [orderValueAt, MarketOrder.empty]

@[simp] theorem silent_holdings_zero
    (P : BeliefProcess Const)
    (n : Nat)
    (M : Model) :
    holdingsValueUpTo (Const := Const) satisfies P (Trader.silent (Const := Const)) n M = 0 := by
  simp [holdingsValueUpTo, Trader.orderAt, Trader.silent, orderValueAt_empty]

theorem silent_not_unboundedAbove
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) :
    ¬ UnboundedAboveOnPlausible (Const := Const) satisfies D P (Trader.silent (Const := Const)) := by
  intro hunb
  rcases hunb 1 with ⟨n, M, _hpl, hge⟩
  rw [silent_holdings_zero (Const := Const) satisfies P n M] at hge
  norm_num at hge

theorem silent_not_exploits
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const) :
    ¬ Exploits (Const := Const) satisfies D P (Trader.silent (Const := Const)) := by
  intro hex
  exact silent_not_unboundedAbove (Const := Const) satisfies D P hex.2

theorem criterion_holds_if_all_admissible_traders_are_nonexploitative
    (Admissible : Trader Const → Prop)
    (D : DeductiveProcess Const)
    (P : BeliefProcess Const)
    (h : ∀ T : Trader Const, Admissible T → ¬ Exploits (Const := Const) satisfies D P T) :
    LogicalInductionCriterion (Const := Const) satisfies Admissible D P := by
  simpa [LogicalInductionCriterion] using h

end Mettapedia.Logic.HOL.LogicalInduction
