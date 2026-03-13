import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mettapedia.Logic.HOL.LogicalInduction.DeductiveProcess

/-!
# Market-Style Belief States Over Closed HOL Formulas

This module provides the day-by-day belief/price vocabulary for the
logical-induction-ready HOL layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), we treat beliefs as
time-indexed prices on closed formulas.  The present module deliberately keeps
this layer separate from semantic truth in Henkin models and from the static
HOL↔WM bridge.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Rational probabilities/prices in the unit interval. -/
structure Price01 where
  val : Rat
  zero_le : 0 ≤ val
  le_one : val ≤ 1
deriving Repr

namespace Price01

instance : Coe Price01 Rat := ⟨Price01.val⟩

@[ext] theorem ext {p q : Price01} (h : p.val = q.val) : p = q := by
  cases p
  cases q
  cases h
  simp

def zero : Price01 := ⟨0, by norm_num, by norm_num⟩
def one : Price01 := ⟨1, by norm_num, by norm_num⟩
def half : Price01 := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] theorem coe_zero : ((zero : Price01) : Rat) = 0 := rfl
@[simp] theorem coe_one : ((one : Price01) : Rat) = 1 := rfl
@[simp] theorem coe_half : ((half : Price01) : Rat) = 1 / 2 := rfl

end Price01

/-- A single day of prices on closed HOL formulas. -/
abbrev BeliefDay (Const : Ty Base → Type v) := ClosedFormulaCode Const → Price01

/-- A time-indexed belief process over closed HOL formulas. -/
abbrev BeliefProcess (Const : Ty Base → Type v) := Nat → BeliefDay Const

/-- The visible prefix of a belief process before day `n`. -/
abbrev BeliefPrefix (Const : Ty Base → Type v) (n : Nat) := Fin n → BeliefDay Const

/-- Prefix extraction for a belief process. -/
def historyPrefix (P : BeliefProcess Const) (n : Nat) : BeliefPrefix Const n :=
  fun i => P i.1

/-- Constant belief day. -/
def constantDay (p : Price01) : BeliefDay Const := fun _ => p

/-- Constant belief process. -/
def constantProcess (p : Price01) : BeliefProcess Const := fun _ => constantDay (Const := Const) p

/-- A finite-support affine order over closed HOL formulas. -/
structure MarketOrder (Const : Ty Base → Type v) where
  positions : Finset (ClosedFormulaCode Const × Rat)

namespace MarketOrder

def empty : MarketOrder Const := ⟨∅⟩

@[simp] theorem positions_empty :
    (empty (Const := Const)).positions = ∅ := rfl

end MarketOrder

/-- A trader reads the day and all prior prices, then emits a finite order. -/
structure Trader (Const : Ty Base → Type v) where
  act : (n : Nat) → BeliefPrefix Const n → MarketOrder Const

/-- The order chosen by a trader on day `n` against a given belief process. -/
def Trader.orderAt (T : Trader Const) (P : BeliefProcess Const) (n : Nat) : MarketOrder Const :=
  T.act n (historyPrefix (Const := Const) P n)

/-- Trader that never trades. -/
def Trader.silent : Trader Const where
  act := fun _ _ => MarketOrder.empty

/-- The constant-one process, useful for positive calibration/timely-learning fixtures. -/
def processOne : BeliefProcess Const := constantProcess (Const := Const) Price01.one

/-- The constant-zero process, useful for negative calibration/timely-learning fixtures. -/
def processZero : BeliefProcess Const := constantProcess (Const := Const) Price01.zero

/-- The constant-half process, useful for non-dogmatic toy examples. -/
def processHalf : BeliefProcess Const := constantProcess (Const := Const) Price01.half

@[simp] theorem processOne_apply (n : Nat) (φ : ClosedFormulaCode Const) :
    ((processOne (Const := Const) n φ : Price01) : Rat) = 1 := by
  rfl

@[simp] theorem processZero_apply (n : Nat) (φ : ClosedFormulaCode Const) :
    ((processZero (Const := Const) n φ : Price01) : Rat) = 0 := by
  rfl

@[simp] theorem processHalf_apply (n : Nat) (φ : ClosedFormulaCode Const) :
    ((processHalf (Const := Const) n φ : Price01) : Rat) = 1 / 2 := by
  rfl

end Mettapedia.Logic.HOL.LogicalInduction
