/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Main Theorem: R(3,6) = 18

This file contains the main result combining both bounds.
-/

import Ramsey36.Basic
import Ramsey36.Critical17Clean
import Ramsey36.UpperBound

open SimpleGraph

/-! ## The Bridge Theorem -/

/-- **Main Result**: The Ramsey number R(3,6) equals 18.

    This combines two results:
    - Lower bound: ramsey_three_six_ge_18 (from Critical17Clean)
    - Upper bound: ramsey_three_six_upper (from UpperBound)
-/
theorem ramsey_three_six : ramseyNumber 3 6 = 18 := by
  apply Nat.le_antisymm
  · -- Upper bound: R(3,6) ≤ 18
    exact ramsey_three_six_upper
  · -- Lower bound: 18 ≤ R(3,6)
    exact ramsey_three_six_ge_18
