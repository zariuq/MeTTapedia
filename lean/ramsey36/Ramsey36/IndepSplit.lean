/-
# Split Independent Set Check for Fin 17

The full `decide` on `hasIndepSet 17 adj17Bool 6` causes kernel OOM.
Split into 12 sub-problems (one per first vertex), each fast for the kernel.

## LLM Notes
- adj17Bool and sub17_0..sub17_11 live in IndepSub17 (Mathlib-free).
- Combination uses hasIndepSetAux_false_of_compat from IndepSetChecker.
-/

import Algorithms.Graph.IndepSetChecker
import Ramsey36.IndepSub17

/-! ## Combination -/

/-- The Graver-Yackel graph has no 6-independent set (Bool computation). -/
theorem hasIndepSet_17_adj17Bool_6_false : hasIndepSet 17 adj17Bool 6 = false := by
  show hasIndepSetAux 17 adj17Bool 6 0 [] 18 = false
  exact hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_0 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_1 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_2 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_3 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_4 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_5 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_6 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_7 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_8 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_9 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_10 <|
  hasIndepSetAux_false_of_compat (by decide) (by omega) (by omega) (by decide) sub17_11 <|
  hasIndepSetAux_false_of_pig (by decide) (by omega) (by omega)
