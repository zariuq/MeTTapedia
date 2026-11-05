import Lean

/-!
# Kernel-checked reflexivity for closed computations

The kernel checks the entire requested equality by reduction, including
function-valued fields. No decidable equality or native evaluator is used.
Unlike equation-driven simplification, this does not materialize imported
definitions' lazy equation helpers in independent consumer modules.
-/

namespace Mettapedia.Tools.KernelReflexivity

open Lean Meta Elab Tactic

elab "kernel_reflexivity" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let environment ← getEnv
  if target.hasFVar || target.hasMVar || target.hasLevelParam || target.hasSorry || environment.hasUnsafe target then
    throwError "Expected a closed safe equality"
  let some (_, _, right) := target.eq? | throwError "Expected an equality"
  let proof ← mkEqRefl right
  let checked ← withOptions
    (fun options => debug.skipKernelTC.set (Elab.async.set options false) false)
    (mkAuxLemma [] target proof (cache := false))
  goal.assign (mkConst checked)
  replaceMainGoal []

theorem closed_reduction : (fun value : Nat => value + 1) 2 = 3 := by kernel_reflexivity

theorem false_equation_refused : (2 : Nat) ≠ 3 := by
  fail_if_success have : (2 : Nat) = 3 := by kernel_reflexivity
  decide

end Mettapedia.Tools.KernelReflexivity
