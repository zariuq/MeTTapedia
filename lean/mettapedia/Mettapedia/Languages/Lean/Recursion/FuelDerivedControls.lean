import Mettapedia.Languages.Lean.Recursion.FuelCore

/-! Source-derived fuel interfaces, including the bound and refusal controls. -/

namespace Mettapedia.Languages.Lean.Recursion.FuelDerivedControls

open FuelDerive
open FuelCore
open _root_.Lean Meta Elab Command

example (m n : Nat) : Nat.gcd m n = Gcd.reading m n := Gcd.bridge m n

example {α : Type} (xs : List α) (le : α → α → Bool) :
    xs.mergeSort le = @MergeSort.reading α xs le := @MergeSort.bridge α xs le

example : Gcd.reading 12 8 = 4 := by decide
example : @MergeSort.reading Nat [3, 1, 2] (· ≤ ·) = [1, 2, 3] := by
  rw [← @MergeSort.bridge Nat [3, 1, 2] (fun a b => decide (a ≤ b))]
  simp [List.mergeSort]

example : Gcd.fuel 0 ⟨12, 8⟩ ≠ Nat.gcd 12 8 := by decide
example : @MergeSort.fuel Nat 0 ⟨[3, 1, 2], (· ≤ ·)⟩ ≠ [1, 2, 3] := by decide

example : @Merge.reading Nat [1, 3] [2, 4] (· ≤ ·) = [1, 2, 3, 4] := by decide
example : @Merge.sourceFuel 0 Nat [1] [2] (· ≤ ·) ≠ [1, 2] := by decide

run_cmd liftTermElabM do
  let failure ← withoutModifyingEnv do
    try
      FuelDerive.generate ``Nat.gcd `RejectedFuelRecipe fun reading => do
        let recipe ← forallTelescope (← inferType reading.recipe) fun parameters _ =>
          mkLambdaFVars parameters (mkNatLit 0)
        return { reading with recipe := recipe }
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  let some reason := failure | throwError "a changed fuel recipe was admitted"
  unless (reason.splitOn "generated proof does not establish").length > 1 do
    throwError "changed fuel recipe failed for an unrelated reason: {reason}"
  IO.println "refused changed fuel recipe"

run_cmd liftTermElabM do
  let failure ← withoutModifyingEnv do
    try
      FuelDerive.generate ``Nat.gcd `RejectedFuelBudget
        (budgetEvidence := some fun reading => do
          let rank := mkApp reading.measure.get! reading.application.getAppArgs[4]!
          pure (mkNatLit 0, ← mkAppM ``Nat.lt_succ_self #[rank]))
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  let some reason := failure | throwError "an unproved zero fuel budget was admitted"
  unless (reason.splitOn "fuel budget proof does not establish").length > 1 do
    throwError "zero fuel budget failed for an unrelated reason: {reason}"
  IO.println "refused incorrect fuel budget proof"

example (n k : Nat) : MinFacAux.budget n k = n + 3 := rfl

#print axioms Gcd.bridge
#print axioms MergeSort.bridge
#print axioms PrimeFactorsList.bridge
#print axioms MinFacAux.bridge
#print axioms Merge.bridge

end Mettapedia.Languages.Lean.Recursion.FuelDerivedControls
