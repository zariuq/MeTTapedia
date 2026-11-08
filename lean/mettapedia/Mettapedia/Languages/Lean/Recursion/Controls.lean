import Mettapedia.Languages.Lean.Recursion.MeasuredCore

/-!
# Refusal controls for derived recursion interfaces

The mutated recipe is well-typed but changes the source at (0,0); its bridge
must fail. A second mutation makes the recursive argument nondecreasing while
retaining the old proof. A third supplies well-foundedness evidence for a
different, non-well-founded relation. None may enter the exported registry.
-/

namespace Mettapedia.Languages.Lean.Recursion.Controls

open _root_.Lean Meta Elab Command
open MeasuredCore

abbrev Point := (_ : Nat) ×' Nat

noncomputable def changedRecipe (point : Point)
    (previous : ∀ other, Gcd.measure other < Gcd.measure point → Nat) : Nat :=
  if point.1 = 0 ∧ point.2 = 0 then Gcd.recipe point previous + 1
  else Gcd.recipe point previous

theorem changed_at_zero :
    AccessibleRecipe.evaluate Gcd.measure changedRecipe ⟨0, 0⟩ = 1 := by
  rw [AccessibleRecipe.unfold]
  simp [changedRecipe, Gcd.recipe]

def badRelation (_first _second : Point) : Prop := True

theorem badRelation_not_wellFounded : ¬WellFounded badRelation := by
  intro founded
  exact founded.irrefl.irrefl ⟨0, 0⟩ trivial

def refuses (label fragment : String) (action : MetaM Unit) : MetaM Unit := do
  let failure ← withoutModifyingEnv do
    try
      action
      pure none
    catch error => pure (some (← error.toMessageData.toString))
  let some reason := failure | throwError "negative control was admitted: {label}"
  unless (reason.splitOn fragment).length > 1 do
    throwError "negative control {label} failed for an unrelated reason: {reason}"
  IO.println ("refused " ++ label)

run_cmd liftTermElabM do
  refuses "recipe changed at one input" "generated proof does not establish" do
    Derive.generate ``Nat.gcd `RejectedChangedRecipe fun reading =>
      pure { reading with recipe := mkConst ``changedRecipe }
  refuses "nondecreasing recursive argument" "kernel type checker failed" do
    Derive.generate ``Nat.gcd `RejectedNondecreasing fun reading => do
      let changed := reading.recipe.replace fun expression =>
        if expression.isAppOfArity ``Nat.mod 2 then some (expression.getArg! 1)
        else if expression.isAppOfArity ``HMod.hMod 6 then some (expression.getArg! 5)
        else none
      if changed == reading.recipe then throwError "mutation did not reach the source recursive argument"
      return { reading with recipe := changed }
  refuses "non-well-founded relation" "generated proof does not establish" do
    let claim ← mkAppM ``WellFounded #[mkConst ``badRelation]
    Derive.prove `RejectedRelation [] claim (mkConst ``Gcd.wellFounded)

end Mettapedia.Languages.Lean.Recursion.Controls
