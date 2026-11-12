import Mettapedia.Machines.TIsa.CellEffects

/-!
# Retained p0 instruction fuel as ordinary resource accounting

The p0 native interface uses zero for an unlimited allowance and a 64-bit used
counter. A positive allowance prevents counter wraparound. Exhaustion leaves
the completed prefix available and does not authorize another instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

def fuelAvailable (budget used : Word) : Bool := budget == 0 || decide (used.toNat < budget.toNat)

theorem fuelAvailable_positive (budget used : Word) (positive : budget ≠ 0#64) :
    fuelAvailable budget used = true ↔ used.toNat < budget.toNat := by
  simp [fuelAvailable, positive]

theorem fuel_increment_no_wrap (budget used : Word) (positive : budget ≠ 0#64)
    (available : fuelAvailable budget used = true) :
    (used + 1).toNat = used.toNat + 1 ∧ (used + 1).toNat ≤ budget.toNat := by
  have less := (fuelAvailable_positive budget used positive).mp available
  have within : used.toNat + 1 < 2 ^ 64 := by have := budget.isLt; omega
  have same : (used + 1).toNat = used.toNat + 1 := by simpa [BitVec.toNat_add] using within
  exact ⟨same, by omega⟩

namespace Control

open Cells CellEffects

universe u
variable {Key : Type u} [DecidableEq Key]

structure FuelGate (Key : Type u) where
  point : Key
  atPoint : Word
  nextPoint : Word
  budget : Key
  used : Key
  deriving DecidableEq, Repr

def FuelGate.check (gate : FuelGate Key) : Bool :=
  decide ([gate.point, gate.budget, gate.used].Nodup)

def FuelGate.recipe (gate : FuelGate Key) : Recipe Key where
  inputs := [gate.point, gate.budget, gate.used]
  outputs := [gate.point, gate.used]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, budget, used], [next, following] =>
        gate.check && point == gate.atPoint && next == gate.nextPoint &&
          fuelAvailable budget used && following == used + 1
    | _, _ => false

theorem FuelGate.guard_iff (gate : FuelGate Key) (before after : Key → Word) :
    gate.recipe.guard (gate.recipe.inputs.map before) (gate.recipe.outputs.map after) = true ↔
      gate.check = true ∧ before gate.point = gate.atPoint ∧ after gate.point = gate.nextPoint ∧
      fuelAvailable (before gate.budget) (before gate.used) = true ∧ after gate.used = before gate.used + 1 := by
  simp [recipe, Bool.and_eq_true, and_assoc]

namespace FuelControls

private def gate : FuelGate Nat := ⟨0, 1, 2, 1, 2⟩

example : gate.recipe.guard [1, 3, 2] [2, 3] = true := by decide
example : gate.recipe.guard [1, 3, 3] [2, 4] = false := by decide
example : gate.recipe.guard [1, 0, 100] [2, 101] = true := by decide
example : ({ gate with budget := 2 }).check = false := by decide

end FuelControls

end Control
end Mettapedia.Machines.TIsa
