import Mettapedia.Languages.Lean.Recursion.FuelDerive
import Mettapedia.Languages.Lean.Recursion.MergeRank
import Mettapedia.Languages.Lean.Recursion.MinFacBudget
import Mathlib.Data.Nat.Factors
import Init.Data.List.Sort.Basic

/-! Measured source functions with generated structural-fuel interfaces. -/

namespace Mettapedia.Languages.Lean.Recursion.FuelCore

open FuelDerive

derive_fuel_interface Nat.gcd as Gcd
derive_fuel_interface List.mergeSort as MergeSort
derive_fuel_interface Nat.primeFactorsList as PrimeFactorsList
open _root_.Lean Meta Elab Command in
run_cmd liftTermElabM do
  FuelDerive.generate ``Nat.minFacAux
    `Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux
    (budgetEvidence := some fun reading => do
      unless reading.parameters.size == 2 do throwError "Nat.minFacAux source interface changed"
      let n := reading.parameters[0]!
      let k := reading.parameters[1]!
      pure (← mkAppM ``Nat.add #[n, mkNatLit 3], mkApp2 (mkConst ``MinFacBudget.bound) n k))

open _root_.Lean Meta Elab Command in
run_cmd liftTermElabM do
  FuelDerive.generate ``List.merge
    `Mettapedia.Languages.Lean.Recursion.FuelCore.Merge
    (rankEvidence := some fun reading => do
      unless reading.parameters.size == 4 do
        throwError "List.merge source interface changed"
      let levels := (← getConstInfo ``List.merge).levelParams.map Level.param
      let alpha := reading.parameters[0]!
      let comparator := reading.parameters[3]!
      pure (mkApp (mkConst ``MergeRank.rank levels) alpha,
        mkApp2 (mkConst ``MergeRank.locality levels) alpha comparator))

end Mettapedia.Languages.Lean.Recursion.FuelCore
