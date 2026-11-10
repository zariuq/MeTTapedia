import Mettapedia.Languages.MeTTa.StoreAndDemand.Contracts
import Lean.Util.CollectAxioms

/-! Audit the complete contract namespace, including supporting definitions. -/

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let prefixes := [
    `Mettapedia.Languages.MeTTa.StoreAndDemand,
    `Mettapedia.Machines.StoreAndDemand]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, information) in environment.constants.toList do
    if prefixes.any (fun prefixName => prefixName.isPrefixOf name) then
      let dependencies ← collectAxioms name
      let unexpected := dependencies.filter (fun dependency => !permitted.contains dependency)
      unless unexpected.isEmpty do
        throwError "Unexpected axiom dependencies in {name}: {unexpected}"
      declarations := declarations + 1
      if information.isTheorem then
        theorems := theorems + 1
        logInfo m!"CONTRACT {name}: {dependencies}"
  unless theorems > 0 do
    throwError "No store/demand contract theorems were loaded"
  logInfo m!"STORE_DEMAND_AUDIT declarations={declarations} theorems={theorems}"
