import Mettapedia.PLN.WorldModel.BayesianWMProgramIntegration
import Mettapedia.Logic.KernelFoundationManifest
import Lean.Util.CollectAxioms

/-! # Transitive foundation audit for Bayesian world-program integration -/

open Lean Elab Command
open Mettapedia.Logic.KernelFoundationManifest

private def unexpectedAxioms (name : Name) : CoreM (Array Name) := do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  return (← collectAxioms name).filter fun dependency => !allowed.contains dependency

run_cmd do
  let rejected ← liftCoreM <| unexpectedAxioms ``sorryAx
  unless rejected.contains ``sorryAx do
    throwError "negative control failed: admitted proofs would pass the audit"
  let modules := #[
    `Mettapedia.PLN.WorldModel.FiniteProbabilisticPrograms,
    `Mettapedia.PLN.WorldModel.BayesianObservationLedger,
    `Mettapedia.PLN.WorldModel.BayesianObservationLedgerControls,
    `Mettapedia.PLN.WorldModel.ProgramObservationDenotation,
    `Mettapedia.PLN.WorldModel.WeightedSourcePrograms,
    `Mettapedia.PLN.WorldModel.WeightedSourceExecution,
    `Mettapedia.PLN.WorldModel.WeightedSourceControls,
    `Mettapedia.PLN.WorldModel.WeightedSourceAdequacy,
    `Mettapedia.PLN.Bridges.GSLT.BayesianInferenceController,
    `Mettapedia.PLN.Bridges.GSLT.BayesianInferenceControllerControls,
    `Mettapedia.PLN.Bridges.GSLT.BayesianProofSearchControls,
    `Mettapedia.PLN.WorldModel.BayesianLearningDynamics,
    `Mettapedia.PLN.WorldModel.BayesianLearningDynamicsControls,
    `Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition,
    `Mettapedia.PLN.WorldModel.ProbabilisticWitnessCompositionControls,
    `Mettapedia.PLN.WorldModel.ProbabilisticWitnessJointEvidence,
    `Mettapedia.PLN.WorldModel.BayesianWMProgramIntegration]
  let env ← getEnv
  let mut total := 0
  let mut theorems := 0
  let mut compilerOnly := 0
  let mut runtime := 0
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName
      | throwError "missing audited module {moduleName}"
    let data := env.header.moduleData[index]!
    let names := (data.constNames ++ data.extraConstNames).toList.eraseDups
    let mut checked := 0
    for name in names do
      let some info := env.checked.get.find? name | do
        unless data.extraConstNames.contains name do
          throwError "unavailable kernel declaration {name}"
        compilerOnly := compilerOnly + 1
        continue
      if info matches .axiomInfo _ then
        throwError "owned axiom declaration {name}"
      if info.isUnsafe || info.isPartial then
        let some parent := runtimeCounterpart? env name
          | throwError "unpaired unsafe or partial declaration {name}"
        let dependencies ← liftCoreM <| unexpectedAxioms parent
        unless dependencies.isEmpty do
          throwError "unexpected axioms in safe counterpart {parent}: {dependencies.toList}"
        runtime := runtime + 1
        continue
      let dependencies ← liftCoreM <| unexpectedAxioms name
      unless dependencies.isEmpty do
        throwError "unexpected transitive axioms for {name}: {dependencies.toList}"
      if info matches .thmInfo _ then theorems := theorems + 1
      checked := checked + 1
    total := total + checked
    logInfo m!"AUDIT: {moduleName}; {checked} kernel declarations"
  logInfo m!"QUALIFIED: {modules.size} modules; {total} safe kernel declarations; {theorems} theorem constants; {runtime} paired compiler runtime counterparts; {compilerOnly} compiler-only entries; only propext, Classical.choice, Quot.sound"
