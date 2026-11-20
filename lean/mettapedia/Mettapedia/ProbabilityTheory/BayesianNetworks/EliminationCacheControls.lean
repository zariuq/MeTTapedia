import Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationCache

/-!
# Incremental evidence and factor-table cost controls

Two conditionally independent sensors observe a latent Boolean. An empty
likelihood exhausts support, and replacing that factor restores the previous
query. A separate workload compares placements of a changing input within
the same compiled elimination order.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationCacheControls

open ExecutableFactorTable EliminationPlan

private def domains (_ : Fin 3) : Nat := 2

private theorem positive (v : Fin 3) : 0 < domains v := by simp [domains]

private def reportFactor (sensor : Fin 3) (value : Option Bool) : Table domains :=
  tabulate domains positive [sensor] (by simp) fun config =>
    match value with
    | none => 1
    | some result => if (config sensor).val = (if result then 1 else 0) then 1 else 0

private def sensorLikelihood (sensor : Fin 3) : Table domains :=
  tabulate domains positive ([0, sensor] : List (Fin 3)).dedup (List.nodup_dedup _) fun config =>
    if (config 0).val = (config sensor).val then 3 / 4 else 1 / 4

private def prior : Table domains :=
  tabulate domains positive [0] (by simp) fun _ => 1 / 2

private def factors : Vector (Table domains) 5 :=
  ⟨#[reportFactor 1 none, reportFactor 2 none, sensorLikelihood 1, sensorLikelihood 2, prior], rfl⟩

private def doorMass (table : Table domains) (value : Bool) : ℚ :=
  table.value domains positive fun v =>
    ⟨if v = 0 ∧ value then 1 else 0, by
      simp only [domains]
      split <;> decide⟩

private def doorPosterior (table : Table domains) : Option ℚ :=
  let yes := doorMass table true
  let total := yes + doorMass table false
  if total = 0 then none else some (yes / total)

def sensorUpdates : Option (List (Option ℚ)) := do
  let start := Runtime.prepare positive factors [1, 2]
  let (oneReport, _) ← start.tryReplace 0 (reportFactor 1 (some true))
  let (replay, _) ← oneReport.tryReplace 0 (reportFactor 1 (some true))
  let (twoReports, _) ← replay.tryReplace 1 (reportFactor 2 (some true))
  let (impossible, _) ← twoReports.tryReplace 0
    (tabulate domains positive [1] (by simp) (fun _ => 0))
  let (recovered, _) ← impossible.tryReplace 0 (reportFactor 1 none)
  pure ([start, oneReport, replay, twoReports, impossible, recovered].map
    (fun runtime => doorPosterior runtime.table))

#guard sensorUpdates == some [some (1/2), some (3/4), some (3/4), some (9/10), none, some (3/4)]

private def incompatibleScope : Option ℚ := do
  let (edited, _) ← (Runtime.prepare positive factors [1, 2]).tryReplace 0
    (reportFactor 2 (some true))
  doorPosterior edited.table

#guard incompatibleScope == none

def workloadDomains (_ : Fin 1) : Nat := 2

theorem workloadPositive (v : Fin 1) : 0 < workloadDomains v := by simp [workloadDomains]

def workloadFactor (weight : ℚ) : Table workloadDomains :=
  tabulate workloadDomains workloadPositive [0] (by simp) fun config =>
    if (config 0).val = 0 then 1 else weight

def workloadFactors : Vector (Table workloadDomains) 32 :=
  Vector.ofFn fun _ => workloadFactor 1

def workloadScopes (slot : Fin 32) : List (Fin 1) := workloadFactors[slot].scope

def workloadStart : Runtime workloadPositive workloadScopes [0] :=
  Runtime.prepare workloadPositive workloadFactors [0]

def replacementWork : Option (Nat × Nat × Nat) := do
  let (front, frontWork) ← workloadStart.tryReplace 0 (workloadFactor 2)
  let (back, backWork) ← workloadStart.tryReplace 31 (workloadFactor 2)
  if front.table.coefficients = #[3] ∧ back.table.coefficients = #[3] then
    pure (frontWork, backWork, (compile workloadScopes [0]).operations)
  else none

#guard replacementWork == some (3, 34, 34)

end Mettapedia.ProbabilityTheory.BayesianNetworks.EliminationCacheControls
