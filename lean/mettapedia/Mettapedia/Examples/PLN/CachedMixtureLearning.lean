import Mettapedia.ProbabilityTheory.StochasticInference.CachedLearning

/-!
# A cached E-step with a live evidence edit

Several cases share an unknown prevalence. Reports have a fixed known
emission model. A retained factor gives the likelihood under each value
of the latent state. Adding or removing the report only replaces its
own factor slot.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.CachedMixtureLearning

open Mettapedia.ProbabilityTheory.StochasticInference
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Table)

abbrev Domains := BinaryDomains 3

private theorem positive : ∀ v, 0 < Domains v := binaryPositive 3

private def half : UnitProbability := ⟨1 / 2, by decide +kernel, by decide +kernel⟩
private def high : UnitProbability := ⟨9 / 10, by decide +kernel, by decide +kernel⟩
private def low : UnitProbability := ⟨1 / 10, by decide +kernel, by decide +kernel⟩

private def base := binaryTransition (0 : Fin 3) 1 (by decide +kernel) high low
private def revealed (value : Bool) : Table Domains := (binaryEvent (1 : Fin 3) value).table
private def withdrawn : Table Domains :=
  (Potential.neutral positive [1] (by simp)).table
private def outcome : Event Domains := binaryEvent 0 true
private def active : Event Domains := Event.onScope positive [] (by simp) (fun _ => true)
private def nuisance := bernoulli (2 : Fin 3) half

private def bank := Retained.prepare positive [base.table, revealed true, nuisance.table] [1, 2]

structure Replay where
  observed : ℚ × ℚ
  afterWithdrawal : ℚ × ℚ
  afterRestore : ℚ × ℚ
  initialProbability : ℚ
  fittedProbability : ℚ
  initialLikelihood : ℚ
  fittedLikelihood : ℚ
  refreshed : Nat
  deriving Repr

def replay : Option Replay := do
  let slot := ⟨1, by decide +kernel⟩
  let (withoutReport, work1) ← bank.tryReplace slot withdrawn
  let (restored, work2) ← withoutReport.tryReplace slot (revealed true)
  let observed ← Retained.expectedCounts? bank [0] active outcome
  let removed ← Retained.expectedCounts? withoutReport [0] active outcome
  let restoredCounts ← Retained.expectedCounts? restored [0] active outcome
  let on ← (Retained.read? restored [0] outcome.table).bind BinaryMixture.Likelihood.checked
  let (negative, _) ← restored.tryReplace slot (revealed false)
  let off ← (Retained.read? negative [0] outcome.table).bind BinaryMixture.Likelihood.checked
  let data := [on, on, on, off]
  let next ← BinaryMixture.fit? data half 3
  pure ⟨(observed.pos, observed.neg), (removed.pos, removed.neg),
    (restoredCounts.pos, restoredCounts.neg), half.val, next.val,
    BinaryMixture.likelihood data half, BinaryMixture.likelihood data next, work1 + work2⟩

private def explicitOn : BinaryMixture.Likelihood :=
  ⟨1 / 10, 9 / 10, by decide +kernel, by decide +kernel⟩
private def explicitOff : BinaryMixture.Likelihood :=
  ⟨9 / 10, 1 / 10, by decide +kernel, by decide +kernel⟩

theorem first_fit :
    (BinaryMixture.fit? [explicitOn, explicitOn, explicitOn, explicitOff] half 1).map
      UnitProbability.val = some (7 / 10) := by decide +kernel

theorem no_cases_has_no_fit :
    (BinaryMixture.fit? [] half 1).isNone = true := by decide +kernel

#guard replay.any (fun r =>
  r.observed == (9 / 10, 1 / 10) &&
    r.afterWithdrawal == (1 / 2, 1 / 2) &&
    r.afterRestore == r.observed && r.fittedLikelihood > r.initialLikelihood)

end Mettapedia.Examples.PLN.CachedMixtureLearning

def main : IO Unit := do
  let some replay := Mettapedia.Examples.PLN.CachedMixtureLearning.replay
    | throw (IO.userError "The cached learning replay failed")
  IO.println (reprStr replay)
