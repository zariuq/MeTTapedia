import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.ProbabilityTheory.StochasticInference.Propagation
import Mettapedia.ProbabilityTheory.StochasticInference.RowStatistics

/-!
# Exact statistics and mixture learning from retained factors

An elimination cache can supply several statistics on its retained scope.
Keeping a binary latent coordinate yields the two observation likelihoods
needed to fit its mixing probability across independent cases with fixed
emission models. A scope-preserving edit reuses the existing factor plan.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks
open ExecutableFactorTable ScopedFactorReadout
open Mettapedia.PLN.WorldModel.EvidenceSpaces (Evidence)

namespace Retained

variable {n m : Nat} {domains : Fin n → Nat} {positive : ∀ v, 0 < domains v}
variable {scopes : Fin m → List (Fin n)} {early : List (Fin n)}

def expectedCounts? (bank : Bank positive scopes early) (suffix : List (Fin n))
    (active outcome : Event domains) : Option (Evidence ℚ) := do
  let yes ← read? bank suffix (active.conj positive outcome).table
  let no ← read? bank suffix (active.conj positive (outcome.neg positive)).table
  pure ⟨← yes.posterior?, ← no.posterior?⟩

theorem expectedCounts_exact (bank : Bank positive scopes early) (suffix : List (Fin n))
    (active outcome : Event domains) (covers : ∀ v : Fin n, v ∈ early ++ suffix)
    (yesRetained : ∀ v ∈ early, v ∉ (active.conj positive outcome).table.scope)
    (noRetained : ∀ v ∈ early, v ∉ (active.conj positive (outcome.neg positive)).table.scope)
    (full : ∀ v : Fin n, ∃ slot : Fin m, v ∈ scopes slot) :
    let inputs := tables bank
    let order := early ++ suffix
    let evidence := weight domains positive inputs order
    expectedCounts? bank suffix active outcome = (do
      let yes : Masses := ⟨weight domains positive
        (inputs ++ [(active.conj positive outcome).table]) order, evidence⟩
      let no : Masses := ⟨weight domains positive
        (inputs ++ [(active.conj positive (outcome.neg positive)).table]) order, evidence⟩
      pure ⟨← yes.posterior?, ← no.posterior?⟩) := by
  dsimp only
  unfold expectedCounts?
  rw [read_exact bank suffix _ covers yesRetained full, read_exact bank suffix _ covers noRetained full]
  rfl

end Retained

namespace BinaryMixture

structure Likelihood where
  absent : ℚ
  present : ℚ
  absent_nonneg : 0 ≤ absent
  present_nonneg : 0 ≤ present
  deriving DecidableEq

def Likelihood.checked (masses : Masses) : Option Likelihood :=
  if valid : 0 ≤ masses.joint ∧ masses.joint ≤ masses.evidence then
    some ⟨masses.evidence - masses.joint, masses.joint, sub_nonneg.mpr valid.2, valid.1⟩
  else none

def Likelihood.masses (data : Likelihood) (prior : UnitProbability) : Masses :=
  ⟨prior.val * data.present, (1 - prior.val) * data.absent + prior.val * data.present⟩

def likelihood (data : List Likelihood) (prior : UnitProbability) : ℚ :=
  (data.map fun item => (item.masses prior).evidence).prod

structure Step (data : List Likelihood) (before : UnitProbability) where
  after : UnitProbability
  expectedPresent : ℚ
  accepted : likelihood data before ≤ likelihood data after

/-- Fit the mixing probability with all emission likelihoods held fixed.
The rational likelihood check compares the proposed step against the
previous fit using the original cases. -/
def step? (data : List Likelihood) (before : UnitProbability) : Option (Step data before) := do
  if data.isEmpty then none else do
    let weights ← data.mapM (fun item => (item.masses before).posterior?)
    let expected := weights.sum
    let after ← UnitProbability.checked (expected / data.length)
    if accepted : likelihood data before ≤ likelihood data after then
      some ⟨after, expected, accepted⟩
    else none

def fit? (data : List Likelihood) (initial : UnitProbability) : Nat → Option UnitProbability
  | 0 => some initial
  | rounds + 1 => do
    let next ← step? data initial
    fit? data next.after rounds

theorem fit_nondecreasing (data : List Likelihood) (initial final : UnitProbability) (rounds : Nat)
    (accepted : fit? data initial rounds = some final) :
    likelihood data initial ≤ likelihood data final := by
  induction rounds generalizing initial with
  | zero =>
    simp only [fit?, Option.some.injEq] at accepted
    subst initial
    exact le_rfl
  | succ rounds ih =>
    cases next : step? data initial with
    | none => simp [fit?, next] at accepted
    | some fitted =>
      have rest : fit? data fitted.after rounds = some final := by simpa [fit?, next] using accepted
      exact fitted.accepted.trans (ih fitted.after rest)

end BinaryMixture
end Mettapedia.ProbabilityTheory.StochasticInference
