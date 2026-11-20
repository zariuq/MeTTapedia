import Mettapedia.ProbabilityTheory.StochasticInference.Finite
import Mettapedia.PLN.WorldModel.EvidenceSpaces

/-!
# E-step statistics from exact stochastic inference

A Bernoulli row contributes a positive or negative occurrence only in
worlds where its context is active. Each count is an expectation in the
same posterior. It can be used to fit a parameter for this snapshot.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference

open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Config)
open Mettapedia.PLN.WorldModel.EvidenceSpaces (Evidence)

variable {n : Nat} {domains : Fin n → Nat} {Id : Type*}

def State.expectedRowCounts? (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (order : Schedule n) (active outcome : Event domains) : Option (Evidence ℚ) := do
  let yes ← state.probability? positive order (active.conj positive outcome)
  let no ← state.probability? positive order (active.conj positive (outcome.neg positive))
  pure ⟨yes, no⟩

theorem State.expectedRowCounts_exact (state : State Id domains) (positive : ∀ v, 0 < domains v)
    (order : Schedule n) (active outcome : Event domains)
    (support : 0 < ∑ x, state.unnormalized positive x) :
    let q := fun x : Config domains =>
      state.unnormalized positive x / ∑ y, state.unnormalized positive y
    state.expectedRowCounts? positive order active outcome = some
      ⟨∑ x, if active.holds positive x && outcome.holds positive x then q x else 0,
       ∑ x, if active.holds positive x && !outcome.holds positive x then q x else 0⟩ := by
  dsimp only
  unfold expectedRowCounts? probability?
  rw [probabilityMasses_exact, probabilityMasses_exact]
  simp only [BayesianNetworks.ScopedFactorReadout.Masses.posterior?, support, if_true,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  simp only [Event.combine_holds, Event.neg_holds]
  congr 1 <;>
    rw [Finset.sum_div] <;>
    apply Finset.sum_congr rfl <;>
    intro x _ <;>
    split <;> simp_all

end Mettapedia.ProbabilityTheory.StochasticInference
