import Mettapedia.Logic.PLNTopologyCPTNoGo
import Mettapedia.Logic.PLNVarianceChainNoGo
import Mettapedia.Logic.PLNHigherOrderDecisionTheorems

/-!
# Higher-Order No-Go Bridge

This module connects the explicit no-go theorems to the certified higher-order
chaining layer.

The point is not to restate the no-go results. The point is to expose them as
constraints on higher-order chaining:

* topology-only summaries cannot certify nontrivial conditioning-residual bounds;
* unrevealed higher-order chains consume a variance budget linearly until a
  reset action occurs.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNBayesNetWorldModel
open Mettapedia.Logic.PLNTopologyCPTNoGo
open Mettapedia.Logic.PLNVarianceChainNoGo

variable {n : ℕ}
variable {R : Type*} [Fintype R] [DecidableEq R]

/-- A topology-only proxy on an actual Boolean BN topology cannot certify a
nontrivial residual upper bound once the topology contains a binary
parent-child fragment. -/
theorem topologyOnlyProxy_not_certifying
    (bn : BoolBayesNet n)
    (w : BoolBNBinaryEdgeWitness bn)
    (f : BoolBayesNet n → ℝ)
    (h : ∀ c : BinaryCPT, condResidual c ≤ f bn) :
    1 ≤ f bn :=
  topology_function_bound_is_trivial_of_binary_edge_fragment bn w f h

/-- Translate one certified higher-order step into the explicit variance-chain
no-go format, treating it as an unresolved `continue` step with variance floor
given by the certified regime-mixture variance. -/
def varianceChainStepOfCertified (step : CertifiedChainStep R) :
    VarianceChainStep where
  action := .continue
  varianceFloor := certifiedVariance step
  varianceFloor_nonneg := certifiedVariance_nonneg step

theorem varianceChainStepOfCertified_action
    (step : CertifiedChainStep R) :
    (varianceChainStepOfCertified step).action = .continue := rfl

theorem varianceChainStepOfCertified_floor
    (step : CertifiedChainStep R) :
    (varianceChainStepOfCertified step).varianceFloor = certifiedVariance step := rfl

/-- An unrevealed higher-order chain requires a linear variance budget:
if every certified step has regime-mixture variance at least `δ`, then the
unresolved variance accumulated by the translated chain is at least
`length * δ`. -/
theorem unrevealedHigherOrderChain_requires_varianceBudget
    (δ : ℝ) (steps : List (CertifiedChainStep R))
    (hfloor : ∀ step ∈ steps, δ ≤ certifiedVariance step) :
    (steps.length : ℝ) * δ ≤
      unresolvedVarianceAfter (steps.map varianceChainStepOfCertified) := by
  simpa using
    (variance_accumulation_along_unrevealed_chain
      (δ := δ)
      (steps := steps.map varianceChainStepOfCertified)
      (by
        intro step hstep
        rcases List.mem_map.1 hstep with ⟨orig, _, rfl⟩
        exact varianceChainStepOfCertified_action orig)
      (by
        intro step hstep
        rcases List.mem_map.1 hstep with ⟨orig, horig, rfl⟩
        simpa [varianceChainStepOfCertified_floor] using hfloor orig horig))

end Mettapedia.Logic
