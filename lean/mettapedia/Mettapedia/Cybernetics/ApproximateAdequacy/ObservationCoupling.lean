import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
import Mettapedia.InformationTheory.FiniteProbability

/-! # The canonical coupling of a state law and its observed law -/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.InformationTheory.FiniteRV

variable {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]

/-- Every source state is paired with its actual observation. -/
noncomputable def observationCoupling (prior : Prob S) (view : S → C) :
    Coupling prior.1 (coarsen prior view).1 where
  weight s c := if view s = c then prior.1 s else 0
  nonneg s c := by split_ifs <;> simp [prior.2.1]
  sum_right s := by simp [eq_comm]
  sum_left c := (pushforward_eq_sum_ite prior.1 view c).symm

/-- Distortion of a consumer is priced under the declared source law. No
small average distortion is treated as an equality or substitution rule. -/
theorem observed_consumer_error (prior : Prob S) (view : S → C)
    (sourceConsumer : S → ℝ) (observedConsumer : C → ℝ) (error : S → ℝ)
    (bounded : ∀ s, |sourceConsumer s - observedConsumer (view s)| ≤ error s) :
    |expect prior.1 sourceConsumer - expect (coarsen prior view).1 observedConsumer| ≤
      expect prior.1 error := by
  have result := (observationCoupling prior view).abs_expect_sub_le_on_support
    (m := fun s _ => error s) (fun s c positive => by
      have same : view s = c := by
        by_contra different
        simp [observationCoupling, different] at positive
      rw [← same]
      exact bounded s)
  simpa [Coupling.cost, observationCoupling, expect, Finset.mul_sum, eq_comm] using result

end Mettapedia.Cybernetics.ApproximateAdequacy
