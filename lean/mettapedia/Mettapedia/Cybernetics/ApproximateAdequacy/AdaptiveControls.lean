import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveSemantics
import Mettapedia.ProbabilityTheory.BayesianInference.Variational

/-!
# The observation contract in adaptive planning

The two processes have identical actionwise latent transition marginals.
Their reported observations are reversed. The same contingent policy
therefore receives reward one in the statistical model and zero in the world.
Exact conditioning within the model cannot repair this predictive error.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveControls

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.BayesianInference

noncomputable def kernel (reversed action state : Bool) : Prob (Bool × Bool) :=
  Prob.dirac (if action then (state, if reversed then !state else state) else (!state, false))

def reward (state : Bool) : ℝ := if state then 1 else 0

def contingent : ObservationPolicy Bool Bool 2 :=
  (true, fun observed => (observed, fun _ => PUnit.unit))

def ignore : ObservationPolicy Bool Bool 2 :=
  (true, fun _ => (true, fun _ => PUnit.unit))

theorem latent_marginals_agree (action state : Bool) :
    coarsen (kernel false action state) Prod.fst =
      coarsen (kernel true action state) Prod.fst := by
  rw [kernel, kernel, coarsen_dirac, coarsen_dirac]
  cases action <;> rfl

theorem model_contingent_value : adaptiveValue (kernel false) reward contingent true = 1 := by
  norm_num [adaptiveValue, expect, kernel, reward, contingent, Prob.dirac,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem world_contingent_value : adaptiveValue (kernel true) reward contingent true = 0 := by
  norm_num [adaptiveValue, expect, kernel, reward, contingent, Prob.dirac,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem world_ignore_value : adaptiveValue (kernel true) reward ignore true = 1 := by
  norm_num [adaptiveValue, expect, kernel, reward, ignore, Prob.dirac,
    Fintype.sum_prod_type, Fintype.sum_bool]
  decide

theorem regret_despite_equal_latent_kernels :
    adaptiveValue (kernel true) reward ignore true -
      adaptiveValue (kernel true) reward contingent true = 1 := by
  rw [world_ignore_value, world_contingent_value]
  norm_num

theorem exact_conditioning :
    posterior (Prob.dirac true) (fun _ => 1) (fun _ => by norm_num)
      (by rw [evidence_one]; norm_num) = Prob.dirac true :=
  posterior_one _

end Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveControls
