import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNBayesNetWorldModel
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

/-!
# Exact BN Query Answering from PLN CPT Evidence (Boolean Case)

This module connects the PLN BN world-model sublayer (CPT evidence counts)
to **exact BN query answering** via variable elimination.

Key idea:
* CPT evidence is stored as `Evidence` per CPT entry.
* Convert each CPT entry into a Bernoulli PMF using `Evidence.toStrength`.
* Use the existing VE engine to answer prop/link queries exactly for the BN class.

This is the first concrete instance of the “BN sublayer = tractable WM class” story.
-/

namespace Mettapedia.Logic.PLNBayesNetInference

open scoped Classical BigOperators ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNBayesNetWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

/-! ## Bernoulli PMF from ENNReal probability -/

noncomputable def bernoulliPMF (p : ℝ≥0∞) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then p else 1 - p) (by
    classical
    have hsum : (∑ b : Bool, (if b then p else 1 - p)) = p + (1 - p) := by
      simp
    have hsum' : p + (1 - p) = 1 := by
      simpa [add_comm] using (tsub_add_cancel_of_le hp)
    simp [hsum'])
end Mettapedia.Logic.PLNBayesNetInference

/-! ## BoolBayesNet → BayesianNetwork -/

namespace Mettapedia.Logic.PLNBayesNetWorldModel.BoolBayesNet

variable {n : ℕ} (bn : BoolBayesNet n)

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale

noncomputable def toBayesianNetwork :
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork (Fin n) :=
  { graph := bn.graph
    acyclic := bn.acyclic
    stateSpace := fun _ => Bool
    measurableSpace := fun _ => by infer_instance }

variable [DecidableRel bn.graph.edges]

/-! ## Parent-configuration bridge -/

abbrev ParentAssignment (v : Fin n) :=
  (toBayesianNetwork bn).ParentAssignment v

def parentConfigOfAssignment (v : Fin n) (pa : ParentAssignment (bn := bn) v) :
    ParentConfig (bn := bn) v :=
  fun u => pa u.val u.property

/-! ## CPT evidence → CPT probabilities -/

noncomputable def cptEvidenceOfState (W : CPTState (bn := bn)) (v : Fin n)
    (pa : ParentAssignment (bn := bn) v) : Evidence :=
  W ⟨v, parentConfigOfAssignment (bn := bn) v pa⟩

noncomputable def cptOfState (W : CPTState (bn := bn)) :
    (toBayesianNetwork bn).DiscreteCPT :=
  { cpt := fun v pa =>
      let e := cptEvidenceOfState (bn := bn) W v pa
      Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF
        (Evidence.toStrength e) (Evidence.toStrength_le_one e) }

/-! ## Exact BN query answering via VE (prop/link) -/

noncomputable def propProbVE (W : CPTState (bn := bn)) (v : Fin n) (val : Bool) : ℝ≥0∞ := by
  classical
  let _ : ∀ v, Fintype ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  let _ : ∀ v, DecidableEq ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  exact
    Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination.BayesianNetwork.propProbVE
      (bn := toBayesianNetwork bn) (cpt := cptOfState (bn := bn) W) v val

noncomputable def linkProbVE (W : CPTState (bn := bn)) (a b : Fin n) (valA valB : Bool) : ℝ≥0∞ := by
  classical
  let _ : ∀ v, Fintype ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  let _ : ∀ v, DecidableEq ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  exact
    Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination.BayesianNetwork.linkProbVE
      (bn := toBayesianNetwork bn) (cpt := cptOfState (bn := bn) W) a b valA valB

end Mettapedia.Logic.PLNBayesNetWorldModel.BoolBayesNet
