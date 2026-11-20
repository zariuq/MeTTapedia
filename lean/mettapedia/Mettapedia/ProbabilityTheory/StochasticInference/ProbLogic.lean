import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.Logic.BDD.HornClosure
import Mettapedia.Logic.BDD.RationalWMC

/-!
# Logical lineage as a stochastic query

Ordered diagrams can be counted directly under a product of primitive
switches. For a dependent joint, the same diagram denotes an event on its
actual support. Conversion to a dense event table is exponential in that
support, so small local lineages are the intended use of that conversion.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic

open Mettapedia.Logic.BDDCore
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable
open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout (Masses)
open StatePredicates (Diagram)

variable {n : Nat}

def coordinates : BDD n → List (Fin n)
  | .zero | .one => []
  | .node v lo hi => v :: (coordinates lo ++ coordinates hi)

theorem eval_agree (tree : BDD n) (x y : Fin n → Bool)
    (agree : ∀ v ∈ coordinates tree, x v = y v) : tree.eval x = tree.eval y := by
  induction tree with
  | zero | one => rfl
  | node v lo hi low high =>
    simp only [BDD.eval]
    rw [agree v (by simp [coordinates])]
    rw [low (fun i member => agree i (by simp [coordinates, member])),
      high (fun i member => agree i (by simp [coordinates, member]))]

def event (diagram : Diagram n) : Event (BinaryDomains n) :=
  Event.fromWorldTest (binaryPositive n) (coordinates diagram.val).dedup (List.nodup_dedup _)
    (fun x => diagram.val.eval (bits x)) (by
      intro x y same
      apply eval_agree
      intro v member
      simp only [bits, same v (List.mem_dedup.mpr member)])

theorem event_holds (diagram : Diagram n) (x : Config (BinaryDomains n)) :
    (event diagram).holds (binaryPositive n) x = diagram.val.eval (bits x) :=
  Event.fromWorldTest_holds _ _ _ _ _ _

def productMass (p : Fin n → UnitProbability) (query : Diagram n) : ℚ :=
  RationalWMC.count (fun i => (p i).val) query.val

theorem productMass_exact (p : Fin n → UnitProbability) (query : Diagram n) :
    ENNReal.ofReal (productMass p query : ℝ) =
      weightedSat query.val.eval (fun i => ENNReal.ofReal ((p i).val : ℝ)) :=
  RationalWMC.exact _ (fun i => ⟨(p i).nonneg, (p i).le_one⟩) _ query.property

def productMasses (p : Fin n → UnitProbability) (evidence query : Diagram n) : Masses :=
  ⟨productMass p (StatePredicates.conj evidence query), productMass p evidence⟩

theorem productMasses_exact (p : Fin n → UnitProbability) (evidence query : Diagram n) :
    let result := productMasses p evidence query
    let weights := fun i => ENNReal.ofReal ((p i).val : ℝ)
    ENNReal.ofReal (result.joint : ℝ) =
      weightedSat (fun x => evidence.val.eval x && query.val.eval x) weights ∧
    ENNReal.ofReal (result.evidence : ℝ) = weightedSat evidence.val.eval weights := by
  constructor
  · dsimp only [productMasses]
    rw [productMass_exact]
    congr 1
    funext x
    exact apply_eval _ _ _ _
  · exact productMass_exact p evidence

end Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic
