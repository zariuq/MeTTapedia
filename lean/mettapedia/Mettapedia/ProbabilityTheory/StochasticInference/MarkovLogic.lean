import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.Logic.MarkovLogicClauseSemantics

/-!
# Exact rational ground Markov logic features

Both clause potentials are explicit. Classical exponential log-weights
can be run here when their potentials have an exact rational representation.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.MarkovLogic

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable

variable {n : Nat}

def clauseTest (clause : List (Literal (Fin n))) (world : Fin n → Bool) : Bool :=
  clause.any fun
    | .pos atom => world atom
    | .neg atom => !world atom

theorem clauseTest_iff (clause : List (Literal (Fin n))) (world : Fin n → Bool) :
    clauseTest clause world = true ↔ GroundClause.holds clause.toFinset world := by
  simp only [clauseTest, List.any_eq_true, GroundClause.holds, List.mem_toFinset]
  apply exists_congr
  intro literal
  apply and_congr_right
  intro _
  cases literal <;> simp

def clauseEvent (clause : List (Literal (Fin n))) : Event (BinaryDomains n) :=
  Event.fromWorldTest (binaryPositive n) (clause.map Literal.atom).dedup (List.nodup_dedup _)
    (fun x => clauseTest clause (bits x)) (by
      intro x y agree
      unfold clauseTest
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      apply exists_congr
      intro literal
      apply and_congr_right
      intro member
      have same := agree literal.atom
        (List.mem_dedup.mpr (List.mem_map.mpr ⟨literal, member, rfl⟩))
      cases literal <;> simp_all [Literal.atom, bits])

theorem clauseEvent_holds (clause : List (Literal (Fin n))) (x : Config (BinaryDomains n)) :
    (clauseEvent clause).holds (binaryPositive n) x = true ↔
      GroundClause.holds clause.toFinset (bits x) := by
  rw [clauseEvent, Event.fromWorldTest_holds]
  exact clauseTest_iff clause (bits x)

structure Feature (n : Nat) where
  clause : List (Literal (Fin n))
  satisfied : ℚ
  unsatisfied : ℚ
  satisfied_nonneg : 0 ≤ satisfied
  unsatisfied_nonneg : 0 ≤ unsatisfied

def Feature.factor (feature : Feature n) : Potential (BinaryDomains n) :=
  (clauseEvent feature.clause).weighted (binaryPositive n) feature.satisfied feature.unsatisfied
    feature.satisfied_nonneg feature.unsatisfied_nonneg

def Feature.toGroundClause (feature : Feature n) : WeightedGroundClause (Fin n) where
  clause := feature.clause.toFinset
  satisfiedPotential := ENNReal.ofReal (feature.satisfied : ℝ)
  unsatisfiedPotential := ENNReal.ofReal (feature.unsatisfied : ℝ)
  satisfied_ne_top := ENNReal.ofReal_ne_top
  unsatisfied_ne_top := ENNReal.ofReal_ne_top

theorem Feature.factor_exact (feature : Feature n) (world : Config (BinaryDomains n)) :
    ENNReal.ofReal (feature.factor.table.value _ (binaryPositive n) world : ℝ) =
      feature.toGroundClause.eval (bits world) := by
  classical
  rw [Feature.factor, Event.weighted_value]
  have same := clauseEvent_holds feature.clause world
  by_cases h : GroundClause.holds feature.clause.toFinset (bits world)
  · simp [same.mpr h, Feature.toGroundClause, WeightedGroundClause.eval, h]
  · have no : (clauseEvent feature.clause).holds (binaryPositive n) world = false :=
      Bool.eq_false_iff.mpr (fun yes => h (same.mp yes))
    simp [no, Feature.toGroundClause, WeightedGroundClause.eval, h]

end Mettapedia.ProbabilityTheory.StochasticInference.MarkovLogic
