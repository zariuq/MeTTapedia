import Mettapedia.Logic.PLNMarkovLogicFiniteRestriction
import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraph

/-!
# Finite Restriction as a Factor Graph

This module realizes a finite-support MLN restriction as a one-variable factor graph.

The construction is intentionally extensional:
- the single variable ranges over the finite supported worlds,
- the single factor stores the restricted world weight.

This is enough to obtain an exact factor-graph specialization without compromising
the infinite-first architecture from the preceding modules.
-/

namespace Mettapedia.Logic.PLNMarkovLogicFactorGraph

open scoped ENNReal BigOperators
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable
open Mettapedia.Logic.PLNMarkovLogicFiniteRestriction
open Mettapedia.ProbabilityTheory.BayesianNetworks

variable {World Query Feature : Type*} [Encodable World] [DecidableEq World]

/-- Extensional one-variable factor graph for a finite restriction. -/
noncomputable def compiledFactorGraph
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) : FactorGraph Unit ENNReal where
  stateSpace _ := RestrictedWorld (World := World) support
  factors := Unit
  scope _ := {()}
  potential _ x := restrictedWorldWeight M support (x () (by simp))

instance compiledFactorGraphFactorsFintype
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) :
    Fintype (compiledFactorGraph M support).factors := by
  dsimp [compiledFactorGraph]
  infer_instance

/-- The full configuration corresponding to one supported world. -/
noncomputable def configOfWorld
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (w : RestrictedWorld (World := World) support) :
    (compiledFactorGraph M support).FullConfig :=
  fun _ => w

omit [DecidableEq World] in
theorem compiledJoint_eq_restrictedWorldWeight
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (w : RestrictedWorld (World := World) support) :
    (compiledFactorGraph M support).unnormalizedJoint (configOfWorld M support w) =
      restrictedWorldWeight M support w := by
  classical
  unfold compiledFactorGraph FactorGraph.unnormalizedJoint restrictedWorldWeight configOfWorld
  simp [FactorGraph.restrictToScope]

/-- Query mass of the compiled factor graph, evaluated against the restricted query truth. -/
noncomputable def compiledQueryMass
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (q : Query) : ENNReal :=
  by
    classical
    exact Finset.sum support.attach (fun w =>
      if M.queryHolds q w.1 then
        (compiledFactorGraph M support).unnormalizedJoint (configOfWorld M support w)
      else
        0)

/-- Partition mass of the compiled factor graph. -/
noncomputable def compiledPartition
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) : ENNReal :=
  Finset.sum support.attach (fun w =>
    (compiledFactorGraph M support).unnormalizedJoint (configOfWorld M support w))

omit [DecidableEq World] in
theorem compiledQueryMass_eq_restrictedQueryMass
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (q : Query) :
    compiledQueryMass M support q = restrictedQueryMass M support q := by
  classical
  unfold compiledQueryMass restrictedQueryMass
  calc
    Finset.sum support.attach (fun w =>
        if M.queryHolds q w.1 then
          (compiledFactorGraph M support).unnormalizedJoint (configOfWorld M support w)
        else 0)
      = Finset.sum support.attach (fun w => if M.queryHolds q w.1 then M.worldWeight w.1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          by_cases hq : M.queryHolds q w.1
          · simp [hq, compiledJoint_eq_restrictedWorldWeight, restrictedWorldWeight]
          · simp [hq]
    _ = Finset.sum support (fun w => if M.queryHolds q w then M.worldWeight w else 0) := by
          simpa using (Finset.sum_attach support (fun w =>
            if M.queryHolds q w then M.worldWeight w else 0))

omit [DecidableEq World] in
theorem compiledPartition_eq_restrictedTotalMass
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) :
    compiledPartition M support = restrictedTotalMass M support := by
  classical
  unfold compiledPartition restrictedTotalMass
  calc
    Finset.sum support.attach (fun w =>
        (compiledFactorGraph M support).unnormalizedJoint (configOfWorld M support w))
      = Finset.sum support.attach (fun w => M.worldWeight w.1) := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          simp [compiledJoint_eq_restrictedWorldWeight, restrictedWorldWeight]
    _ = Finset.sum support (fun w => M.worldWeight w) := by
          simpa using (Finset.sum_attach support (fun w => M.worldWeight w))

/-- The factor-graph specialization also induces a mass semantics object. -/
noncomputable def compiledMassSemantics
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) : MassSemantics Query where
  queryMass := compiledQueryMass M support
  totalMass := compiledPartition M support
  queryMass_le_total := by
    intro q
    rw [compiledQueryMass_eq_restrictedQueryMass M support q]
    rw [compiledPartition_eq_restrictedTotalMass M support]
    exact (restrictedMassSemantics M hs).queryMass_le_total q
  totalMass_ne_top := by
    rw [compiledPartition_eq_restrictedTotalMass M support]
    exact (restrictedMassSemantics M hs).totalMass_ne_top

omit [DecidableEq World] in
theorem compiled_queryProb_eq_restricted_queryProb
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) (q : Query) :
    (compiledMassSemantics M hs).queryProb q = (restrictedMassSemantics M hs).queryProb q := by
  simp [compiledMassSemantics, restrictedMassSemantics, MassSemantics.queryProb,
    compiledQueryMass_eq_restrictedQueryMass, compiledPartition_eq_restrictedTotalMass]

omit [DecidableEq World] in
theorem compiled_queryProb_eq_full_queryProb_of_finite_support
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) (q : Query) :
    (compiledMassSemantics M hs).queryProb q = (M.toMassSemantics.queryProb q) := by
  rw [compiled_queryProb_eq_restricted_queryProb M hs q]
  exact restricted_queryProb_eq_full_queryProb_of_finite_support M hs q

end Mettapedia.Logic.PLNMarkovLogicFactorGraph
