import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.EventSets

/-!
# VE ↔ Joint-Measure Bridge (Discrete BN)

This module connects the **semantic BN joint measure** with the **VE weight engine**
for the discrete BN sublayer.

Key results:
* `weightOfConstraints` equals the joint measure of the constraint event.
* `propProbVE` / `linkProbVE` can be interpreted as conditional probabilities
  in the joint measure (with the usual positivity side-conditions).
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators ENNReal

namespace VariableElimination

open FactorGraph

variable {V K : Type*} [DecidableEq V]
variable {fg : FactorGraph V K}

/-! ## Full-assign restriction -/

omit [DecidableEq V] in
lemma restrict_fullAssign {S T : Finset V} (h : S ⊆ T) (x : fg.FullConfig) :
    FactorGraph.restrict (fg := fg) (h := h)
        (FactorGraph.fullAssign (fg := fg) x T) =
      FactorGraph.fullAssign (fg := fg) x S := by
  funext v hv
  rfl

omit [DecidableEq V] in
lemma fullAssign_eq_restrictToScope (f : fg.factors) (x : fg.FullConfig) :
    FactorGraph.fullAssign (fg := fg) x (fg.scope f) =
      fg.restrictToScope f x := by
  rfl

/-! ## Combine-all evaluation on full configs -/

lemma combineAll_potential_fullAssign (fs : List (Factor fg))
    [One K] [Mul K] (x : fg.FullConfig) :
    (combineAll (fg := fg) fs).potential
        (FactorGraph.fullAssign (fg := fg) x
          (combineAll (fg := fg) fs).scope) =
      (fs.map (fun φ => φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
  classical
  induction fs with
  | nil =>
      simp [combineAll, oneFactor]
  | cons φ fs ih =>
      have hcons :
          combineAll (fg := fg) (φ :: fs) =
            Factor.mul (fg := fg) φ (combineAll (fg := fg) fs) := rfl
      calc
        (combineAll (fg := fg) (φ :: fs)).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) (φ :: fs)).scope)
            =
            (Factor.mul (fg := fg) φ (combineAll (fg := fg) fs)).potential
              (FactorGraph.fullAssign (fg := fg) x
                (Factor.mul (fg := fg) φ (combineAll (fg := fg) fs)).scope) := by
              rw [hcons]
        _ =
            φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope) *
              (combineAll (fg := fg) fs).potential
                (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope) := by
              simp [Factor.mul, restrict_fullAssign]
        _ =
            φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope) *
              (fs.map (fun φ => φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope))).prod := by
              simp [ih]

lemma combineAll_factorsOfGraph_potential_eq_unnormalizedJoint
    (fg : FactorGraph V K) [Fintype fg.factors] [CommMonoid K]
    (x : fg.FullConfig) :
    (combineAll (fg := fg) (factorsOfGraph (fg := fg))).potential
        (FactorGraph.fullAssign (fg := fg) x
          (combineAll (fg := fg) (factorsOfGraph (fg := fg))).scope) =
      fg.unnormalizedJoint x := by
  classical
  -- Reduce to a list product over factor potentials
  have h :=
    combineAll_potential_fullAssign (fg := fg)
      (fs := factorsOfGraph (fg := fg)) x
  have hmap :
      (factorsOfGraph (fg := fg)).map
          (fun φ => φ.potential (FactorGraph.fullAssign (fg := fg) x φ.scope)) =
        (Finset.univ : Finset fg.factors).toList.map
          (fun f : fg.factors => fg.potential f (fg.restrictToScope f x)) := by
    simp [factorsOfGraph, Factor.ofGraph, fullAssign_eq_restrictToScope]
  have hprod :
      ((Finset.univ : Finset fg.factors).toList.map
          (fun f : fg.factors => fg.potential f (fg.restrictToScope f x))).prod =
        ∏ f : fg.factors, fg.potential f (fg.restrictToScope f x) := by
    exact
      (Finset.prod_map_toList
        (s := (Finset.univ : Finset fg.factors))
        (f := fun f : fg.factors => fg.potential f (fg.restrictToScope f x)))
  -- Combine the list-product form with the Finset-product form.
  have h' :
      (combineAll (fg := fg) (factorsOfGraph (fg := fg))).potential
          (FactorGraph.fullAssign (fg := fg) x
            (combineAll (fg := fg) (factorsOfGraph (fg := fg))).scope) =
        ((Finset.univ : Finset fg.factors).toList.map
          (fun f : fg.factors => fg.potential f (fg.restrictToScope f x))).prod := by
    simpa [hmap] using h
  -- Finish with the definition of unnormalizedJoint.
  simpa [FactorGraph.unnormalizedJoint] using h'.trans hprod

end VariableElimination

/-! ## BN bridge lemmas -/

namespace BayesianNetwork

open VariableElimination
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (bn : BayesianNetwork V)

lemma weightOfConstraints_eq_jointWeight_sum
    (cpt : bn.DiscreteCPT) (cs : List (Σ v : V, bn.stateSpace v))
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] :
    VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) cs =
      ∑ x : bn.JointSpace,
        if x ∈ BayesianNetwork.eventOfConstraints (bn := bn) cs then
          cpt.jointWeight x
        else 0 := by
  classical
  have hpot : ∀ x : bn.JointSpace,
      (VariableElimination.combineAll (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt)
        (VariableElimination.factorsOfGraph (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt))).potential
        (FactorGraph.fullAssign (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) x
          (VariableElimination.combineAll (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt)
            (VariableElimination.factorsOfGraph (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt))).scope) =
        cpt.jointWeight x := by
    intro x
    have h :=
      VariableElimination.combineAll_factorsOfGraph_potential_eq_unnormalizedJoint
        (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) (x := x)
    simpa [DiscreteCPT.toFactorGraph_unnormalizedJoint_eq] using h
  -- Expand the semantic weight into a full-config sum.
  unfold VariableElimination.weightOfConstraints
  simp [VariableElimination.weightOfConstraintsList]
  refine Finset.sum_congr rfl ?_
  intro x hx
  by_cases hmem : x ∈ BayesianNetwork.eventOfConstraints (bn := bn) cs
  ·
    have hsat : ∀ c ∈ cs, x c.1 = c.2 := by
      simpa [BayesianNetwork.eventOfConstraints] using hmem
    calc
      (if ∀ c ∈ cs, x c.1 = c.2 then
          (VariableElimination.combineAll (factorsOfGraph cpt.toFactorGraph)).potential
            (FactorGraph.fullAssign cpt.toFactorGraph x
              (VariableElimination.combineAll (factorsOfGraph cpt.toFactorGraph)).scope)
        else 0)
          =
        (VariableElimination.combineAll (factorsOfGraph cpt.toFactorGraph)).potential
          (FactorGraph.fullAssign cpt.toFactorGraph x
            (VariableElimination.combineAll (factorsOfGraph cpt.toFactorGraph)).scope) := by
          exact if_pos hsat
      _ = cpt.jointWeight x := hpot x
      _ = (if x ∈ BayesianNetwork.eventOfConstraints (bn := bn) cs then
            cpt.jointWeight x else 0) := by
          exact (if_pos hmem).symm
  ·
    have hsat : ¬∀ c ∈ cs, x c.1 = c.2 := by
      intro hsat
      apply hmem
      simpa [BayesianNetwork.eventOfConstraints] using hsat
    calc
      (if ∀ c ∈ cs, x c.1 = c.2 then
          (VariableElimination.combineAll (factorsOfGraph cpt.toFactorGraph)).potential
            (FactorGraph.fullAssign cpt.toFactorGraph x
              (VariableElimination.combineAll (factorsOfGraph cpt.toFactorGraph)).scope)
        else 0) = 0 := by
          exact if_neg hsat
      _ = (if x ∈ BayesianNetwork.eventOfConstraints (bn := bn) cs then
            cpt.jointWeight x else 0) := by
          exact (if_neg hmem).symm

lemma weightOfConstraints_eq_jointMeasure_eventOfConstraints
    (cpt : bn.DiscreteCPT) (cs : List (Σ v : V, bn.stateSpace v))
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    [∀ v, Nonempty (bn.stateSpace v)] :
    VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) cs =
      cpt.jointMeasure (BayesianNetwork.eventOfConstraints (bn := bn) cs) := by
  classical
  -- Rewrite via the jointWeight sum characterization of the joint measure.
  have hsum := weightOfConstraints_eq_jointWeight_sum (bn := bn) (cpt := cpt) cs
  -- Use the joint-measure expansion lemma.
  have hμ := DiscreteCPT.jointMeasure_eventOfConstraints (bn := bn) (cpt := cpt) cs
  -- Align both sums.
  simpa [hsum] using hμ.symm

lemma weightOfConstraints_eq_jointMeasure_eventEq
    (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    [∀ v, Nonempty (bn.stateSpace v)] :
    VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) [⟨v, val⟩] =
      cpt.jointMeasure (BayesianNetwork.eventEq (bn := bn) v val) := by
  classical
  -- Reduce to the general constraint-event lemma and simplify the single-constraint event.
  have h :=
    weightOfConstraints_eq_jointMeasure_eventOfConstraints (bn := bn) (cpt := cpt)
      (cs := [⟨v, val⟩])
  -- `eventOfConstraints [⟨v,val⟩] = eventEq v val`.
  simpa [BayesianNetwork.eventOfConstraints_cons, BayesianNetwork.eventOfConstraints_nil] using h

lemma propProbVE_eq_jointMeasure_eventEq
    (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    [∀ v, Nonempty (bn.stateSpace v)] :
    BayesianNetwork.propProbVE (bn := bn) cpt v val =
      cpt.jointMeasure (BayesianNetwork.eventEq (bn := bn) v val) := by
  classical
  -- Rewrite the VE numerator/denominator using the joint-measure bridge.
  have hnum :
      VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) [⟨v, val⟩] =
        cpt.jointMeasure (BayesianNetwork.eventEq (bn := bn) v val) :=
    weightOfConstraints_eq_jointMeasure_eventEq (bn := bn) (cpt := cpt) v val
  have hden :
      VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt) [] =
        cpt.jointMeasure (Set.univ : Set bn.JointSpace) := by
    simpa [BayesianNetwork.eventOfConstraints_nil] using
      (weightOfConstraints_eq_jointMeasure_eventOfConstraints (bn := bn) (cpt := cpt) (cs := []))
  -- Denominator is 1 because `jointMeasure` is a probability measure.
  have hden' : cpt.jointMeasure (Set.univ : Set bn.JointSpace) = 1 := by
    simp
  -- Finish by unfolding the VE definition.
  simp [BayesianNetwork.propProbVE, hnum, hden, hden']  -- `simp` handles the `if`.

lemma linkProbVE_eq_jointMeasure_eventEq
    (cpt : bn.DiscreteCPT) (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    [∀ v, Nonempty (bn.stateSpace v)] :
    BayesianNetwork.linkProbVE (bn := bn) cpt a b valA valB =
      if cpt.jointMeasure (BayesianNetwork.eventEq (bn := bn) a valA) = 0 then 0 else
        cpt.jointMeasure
            (BayesianNetwork.eventEq (bn := bn) a valA ∩
              BayesianNetwork.eventEq (bn := bn) b valB) /
          cpt.jointMeasure (BayesianNetwork.eventEq (bn := bn) a valA) := by
  classical
  have hnum :
      VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt)
          [⟨a, valA⟩, ⟨b, valB⟩] =
        cpt.jointMeasure
          (BayesianNetwork.eventEq (bn := bn) a valA ∩
            BayesianNetwork.eventEq (bn := bn) b valB) := by
    -- Reduce to the general constraint-event lemma and simplify.
    have h :=
      weightOfConstraints_eq_jointMeasure_eventOfConstraints (bn := bn) (cpt := cpt)
        (cs := [⟨a, valA⟩, ⟨b, valB⟩])
    -- `eventOfConstraints` for two constraints is the intersection.
    simpa [BayesianNetwork.eventOfConstraints_cons, BayesianNetwork.eventOfConstraints_nil,
      Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
  have hden :
      VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt)
          [⟨a, valA⟩] =
        cpt.jointMeasure (BayesianNetwork.eventEq (bn := bn) a valA) :=
    weightOfConstraints_eq_jointMeasure_eventEq (bn := bn) (cpt := cpt) a valA
  -- Unfold the VE definition and rewrite numerator/denominator.
  simp [BayesianNetwork.linkProbVE, hnum, hden]

/-- Bridge for multi-antecedent conditional probability. -/
lemma linkProbVECond_eq_jointMeasure_eventOfConstraints
    (cpt : bn.DiscreteCPT)
    (constraints : List (Σ v : V, bn.stateSpace v)) (b : Σ v : V, bn.stateSpace v)
    [DecidableRel bn.graph.edges]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)]
    [∀ v, Nonempty (bn.stateSpace v)] :
    BayesianNetwork.linkProbVECond (bn := bn) cpt constraints b =
      if cpt.jointMeasure (BayesianNetwork.eventOfConstraints (bn := bn) constraints) = 0 then 0 else
        cpt.jointMeasure
            (BayesianNetwork.eventOfConstraints (bn := bn) (constraints ++ [b])) /
          cpt.jointMeasure (BayesianNetwork.eventOfConstraints (bn := bn) constraints) := by
  classical
  have hnum :
      VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt)
          (constraints ++ [b]) =
        cpt.jointMeasure (BayesianNetwork.eventOfConstraints (bn := bn) (constraints ++ [b])) := by
    exact weightOfConstraints_eq_jointMeasure_eventOfConstraints
      (bn := bn) (cpt := cpt) (cs := constraints ++ [b])
  have hden :
      VariableElimination.weightOfConstraints (fg := DiscreteCPT.toFactorGraph (bn := bn) cpt)
          constraints =
        cpt.jointMeasure (BayesianNetwork.eventOfConstraints (bn := bn) constraints) := by
    exact weightOfConstraints_eq_jointMeasure_eventOfConstraints
      (bn := bn) (cpt := cpt) (cs := constraints)
  simp [BayesianNetwork.linkProbVECond, hnum, hden]

end BayesianNetwork

end Mettapedia.ProbabilityTheory.BayesianNetworks
