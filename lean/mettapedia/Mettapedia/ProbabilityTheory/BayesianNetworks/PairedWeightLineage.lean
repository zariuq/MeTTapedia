import Mathlib.Algebra.Ring.Prod
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.ValuationWorldModel
import Provenance.Semirings.Which

/-!
# Paired Weight + Lineage for Exact Factor-Graph Queries

This module records the smallest honest bridge between:

1. exact factor-graph query weights, and
2. semiring-valued provenance / lineage.

The key point is simple: exact VE is already generic in the carrier `K`, so we can
run it over a product semiring `K × L`. The first projection recovers ordinary
weights; the second recovers ordinary lineage.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

namespace FactorGraph

variable {V K L : Type*}

/-- Project a product-valued factor graph to its weight component. -/
def toWeight (fg : FactorGraph V (K × L)) : FactorGraph V K where
  stateSpace := fg.stateSpace
  factors := fg.factors
  scope := fg.scope
  potential := fun f x => (fg.potential f x).1

/-- Project a product-valued factor graph to its lineage component. -/
def toLineage (fg : FactorGraph V (K × L)) : FactorGraph V L where
  stateSpace := fg.stateSpace
  factors := fg.factors
  scope := fg.scope
  potential := fun f x => (fg.potential f x).2

instance {fg : FactorGraph V (K × L)} [Fintype fg.factors] :
    Fintype (toWeight fg).factors := by
  dsimp [toWeight]
  infer_instance

instance {fg : FactorGraph V (K × L)} [Fintype fg.factors] :
    Fintype (toLineage fg).factors := by
  dsimp [toLineage]
  infer_instance

instance {fg : FactorGraph V (K × L)} [∀ v, Fintype (fg.stateSpace v)] :
    ∀ v, Fintype ((toWeight fg).stateSpace v) := by
  intro v
  dsimp [toWeight]
  infer_instance

instance {fg : FactorGraph V (K × L)} [∀ v, Fintype (fg.stateSpace v)] :
    ∀ v, Fintype ((toLineage fg).stateSpace v) := by
  intro v
  dsimp [toLineage]
  infer_instance

instance {fg : FactorGraph V (K × L)} [∀ v, DecidableEq (fg.stateSpace v)] :
    ∀ v, DecidableEq ((toWeight fg).stateSpace v) := by
  intro v
  dsimp [toWeight]
  infer_instance

instance {fg : FactorGraph V (K × L)} [∀ v, DecidableEq (fg.stateSpace v)] :
    ∀ v, DecidableEq ((toLineage fg).stateSpace v) := by
  intro v
  dsimp [toLineage]
  infer_instance

end FactorGraph

namespace VariableElimination

namespace Factor

variable {V K L : Type*} [DecidableEq V]
variable {fg : FactorGraph V (K × L)}

/-- Project an explicit factor to its weight component. -/
def toWeight (φ : Factor fg) : Factor (fg := FactorGraph.toWeight fg) where
  scope := φ.scope
  potential := fun x => (φ.potential x).1

/-- Project an explicit factor to its lineage component. -/
def toLineage (φ : Factor fg) : Factor (fg := FactorGraph.toLineage fg) where
  scope := φ.scope
  potential := fun x => (φ.potential x).2

omit [DecidableEq V] in
@[simp] theorem toWeight_scope (φ : Factor fg) :
    (toWeight (fg := fg) φ).scope = φ.scope := rfl

omit [DecidableEq V] in
@[simp] theorem toLineage_scope (φ : Factor fg) :
    (toLineage (fg := fg) φ).scope = φ.scope := rfl

omit [DecidableEq V] in
@[simp] theorem toWeight_potential (φ : Factor fg)
    (x : FactorGraph.Assign (fg := FactorGraph.toWeight fg) φ.scope) :
    (toWeight (fg := fg) φ).potential x = (φ.potential x).1 := rfl

omit [DecidableEq V] in
@[simp] theorem toLineage_potential (φ : Factor fg)
    (x : FactorGraph.Assign (fg := FactorGraph.toLineage fg) φ.scope) :
    (toLineage (fg := fg) φ).potential x = (φ.potential x).2 := rfl

omit [DecidableEq V] in
@[simp] theorem toWeight_ofGraph (f : fg.factors) :
    toWeight (fg := fg) (ofGraph (fg := fg) f) =
      ofGraph (fg := FactorGraph.toWeight fg) f := rfl

omit [DecidableEq V] in
@[simp] theorem toLineage_ofGraph (f : fg.factors) :
    toLineage (fg := fg) (ofGraph (fg := fg) f) =
      ofGraph (fg := FactorGraph.toLineage fg) f := rfl

@[simp] theorem toWeight_mul [Mul K] [Mul L] (φ ψ : Factor fg) :
    toWeight (fg := fg) (mul (fg := fg) φ ψ) =
      mul (fg := FactorGraph.toWeight fg) (toWeight (fg := fg) φ) (toWeight (fg := fg) ψ) := by
  rfl

@[simp] theorem toLineage_mul [Mul K] [Mul L] (φ ψ : Factor fg) :
    toLineage (fg := fg) (mul (fg := fg) φ ψ) =
      mul (fg := FactorGraph.toLineage fg) (toLineage (fg := fg) φ) (toLineage (fg := fg) ψ) := by
  rfl

omit [DecidableEq V] in
@[simp] theorem toWeight_oneFactor [One K] [One L] :
    toWeight (fg := fg) (oneFactor fg) = oneFactor (FactorGraph.toWeight fg) := by
  rfl

omit [DecidableEq V] in
@[simp] theorem toLineage_oneFactor [One K] [One L] :
    toLineage (fg := fg) (oneFactor fg) = oneFactor (FactorGraph.toLineage fg) := by
  rfl

theorem combineAll_toWeight [One K] [One L] [Mul K] [Mul L]
    (fs : List (Factor fg)) :
    toWeight (fg := fg) (combineAll (fg := fg) fs) =
      combineAll (fg := FactorGraph.toWeight fg) (fs.map (toWeight (fg := fg))) := by
  induction fs with
  | nil =>
      simp [combineAll]
  | cons φ fs ih =>
      simpa [combineAll] using
        congrArg
          (fun ψ => Factor.mul (fg := FactorGraph.toWeight fg) (Factor.toWeight (fg := fg) φ) ψ)
          ih

theorem combineAll_toLineage [One K] [One L] [Mul K] [Mul L]
    (fs : List (Factor fg)) :
    toLineage (fg := fg) (combineAll (fg := fg) fs) =
      combineAll (fg := FactorGraph.toLineage fg) (fs.map (toLineage (fg := fg))) := by
  induction fs with
  | nil =>
      simp [combineAll]
  | cons φ fs ih =>
      simpa [combineAll] using
        congrArg
          (fun ψ => Factor.mul (fg := FactorGraph.toLineage fg) (Factor.toLineage (fg := fg) φ) ψ)
          ih

end Factor

variable {V K L : Type*} [DecidableEq V]
variable {fg : FactorGraph V (K × L)}

omit [DecidableEq V] in
@[simp] theorem factorsOfGraph_toWeight [Fintype fg.factors] :
    factorsOfGraph (fg := FactorGraph.toWeight fg) =
      (factorsOfGraph (fg := fg)).map (Factor.toWeight (fg := fg)) := by
  simp [factorsOfGraph]

omit [DecidableEq V] in
@[simp] theorem factorsOfGraph_toLineage [Fintype fg.factors] :
    factorsOfGraph (fg := FactorGraph.toLineage fg) =
      (factorsOfGraph (fg := fg)).map (Factor.toLineage (fg := fg)) := by
  simp [factorsOfGraph]

/-- Exact query weights on a product semiring recover ordinary exact weights on
the first projection. -/
theorem weightOfConstraintsList_fst
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] [CommSemiring L] :
    (weightOfConstraintsList (fg := fg) fs constraints).1 =
      weightOfConstraintsList
        (fg := FactorGraph.toWeight fg)
        (fs.map (Factor.toWeight (fg := fg)))
        constraints := by
  classical
  unfold weightOfConstraintsList
  have hpot :
      ∀ x,
        ((combineAll (fg := fg) fs).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)).1 =
          (combineAll (fg := FactorGraph.toWeight fg)
              (fs.map (Factor.toWeight (fg := fg)))).potential
            (FactorGraph.fullAssign (fg := FactorGraph.toWeight fg) x
              (combineAll (fg := FactorGraph.toWeight fg)
                (fs.map (Factor.toWeight (fg := fg)))).scope) := by
    intro x
    simpa using
      congrArg
        (fun φ =>
          φ.potential
            (FactorGraph.fullAssign (fg := FactorGraph.toWeight fg) x φ.scope))
        (Factor.combineAll_toWeight (fg := fg) fs)
  let hfst : (K × L) →+* K := RingHom.fst K L
  change hfst (weightOfConstraintsList (fg := fg) fs constraints) = _
  unfold weightOfConstraintsList
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hs : ∀ c ∈ constraints, x c.1 = c.2
  · have hsx : (fun x => ∀ c ∈ constraints, x c.1 = c.2) x := hs
    calc
      (if ∀ c ∈ constraints, x c.1 = c.2 then
          (combineAll (fg := fg) fs).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)
        else 0).1
          = ((combineAll (fg := fg) fs).potential
              (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)).1 := by
                rw [if_pos hsx]
      _ = (combineAll (fg := FactorGraph.toWeight fg)
            (fs.map (Factor.toWeight (fg := fg)))).potential
            (FactorGraph.fullAssign (fg := FactorGraph.toWeight fg) x
              (combineAll (fg := FactorGraph.toWeight fg)
                (fs.map (Factor.toWeight (fg := fg)))).scope) := hpot x
      _ = if ∀ c ∈ constraints, x c.1 = c.2 then
            (combineAll (fg := FactorGraph.toWeight fg)
              (fs.map (Factor.toWeight (fg := fg)))).potential
              (FactorGraph.fullAssign (fg := FactorGraph.toWeight fg) x
                (combineAll (fg := FactorGraph.toWeight fg)
                  (fs.map (Factor.toWeight (fg := fg)))).scope)
          else 0 := by rw [if_pos hsx]
  · have hsx : ¬ (fun x => ∀ c ∈ constraints, x c.1 = c.2) x := hs
    calc
      (if ∀ c ∈ constraints, x c.1 = c.2 then
          (combineAll (fg := fg) fs).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)
        else 0).1 = 0 := by simp [hsx]
      _ = if ∀ c ∈ constraints, x c.1 = c.2 then
            (combineAll (fg := FactorGraph.toWeight fg)
              (fs.map (Factor.toWeight (fg := fg)))).potential
              (FactorGraph.fullAssign (fg := FactorGraph.toWeight fg) x
                (combineAll (fg := FactorGraph.toWeight fg)
                  (fs.map (Factor.toWeight (fg := fg)))).scope)
          else 0 := by rw [if_neg hsx]

/-- Exact query lineage on a product semiring recovers ordinary exact lineage on
the second projection. -/
theorem weightOfConstraintsList_snd
    (fs : List (Factor fg))
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] [CommSemiring L] :
    (weightOfConstraintsList (fg := fg) fs constraints).2 =
      weightOfConstraintsList
        (fg := FactorGraph.toLineage fg)
        (fs.map (Factor.toLineage (fg := fg)))
        constraints := by
  classical
  unfold weightOfConstraintsList
  have hpot :
      ∀ x,
        ((combineAll (fg := fg) fs).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)).2 =
          (combineAll (fg := FactorGraph.toLineage fg)
              (fs.map (Factor.toLineage (fg := fg)))).potential
            (FactorGraph.fullAssign (fg := FactorGraph.toLineage fg) x
              (combineAll (fg := FactorGraph.toLineage fg)
                (fs.map (Factor.toLineage (fg := fg)))).scope) := by
    intro x
    simpa using
      congrArg
        (fun φ =>
          φ.potential
            (FactorGraph.fullAssign (fg := FactorGraph.toLineage fg) x φ.scope))
        (Factor.combineAll_toLineage (fg := fg) fs)
  let hsnd : (K × L) →+* L := RingHom.snd K L
  change hsnd (weightOfConstraintsList (fg := fg) fs constraints) = _
  unfold weightOfConstraintsList
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hs : ∀ c ∈ constraints, x c.1 = c.2
  · have hsx : (fun x => ∀ c ∈ constraints, x c.1 = c.2) x := hs
    calc
      (if ∀ c ∈ constraints, x c.1 = c.2 then
          (combineAll (fg := fg) fs).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)
        else 0).2
          = ((combineAll (fg := fg) fs).potential
              (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)).2 := by
                rw [if_pos hsx]
      _ = (combineAll (fg := FactorGraph.toLineage fg)
            (fs.map (Factor.toLineage (fg := fg)))).potential
            (FactorGraph.fullAssign (fg := FactorGraph.toLineage fg) x
              (combineAll (fg := FactorGraph.toLineage fg)
                (fs.map (Factor.toLineage (fg := fg)))).scope) := hpot x
      _ = if ∀ c ∈ constraints, x c.1 = c.2 then
            (combineAll (fg := FactorGraph.toLineage fg)
              (fs.map (Factor.toLineage (fg := fg)))).potential
              (FactorGraph.fullAssign (fg := FactorGraph.toLineage fg) x
                (combineAll (fg := FactorGraph.toLineage fg)
                  (fs.map (Factor.toLineage (fg := fg)))).scope)
          else 0 := by rw [if_pos hsx]
  · have hsx : ¬ (fun x => ∀ c ∈ constraints, x c.1 = c.2) x := hs
    calc
      (if ∀ c ∈ constraints, x c.1 = c.2 then
          (combineAll (fg := fg) fs).potential
            (FactorGraph.fullAssign (fg := fg) x (combineAll (fg := fg) fs).scope)
        else 0).2 = 0 := by simp [hsx]
      _ = if ∀ c ∈ constraints, x c.1 = c.2 then
            (combineAll (fg := FactorGraph.toLineage fg)
              (fs.map (Factor.toLineage (fg := fg)))).potential
              (FactorGraph.fullAssign (fg := FactorGraph.toLineage fg) x
                (combineAll (fg := FactorGraph.toLineage fg)
                  (fs.map (Factor.toLineage (fg := fg)))).scope)
          else 0 := by rw [if_neg hsx]

/-- Graph-level exact query weights on a product semiring recover the ordinary
weight query on the first projection. -/
theorem weightOfConstraints_fst
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] [CommSemiring L] :
    (weightOfConstraints (fg := fg) constraints).1 =
      weightOfConstraints (fg := FactorGraph.toWeight fg) constraints := by
  simp [weightOfConstraints, weightOfConstraintsList_fst]

/-- Graph-level exact query lineage on a product semiring recovers the ordinary
lineage query on the second projection. -/
theorem weightOfConstraints_snd
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [Fintype fg.factors] [CommSemiring K] [CommSemiring L] :
    (weightOfConstraints (fg := fg) constraints).2 =
      weightOfConstraints (fg := FactorGraph.toLineage fg) constraints := by
  simp [weightOfConstraints, weightOfConstraintsList_snd]

end VariableElimination

namespace ValuationWorldModel

variable {V K L : Type*} [DecidableEq V]
variable {fg : FactorGraph V (K × L)}

/-- WM-source exact weights on a product carrier recover the ordinary exact
weight query on the weight projection. -/
theorem weight_fst
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] [CommSemiring L] :
    (weight (fg := fg) (W := W) constraints).1 =
      weight
        (fg := FactorGraph.toWeight fg)
        (W := W.map (VariableElimination.Factor.toWeight (fg := fg)))
        constraints := by
  exact VariableElimination.weightOfConstraintsList_fst (fg := fg) W constraints

/-- WM-source exact lineage on a product carrier recovers the ordinary exact
lineage query on the lineage projection. -/
theorem weight_snd
    (W : WMSource fg)
    (constraints : List (Σ v : V, fg.stateSpace v))
    [Fintype V] [∀ v, Fintype (fg.stateSpace v)] [∀ v, DecidableEq (fg.stateSpace v)]
    [CommSemiring K] [CommSemiring L] :
    (weight (fg := fg) (W := W) constraints).2 =
      weight
        (fg := FactorGraph.toLineage fg)
        (W := W.map (VariableElimination.Factor.toLineage (fg := fg)))
        constraints := by
  exact VariableElimination.weightOfConstraintsList_snd (fg := fg) W constraints

end ValuationWorldModel

namespace PairedWeightLineageCanary

open VariableElimination

/-! A tiny one-variable canary showing that exact queries on `(weight, lineage)`
recover the same weight and lineage as querying the two projected factor graphs. -/

inductive DemoVar
  | target
  deriving DecidableEq, Fintype

inductive DemoFactor
  | left
  | right
  deriving DecidableEq, Fintype

abbrev DemoLineage := Which (Fin 2)
abbrev DemoValue := ℕ × DemoLineage

def demoFg : FactorGraph DemoVar DemoValue where
  stateSpace := fun _ => Bool
  factors := DemoFactor
  scope := fun _ => {DemoVar.target}
  potential := fun f x =>
    match f with
    | .left =>
        if x DemoVar.target (by simp) then
          (2, Which.wset {⟨0, by decide⟩})
        else
          (1, 1)
    | .right =>
        if x DemoVar.target (by simp) then
          (3, Which.wset {⟨1, by decide⟩})
        else
          (1, 1)

def trueConstraint : List (Σ v : DemoVar, demoFg.stateSpace v) :=
  [⟨DemoVar.target, true⟩]

instance : ∀ v : DemoVar, Fintype (demoFg.stateSpace v) := by
  intro v
  simpa [demoFg] using (inferInstance : Fintype Bool)

instance : ∀ v : DemoVar, DecidableEq (demoFg.stateSpace v) := by
  intro v
  simpa [demoFg] using (inferInstance : DecidableEq Bool)

instance : Fintype demoFg.factors := by
  dsimp [demoFg]
  infer_instance

noncomputable def demoFactors : List (VariableElimination.Factor demoFg) :=
  [VariableElimination.Factor.ofGraph (fg := demoFg) .left,
   VariableElimination.Factor.ofGraph (fg := demoFg) .right]

theorem canary_projection_weight :
    VariableElimination.weightOfConstraintsList
      (fg := FactorGraph.toWeight demoFg)
      (demoFactors.map (VariableElimination.Factor.toWeight (fg := demoFg)))
      trueConstraint = 6 := by
  decide

theorem canary_projection_lineage :
    VariableElimination.weightOfConstraintsList
      (fg := FactorGraph.toLineage demoFg)
      (demoFactors.map (VariableElimination.Factor.toLineage (fg := demoFg)))
      trueConstraint =
      (VariableElimination.weightOfConstraintsList (fg := demoFg) demoFactors trueConstraint).2 := by
  rw [VariableElimination.weightOfConstraintsList_snd (fg := demoFg)]

theorem canary_pair_query_true_fst :
    (VariableElimination.weightOfConstraintsList (fg := demoFg) demoFactors trueConstraint).1 = 6 := by
  rw [VariableElimination.weightOfConstraintsList_fst (fg := demoFg)]
  exact canary_projection_weight

end PairedWeightLineageCanary

end Mettapedia.ProbabilityTheory.BayesianNetworks
