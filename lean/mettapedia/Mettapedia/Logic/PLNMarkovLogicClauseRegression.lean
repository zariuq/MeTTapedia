import Mettapedia.Logic.PLNMarkovLogicClauseWorldModel

/-!
# Clause-Level MLN Regression Tests

Concrete clause-native MLN instances exercising the full pipeline:

  GroundMLN → compiledClauseFactorGraph → clauseWMState → WorldModel.queryStrength

Each regression verifies an exact `queryProb` value at a concrete MLN instantiation.

## Examples

1. **Sigmoid**: 1 atom, 1 positive clause, weight 3/1. Strength = 3/4.
2. **Conflicting soft**: 1 atom, 2 opposing clauses. Intermediate strength 3/5.
3. **Hard zero**: 1 atom, hard constraint (unsatisfied=0). Impossible query → strength 0.
-/

namespace Mettapedia.Logic.PLNMarkovLogicClauseRegression

open scoped ENNReal BigOperators
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable
open Mettapedia.Logic.PLNMarkovLogicClauseSemantics
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicClauseWorldModel
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.BayesianNetworks

/-! ## Shared Helpers -/

/-- The atomic positive query `[A = true]` for the unique unit atom. -/
def qTrue : ConstraintQuery Unit := [⟨(), true⟩]

/-- The atomic negative query `[A = false]` for the unique unit atom. -/
def qFalse : ConstraintQuery Unit := [⟨(), false⟩]

/-- The valuation setting the unique atom to `true`. -/
def valTrue : AtomValuation Unit := fun _ => true

/-- The valuation setting the unique atom to `false`. -/
def valFalse : AtomValuation Unit := fun _ => false

/-- The finite valuation space over a single Boolean atom has exactly two worlds. -/
theorem univ_atomValuation_unit :
    (Finset.univ : Finset (AtomValuation Unit)) = {valTrue, valFalse} := by
  ext W
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  cases hW : W ()
  · right
    funext u
    cases u
    exact hW
  · left
    funext u
    cases u
    exact hW

theorem valTrue_ne_valFalse : valTrue ≠ valFalse := by
  intro h
  have h' := congrFun h ()
  simp [valTrue, valFalse] at h'

theorem valTrue_not_mem_singleton_valFalse :
    valTrue ∉ ({valFalse} : Finset (AtomValuation Unit)) := by
  simpa [Finset.mem_singleton] using valTrue_ne_valFalse

theorem qTrue_holds_valTrue : constraintQueryHolds qTrue valTrue := by
  simp [qTrue, constraintQueryHolds, satisfiesConstraints, valTrue]

theorem qTrue_not_holds_valFalse : ¬ constraintQueryHolds qTrue valFalse := by
  simp [qTrue, constraintQueryHolds, satisfiesConstraints, valFalse]

theorem qFalse_not_holds_valTrue : ¬ constraintQueryHolds qFalse valTrue := by
  simp [qFalse, constraintQueryHolds, satisfiesConstraints, valTrue]

theorem qFalse_holds_valFalse : constraintQueryHolds qFalse valFalse := by
  simp [qFalse, constraintQueryHolds, satisfiesConstraints, valFalse]

/-! ## Helper: worldWeight reduction for small clause supports -/

open GroundMLN in
/-- For singleton support `{()}`, the world weight is just the single clause's eval. -/
theorem worldWeight_unit_singleton
    {Atom : Type*} [DecidableEq Atom]
    (M : GroundMLN Atom Unit) (W : AtomValuation Atom) :
    M.worldWeight {()} W = (M.clauseData ()).eval W := by
  classical
  unfold worldWeight
  calc
    (∏ i : (({()} : Finset Unit).attach), (M.clauseData i.1).eval W)
      = ∏ i ∈ (({()} : Finset Unit).attach), (M.clauseData i.1).eval W := by
          simpa using
            (Finset.prod_coe_sort (({()} : Finset Unit).attach)
              (fun i => (M.clauseData i.1).eval W))
    _ = ∏ i ∈ ({()} : Finset Unit), (M.clauseData i).eval W := by
          simpa using
            (Finset.prod_attach (s := ({()} : Finset Unit))
              (f := fun i => (M.clauseData i).eval W))
    _ = (M.clauseData ()).eval W := by
          simp

open GroundMLN in
/-- For Boolean clause ids over `univ`, the world weight is the product of the two clause evals. -/
theorem worldWeight_bool_univ
    {Atom : Type*} [DecidableEq Atom]
    (M : GroundMLN Atom Bool) (W : AtomValuation Atom) :
    M.worldWeight (Finset.univ : Finset Bool) W =
      (M.clauseData true).eval W * (M.clauseData false).eval W := by
  classical
  unfold worldWeight
  calc
    (∏ i : ((Finset.univ : Finset Bool).attach), (M.clauseData i.1).eval W)
      = ∏ i ∈ ((Finset.univ : Finset Bool).attach), (M.clauseData i.1).eval W := by
          simpa using
            (Finset.prod_coe_sort ((Finset.univ : Finset Bool).attach)
              (fun i => (M.clauseData i.1).eval W))
    _ = ∏ i ∈ (Finset.univ : Finset Bool), (M.clauseData i).eval W := by
          simpa using
            (Finset.prod_attach (s := (Finset.univ : Finset Bool))
              (f := fun i => (M.clauseData i).eval W))
    _ = (M.clauseData true).eval W * (M.clauseData false).eval W := by
          rw [Fintype.univ_bool]
          simp [Finset.prod_insert, mul_comm]

/-! ## Example 1: Single Positive Clause (Sigmoid) -/

/-- A single-atom, single-clause MLN with potentials 3 (satisfied) / 1 (unsatisfied). -/
noncomputable def sigmoidMLN : GroundMLN Unit Unit where
  clauseData _ :=
    { clause := {Literal.pos ()}
      satisfiedPotential := 3
      unsatisfiedPotential := 1
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }

section Sigmoid

private theorem sigmoid_eval_true :
    (sigmoidMLN.clauseData ()).eval valTrue = 3 := by
  classical
  unfold sigmoidMLN WeightedGroundClause.eval GroundClause.holds Literal.holds valTrue
  simp

private theorem sigmoid_eval_false :
    (sigmoidMLN.clauseData ()).eval valFalse = 1 := by
  classical
  unfold sigmoidMLN WeightedGroundClause.eval GroundClause.holds Literal.holds valFalse
  simp

private theorem sigmoid_worldWeight_true :
    sigmoidMLN.worldWeight {()} valTrue = 3 := by
  rw [worldWeight_unit_singleton]; exact sigmoid_eval_true

private theorem sigmoid_worldWeight_false :
    sigmoidMLN.worldWeight {()} valFalse = 1 := by
  rw [worldWeight_unit_singleton]; exact sigmoid_eval_false

theorem sigmoid_queryMass_true_eq_three :
    (clauseMassSemantics sigmoidMLN ({()} : Finset Unit)).queryMass qTrue = 3 := by
  change CountableMLNSemantics.queryMass
    (sigmoidMLN.toCountableMLNSemantics (Query := ConstraintQuery Unit) ({()} : Finset Unit)
      constraintQueryHolds) qTrue = 3
  unfold CountableMLNSemantics.queryMass constraintQueryHolds satisfiesConstraints
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Unit)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  rw [univ_atomValuation_unit]
  rw [Finset.sum_insert valTrue_not_mem_singleton_valFalse, Finset.sum_singleton]
  simp only [GroundMLN.toCountableMLNSemantics]
  rw [if_pos (by simpa [constraintQueryHolds, satisfiesConstraints] using qTrue_holds_valTrue),
    if_neg (by simpa [constraintQueryHolds, satisfiesConstraints] using qTrue_not_holds_valFalse)]
  simp [sigmoid_worldWeight_true]

theorem sigmoid_totalMass_eq_four :
    (clauseMassSemantics sigmoidMLN ({()} : Finset Unit)).totalMass = 4 := by
  change CountableMLNSemantics.totalMass
    (sigmoidMLN.toCountableMLNSemantics (Query := ConstraintQuery Unit) ({()} : Finset Unit)
      constraintQueryHolds) = 4
  unfold CountableMLNSemantics.totalMass
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Unit)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  rw [univ_atomValuation_unit]
  rw [Finset.sum_insert valTrue_not_mem_singleton_valFalse, Finset.sum_singleton]
  simp only [GroundMLN.toCountableMLNSemantics]
  rw [sigmoid_worldWeight_true, sigmoid_worldWeight_false]
  norm_num

theorem sigmoid_queryProb_true_eq_three_fourths :
    (clauseMassSemantics sigmoidMLN ({()} : Finset Unit)).queryProb qTrue = (3 : ENNReal) / 4 := by
  have htotal_ne_zero :
      (clauseMassSemantics sigmoidMLN ({()} : Finset Unit)).totalMass ≠ 0 := by
    rw [sigmoid_totalMass_eq_four]
    norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal_ne_zero, sigmoid_queryMass_true_eq_three, sigmoid_totalMass_eq_four]

theorem sigmoid_queryStrength_true_eq_three_fourths :
    WorldModel.queryStrength (clauseWMState sigmoidMLN ({()} : Finset Unit)) qTrue =
      (3 : ENNReal) / 4 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact sigmoid_queryProb_true_eq_three_fourths

theorem sigmoid_evidence_true_eq_three_one :
    WorldModel.evidence (clauseWMState sigmoidMLN ({()} : Finset Unit)) qTrue = ⟨3, 1⟩ := by
  rw [clauseWM_evidence_eq_evidenceOfMasses]
  unfold MassSemantics.evidenceOfMasses
  rw [sigmoid_queryMass_true_eq_three, sigmoid_totalMass_eq_four]
  ext <;> simp
  exact (ENNReal.eq_sub_of_add_eq (a := (1 : ENNReal)) (b := (4 : ENNReal)) (c := (3 : ENNReal))
    (by norm_num) (by norm_num)).symm

end Sigmoid

/-! ## Example 2: Conflicting Soft Clauses -/

/-- Two soft clauses over one atom:
    - positive clause: 3 if `A=true`, 1 otherwise
    - negative clause: 2 if `A=false`, 1 otherwise
    Hence `P(A=true) = 3 / (3 + 2) = 3/5`. -/
noncomputable def conflictingMLN : GroundMLN Unit Bool where
  clauseData
  | false =>
      { clause := {Literal.pos ()}
        satisfiedPotential := 3
        unsatisfiedPotential := 1
        satisfied_ne_top := by norm_num
        unsatisfied_ne_top := by norm_num }
  | true =>
      { clause := {Literal.neg ()}
        satisfiedPotential := 2
        unsatisfiedPotential := 1
        satisfied_ne_top := by norm_num
        unsatisfied_ne_top := by norm_num }

section Conflicting

private theorem conflicting_worldWeight_true :
    conflictingMLN.worldWeight (Finset.univ : Finset Bool) valTrue = 3 := by
  rw [worldWeight_bool_univ]
  unfold conflictingMLN WeightedGroundClause.eval GroundClause.holds Literal.holds valTrue
  simp

private theorem conflicting_worldWeight_false :
    conflictingMLN.worldWeight (Finset.univ : Finset Bool) valFalse = 2 := by
  rw [worldWeight_bool_univ]
  unfold conflictingMLN WeightedGroundClause.eval GroundClause.holds Literal.holds valFalse
  simp

theorem conflicting_queryMass_true_eq_three :
    (clauseMassSemantics conflictingMLN (Finset.univ : Finset Bool)).queryMass qTrue = 3 := by
  change CountableMLNSemantics.queryMass
    (conflictingMLN.toCountableMLNSemantics (Query := ConstraintQuery Unit) (Finset.univ : Finset Bool)
      constraintQueryHolds) qTrue = 3
  unfold CountableMLNSemantics.queryMass constraintQueryHolds satisfiesConstraints
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Unit)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  rw [univ_atomValuation_unit]
  rw [Finset.sum_insert valTrue_not_mem_singleton_valFalse, Finset.sum_singleton]
  simp only [GroundMLN.toCountableMLNSemantics]
  rw [if_pos (by simpa [constraintQueryHolds, satisfiesConstraints] using qTrue_holds_valTrue),
    if_neg (by simpa [constraintQueryHolds, satisfiesConstraints] using qTrue_not_holds_valFalse)]
  rw [add_zero]
  exact conflicting_worldWeight_true

theorem conflicting_totalMass_eq_five :
    (clauseMassSemantics conflictingMLN (Finset.univ : Finset Bool)).totalMass = 5 := by
  change CountableMLNSemantics.totalMass
    (conflictingMLN.toCountableMLNSemantics (Query := ConstraintQuery Unit) (Finset.univ : Finset Bool)
      constraintQueryHolds) = 5
  unfold CountableMLNSemantics.totalMass
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Unit)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  rw [univ_atomValuation_unit]
  rw [Finset.sum_insert valTrue_not_mem_singleton_valFalse, Finset.sum_singleton]
  simp only [GroundMLN.toCountableMLNSemantics]
  rw [conflicting_worldWeight_true, conflicting_worldWeight_false]
  norm_num

theorem conflicting_queryProb_true_eq_three_fifths :
    (clauseMassSemantics conflictingMLN (Finset.univ : Finset Bool)).queryProb qTrue =
      (3 : ENNReal) / 5 := by
  have htotal_ne_zero :
      (clauseMassSemantics conflictingMLN (Finset.univ : Finset Bool)).totalMass ≠ 0 := by
    rw [conflicting_totalMass_eq_five]
    norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal_ne_zero, conflicting_queryMass_true_eq_three, conflicting_totalMass_eq_five]

theorem conflicting_queryStrength_true_eq_three_fifths :
    WorldModel.queryStrength (clauseWMState conflictingMLN (Finset.univ : Finset Bool)) qTrue =
      (3 : ENNReal) / 5 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact conflicting_queryProb_true_eq_three_fifths

theorem conflicting_true_not_entailed_by_live_worlds :
    ¬ ∀ W, conflictingMLN.worldWeight (Finset.univ : Finset Bool) W ≠ 0 → constraintQueryHolds qTrue W := by
  intro h
  have hw : conflictingMLN.worldWeight (Finset.univ : Finset Bool) valFalse ≠ 0 := by
    rw [conflicting_worldWeight_false]
    norm_num
  have hq := h valFalse hw
  simp [constraintQueryHolds, satisfiesConstraints, qTrue, valFalse] at hq

end Conflicting

/-! ## Example 3: Hard Zero Clause -/

/-- A single clause with unsatisfied potential `0`: worlds violating the clause are impossible. -/
noncomputable def hardZeroMLN : GroundMLN Unit Unit where
  clauseData _ :=
    { clause := {Literal.pos ()}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }

section HardZero

private theorem hardZero_worldWeight_true :
    hardZeroMLN.worldWeight {()} valTrue = 1 := by
  rw [worldWeight_unit_singleton]
  unfold hardZeroMLN WeightedGroundClause.eval GroundClause.holds Literal.holds valTrue
  simp

private theorem hardZero_worldWeight_false :
    hardZeroMLN.worldWeight {()} valFalse = 0 := by
  rw [worldWeight_unit_singleton]
  unfold hardZeroMLN WeightedGroundClause.eval GroundClause.holds Literal.holds valFalse
  simp

theorem hardZero_queryMass_false_eq_zero :
    (clauseMassSemantics hardZeroMLN ({()} : Finset Unit)).queryMass qFalse = 0 := by
  change CountableMLNSemantics.queryMass
    (hardZeroMLN.toCountableMLNSemantics (Query := ConstraintQuery Unit) ({()} : Finset Unit)
      constraintQueryHolds) qFalse = 0
  unfold CountableMLNSemantics.queryMass constraintQueryHolds satisfiesConstraints
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Unit)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  rw [univ_atomValuation_unit]
  rw [Finset.sum_insert valTrue_not_mem_singleton_valFalse, Finset.sum_singleton]
  simp only [GroundMLN.toCountableMLNSemantics]
  rw [if_neg (by simpa [constraintQueryHolds, satisfiesConstraints] using qFalse_not_holds_valTrue),
    if_pos (by simpa [constraintQueryHolds, satisfiesConstraints] using qFalse_holds_valFalse)]
  simp [hardZero_worldWeight_false]

theorem hardZero_totalMass_eq_one :
    (clauseMassSemantics hardZeroMLN ({()} : Finset Unit)).totalMass = 1 := by
  change CountableMLNSemantics.totalMass
    (hardZeroMLN.toCountableMLNSemantics (Query := ConstraintQuery Unit) ({()} : Finset Unit)
      constraintQueryHolds) = 1
  unfold CountableMLNSemantics.totalMass
  rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Unit)))
    (fun W hW => (hW (Finset.mem_univ W)).elim)]
  rw [univ_atomValuation_unit]
  rw [Finset.sum_insert valTrue_not_mem_singleton_valFalse, Finset.sum_singleton]
  simp only [GroundMLN.toCountableMLNSemantics]
  rw [hardZero_worldWeight_true, hardZero_worldWeight_false]
  norm_num

theorem hardZero_queryProb_false_eq_zero :
    (clauseMassSemantics hardZeroMLN ({()} : Finset Unit)).queryProb qFalse = 0 := by
  have htotal_ne_zero :
      (clauseMassSemantics hardZeroMLN ({()} : Finset Unit)).totalMass ≠ 0 := by
    rw [hardZero_totalMass_eq_one]
    norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal_ne_zero, hardZero_queryMass_false_eq_zero, hardZero_totalMass_eq_one]
  simp

theorem hardZero_queryStrength_false_eq_zero :
    WorldModel.queryStrength (clauseWMState hardZeroMLN ({()} : Finset Unit)) qFalse = 0 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact hardZero_queryProb_false_eq_zero

end HardZero

end Mettapedia.Logic.PLNMarkovLogicClauseRegression
