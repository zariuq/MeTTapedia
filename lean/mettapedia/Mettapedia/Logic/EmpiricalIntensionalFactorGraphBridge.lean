import Mettapedia.Logic.EmpiricalIntensionalInformation
import Mettapedia.Logic.BinaryEvidence
import Mettapedia.Logic.ConceptOntology.Formation
import Mettapedia.Logic.ConceptOntology.CredalFormation
import Mettapedia.Logic.ConceptOntology.WMBridge
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassing

/-!
# Empirical Intensional Information ↔ Tiny Factor-Graph Bridge

This file closes the smallest concrete loop between the regrounded inheritance
surface and the factor-graph / belief-propagation stack.

For a single empirical 2x2 `MembershipCounts` table, we build the corresponding
one-factor Boolean factor graph and prove that:

* exact VE constraint weights recover the table counts;
* the inherited probabilities are read as exact ratios of those weights;
* the corresponding BP messages and factor belief recover the same local counts.
-/

namespace Mettapedia.Logic.IntensionalInheritance

open scoped Classical BigOperators
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.BayesianNetworks

namespace MembershipCounts

inductive EmpiricalFactor
  | joint
  deriving DecidableEq, Fintype

/-- The joint factor scope for the empirical 2x2 table. -/
def pairScope : Finset MembershipConcept :=
  {MembershipConcept.feature, MembershipConcept.witness}

@[simp] theorem pairScope_mem_feature :
    MembershipConcept.feature ∈ pairScope := by
  simp [pairScope]

@[simp] theorem pairScope_mem_witness :
    MembershipConcept.witness ∈ pairScope := by
  simp [pairScope]

theorem pairScope_erase_witness :
    pairScope.erase MembershipConcept.witness = {MembershipConcept.feature} := by
  ext v
  cases v <;> simp [pairScope]

theorem pairScope_erase_feature :
    pairScope.erase MembershipConcept.feature = {MembershipConcept.witness} := by
  ext v
  cases v <;> simp [pairScope]

/-- The raw joint weight table induced by the four empirical regions. -/
def rawPotential (c : MembershipCounts) (feature witness : Bool) : Nat :=
  match feature, witness with
  | false, false => c.neither
  | false, true => c.witnessOnly
  | true, false => c.featureOnly
  | true, true => c.both

def pairPotential (c : MembershipCounts) (x : ∀ v ∈ pairScope, Bool) : Nat :=
  rawPotential c
    (x MembershipConcept.feature (by simp [pairScope]))
    (x MembershipConcept.witness (by simp [pairScope]))

/-- The one-factor graph whose joint potential is exactly the empirical 2x2
table. -/
def factorGraph (c : MembershipCounts) : FactorGraph MembershipConcept Nat where
  stateSpace := fun _ => Bool
  factors := EmpiricalFactor
  scope := fun _ => pairScope
  potential := fun _ => pairPotential c

instance (c : MembershipCounts) : ∀ v : MembershipConcept, Fintype ((factorGraph c).stateSpace v) := by
  intro _
  dsimp [factorGraph]
  infer_instance

instance (c : MembershipCounts) : ∀ v : MembershipConcept, DecidableEq ((factorGraph c).stateSpace v) := by
  intro _
  dsimp [factorGraph]
  infer_instance

instance (c : MembershipCounts) : Fintype (factorGraph c).factors := by
  dsimp [factorGraph]
  infer_instance

instance (c : MembershipCounts) : DecidableEq (factorGraph c).factors := by
  dsimp [factorGraph]
  infer_instance

instance (c : MembershipCounts) : Fintype (factorGraph c).FullConfig := by
  dsimp [FactorGraph.FullConfig, factorGraph]
  infer_instance

/-- The explicit singleton factor list corresponding to the empirical graph. -/
noncomputable def empiricalFactors (c : MembershipCounts) :
    List (VariableElimination.Factor (fg := factorGraph c)) :=
  [VariableElimination.Factor.ofGraph (fg := factorGraph c) EmpiricalFactor.joint]

/-- The exact VE weight of a constraint set on the tiny empirical graph. -/
noncomputable def veWeight (c : MembershipCounts)
    (constraints : List (Σ v : MembershipConcept, (factorGraph c).stateSpace v)) : Nat :=
  VariableElimination.veQueryWeightList
    (factorGraph c) (empiricalFactors c) constraints

/-- Direct pair-level semantics for the same constraint set. -/
def pairSatisfies
    (constraints : List (Σ _ : MembershipConcept, Bool)) (p : Bool × Bool) : Prop :=
  ∀ q ∈ constraints,
    match q.1 with
    | MembershipConcept.feature => p.1 = q.2
    | MembershipConcept.witness => p.2 = q.2

noncomputable def pairWeight (c : MembershipCounts)
    (constraints : List (Σ _ : MembershipConcept, Bool)) : Nat :=
  ∑ p : Bool × Bool,
    if pairSatisfies constraints p then rawPotential c p.1 p.2 else 0

noncomputable def fullConfigEquiv (c : MembershipCounts) :
    (factorGraph c).FullConfig ≃ Bool × Bool where
  toFun x := (x MembershipConcept.feature, x MembershipConcept.witness)
  invFun p := fun
    | MembershipConcept.feature => p.1
    | MembershipConcept.witness => p.2
  left_inv x := by
    funext v
    cases v <;> rfl
  right_inv p := by
    cases p
    rfl

noncomputable def combinedFactor (c : MembershipCounts) :
    VariableElimination.Factor (fg := factorGraph c) :=
  VariableElimination.combineAll (fg := factorGraph c) (empiricalFactors c)

theorem combinedFactor_apply (c : MembershipCounts) (x : (factorGraph c).FullConfig) :
    (combinedFactor c).potential
        (VariableElimination.FactorGraph.fullAssign (fg := factorGraph c) x (combinedFactor c).scope) =
      rawPotential c (x MembershipConcept.feature) (x MembershipConcept.witness) := by
  cases hFeature : x MembershipConcept.feature <;>
    cases hWitness : x MembershipConcept.witness <;>
      simp [combinedFactor, empiricalFactors, VariableElimination.combineAll,
        VariableElimination.oneFactor, VariableElimination.Factor.mul,
        VariableElimination.Factor.ofGraph, VariableElimination.FactorGraph.fullAssign,
        VariableElimination.FactorGraph.restrict, factorGraph, pairPotential, rawPotential,
        pairScope, hFeature, hWitness]

theorem veWeight_eq_pairWeight
    (c : MembershipCounts) (constraints : List (Σ _ : MembershipConcept, Bool)) :
    veWeight c constraints = pairWeight c constraints := by
  classical
  have hsum :
      (∑ x : (factorGraph c).FullConfig,
          if (∀ q ∈ constraints, x q.1 = q.2) then
            (combinedFactor c).potential
              (VariableElimination.FactorGraph.fullAssign (fg := factorGraph c) x (combinedFactor c).scope)
          else 0) =
        ∑ p : Bool × Bool,
          if pairSatisfies constraints p then rawPotential c p.1 p.2 else 0 := by
    refine Fintype.sum_equiv (fullConfigEquiv c)
      (fun x =>
        if (∀ q ∈ constraints, x q.1 = q.2) then
          (combinedFactor c).potential
            (VariableElimination.FactorGraph.fullAssign (fg := factorGraph c) x (combinedFactor c).scope)
        else 0)
      (fun p =>
        if pairSatisfies constraints p then rawPotential c p.1 p.2 else 0)
      (by
        intro x
        have hSat :
            (∀ q ∈ constraints, x q.1 = q.2) ↔
              pairSatisfies constraints ((fullConfigEquiv c) x) := by
          constructor
          · intro hx q hq
            rcases q with ⟨v, b⟩
            cases v <;> exact hx ⟨_, b⟩ hq
          · intro hx q hq
            rcases q with ⟨v, b⟩
            cases v <;> exact hx ⟨_, b⟩ hq
        simp [hSat, combinedFactor_apply, fullConfigEquiv])
  rw [veWeight, VariableElimination.veQueryWeightList_eq_weightOfConstraintsList]
  exact hsum

theorem pairWeight_nil (c : MembershipCounts) :
    pairWeight c [] = total c := by
  simp [pairWeight, pairSatisfies, rawPotential, total, Fintype.sum_prod_type]
  omega

theorem pairWeight_witness_true (c : MembershipCounts) :
    pairWeight c [⟨MembershipConcept.witness, true⟩] = witnessSupport c := by
  simp [pairWeight, pairSatisfies, rawPotential, witnessSupport, Fintype.sum_prod_type]
  omega

theorem pairWeight_feature_true (c : MembershipCounts) :
    pairWeight c [⟨MembershipConcept.feature, true⟩] = featureSupport c := by
  simp [pairWeight, pairSatisfies, rawPotential, featureSupport, Fintype.sum_prod_type]
  omega

theorem pairWeight_feature_witness_true (c : MembershipCounts) :
    pairWeight c [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] = c.both := by
  simp [pairWeight, pairSatisfies, rawPotential, Fintype.sum_prod_type]

theorem veWeight_nil (c : MembershipCounts) :
    veWeight c [] = total c := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_nil c

theorem veWeight_witness_true (c : MembershipCounts) :
    veWeight c [⟨MembershipConcept.witness, true⟩] = witnessSupport c := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_witness_true c

theorem veWeight_feature_true (c : MembershipCounts) :
    veWeight c [⟨MembershipConcept.feature, true⟩] = featureSupport c := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_feature_true c

theorem veWeight_feature_witness_true (c : MembershipCounts) :
    veWeight c [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] = c.both := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_feature_witness_true c

theorem priorProbWitness_eq_veWeight_ratio (c : MembershipCounts) :
    priorProbWitness c =
      (veWeight c [⟨MembershipConcept.witness, true⟩] : ℝ) / veWeight c [] := by
  rw [veWeight_witness_true, veWeight_nil]
  simp [priorProbWitness]

theorem finitePriorProb_semanticInterpretation_witness_eq_veWeight_ratio
    (c : MembershipCounts) :
    Interpretation.finitePriorProb
        (semanticInterpretation c)
        MembershipConcept.witness =
      (veWeight c [⟨MembershipConcept.witness, true⟩] : ℝ) / veWeight c [] := by
  rw [finitePriorProb_semanticInterpretation_witness, priorProbWitness_eq_veWeight_ratio]

theorem extensionalInheritance_eq_veWeight_ratio (c : MembershipCounts) :
    extensionalInheritance c =
      if veWeight c [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (veWeight c [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          veWeight c [⟨MembershipConcept.feature, true⟩] := by
  rw [veWeight_feature_true, veWeight_feature_witness_true]
  simp [extensionalInheritance]

theorem finiteExtensionalProb_semanticInterpretation_feature_witness_eq_veWeight_ratio
    (c : MembershipCounts) :
    Interpretation.finiteExtensionalProb
        (semanticInterpretation c)
        MembershipConcept.feature
        MembershipConcept.witness =
      if veWeight c [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (veWeight c [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          veWeight c [⟨MembershipConcept.feature, true⟩] := by
  rw [finiteExtensionalProb_semanticInterpretation_feature_witness,
    extensionalInheritance_eq_veWeight_ratio]

theorem pointwiseIntensionalScoreBits_eq_ve_query_score (c : MembershipCounts) :
    pointwiseIntensionalScoreBits c =
      logRatioInformationGainFromEvidence
        (if veWeight c [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (veWeight c [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            veWeight c [⟨MembershipConcept.feature, true⟩])
        ((veWeight c [⟨MembershipConcept.witness, true⟩] : ℝ) / veWeight c []) := by
  unfold pointwiseIntensionalScoreBits
  rw [priorProbWitness_eq_veWeight_ratio, extensionalInheritance_eq_veWeight_ratio]

theorem finitePointwiseLogRatioBits_semanticInterpretation_feature_witness_eq_ve_query_score
    (c : MembershipCounts) :
    Interpretation.finitePointwiseLogRatioBits
        (semanticInterpretation c)
        MembershipConcept.feature
        MembershipConcept.witness =
      logRatioInformationGainFromEvidence
        (if veWeight c [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (veWeight c [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            veWeight c [⟨MembershipConcept.feature, true⟩])
        ((veWeight c [⟨MembershipConcept.witness, true⟩] : ℝ) / veWeight c []) := by
  rw [finitePointwiseLogRatioBits_semanticInterpretation_feature_witness,
    pointwiseIntensionalScoreBits_eq_ve_query_score]

noncomputable def witnessMessage (c : MembershipCounts) : Bool → Nat :=
  MessagePassing.factorToVarUpdate
    (fg := factorGraph c)
    (MessagePassing.unitVarToFactor (fg := factorGraph c))
    EmpiricalFactor.joint
    MembershipConcept.witness
    (by simp [factorGraph, pairScope])

noncomputable def featureMessage (c : MembershipCounts) : Bool → Nat :=
  MessagePassing.factorToVarUpdate
    (fg := factorGraph c)
    (MessagePassing.unitVarToFactor (fg := factorGraph c))
    EmpiricalFactor.joint
    MembershipConcept.feature
    (by simp [factorGraph, pairScope])

theorem witnessMessage_eq (c : MembershipCounts) :
    witnessMessage c = fun b => if b then witnessSupport c else c.neither + c.featureOnly := by
  funext b
  have h :=
    MessagePassing.factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := factorGraph c)
      (μ := MessagePassing.unitVarToFactor (fg := factorGraph c))
      (f := EmpiricalFactor.joint)
      (v := MembershipConcept.witness)
      (u := MembershipConcept.feature)
      (hv := by simp [factorGraph, pairScope])
      (hSingle := pairScope_erase_witness)
  have hsum :
      ∀ x_v : Bool,
        witnessMessage c x_v =
          ∑ x_u : Bool, rawPotential c x_u x_v := by
    intro x_v
    have h2 := congrArg (fun φ => φ x_v) h
    refine h2.trans ?_
    refine Fintype.sum_congr _ _ ?_
    intro x_u
    simp [MessagePassing.unitVarToFactor, factorGraph, pairPotential, rawPotential, pairScope,
      VariableElimination.Factor.extend_apply_eq, VariableElimination.Factor.extend_apply_ne,
      MessagePassing.singletonOtherScopeAssign]
  cases b with
  | false =>
      rw [hsum]
      simp [rawPotential, add_comm]
  | true =>
      rw [hsum]
      simp [rawPotential, witnessSupport, add_comm]

theorem featureMessage_eq (c : MembershipCounts) :
    featureMessage c = fun b => if b then featureSupport c else c.neither + c.witnessOnly := by
  funext b
  have h :=
    MessagePassing.factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := factorGraph c)
      (μ := MessagePassing.unitVarToFactor (fg := factorGraph c))
      (f := EmpiricalFactor.joint)
      (v := MembershipConcept.feature)
      (u := MembershipConcept.witness)
      (hv := by simp [factorGraph, pairScope])
      (hSingle := pairScope_erase_feature)
  have hsum :
      ∀ x_v : Bool,
        featureMessage c x_v =
          ∑ x_u : Bool, rawPotential c x_v x_u := by
    intro x_v
    have h2 := congrArg (fun φ => φ x_v) h
    refine h2.trans ?_
    refine Fintype.sum_congr _ _ ?_
    intro x_u
    simp [MessagePassing.unitVarToFactor, factorGraph, pairPotential, rawPotential, pairScope,
      VariableElimination.Factor.extend_apply_eq, VariableElimination.Factor.extend_apply_ne,
      MessagePassing.singletonOtherScopeAssign]
  cases b with
  | false =>
      rw [hsum]
      simp [rawPotential, add_comm]
  | true =>
      rw [hsum]
      simp [rawPotential, featureSupport, add_comm]

theorem witnessMessage_true (c : MembershipCounts) :
    witnessMessage c true = witnessSupport c := by
  simp [witnessMessage_eq]

theorem featureMessage_true (c : MembershipCounts) :
    featureMessage c true = featureSupport c := by
  simp [featureMessage_eq]

noncomputable def ttConfig (c : MembershipCounts) : (factorGraph c).FullConfig :=
  fun _ => true

noncomputable def ttJointAssign (c : MembershipCounts) :
    VariableElimination.FactorGraph.Assign (fg := factorGraph c) ((factorGraph c).scope EmpiricalFactor.joint) :=
  fun _ _ => true

noncomputable def jointFactorBelief (c : MembershipCounts) :
    VariableElimination.FactorGraph.Assign
        (fg := factorGraph c) ((factorGraph c).scope EmpiricalFactor.joint) → Nat :=
  MessagePassing.factorBelief
    (fg := factorGraph c)
    (MessagePassing.unitVarToFactor (fg := factorGraph c))
    EmpiricalFactor.joint

theorem factorBelief_tt_eq_both (c : MembershipCounts) :
    jointFactorBelief c (ttJointAssign c) =
      c.both := by
  have h :=
    congrArg
      (fun φ =>
        φ (ttJointAssign c))
      (MessagePassing.factorBelief_unitVarToFactor_eq_ofGraph
        (fg := factorGraph c) EmpiricalFactor.joint)
  simpa [jointFactorBelief, factorGraph, pairPotential, rawPotential, pairScope,
    ttConfig, ttJointAssign, VariableElimination.Factor.ofGraph] using h

theorem priorProbWitness_eq_bpMessage_ratio (c : MembershipCounts) :
    priorProbWitness c = (witnessMessage c true : ℝ) / veWeight c [] := by
  rw [witnessMessage_true, veWeight_nil]
  simp [priorProbWitness]

theorem finitePriorProb_semanticInterpretation_witness_eq_bpMessage_ratio
    (c : MembershipCounts) :
    Interpretation.finitePriorProb
        (semanticInterpretation c)
        MembershipConcept.witness =
      (witnessMessage c true : ℝ) / veWeight c [] := by
  rw [finitePriorProb_semanticInterpretation_witness, priorProbWitness_eq_bpMessage_ratio]

theorem extensionalInheritance_eq_bp_ratio (c : MembershipCounts) :
    extensionalInheritance c =
      if featureMessage c true = 0 then
        0
      else
        (jointFactorBelief c (ttJointAssign c) : ℝ) /
            featureMessage c true := by
  rw [featureMessage_true, factorBelief_tt_eq_both]
  simp [extensionalInheritance]

theorem finiteExtensionalProb_semanticInterpretation_feature_witness_eq_bp_ratio
    (c : MembershipCounts) :
    Interpretation.finiteExtensionalProb
        (semanticInterpretation c)
        MembershipConcept.feature
        MembershipConcept.witness =
      if featureMessage c true = 0 then
        0
      else
        (jointFactorBelief c (ttJointAssign c) : ℝ) /
            featureMessage c true := by
  rw [finiteExtensionalProb_semanticInterpretation_feature_witness,
    extensionalInheritance_eq_bp_ratio]

end MembershipCounts

/-- A reusable finite 2x2 witness/feature empirical table, factored out from
the specific `MembershipCounts` presentation so the factor-graph bridge can be
used as a generic finite-table translation theorem. -/
structure FiniteWitnessFeatureTable where
  neither : Nat
  witnessOnly : Nat
  featureOnly : Nat
  both : Nat
  total_pos : 0 < neither + witnessOnly + featureOnly + both

namespace FiniteWitnessFeatureTable

/-- Interpret a generic finite witness/feature table as the concrete
`MembershipCounts` object already used by the inheritance layer. -/
def toMembershipCounts (t : FiniteWitnessFeatureTable) : MembershipCounts where
  neither := t.neither
  witnessOnly := t.witnessOnly
  featureOnly := t.featureOnly
  both := t.both
  total_pos := t.total_pos

/-- Neutral finite-table name for the witness prior quantity. -/
noncomputable def witnessPrior (t : FiniteWitnessFeatureTable) : ℝ :=
  MembershipCounts.priorProbWitness (toMembershipCounts t)

/-- Neutral finite-table name for the feature-to-witness conditional strength. -/
noncomputable def featureToWitnessStrength (t : FiniteWitnessFeatureTable) : ℝ :=
  MembershipCounts.extensionalInheritance (toMembershipCounts t)

/-- Neutral finite-table name for the pointwise log-ratio score. -/
noncomputable def logRatioBits (t : FiniteWitnessFeatureTable) : ℝ :=
  MembershipCounts.pointwiseIntensionalScoreBits (toMembershipCounts t)

/-- The translated tiny factor graph associated to the finite table. -/
abbrev factorGraph (t : FiniteWitnessFeatureTable) :
    FactorGraph MembershipConcept Nat :=
  MembershipCounts.factorGraph (toMembershipCounts t)

/-- Exact VE query weight on the translated tiny factor graph. -/
noncomputable def veWeight (t : FiniteWitnessFeatureTable)
    (constraints : List (Σ v : MembershipConcept, (factorGraph t).stateSpace v)) : Nat :=
  MembershipCounts.veWeight (toMembershipCounts t) constraints

/-- Exact BP witness-side message on the translated tiny factor graph. -/
noncomputable def witnessMessage (t : FiniteWitnessFeatureTable) : Bool → Nat :=
  MembershipCounts.witnessMessage (toMembershipCounts t)

/-- Exact BP feature-side message on the translated tiny factor graph. -/
noncomputable def featureMessage (t : FiniteWitnessFeatureTable) : Bool → Nat :=
  MembershipCounts.featureMessage (toMembershipCounts t)

/-- Exact BP factor belief on the translated tiny factor graph. -/
noncomputable def jointFactorBelief (t : FiniteWitnessFeatureTable) :
    VariableElimination.FactorGraph.Assign
        (fg := factorGraph t) ((factorGraph t).scope MembershipCounts.EmpiricalFactor.joint) → Nat :=
  MembershipCounts.jointFactorBelief (toMembershipCounts t)

/-- Canonical all-true joint assignment on the translated tiny factor graph. -/
noncomputable def ttJointAssign (t : FiniteWitnessFeatureTable) :
    VariableElimination.FactorGraph.Assign
        (fg := factorGraph t) ((factorGraph t).scope MembershipCounts.EmpiricalFactor.joint) :=
  MembershipCounts.ttJointAssign (toMembershipCounts t)

/-- Generic finite-table VE bridge: the witness prior is exactly the VE weight
ratio on the translated tiny factor graph. -/
theorem witnessPrior_eq_veWeight_ratio (t : FiniteWitnessFeatureTable) :
    witnessPrior t =
      (veWeight t [⟨MembershipConcept.witness, true⟩] : ℝ) / veWeight t [] := by
  exact MembershipCounts.priorProbWitness_eq_veWeight_ratio (toMembershipCounts t)

/-- Generic finite-table VE bridge: the feature-to-witness conditional strength
is exactly the corresponding VE weight ratio. -/
theorem featureToWitnessStrength_eq_veWeight_ratio (t : FiniteWitnessFeatureTable) :
    featureToWitnessStrength t =
      if veWeight t [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (veWeight t [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          veWeight t [⟨MembershipConcept.feature, true⟩] := by
  exact MembershipCounts.extensionalInheritance_eq_veWeight_ratio (toMembershipCounts t)

/-- Generic finite-table VE bridge: the finite-table log-ratio score is exactly
the VE query score induced by the translated graph. -/
theorem logRatioBits_eq_ve_query_score (t : FiniteWitnessFeatureTable) :
    logRatioBits t =
      logRatioInformationGainFromEvidence
        (if veWeight t [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (veWeight t [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            veWeight t [⟨MembershipConcept.feature, true⟩])
        ((veWeight t [⟨MembershipConcept.witness, true⟩] : ℝ) / veWeight t []) := by
  exact MembershipCounts.pointwiseIntensionalScoreBits_eq_ve_query_score (toMembershipCounts t)

/-- Generic finite-table BP bridge: the witness prior is also recovered by the
BP message ratio on the translated graph. -/
theorem witnessPrior_eq_bpMessage_ratio (t : FiniteWitnessFeatureTable) :
    witnessPrior t = (witnessMessage t true : ℝ) / veWeight t [] := by
  exact MembershipCounts.priorProbWitness_eq_bpMessage_ratio (toMembershipCounts t)

/-- Generic finite-table BP bridge: the feature-to-witness conditional strength
is recovered by the BP factor-belief/message ratio on the translated graph. -/
theorem featureToWitnessStrength_eq_bp_ratio (t : FiniteWitnessFeatureTable) :
    featureToWitnessStrength t =
      if featureMessage t true = 0 then
        0
      else
        (jointFactorBelief t (ttJointAssign t) : ℝ) / featureMessage t true := by
  simpa [featureToWitnessStrength, featureMessage, jointFactorBelief,
    ttJointAssign, toMembershipCounts] using
    MembershipCounts.extensionalInheritance_eq_bp_ratio (toMembershipCounts t)

end FiniteWitnessFeatureTable

/-- A generic finite feature/witness count table, widening the Boolean 2x2
bridge to arbitrary finite feature and witness state spaces while keeping the
same one-factor exact VE/BP semantics. -/
structure FiniteFeatureWitnessCountTable
    (Feature Witness : Type) [Fintype Feature] [Fintype Witness] where
  count : Feature → Witness → Nat
  total_pos : 0 < ∑ feature : Feature, ∑ witness : Witness, count feature witness

namespace FiniteFeatureWitnessCountTable

variable {Feature Witness : Type} [Fintype Feature] [Fintype Witness]

inductive CountFactor
  | joint
  deriving DecidableEq, Fintype

/-- Total mass of the finite feature/witness count table. -/
noncomputable def total (t : FiniteFeatureWitnessCountTable Feature Witness) : Nat :=
  ∑ feature : Feature, ∑ witness : Witness, t.count feature witness

/-- Marginal support of a feature state. -/
noncomputable def featureSupport
    (t : FiniteFeatureWitnessCountTable Feature Witness) (feature : Feature) : Nat :=
  ∑ witness : Witness, t.count feature witness

/-- Marginal support of a witness state. -/
noncomputable def witnessSupport
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) : Nat :=
  ∑ feature : Feature, t.count feature witness

/-- Prior probability of a witness state in the finite table. -/
noncomputable def witnessPrior
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) : ℝ :=
  (witnessSupport t witness : ℝ) / total t

/-- Conditional witness strength given a feature state. -/
noncomputable def witnessGivenFeatureStrength
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) : ℝ :=
  if featureSupport t feature = 0 then
    0
  else
    (t.count feature witness : ℝ) / featureSupport t feature

/-- Pointwise log-ratio score for a feature/witness pair. -/
noncomputable def logRatioBits
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) : ℝ :=
  logRatioInformationGainFromEvidence
    (witnessGivenFeatureStrength t feature witness)
    (witnessPrior t witness)

/-- The one-factor graph whose joint potential is exactly the finite count
table. -/
def factorGraph (t : FiniteFeatureWitnessCountTable Feature Witness) :
    FactorGraph MembershipConcept Nat where
  stateSpace
    | MembershipConcept.feature => Feature
    | MembershipConcept.witness => Witness
  factors := CountFactor
  scope := fun _ => MembershipCounts.pairScope
  potential := fun _ x =>
    t.count
      (x MembershipConcept.feature (by simp [MembershipCounts.pairScope]))
      (x MembershipConcept.witness (by simp [MembershipCounts.pairScope]))

noncomputable def fullConfigEquiv
    (t : FiniteFeatureWitnessCountTable Feature Witness) :
    (factorGraph t).FullConfig ≃ Feature × Witness where
  toFun x := (x MembershipConcept.feature, x MembershipConcept.witness)
  invFun p := fun
    | MembershipConcept.feature => p.1
    | MembershipConcept.witness => p.2
  left_inv x := by
    funext v
    cases v <;> rfl
  right_inv p := by
    cases p
    rfl

instance (t : FiniteFeatureWitnessCountTable Feature Witness) :
    ∀ v : MembershipConcept, Fintype ((factorGraph t).stateSpace v) := by
  intro v
  cases v <;> dsimp [factorGraph] <;> infer_instance

noncomputable instance (t : FiniteFeatureWitnessCountTable Feature Witness) :
    ∀ v : MembershipConcept, DecidableEq ((factorGraph t).stateSpace v) := by
  intro v
  cases v <;> dsimp [factorGraph] <;> infer_instance

instance (t : FiniteFeatureWitnessCountTable Feature Witness) :
    Fintype (factorGraph t).factors := by
  dsimp [factorGraph]
  infer_instance

instance (t : FiniteFeatureWitnessCountTable Feature Witness) :
    DecidableEq (factorGraph t).factors := by
  dsimp [factorGraph]
  infer_instance

noncomputable instance (t : FiniteFeatureWitnessCountTable Feature Witness) :
    Fintype (factorGraph t).FullConfig :=
  Fintype.ofEquiv (Feature × Witness) (fullConfigEquiv t).symm

/-- The explicit singleton factor list corresponding to the count-table graph. -/
noncomputable def factors
    (t : FiniteFeatureWitnessCountTable Feature Witness) :
    List (VariableElimination.Factor (fg := factorGraph t)) :=
  [VariableElimination.Factor.ofGraph (fg := factorGraph t) CountFactor.joint]

/-- Exact VE query weight on the generic finite table graph. -/
noncomputable def veWeight
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (constraints : List (Σ v : MembershipConcept, (factorGraph t).stateSpace v)) : Nat := by
  classical
  letI : Fintype (factorGraph t).FullConfig :=
    t.instFintypeFullConfigMembershipConceptNatFactorGraph
  let f := VariableElimination.combineAll (fg := factorGraph t) (factors t)
  let cfgs : Finset ((factorGraph t).FullConfig) := Finset.univ
  let satisfies : (factorGraph t).FullConfig → Prop :=
    fun x => ∀ c ∈ constraints, x c.1 = c.2
  exact
    cfgs.sum (fun x =>
      if satisfies x then
        f.potential (VariableElimination.FactorGraph.fullAssign (fg := factorGraph t) x f.scope)
      else 0)

/-- Direct pair-level semantics for the same constraint set. -/
def pairSatisfies
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (constraints : List (Σ v : MembershipConcept, (factorGraph t).stateSpace v))
    (p : Feature × Witness) : Prop :=
  ∀ q ∈ constraints,
    match q with
    | ⟨MembershipConcept.feature, y⟩ => p.1 = y
    | ⟨MembershipConcept.witness, y⟩ => p.2 = y

noncomputable def pairWeight
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (constraints : List (Σ v : MembershipConcept, (factorGraph t).stateSpace v)) : Nat :=
  ∑ p : Feature × Witness, if pairSatisfies t constraints p then t.count p.1 p.2 else 0

noncomputable def combinedFactor
    (t : FiniteFeatureWitnessCountTable Feature Witness) :
    VariableElimination.Factor (fg := factorGraph t) :=
  VariableElimination.combineAll (fg := factorGraph t) (factors t)

theorem combinedFactor_apply
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (x : (factorGraph t).FullConfig) :
    (combinedFactor t).potential
        (VariableElimination.FactorGraph.fullAssign
          (fg := factorGraph t) x (combinedFactor t).scope) =
      t.count (x MembershipConcept.feature) (x MembershipConcept.witness) := by
  simp [combinedFactor, factors, VariableElimination.combineAll,
    VariableElimination.oneFactor, VariableElimination.Factor.mul,
    VariableElimination.Factor.ofGraph, VariableElimination.FactorGraph.fullAssign,
    VariableElimination.FactorGraph.restrict, factorGraph, MembershipCounts.pairScope]

theorem veWeight_eq_pairWeight
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (constraints : List (Σ v : MembershipConcept, (factorGraph t).stateSpace v)) :
    veWeight t constraints = pairWeight t constraints := by
  classical
  letI : Fintype (factorGraph t).FullConfig :=
    t.instFintypeFullConfigMembershipConceptNatFactorGraph
  have hsum :
      (∑ x : (factorGraph t).FullConfig,
          if (∀ q ∈ constraints, x q.1 = q.2) then
            (combinedFactor t).potential
              (VariableElimination.FactorGraph.fullAssign
                (fg := factorGraph t) x (combinedFactor t).scope)
          else 0) =
        ∑ p : Feature × Witness,
          if pairSatisfies t constraints p then t.count p.1 p.2 else 0 := by
    refine Fintype.sum_equiv (fullConfigEquiv t)
      (fun x =>
        if (∀ q ∈ constraints, x q.1 = q.2) then
          (combinedFactor t).potential
            (VariableElimination.FactorGraph.fullAssign
              (fg := factorGraph t) x (combinedFactor t).scope)
        else 0)
      (fun p =>
        if pairSatisfies t constraints p then t.count p.1 p.2 else 0) ?_
    intro x
    have hSat :
        (∀ q ∈ constraints, x q.1 = q.2) ↔
          pairSatisfies t constraints ((fullConfigEquiv t) x) := by
      constructor
      · intro hx q hq
        rcases q with ⟨v, y⟩
        cases v <;> exact hx ⟨_, y⟩ hq
      · intro hx q hq
        rcases q with ⟨v, y⟩
        cases v <;> exact hx ⟨_, y⟩ hq
    have hpot := combinedFactor_apply t x
    by_cases hRaw : ∀ q ∈ constraints, x q.1 = q.2
    · have hp' : pairSatisfies t constraints ((fullConfigEquiv t) x) :=
        hSat.mp hRaw
      change
        (if (∀ q ∈ constraints, x q.1 = q.2) then
          (combinedFactor t).potential
            (VariableElimination.FactorGraph.fullAssign
              (fg := factorGraph t) x (combinedFactor t).scope)
        else 0) =
          (if pairSatisfies t constraints ((fullConfigEquiv t) x) then
            t.count ((fullConfigEquiv t) x).1 ((fullConfigEquiv t) x).2
          else 0)
      rw [if_pos hRaw, if_pos hp']
      simpa [fullConfigEquiv] using hpot
    · have hp' : ¬ pairSatisfies t constraints ((fullConfigEquiv t) x) :=
        fun hp' => hRaw (hSat.mpr hp')
      change
        (if (∀ q ∈ constraints, x q.1 = q.2) then
          (combinedFactor t).potential
            (VariableElimination.FactorGraph.fullAssign
              (fg := factorGraph t) x (combinedFactor t).scope)
        else 0) =
          (if pairSatisfies t constraints ((fullConfigEquiv t) x) then
            t.count ((fullConfigEquiv t) x).1 ((fullConfigEquiv t) x).2
          else 0)
      rw [if_neg hRaw, if_neg hp']
  simpa [veWeight, pairWeight, combinedFactor, factors] using hsum

theorem pairWeight_nil (t : FiniteFeatureWitnessCountTable Feature Witness) :
    pairWeight t [] = total t := by
  simp [pairWeight, pairSatisfies, total, Fintype.sum_prod_type]

theorem pairWeight_feature
    (t : FiniteFeatureWitnessCountTable Feature Witness) (feature : Feature) :
    pairWeight t [⟨MembershipConcept.feature, feature⟩] = featureSupport t feature := by
  simp [pairWeight, pairSatisfies, featureSupport, Fintype.sum_prod_type]

theorem pairWeight_witness
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) :
    pairWeight t [⟨MembershipConcept.witness, witness⟩] = witnessSupport t witness := by
  simp [pairWeight, pairSatisfies, witnessSupport, Fintype.sum_prod_type]

theorem pairWeight_feature_witness
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    pairWeight t
        [⟨MembershipConcept.feature, feature⟩, ⟨MembershipConcept.witness, witness⟩] =
      t.count feature witness := by
  classical
  have hSat :
      ∀ x : Feature, ∀ x_1 : Witness,
        pairSatisfies t
            [⟨MembershipConcept.feature, feature⟩, ⟨MembershipConcept.witness, witness⟩]
            (x, x_1) ↔ x = feature ∧ x_1 = witness := by
    intro x x_1
    constructor
    · intro hx
      constructor
      · exact hx ⟨MembershipConcept.feature, feature⟩ (by simp)
      · exact hx ⟨MembershipConcept.witness, witness⟩ (by simp)
    · rintro ⟨rfl, rfl⟩ q hq
      rcases q with ⟨v, y⟩
      cases v <;> simp at hq <;> simp [hq]
  rw [pairWeight, Fintype.sum_prod_type]
  simp_rw [hSat]
  have hInner :
      ∀ x : Feature,
        (∑ x_1 : Witness, if x = feature ∧ x_1 = witness then t.count x x_1 else 0) =
          if x = feature then t.count feature witness else 0 := by
    intro x
    by_cases hx : x = feature
    · subst hx
      simp
    · simp [hx]
  simp_rw [hInner]
  classical
  rw [Fintype.sum_eq_single feature]
  · simp
  · intro x hx
    simp [hx]

theorem veWeight_nil (t : FiniteFeatureWitnessCountTable Feature Witness) :
    veWeight t [] = total t := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_nil t

theorem veWeight_feature
    (t : FiniteFeatureWitnessCountTable Feature Witness) (feature : Feature) :
    veWeight t [⟨MembershipConcept.feature, feature⟩] = featureSupport t feature := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_feature t feature

theorem veWeight_witness
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) :
    veWeight t [⟨MembershipConcept.witness, witness⟩] = witnessSupport t witness := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_witness t witness

theorem veWeight_feature_witness
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    veWeight t
        [⟨MembershipConcept.feature, feature⟩, ⟨MembershipConcept.witness, witness⟩] =
      t.count feature witness := by
  rw [veWeight_eq_pairWeight]
  exact pairWeight_feature_witness t feature witness

theorem witnessPrior_eq_veWeight_ratio
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) :
    witnessPrior t witness =
      (veWeight t [⟨MembershipConcept.witness, witness⟩] : ℝ) / veWeight t [] := by
  rw [veWeight_witness, veWeight_nil]
  simp [witnessPrior]

theorem witnessGivenFeatureStrength_eq_veWeight_ratio
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    witnessGivenFeatureStrength t feature witness =
      if veWeight t [⟨MembershipConcept.feature, feature⟩] = 0 then
        0
      else
        (veWeight t [⟨MembershipConcept.feature, feature⟩,
            ⟨MembershipConcept.witness, witness⟩] : ℝ) /
          veWeight t [⟨MembershipConcept.feature, feature⟩] := by
  rw [veWeight_feature, veWeight_feature_witness]
  simp [witnessGivenFeatureStrength]

theorem logRatioBits_eq_ve_query_score
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    logRatioBits t feature witness =
      logRatioInformationGainFromEvidence
        (if veWeight t [⟨MembershipConcept.feature, feature⟩] = 0 then
          0
        else
          (veWeight t [⟨MembershipConcept.feature, feature⟩,
              ⟨MembershipConcept.witness, witness⟩] : ℝ) /
            veWeight t [⟨MembershipConcept.feature, feature⟩])
        ((veWeight t [⟨MembershipConcept.witness, witness⟩] : ℝ) /
          veWeight t []) := by
  unfold logRatioBits
  rw [witnessGivenFeatureStrength_eq_veWeight_ratio,
    witnessPrior_eq_veWeight_ratio]

noncomputable def witnessMessage
    (t : FiniteFeatureWitnessCountTable Feature Witness) : Witness → Nat :=
  MessagePassing.factorToVarUpdate
    (fg := factorGraph t)
    (MessagePassing.unitVarToFactor (fg := factorGraph t))
    CountFactor.joint
    MembershipConcept.witness
    (by simp [factorGraph, MembershipCounts.pairScope])

noncomputable def featureMessage
    (t : FiniteFeatureWitnessCountTable Feature Witness) : Feature → Nat :=
  MessagePassing.factorToVarUpdate
    (fg := factorGraph t)
    (MessagePassing.unitVarToFactor (fg := factorGraph t))
    CountFactor.joint
    MembershipConcept.feature
    (by simp [factorGraph, MembershipCounts.pairScope])

theorem witnessMessage_eq
    (t : FiniteFeatureWitnessCountTable Feature Witness) :
    witnessMessage t = fun witness => witnessSupport t witness := by
  funext witness
  have h :=
    MessagePassing.factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := factorGraph t)
      (μ := MessagePassing.unitVarToFactor (fg := factorGraph t))
      (f := CountFactor.joint)
      (v := MembershipConcept.witness)
      (u := MembershipConcept.feature)
      (hv := by simp [factorGraph, MembershipCounts.pairScope])
      (hSingle := MembershipCounts.pairScope_erase_witness)
  rw [witnessSupport]
  refine (congrArg (fun φ => φ witness) h).trans ?_
  refine Fintype.sum_congr _ _ ?_
  intro feature
  simp [MessagePassing.unitVarToFactor, factorGraph, MembershipCounts.pairScope,
    VariableElimination.Factor.extend_apply_eq, VariableElimination.Factor.extend_apply_ne,
    MessagePassing.singletonOtherScopeAssign]

theorem featureMessage_eq
    (t : FiniteFeatureWitnessCountTable Feature Witness) :
    featureMessage t = fun feature => featureSupport t feature := by
  funext feature
  have h :=
    MessagePassing.factorToVarUpdate_eq_sum_of_otherScopeSingleton
      (fg := factorGraph t)
      (μ := MessagePassing.unitVarToFactor (fg := factorGraph t))
      (f := CountFactor.joint)
      (v := MembershipConcept.feature)
      (u := MembershipConcept.witness)
      (hv := by simp [factorGraph, MembershipCounts.pairScope])
      (hSingle := MembershipCounts.pairScope_erase_feature)
  rw [featureSupport]
  refine (congrArg (fun φ => φ feature) h).trans ?_
  refine Fintype.sum_congr _ _ ?_
  intro witness
  simp [MessagePassing.unitVarToFactor, factorGraph, MembershipCounts.pairScope,
    VariableElimination.Factor.extend_apply_eq, VariableElimination.Factor.extend_apply_ne,
    MessagePassing.singletonOtherScopeAssign]

theorem witnessMessage_value
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) :
    witnessMessage t witness = witnessSupport t witness := by
  simp [witnessMessage_eq]

theorem featureMessage_value
    (t : FiniteFeatureWitnessCountTable Feature Witness) (feature : Feature) :
    featureMessage t feature = featureSupport t feature := by
  simp [featureMessage_eq]

noncomputable def jointAssign
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    VariableElimination.FactorGraph.Assign
        (fg := factorGraph t) ((factorGraph t).scope CountFactor.joint) :=
  fun v _ =>
    match v with
    | MembershipConcept.feature => feature
    | MembershipConcept.witness => witness

noncomputable def jointFactorBelief
    (t : FiniteFeatureWitnessCountTable Feature Witness) :
    VariableElimination.FactorGraph.Assign
        (fg := factorGraph t) ((factorGraph t).scope CountFactor.joint) → Nat :=
  MessagePassing.factorBelief
    (fg := factorGraph t)
    (MessagePassing.unitVarToFactor (fg := factorGraph t))
    CountFactor.joint

theorem jointFactorBelief_eq_count
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    jointFactorBelief t (jointAssign t feature witness) = t.count feature witness := by
  have h :=
    congrArg
      (fun φ =>
        φ (jointAssign t feature witness))
      (MessagePassing.factorBelief_unitVarToFactor_eq_ofGraph
        (fg := factorGraph t) CountFactor.joint)
  simpa [jointFactorBelief, jointAssign, factorGraph, MembershipCounts.pairScope,
    VariableElimination.Factor.ofGraph] using h

theorem witnessPrior_eq_bpMessage_ratio
    (t : FiniteFeatureWitnessCountTable Feature Witness) (witness : Witness) :
    witnessPrior t witness =
      (witnessMessage t witness : ℝ) / veWeight t [] := by
  rw [witnessMessage_value, veWeight_nil]
  simp [witnessPrior]

theorem witnessGivenFeatureStrength_eq_bp_ratio
    (t : FiniteFeatureWitnessCountTable Feature Witness)
    (feature : Feature) (witness : Witness) :
    witnessGivenFeatureStrength t feature witness =
      if featureMessage t feature = 0 then
        0
      else
        (jointFactorBelief t (jointAssign t feature witness) : ℝ) /
          featureMessage t feature := by
  rw [featureMessage_value, jointFactorBelief_eq_count]
  simp [witnessGivenFeatureStrength]

/-- The original Boolean 2x2 witness/feature table as a specialization of the
generic finite feature/witness count-table bridge. -/
noncomputable def ofFiniteWitnessFeatureTable
    (t : FiniteWitnessFeatureTable) : FiniteFeatureWitnessCountTable Bool Bool where
  count := fun feature witness =>
    MembershipCounts.rawPotential (FiniteWitnessFeatureTable.toMembershipCounts t) feature witness
  total_pos := by
    have h := t.total_pos
    simp [MembershipCounts.rawPotential,
      FiniteWitnessFeatureTable.toMembershipCounts] at h ⊢
    omega

end FiniteFeatureWitnessCountTable

namespace Interpretation

section FinitePairBridge

variable {Carrier Obj Attr : Type*} [Fintype Obj] [Nonempty Obj]

private abbrev NeitherRegion
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :=
  {x : Obj // x ∉ (I.meaning feature).extent ∧ x ∉ (I.meaning witness).extent}

private abbrev WitnessOnlyRegion
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :=
  {x : Obj // x ∉ (I.meaning feature).extent ∧ x ∈ (I.meaning witness).extent}

private abbrev FeatureOnlyRegion
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :=
  {x : Obj // x ∈ (I.meaning feature).extent ∧ x ∉ (I.meaning witness).extent}

private abbrev BothRegion
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :=
  {x : Obj // x ∈ (I.meaning feature).extent ∧ x ∈ (I.meaning witness).extent}

private noncomputable def pairPartitionEquiv
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Obj ≃ Sum (NeitherRegion I feature witness)
      (Sum (WitnessOnlyRegion I feature witness)
        (Sum (FeatureOnlyRegion I feature witness)
          (BothRegion I feature witness))) where
  toFun x := by
    classical
    by_cases hFeature : x ∈ (I.meaning feature).extent
    · by_cases hWitness : x ∈ (I.meaning witness).extent
      · exact Sum.inr (Sum.inr (Sum.inr ⟨x, hFeature, hWitness⟩))
      · exact Sum.inr (Sum.inr (Sum.inl ⟨x, hFeature, hWitness⟩))
    · by_cases hWitness : x ∈ (I.meaning witness).extent
      · exact Sum.inr (Sum.inl ⟨x, hFeature, hWitness⟩)
      · exact Sum.inl ⟨x, hFeature, hWitness⟩
  invFun s :=
    match s with
    | Sum.inl x => x.1
    | Sum.inr (Sum.inl x) => x.1
    | Sum.inr (Sum.inr (Sum.inl x)) => x.1
    | Sum.inr (Sum.inr (Sum.inr x)) => x.1
  left_inv x := by
    classical
    by_cases hFeature : x ∈ (I.meaning feature).extent <;>
      by_cases hWitness : x ∈ (I.meaning witness).extent <;>
      simp [hFeature, hWitness]
  right_inv s := by
    cases s with
    | inl x =>
        simp [x.2.1, x.2.2]
    | inr s =>
        cases s with
        | inl x =>
            simp [x.2.1, x.2.2]
        | inr s =>
            cases s with
            | inl x =>
                simp [x.2.1, x.2.2]
            | inr x =>
                simp [x.2.1, x.2.2]

private noncomputable def witnessExtentEquiv
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    {x : Obj // x ∈ (I.meaning witness).extent} ≃
      Sum (WitnessOnlyRegion I feature witness) (BothRegion I feature witness) where
  toFun x := by
    classical
    by_cases hFeature : x.1 ∈ (I.meaning feature).extent
    · exact Sum.inr ⟨x.1, hFeature, x.2⟩
    · exact Sum.inl ⟨x.1, hFeature, x.2⟩
  invFun s :=
    match s with
    | Sum.inl x => ⟨x.1, x.2.2⟩
    | Sum.inr x => ⟨x.1, x.2.2⟩
  left_inv x := by
    classical
    by_cases hFeature : x.1 ∈ (I.meaning feature).extent <;>
      simp [hFeature]
  right_inv s := by
    cases s with
    | inl x =>
        simp [x.2.1]
    | inr x =>
        simp [x.2.1]

private noncomputable def featureExtentEquiv
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    {x : Obj // x ∈ (I.meaning feature).extent} ≃
      Sum (FeatureOnlyRegion I feature witness) (BothRegion I feature witness) where
  toFun x := by
    classical
    by_cases hWitness : x.1 ∈ (I.meaning witness).extent
    · exact Sum.inr ⟨x.1, x.2, hWitness⟩
    · exact Sum.inl ⟨x.1, x.2, hWitness⟩
  invFun s :=
    match s with
    | Sum.inl x => ⟨x.1, x.2.1⟩
    | Sum.inr x => ⟨x.1, x.2.1⟩
  left_inv x := by
    classical
    by_cases hWitness : x.1 ∈ (I.meaning witness).extent <;>
      simp [hWitness]
  right_inv s := by
    cases s with
    | inl x =>
        simp [x.2.2]
    | inr x =>
        simp [x.2.2]

/-- Collapse an arbitrary finite interpreted concept pair into the reusable 2x2
witness/feature contingency table that powers the factor-graph bridge. -/
noncomputable def toFiniteWitnessFeatureTable
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) : FiniteWitnessFeatureTable where
  neither := Fintype.card (NeitherRegion I feature witness)
  witnessOnly := Fintype.card (WitnessOnlyRegion I feature witness)
  featureOnly := Fintype.card (FeatureOnlyRegion I feature witness)
  both := Fintype.card (BothRegion I feature witness)
  total_pos := by
    classical
    have hCard :
        Fintype.card Obj =
          Fintype.card (NeitherRegion I feature witness) +
            (Fintype.card (WitnessOnlyRegion I feature witness) +
              (Fintype.card (FeatureOnlyRegion I feature witness) +
                Fintype.card (BothRegion I feature witness))) := by
      rw [Fintype.card_congr (pairPartitionEquiv I feature witness)]
      simp
    have hPos : 0 < Fintype.card Obj := Fintype.card_pos_iff.mpr inferInstance
    rw [hCard] at hPos
    simpa [Nat.add_assoc]
      using hPos

theorem toFiniteWitnessFeatureTable_total
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    (toFiniteWitnessFeatureTable I feature witness).neither +
        (toFiniteWitnessFeatureTable I feature witness).witnessOnly +
        (toFiniteWitnessFeatureTable I feature witness).featureOnly +
        (toFiniteWitnessFeatureTable I feature witness).both =
      Fintype.card Obj := by
  classical
  unfold toFiniteWitnessFeatureTable
  rw [Fintype.card_congr (pairPartitionEquiv I feature witness)]
  simp [Nat.add_assoc]

theorem extentCount_witness_eq_toFiniteWitnessFeatureTable
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.extentCount I witness =
      (toFiniteWitnessFeatureTable I feature witness).witnessOnly +
        (toFiniteWitnessFeatureTable I feature witness).both := by
  classical
  unfold Mettapedia.Logic.IntensionalInheritance.Interpretation.extentCount
    toFiniteWitnessFeatureTable
  rw [Fintype.card_congr (witnessExtentEquiv I feature witness)]
  simp

theorem extentCount_feature_eq_toFiniteWitnessFeatureTable
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.extentCount I feature =
      (toFiniteWitnessFeatureTable I feature witness).featureOnly +
        (toFiniteWitnessFeatureTable I feature witness).both := by
  classical
  unfold Mettapedia.Logic.IntensionalInheritance.Interpretation.extentCount
    toFiniteWitnessFeatureTable
  rw [Fintype.card_congr (featureExtentEquiv I feature witness)]
  simp

@[simp] theorem jointExtentCount_eq_toFiniteWitnessFeatureTable
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.jointExtentCount I feature witness =
      (toFiniteWitnessFeatureTable I feature witness).both := by
  rfl

theorem finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb I witness =
      FiniteWitnessFeatureTable.witnessPrior
        (toFiniteWitnessFeatureTable I feature witness) := by
  rw [Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb]
  rw [extentCount_witness_eq_toFiniteWitnessFeatureTable
    (I := I) (feature := feature) (witness := witness)]
  rw [FiniteWitnessFeatureTable.witnessPrior]
  simp [FiniteWitnessFeatureTable.toMembershipCounts, MembershipCounts.priorProbWitness,
    MembershipCounts.witnessSupport, MembershipCounts.total, toFiniteWitnessFeatureTable_total]

theorem finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb I feature witness =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (toFiniteWitnessFeatureTable I feature witness) := by
  rw [Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb]
  rw [extentCount_feature_eq_toFiniteWitnessFeatureTable
    (I := I) (feature := feature) (witness := witness)]
  rw [jointExtentCount_eq_toFiniteWitnessFeatureTable
    (I := I) (feature := feature) (witness := witness)]
  simp [FiniteWitnessFeatureTable.featureToWitnessStrength, FiniteWitnessFeatureTable.toMembershipCounts,
    MembershipCounts.extensionalInheritance, MembershipCounts.featureSupport]

theorem finitePointwiseLogRatioBits_eq_toFiniteWitnessFeatureTable
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePointwiseLogRatioBits
        I feature witness =
      FiniteWitnessFeatureTable.logRatioBits
        (toFiniteWitnessFeatureTable I feature witness) := by
  rw [Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePointwiseLogRatioBits]
  rw [finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior
    (I := I) (feature := feature) (witness := witness)]
  rw [finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength
    (I := I) (feature := feature) (witness := witness)]
  unfold FiniteWitnessFeatureTable.logRatioBits FiniteWitnessFeatureTable.featureToWitnessStrength
    FiniteWitnessFeatureTable.witnessPrior FiniteWitnessFeatureTable.toMembershipCounts
    MembershipCounts.pointwiseIntensionalScoreBits logRatioInformationGainFromEvidence
  rfl

theorem finitePriorProb_eq_veWeight_ratio
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb I witness =
      (FiniteWitnessFeatureTable.veWeight
        (toFiniteWitnessFeatureTable I feature witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (toFiniteWitnessFeatureTable I feature witness) [] := by
  rw [finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior]
  exact FiniteWitnessFeatureTable.witnessPrior_eq_veWeight_ratio _

theorem finiteExtensionalProb_eq_veWeight_ratio
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb I feature witness =
      if FiniteWitnessFeatureTable.veWeight
          (toFiniteWitnessFeatureTable I feature witness)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (toFiniteWitnessFeatureTable I feature witness)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (toFiniteWitnessFeatureTable I feature witness)
            [⟨MembershipConcept.feature, true⟩] := by
  rw [finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength]
  exact FiniteWitnessFeatureTable.featureToWitnessStrength_eq_veWeight_ratio _

theorem finitePointwiseLogRatioBits_eq_ve_query_score
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePointwiseLogRatioBits
        I feature witness =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (toFiniteWitnessFeatureTable I feature witness)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (toFiniteWitnessFeatureTable I feature witness)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (toFiniteWitnessFeatureTable I feature witness)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (toFiniteWitnessFeatureTable I feature witness)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (toFiniteWitnessFeatureTable I feature witness) []) := by
  rw [finitePointwiseLogRatioBits_eq_toFiniteWitnessFeatureTable]
  exact FiniteWitnessFeatureTable.logRatioBits_eq_ve_query_score _

theorem finitePriorProb_eq_bp_ratio
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb I witness =
      (FiniteWitnessFeatureTable.witnessMessage
        (toFiniteWitnessFeatureTable I feature witness) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (toFiniteWitnessFeatureTable I feature witness) [] := by
  rw [finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior]
  exact FiniteWitnessFeatureTable.witnessPrior_eq_bpMessage_ratio _

theorem finiteExtensionalProb_eq_bp_ratio
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Carrier Obj Attr)
    (feature witness : Carrier) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb I feature witness =
      if FiniteWitnessFeatureTable.featureMessage
          (toFiniteWitnessFeatureTable I feature witness) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (toFiniteWitnessFeatureTable I feature witness)
          (FiniteWitnessFeatureTable.ttJointAssign
            (toFiniteWitnessFeatureTable I feature witness)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (toFiniteWitnessFeatureTable I feature witness) true := by
  rw [finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength]
  exact FiniteWitnessFeatureTable.featureToWitnessStrength_eq_bp_ratio _

end FinitePairBridge

end Interpretation

namespace AbstractInheritance

section FormedConceptFinitePairBridge

variable {Obj Attr Q : Type*}
variable [Preorder Q] [Fintype Obj] [Nonempty Obj] [Fintype Attr]

noncomputable def formedConceptInheritanceTable
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    FiniteWitnessFeatureTable :=
  Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
    (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
    subConcept superConcept

theorem finitePriorProb_formedConceptInterpretation_eq_toFiniteWitnessFeatureTable_witnessPrior
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) witness =
      FiniteWitnessFeatureTable.witnessPrior
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) := by
  simpa using
    Interpretation.finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finiteExtensionalProb_formedConceptInterpretation_eq_toFiniteWitnessFeatureTable_strength
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finitePointwiseLogRatioBits_formedConceptInterpretation_eq_toFiniteWitnessFeatureTable
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePointwiseLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness =
      FiniteWitnessFeatureTable.logRatioBits
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) := by
  simpa using
    Interpretation.finitePointwiseLogRatioBits_eq_toFiniteWitnessFeatureTable
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finitePriorProb_formedConceptInterpretation_eq_veWeight_ratio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) witness =
      (FiniteWitnessFeatureTable.veWeight
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) [] := by
  simpa using
    Interpretation.finitePriorProb_eq_veWeight_ratio
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finiteExtensionalProb_formedConceptInterpretation_eq_veWeight_ratio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness =
      if FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
            [⟨MembershipConcept.feature, true⟩] := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_veWeight_ratio
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finitePointwiseLogRatioBits_formedConceptInterpretation_eq_ve_query_score
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePointwiseLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) []) := by
  simpa using
    Interpretation.finitePointwiseLogRatioBits_eq_ve_query_score
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finitePriorProb_formedConceptInterpretation_eq_bp_ratio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) witness =
      (FiniteWitnessFeatureTable.witnessMessage
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) [] := by
  simpa using
    Interpretation.finitePriorProb_eq_bp_ratio
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finiteExtensionalProb_formedConceptInterpretation_eq_bp_ratio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteExtensionalProb
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness =
      if FiniteWitnessFeatureTable.featureMessage
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) feature witness) true := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_bp_ratio
      (I := Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
      (feature := feature) (witness := witness)

theorem finiteInheritancePrior_formedConceptInterpretation_eq_veWeight_ratio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) superConcept =
      (FiniteWitnessFeatureTable.veWeight
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
          subConcept superConcept)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept) [] := by
  simpa [Interpretation.finiteInheritancePrior_eq] using
    finitePriorProb_formedConceptInterpretation_eq_veWeight_ratio
      (G := G) (M := M) (feature := subConcept) (witness := superConcept)

theorem finiteInheritanceStrength_formedConceptInterpretation_eq_veWeight_ratio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] := by
  simpa [Interpretation.finiteInheritanceStrength_eq] using
    finiteExtensionalProb_formedConceptInterpretation_eq_veWeight_ratio
      (G := G) (M := M) (feature := subConcept) (witness := superConcept)

theorem finiteInheritanceLogRatioBits_formedConceptInterpretation_eq_veQueryScore
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
                subConcept superConcept)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
                subConcept superConcept) []) := by
  simpa [Interpretation.finiteInheritanceLogRatioBits_eq] using
    finitePointwiseLogRatioBits_formedConceptInterpretation_eq_ve_query_score
      (G := G) (M := M) (feature := subConcept) (witness := superConcept)

theorem finiteInheritancePrior_formedConceptInterpretation_eq_bpRatio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) superConcept =
      (FiniteWitnessFeatureTable.witnessMessage
        (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
          subConcept superConcept) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept) [] := by
  simpa [Interpretation.finiteInheritancePrior_eq] using
    finitePriorProb_formedConceptInterpretation_eq_bp_ratio
      (G := G) (M := M) (feature := subConcept) (witness := superConcept)

theorem finiteInheritanceStrength_formedConceptInterpretation_eq_bpRatio
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.featureMessage
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
            subConcept superConcept)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Mettapedia.Logic.IntensionalInheritance.Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
              subConcept superConcept) true := by
  simpa [Interpretation.finiteInheritanceStrength_eq] using
    finiteExtensionalProb_formedConceptInterpretation_eq_bp_ratio
      (G := G) (M := M) (feature := subConcept) (witness := superConcept)

/-- Supported formed-concept exactness surface for the extensional inheritance
query family: prior, strength, and log-ratio are read exactly through the
generated finite witness/feature table. Mixed ASSOC/PAT channels are handled
separately in `PLNIntensionalAssocPatClosure`. -/
theorem formedConceptInheritance_exact_via_table
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) superConcept =
      FiniteWitnessFeatureTable.witnessPrior
        (formedConceptInheritanceTable G M subConcept superConcept)
    ∧
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (formedConceptInheritanceTable G M subConcept superConcept)
    ∧
    Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      FiniteWitnessFeatureTable.logRatioBits
        (formedConceptInheritanceTable G M subConcept superConcept) := by
  constructor
  · simpa [formedConceptInheritanceTable, Interpretation.finiteInheritancePrior_eq] using
      finitePriorProb_formedConceptInterpretation_eq_toFiniteWitnessFeatureTable_witnessPrior
        (G := G) (M := M) (feature := subConcept) (witness := superConcept)
  constructor
  · simpa [formedConceptInheritanceTable, Interpretation.finiteInheritanceStrength_eq] using
      finiteExtensionalProb_formedConceptInterpretation_eq_toFiniteWitnessFeatureTable_strength
        (G := G) (M := M) (feature := subConcept) (witness := superConcept)
  · simpa [formedConceptInheritanceTable, Interpretation.finiteInheritanceLogRatioBits_eq] using
      finitePointwiseLogRatioBits_formedConceptInterpretation_eq_toFiniteWitnessFeatureTable
        (G := G) (M := M) (feature := subConcept) (witness := superConcept)

/-- The same supported formed-concept extensional slice, re-expressed through
VE and BP on the generated finite witness/feature table. Mixed ASSOC/PAT
channels are not packaged by this theorem. -/
theorem formedConceptInheritance_exact_via_ve_bp
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : Mettapedia.Logic.AbstractInheritance.FormedConcept G M) :
    (Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) superConcept =
      (FiniteWitnessFeatureTable.veWeight
        (formedConceptInheritanceTable G M subConcept superConcept)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (formedConceptInheritanceTable G M subConcept superConcept) [])
    ∧
    (Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.veWeight
          (formedConceptInheritanceTable G M subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (formedConceptInheritanceTable G M subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (formedConceptInheritanceTable G M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩])
    ∧
    (Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (formedConceptInheritanceTable G M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (formedConceptInheritanceTable G M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (formedConceptInheritanceTable G M subConcept superConcept)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (formedConceptInheritanceTable G M subConcept superConcept)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (formedConceptInheritanceTable G M subConcept superConcept) []))
    ∧
    (Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M) superConcept =
      (FiniteWitnessFeatureTable.witnessMessage
        (formedConceptInheritanceTable G M subConcept superConcept) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (formedConceptInheritanceTable G M subConcept superConcept) [])
    ∧
    (Mettapedia.Logic.IntensionalInheritance.Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.featureMessage
          (formedConceptInheritanceTable G M subConcept superConcept) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (formedConceptInheritanceTable G M subConcept superConcept)
          (FiniteWitnessFeatureTable.ttJointAssign
            (formedConceptInheritanceTable G M subConcept superConcept)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (formedConceptInheritanceTable G M subConcept superConcept) true) := by
  constructor
  · simpa [formedConceptInheritanceTable] using
      finiteInheritancePrior_formedConceptInterpretation_eq_veWeight_ratio
        (G := G) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [formedConceptInheritanceTable] using
      finiteInheritanceStrength_formedConceptInterpretation_eq_veWeight_ratio
        (G := G) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [formedConceptInheritanceTable] using
      finiteInheritanceLogRatioBits_formedConceptInterpretation_eq_veQueryScore
        (G := G) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [formedConceptInheritanceTable] using
      finiteInheritancePrior_formedConceptInterpretation_eq_bpRatio
        (G := G) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  · simpa [formedConceptInheritanceTable] using
      finiteInheritanceStrength_formedConceptInterpretation_eq_bpRatio
        (G := G) (M := M) (subConcept := subConcept) (superConcept := superConcept)

end FormedConceptFinitePairBridge

end AbstractInheritance

section RobustCredalFinitePairBridge

variable {Obj Attr Q Gate : Type*}
variable [Preorder Q] [Fintype Gate] [Nonempty Gate] [Fintype Obj] [Nonempty Obj] [Fintype Attr]

open Mettapedia.Logic.ConceptOntology
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

noncomputable def lowerCredalConceptInheritanceTable
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    FiniteWitnessFeatureTable :=
  Interpretation.toFiniteWitnessFeatureTable
    (lowerFormedConceptInterpretation Γ M)
    subConcept superConcept

omit [Fintype Gate] [Nonempty Gate] in
theorem finitePriorProb_lowerFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_witnessPrior
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : LowerFormedConcept Γ M) :
    Interpretation.finitePriorProb
        (lowerFormedConceptInterpretation Γ M) witness =
      FiniteWitnessFeatureTable.witnessPrior
        (Interpretation.toFiniteWitnessFeatureTable
          (lowerFormedConceptInterpretation Γ M)
          feature witness) := by
  simpa using
    Interpretation.finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior
      (I := lowerFormedConceptInterpretation Γ M)
      (feature := feature) (witness := witness)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteExtensionalProb_lowerFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_strength
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : LowerFormedConcept Γ M) :
    Interpretation.finiteExtensionalProb
        (lowerFormedConceptInterpretation Γ M)
        feature witness =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (Interpretation.toFiniteWitnessFeatureTable
          (lowerFormedConceptInterpretation Γ M)
          feature witness) := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength
      (I := lowerFormedConceptInterpretation Γ M)
      (feature := feature) (witness := witness)

omit [Fintype Gate] [Nonempty Gate] in
theorem finitePointwiseLogRatioBits_lowerFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : LowerFormedConcept Γ M) :
    Interpretation.finitePointwiseLogRatioBits
        (lowerFormedConceptInterpretation Γ M)
        feature witness =
      FiniteWitnessFeatureTable.logRatioBits
        (Interpretation.toFiniteWitnessFeatureTable
          (lowerFormedConceptInterpretation Γ M)
          feature witness) := by
  simpa using
    Interpretation.finitePointwiseLogRatioBits_eq_toFiniteWitnessFeatureTable
      (I := lowerFormedConceptInterpretation Γ M)
      (feature := feature) (witness := witness)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritancePrior_lowerFormedConceptInterpretation_eq_veWeight_ratio
    (Γ : Gate → _root_.Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      _root_.Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
          subConcept superConcept)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept) [] := by
  simpa [Interpretation.finiteInheritancePrior_eq] using
    Interpretation.finitePriorProb_eq_veWeight_ratio
      (I := _root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritanceStrength_lowerFormedConceptInterpretation_eq_veWeight_ratio
    (Γ : Gate → _root_.Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      _root_.Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    Interpretation.finiteInheritanceStrength
        (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] := by
  simpa [Interpretation.finiteInheritanceStrength_eq] using
    Interpretation.finiteExtensionalProb_eq_veWeight_ratio
      (I := _root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritanceLogRatioBits_lowerFormedConceptInterpretation_eq_veQueryScore
    (Γ : Gate → _root_.Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      _root_.Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    Interpretation.finiteInheritanceLogRatioBits
        (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
                subConcept superConcept)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (_root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
                subConcept superConcept) []) := by
  simpa [Interpretation.finiteInheritanceLogRatioBits_eq] using
    Interpretation.finitePointwiseLogRatioBits_eq_ve_query_score
      (I := _root_.Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritancePrior_lowerFormedConceptInterpretation_eq_bpRatio
    (Γ : Gate → Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.witnessMessage
        (Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
          subConcept superConcept) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept) [] := by
  simpa [Interpretation.finiteInheritancePrior_eq] using
    Interpretation.finitePriorProb_eq_bp_ratio
      (I := Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritanceStrength_lowerFormedConceptInterpretation_eq_bpRatio
    (Γ : Gate → Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.featureMessage
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            subConcept superConcept)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept) true := by
  simpa [Interpretation.finiteInheritanceStrength_eq] using
    Interpretation.finiteExtensionalProb_eq_bp_ratio
      (I := Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem lowerFormedConceptInheritance_exact_via_table
    (Γ : Gate → Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M) superConcept =
      FiniteWitnessFeatureTable.witnessPrior
        (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
    ∧
    Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
    ∧
    Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      FiniteWitnessFeatureTable.logRatioBits
        (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) := by
  constructor
  · simpa [lowerCredalConceptInheritanceTable, Interpretation.finiteInheritancePrior_eq] using
      finitePriorProb_lowerFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_witnessPrior
        (Γ := Γ) (M := M) (feature := subConcept) (witness := superConcept)
  constructor
  · simpa [lowerCredalConceptInheritanceTable, Interpretation.finiteInheritanceStrength_eq] using
      finiteExtensionalProb_lowerFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_strength
        (Γ := Γ) (M := M) (feature := subConcept) (witness := superConcept)
  · simpa [lowerCredalConceptInheritanceTable, Interpretation.finiteInheritanceLogRatioBits_eq] using
      finitePointwiseLogRatioBits_lowerFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable
        (Γ := Γ) (M := M) (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem lowerFormedConceptInheritance_exact_via_ve_bp
    (Γ : Gate → Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept Γ M) :
    (Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.veWeight
        (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) [])
    ∧
    (Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.veWeight
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩])
    ∧
    (Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) []))
    ∧
    (Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.witnessMessage
        (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) [])
    ∧
    (Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.featureMessage
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)
          (FiniteWitnessFeatureTable.ttJointAssign
            (lowerCredalConceptInheritanceTable Γ M subConcept superConcept)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (lowerCredalConceptInheritanceTable Γ M subConcept superConcept) true) := by
  constructor
  · simpa [lowerCredalConceptInheritanceTable] using
      finiteInheritancePrior_lowerFormedConceptInterpretation_eq_veWeight_ratio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [lowerCredalConceptInheritanceTable] using
      finiteInheritanceStrength_lowerFormedConceptInterpretation_eq_veWeight_ratio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [lowerCredalConceptInheritanceTable] using
      finiteInheritanceLogRatioBits_lowerFormedConceptInterpretation_eq_veQueryScore
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [lowerCredalConceptInheritanceTable] using
      finiteInheritancePrior_lowerFormedConceptInterpretation_eq_bpRatio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  · simpa [lowerCredalConceptInheritanceTable] using
      finiteInheritanceStrength_lowerFormedConceptInterpretation_eq_bpRatio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)

theorem lowerCredalConceptInheritanceTable_singleton_eq
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept (Gate := PUnit) (fun _ => G) M) :
    lowerCredalConceptInheritanceTable (Gate := PUnit) (fun _ => G) M subConcept superConcept =
      AbstractInheritance.formedConceptInheritanceTable G M
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptSingletonEquiv G M subConcept)
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptSingletonEquiv G M superConcept) := by
  rfl

omit [Nonempty Obj] in
theorem finiteInheritanceStrength_lowerFormedConceptInterpretation_singleton_eq
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept (Gate := PUnit) (fun _ => G) M) :
    Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        subConcept superConcept =
      Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptSingletonEquiv G M subConcept)
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptSingletonEquiv G M superConcept) := by
  rfl

omit [Nonempty Obj] in
theorem lowerFormedConceptInheritance_exact_via_table_singleton
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      Mettapedia.Logic.ConceptOntology.LowerFormedConcept (Gate := PUnit) (fun _ => G) M) :
    let subExact :=
      Mettapedia.Logic.ConceptOntology.lowerFormedConceptSingletonEquiv G M subConcept
    let superExact :=
      Mettapedia.Logic.ConceptOntology.lowerFormedConceptSingletonEquiv G M superConcept
    Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        superConcept =
      Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        superExact
    ∧
    Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        subConcept superConcept =
      Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subExact superExact
    ∧
    Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.ConceptOntology.lowerFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        subConcept superConcept =
      Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subExact superExact := by
  constructor <;> constructor <;> rfl

noncomputable def upperCredalConceptInheritanceTable
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    FiniteWitnessFeatureTable :=
  Interpretation.toFiniteWitnessFeatureTable
    (upperFormedConceptInterpretation Γ M)
    subConcept superConcept

omit [Fintype Gate] [Nonempty Gate] in
theorem finitePriorProb_upperFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_witnessPrior
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : UpperFormedConcept Γ M) :
    Interpretation.finitePriorProb
        (upperFormedConceptInterpretation Γ M) witness =
      FiniteWitnessFeatureTable.witnessPrior
        (Interpretation.toFiniteWitnessFeatureTable
          (upperFormedConceptInterpretation Γ M)
          feature witness) := by
  simpa using
    Interpretation.finitePriorProb_eq_toFiniteWitnessFeatureTable_witnessPrior
      (I := upperFormedConceptInterpretation Γ M)
      (feature := feature) (witness := witness)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteExtensionalProb_upperFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_strength
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : UpperFormedConcept Γ M) :
    Interpretation.finiteExtensionalProb
        (upperFormedConceptInterpretation Γ M)
        feature witness =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (Interpretation.toFiniteWitnessFeatureTable
          (upperFormedConceptInterpretation Γ M)
          feature witness) := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_toFiniteWitnessFeatureTable_strength
      (I := upperFormedConceptInterpretation Γ M)
      (feature := feature) (witness := witness)

omit [Fintype Gate] [Nonempty Gate] in
theorem finitePointwiseLogRatioBits_upperFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (feature witness : UpperFormedConcept Γ M) :
    Interpretation.finitePointwiseLogRatioBits
        (upperFormedConceptInterpretation Γ M)
        feature witness =
      FiniteWitnessFeatureTable.logRatioBits
        (Interpretation.toFiniteWitnessFeatureTable
          (upperFormedConceptInterpretation Γ M)
          feature witness) := by
  simpa using
    Interpretation.finitePointwiseLogRatioBits_eq_toFiniteWitnessFeatureTable
      (I := upperFormedConceptInterpretation Γ M)
      (feature := feature) (witness := witness)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritancePrior_upperFormedConceptInterpretation_eq_veWeight_ratio
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (upperFormedConceptInterpretation Γ M)
          subConcept superConcept)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept) [] := by
  simpa [Interpretation.finiteInheritancePrior_eq] using
    Interpretation.finitePriorProb_eq_veWeight_ratio
      (I := upperFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritanceStrength_upperFormedConceptInterpretation_eq_veWeight_ratio
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (upperFormedConceptInterpretation Γ M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] := by
  simpa [Interpretation.finiteInheritanceStrength_eq] using
    Interpretation.finiteExtensionalProb_eq_veWeight_ratio
      (I := upperFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritanceLogRatioBits_upperFormedConceptInterpretation_eq_veQueryScore
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Interpretation.finiteInheritanceLogRatioBits
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (upperFormedConceptInterpretation Γ M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (upperFormedConceptInterpretation Γ M)
              subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (upperFormedConceptInterpretation Γ M)
                subConcept superConcept)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (upperFormedConceptInterpretation Γ M)
                subConcept superConcept) []) := by
  simpa [Interpretation.finiteInheritanceLogRatioBits_eq] using
    Interpretation.finitePointwiseLogRatioBits_eq_ve_query_score
      (I := upperFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritancePrior_upperFormedConceptInterpretation_eq_bpRatio
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.witnessMessage
        (Interpretation.toFiniteWitnessFeatureTable
          (upperFormedConceptInterpretation Γ M)
          subConcept superConcept) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept) [] := by
  simpa [Interpretation.finiteInheritancePrior_eq] using
    Interpretation.finitePriorProb_eq_bp_ratio
      (I := upperFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem finiteInheritanceStrength_upperFormedConceptInterpretation_eq_bpRatio
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.featureMessage
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Interpretation.toFiniteWitnessFeatureTable
            (upperFormedConceptInterpretation Γ M)
            subConcept superConcept)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Interpretation.toFiniteWitnessFeatureTable
              (upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Interpretation.toFiniteWitnessFeatureTable
              (upperFormedConceptInterpretation Γ M)
              subConcept superConcept) true := by
  simpa [Interpretation.finiteInheritanceStrength_eq] using
    Interpretation.finiteExtensionalProb_eq_bp_ratio
      (I := upperFormedConceptInterpretation Γ M)
      (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem upperFormedConceptInheritance_exact_via_table
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation Γ M) superConcept =
      FiniteWitnessFeatureTable.witnessPrior
        (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
    ∧
    Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      FiniteWitnessFeatureTable.featureToWitnessStrength
        (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
    ∧
    Interpretation.finiteInheritanceLogRatioBits
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      FiniteWitnessFeatureTable.logRatioBits
        (upperCredalConceptInheritanceTable Γ M subConcept superConcept) := by
  constructor
  · simpa [upperCredalConceptInheritanceTable, Interpretation.finiteInheritancePrior_eq] using
      finitePriorProb_upperFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_witnessPrior
        (Γ := Γ) (M := M) (feature := subConcept) (witness := superConcept)
  constructor
  · simpa [upperCredalConceptInheritanceTable, Interpretation.finiteInheritanceStrength_eq] using
      finiteExtensionalProb_upperFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable_strength
        (Γ := Γ) (M := M) (feature := subConcept) (witness := superConcept)
  · simpa [upperCredalConceptInheritanceTable, Interpretation.finiteInheritanceLogRatioBits_eq] using
      finitePointwiseLogRatioBits_upperFormedConceptInterpretation_eq_toFiniteWitnessFeatureTable
        (Γ := Γ) (M := M) (feature := subConcept) (witness := superConcept)

omit [Fintype Gate] [Nonempty Gate] in
theorem upperFormedConceptInheritance_exact_via_ve_bp
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    (Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.veWeight
        (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept) [])
    ∧
    (Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.veWeight
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩])
    ∧
    (Interpretation.finiteInheritanceLogRatioBits
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (upperCredalConceptInheritanceTable Γ M subConcept superConcept) []))
    ∧
    (Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation Γ M) superConcept =
      (FiniteWitnessFeatureTable.witnessMessage
        (upperCredalConceptInheritanceTable Γ M subConcept superConcept) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept) [])
    ∧
    (Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation Γ M)
        subConcept superConcept =
      if FiniteWitnessFeatureTable.featureMessage
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (upperCredalConceptInheritanceTable Γ M subConcept superConcept)
          (FiniteWitnessFeatureTable.ttJointAssign
            (upperCredalConceptInheritanceTable Γ M subConcept superConcept)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (upperCredalConceptInheritanceTable Γ M subConcept superConcept) true) := by
  constructor
  · simpa [upperCredalConceptInheritanceTable] using
      finiteInheritancePrior_upperFormedConceptInterpretation_eq_veWeight_ratio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [upperCredalConceptInheritanceTable] using
      finiteInheritanceStrength_upperFormedConceptInterpretation_eq_veWeight_ratio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [upperCredalConceptInheritanceTable] using
      finiteInheritanceLogRatioBits_upperFormedConceptInterpretation_eq_veQueryScore
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  constructor
  · simpa [upperCredalConceptInheritanceTable] using
      finiteInheritancePrior_upperFormedConceptInterpretation_eq_bpRatio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)
  · simpa [upperCredalConceptInheritanceTable] using
      finiteInheritanceStrength_upperFormedConceptInterpretation_eq_bpRatio
        (Γ := Γ) (M := M) (subConcept := subConcept) (superConcept := superConcept)

theorem upperCredalConceptInheritanceTable_singleton_eq
    (G : EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      UpperFormedConcept (Gate := PUnit) (fun _ => G) M) :
    upperCredalConceptInheritanceTable (Gate := PUnit) (fun _ => G) M subConcept superConcept =
      AbstractInheritance.formedConceptInheritanceTable G M
        (upperFormedConceptSingletonEquiv G M subConcept)
        (upperFormedConceptSingletonEquiv G M superConcept) := by
  rfl

omit [Nonempty Obj] in
theorem finiteInheritanceStrength_upperFormedConceptInterpretation_singleton_eq
    (G : EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      UpperFormedConcept (Gate := PUnit) (fun _ => G) M) :
    Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        subConcept superConcept =
      Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        (upperFormedConceptSingletonEquiv G M subConcept)
        (upperFormedConceptSingletonEquiv G M superConcept) := by
  rfl

omit [Nonempty Obj] in
theorem upperFormedConceptInheritance_exact_via_table_singleton
    (G : EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept :
      UpperFormedConcept (Gate := PUnit) (fun _ => G) M) :
    let subExact :=
      upperFormedConceptSingletonEquiv G M subConcept
    let superExact :=
      upperFormedConceptSingletonEquiv G M superConcept
    Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        superConcept =
      Interpretation.finiteInheritancePrior
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        superExact
    ∧
    Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        subConcept superConcept =
      Interpretation.finiteInheritanceStrength
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subExact superExact
    ∧
    Interpretation.finiteInheritanceLogRatioBits
        (upperFormedConceptInterpretation
          (Gate := PUnit) (fun _ => G) M)
        subConcept superConcept =
      Interpretation.finiteInheritanceLogRatioBits
        (Mettapedia.Logic.AbstractInheritance.formedConceptInterpretation G M)
        subExact superExact := by
  constructor <;> constructor <;> rfl

omit [Fintype Gate] in
theorem upperCredalConceptInheritanceTable_of_lowerLift_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    upperCredalConceptInheritanceTable Γ M
      (lowerToUpperFormedConcept Γ M subConcept)
      (lowerToUpperFormedConcept Γ M superConcept) =
    lowerCredalConceptInheritanceTable Γ M subConcept superConcept := by
  rfl

omit [Fintype Gate] [Nonempty Obj] in
theorem lower_upperCredalInheritance_exact_of_lowerLift
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    Interpretation.finiteInheritancePrior
        (lowerFormedConceptInterpretation Γ M) superConcept =
      Interpretation.finiteInheritancePrior
        (upperFormedConceptInterpretation Γ M)
        (lowerToUpperFormedConcept Γ M superConcept)
    ∧
    Interpretation.finiteInheritanceStrength
        (lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      Interpretation.finiteInheritanceStrength
        (upperFormedConceptInterpretation Γ M)
        (lowerToUpperFormedConcept Γ M subConcept)
        (lowerToUpperFormedConcept Γ M superConcept)
    ∧
    Interpretation.finiteInheritanceLogRatioBits
        (lowerFormedConceptInterpretation Γ M)
        subConcept superConcept =
      Interpretation.finiteInheritanceLogRatioBits
        (upperFormedConceptInterpretation Γ M)
        (lowerToUpperFormedConcept Γ M subConcept)
        (lowerToUpperFormedConcept Γ M superConcept) := by
  constructor <;> constructor <;> rfl

/-- A credal inheritance query is at least permissively supported when both
concepts are formed under some admissible gate. -/
def credalInheritanceJudgment
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) : Prop :=
  subConcept ∈ upperConceptFamily Γ M ∧
    superConcept ∈ upperConceptFamily Γ M

/-- A credal inheritance query is precise when both concepts are robustly
formed under every admissible gate. -/
def credallyPreciseInheritance
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) : Prop :=
  subConcept ∈ lowerConceptFamily Γ M ∧
    superConcept ∈ lowerConceptFamily Γ M

/-- A credal inheritance query is imprecise when it is permissively supported
but at least one side fails robust formation. -/
def credallyImpreciseInheritance
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) : Prop :=
  subConcept ∈ upperConceptFamily Γ M ∧
    superConcept ∈ upperConceptFamily Γ M ∧
      (subConcept ∉ lowerConceptFamily Γ M ∨
        superConcept ∉ lowerConceptFamily Γ M)

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credalInheritanceJudgment_iff
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credalInheritanceJudgment Γ M subConcept superConcept ↔
      subConcept ∈ upperConceptFamily Γ M ∧
        superConcept ∈ upperConceptFamily Γ M := Iff.rfl

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credallyPreciseInheritance_iff
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credallyPreciseInheritance Γ M subConcept superConcept ↔
      subConcept ∈ lowerConceptFamily Γ M ∧
        superConcept ∈ lowerConceptFamily Γ M := Iff.rfl

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credallyImpreciseInheritance_iff
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credallyImpreciseInheritance Γ M subConcept superConcept ↔
      subConcept ∈ upperConceptFamily Γ M ∧
        superConcept ∈ upperConceptFamily Γ M ∧
          (subConcept ∉ lowerConceptFamily Γ M ∨
            superConcept ∉ lowerConceptFamily Γ M) := Iff.rfl

omit [Fintype Gate] [Nonempty Obj] in
theorem credallyPreciseInheritance_imp_judgment
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr)
    (hPrecise : credallyPreciseInheritance Γ M subConcept superConcept) :
    credalInheritanceJudgment Γ M subConcept superConcept := by
  rcases hPrecise with ⟨hSub, hSuper⟩
  exact ⟨lowerConceptFamily_subset_upperConceptFamily Γ M hSub,
    lowerConceptFamily_subset_upperConceptFamily Γ M hSuper⟩

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
theorem credallyImpreciseInheritance_imp_judgment
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr)
    (hImprecise : credallyImpreciseInheritance Γ M subConcept superConcept) :
    credalInheritanceJudgment Γ M subConcept superConcept := by
  exact ⟨hImprecise.1, hImprecise.2.1⟩

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
theorem not_credallyImpreciseInheritance_of_precise
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr)
    (hPrecise : credallyPreciseInheritance Γ M subConcept superConcept) :
    ¬ credallyImpreciseInheritance Γ M subConcept superConcept := by
  rcases hPrecise with ⟨hSub, hSuper⟩
  intro hImprecise
  rcases hImprecise with ⟨_, _, hGap⟩
  rcases hGap with hSubNot | hSuperNot
  · exact hSubNot hSub
  · exact hSuperNot hSuper

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credalInheritanceJudgment_singleton_iff
    (G : EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credalInheritanceJudgment (Gate := PUnit) (fun _ => G) M subConcept superConcept ↔
      subConcept ∈ AbstractInheritance.finiteConceptFamily G M ∧
        superConcept ∈ AbstractInheritance.finiteConceptFamily G M := by
  simp [credalInheritanceJudgment]

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credallyPreciseInheritance_singleton_iff
    (G : EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credallyPreciseInheritance (Gate := PUnit) (fun _ => G) M subConcept superConcept ↔
      subConcept ∈ AbstractInheritance.finiteConceptFamily G M ∧
        superConcept ∈ AbstractInheritance.finiteConceptFamily G M := by
  simp [credallyPreciseInheritance]

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credallyImpreciseInheritance_singleton_iff
    (G : EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credallyImpreciseInheritance (Gate := PUnit) (fun _ => G) M subConcept superConcept ↔
      False := by
  constructor
  · intro h
    rcases h with ⟨hSubUpper, hSuperUpper, hGap⟩
    have hSubLower :
        subConcept ∈ AbstractInheritance.finiteConceptFamily G M :=
      (mem_upperConceptFamily_singleton_iff (G := G) (M := M) subConcept).1 hSubUpper
    have hSuperLower :
        superConcept ∈ AbstractInheritance.finiteConceptFamily G M :=
      (mem_upperConceptFamily_singleton_iff (G := G) (M := M) superConcept).1 hSuperUpper
    rcases hGap with hSubNot | hSuperNot
    · exact hSubNot ((mem_lowerConceptFamily_singleton_iff (G := G) (M := M) subConcept).2 hSubLower)
    · exact hSuperNot ((mem_lowerConceptFamily_singleton_iff (G := G) (M := M) superConcept).2 hSuperLower)
  · intro h
    exact False.elim h

/-- Gate-indexed gamble for the credal inheritance judgment.

The two coordinates of `Gate × Gate` intentionally track independent admissible
gate choices for the subconcept and superconcept.  This matches
`credalInheritanceJudgment`, whose upper support requires each side to be formed
under some admissible gate, not necessarily the same one. -/
noncomputable def credalInheritanceGamble
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    Gamble (Gate × Gate) :=
  fun gs =>
    if subConcept ∈ AbstractInheritance.finiteConceptFamily (Γ gs.1) M ∧
        superConcept ∈ AbstractInheritance.finiteConceptFamily (Γ gs.2) M then
      1
    else
      0

omit [Fintype Gate] [Nonempty Gate] [Nonempty Obj] in
@[simp] theorem credalInheritanceGamble_apply
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr)
    (gs : Gate × Gate) :
    credalInheritanceGamble Γ M subConcept superConcept gs =
      if subConcept ∈ AbstractInheritance.finiteConceptFamily (Γ gs.1) M ∧
          superConcept ∈ AbstractInheritance.finiteConceptFamily (Γ gs.2) M then
        1
      else
        0 :=
  rfl

omit [Nonempty Obj] in
theorem lowerEnvelope_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    lowerEnvelope (gateCredalSet (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyPreciseInheritance Γ M subConcept superConcept then 1 else 0 := by
  classical
  by_cases hPrecise : credallyPreciseInheritance Γ M subConcept superConcept
  · rcases hPrecise with ⟨hSubLower, hSuperLower⟩
    apply le_antisymm
    · rw [if_pos ⟨hSubLower, hSuperLower⟩]
      obtain ⟨g₀⟩ := ‹Nonempty Gate›
      have hmem :
          PrecisePrevision.dirac (g₀, g₀) ∈ gateCredalSet (Gate := Gate × Gate) :=
        ⟨(g₀, g₀), rfl⟩
      have hle :=
        lowerEnvelope_le_of_mem (gateCredalSet (Gate := Gate × Gate))
          (credalInheritanceGamble Γ M subConcept superConcept)
          (finite_credalRange_bddBelow (gateCredalSet (Gate := Gate × Gate))
            (credalInheritanceGamble Γ M subConcept superConcept))
          hmem
      simpa [gateCredalSet, credalInheritanceGamble, hSubLower g₀, hSuperLower g₀]
        using hle
    · apply le_lowerEnvelope_of_forall_le
        (gateCredalSet (Gate := Gate × Gate))
        (gateCredalSet_nonempty (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept)
      intro P hP
      rcases hP with ⟨gs, rfl⟩
      rw [if_pos ⟨hSubLower, hSuperLower⟩]
      simp [credalInheritanceGamble, hSubLower gs.1, hSuperLower gs.2]
  · have hWitness :
        ∃ gs : Gate × Gate,
          ¬ (subConcept ∈ AbstractInheritance.finiteConceptFamily (Γ gs.1) M ∧
            superConcept ∈ AbstractInheritance.finiteConceptFamily (Γ gs.2) M) := by
      by_contra hNoWitness
      push_neg at hNoWitness
      apply hPrecise
      exact ⟨fun g => (hNoWitness (g, Classical.choice ‹Nonempty Gate›)).1,
        fun g => (hNoWitness (Classical.choice ‹Nonempty Gate›, g)).2⟩
    apply le_antisymm
    · rw [if_neg hPrecise]
      rcases hWitness with ⟨gs₀, hgs₀⟩
      have hmem :
          PrecisePrevision.dirac gs₀ ∈ gateCredalSet (Gate := Gate × Gate) :=
        ⟨gs₀, rfl⟩
      have hle :=
        lowerEnvelope_le_of_mem (gateCredalSet (Gate := Gate × Gate))
          (credalInheritanceGamble Γ M subConcept superConcept)
          (finite_credalRange_bddBelow (gateCredalSet (Gate := Gate × Gate))
            (credalInheritanceGamble Γ M subConcept superConcept))
          hmem
      have hgsClosed :
          ¬ (AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs₀.1) M)
              subConcept ∧
            AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs₀.2) M)
              superConcept) := by
        intro hClosed
        exact hgs₀
          ⟨(AbstractInheritance.mem_finiteConceptFamily_iff
              (G := Γ gs₀.1) (M := M) (A := subConcept)).2 hClosed.1,
            (AbstractInheritance.mem_finiteConceptFamily_iff
              (G := Γ gs₀.2) (M := M) (A := superConcept)).2 hClosed.2⟩
      simpa [gateCredalSet, credalInheritanceGamble,
        AbstractInheritance.mem_finiteConceptFamily_iff, hgsClosed] using hle
    · apply le_lowerEnvelope_of_forall_le
        (gateCredalSet (Gate := Gate × Gate))
        (gateCredalSet_nonempty (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept)
      intro P hP
      rcases hP with ⟨gs, rfl⟩
      rw [if_neg hPrecise]
      by_cases hgsClosed :
          AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs.1) M)
              subConcept ∧
            AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs.2) M)
              superConcept <;>
        simp [credalInheritanceGamble, AbstractInheritance.mem_finiteConceptFamily_iff,
          hgsClosed]

omit [Nonempty Obj] in
theorem upperEnvelope_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    upperEnvelope (gateCredalSet (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credalInheritanceJudgment Γ M subConcept superConcept then 1 else 0 := by
  classical
  by_cases hJudgment : credalInheritanceJudgment Γ M subConcept superConcept
  · rcases hJudgment with ⟨hSubUpper, hSuperUpper⟩
    rcases hSubUpper with ⟨gSub, hSub⟩
    rcases hSuperUpper with ⟨gSuper, hSuper⟩
    apply le_antisymm
    · apply upperEnvelope_le_of_forall_le
        (gateCredalSet (Gate := Gate × Gate))
        (gateCredalSet_nonempty (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept)
      intro P hP
      rcases hP with ⟨gs, rfl⟩
      rw [if_pos ⟨⟨gSub, hSub⟩, ⟨gSuper, hSuper⟩⟩]
      by_cases hgsClosed :
          AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs.1) M)
              subConcept ∧
            AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs.2) M)
              superConcept <;>
        simp [credalInheritanceGamble, AbstractInheritance.mem_finiteConceptFamily_iff,
          hgsClosed]
    · have hmem :
          PrecisePrevision.dirac (gSub, gSuper) ∈ gateCredalSet (Gate := Gate × Gate) :=
        ⟨(gSub, gSuper), rfl⟩
      have hge :=
        le_upperEnvelope_of_mem (gateCredalSet (Gate := Gate × Gate))
          (credalInheritanceGamble Γ M subConcept superConcept)
          (finite_credalRange_bddAbove (gateCredalSet (Gate := Gate × Gate))
            (credalInheritanceGamble Γ M subConcept superConcept))
          hmem
      rw [if_pos ⟨⟨gSub, hSub⟩, ⟨gSuper, hSuper⟩⟩]
      simpa [gateCredalSet, credalInheritanceGamble, hSub, hSuper] using hge
  · have hAllClosed :
        ∀ gs : Gate × Gate,
          ¬ (AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs.1) M)
              subConcept ∧
            AbstractInheritance.DualConcept.IsClosed (crispRelation (Γ gs.2) M)
              superConcept) := by
      intro gs hClosed
      apply hJudgment
      exact
        ⟨⟨gs.1, (AbstractInheritance.mem_finiteConceptFamily_iff
            (G := Γ gs.1) (M := M) (A := subConcept)).2 hClosed.1⟩,
          ⟨gs.2, (AbstractInheritance.mem_finiteConceptFamily_iff
            (G := Γ gs.2) (M := M) (A := superConcept)).2 hClosed.2⟩⟩
    apply le_antisymm
    · apply upperEnvelope_le_of_forall_le
        (gateCredalSet (Gate := Gate × Gate))
        (gateCredalSet_nonempty (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept)
      intro P hP
      rcases hP with ⟨gs, rfl⟩
      rw [if_neg hJudgment]
      simp [credalInheritanceGamble, AbstractInheritance.mem_finiteConceptFamily_iff,
        hAllClosed gs]
    · obtain ⟨g₀⟩ := ‹Nonempty Gate›
      let gs₀ : Gate × Gate := (g₀, g₀)
      have hmem :
          PrecisePrevision.dirac gs₀ ∈ gateCredalSet (Gate := Gate × Gate) :=
        ⟨gs₀, rfl⟩
      have hge :=
        le_upperEnvelope_of_mem (gateCredalSet (Gate := Gate × Gate))
          (credalInheritanceGamble Γ M subConcept superConcept)
          (finite_credalRange_bddAbove (gateCredalSet (Gate := Gate × Gate))
            (credalInheritanceGamble Γ M subConcept superConcept))
          hmem
      rw [if_neg hJudgment]
      simpa [gateCredalSet, credalInheritanceGamble,
        AbstractInheritance.mem_finiteConceptFamily_iff, hAllClosed gs₀] using hge

omit [Nonempty Obj] in
theorem credalEnvelopeWidth_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credalEnvelopeWidth (gateCredalSet (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyImpreciseInheritance Γ M subConcept superConcept then 1 else 0 := by
  classical
  by_cases hPrecise : credallyPreciseInheritance Γ M subConcept superConcept
  · have hJudgment :=
      credallyPreciseInheritance_imp_judgment Γ M subConcept superConcept hPrecise
    have hNotImprecise :=
      not_credallyImpreciseInheritance_of_precise Γ M subConcept superConcept hPrecise
    rw [if_neg hNotImprecise]
    unfold credalEnvelopeWidth
    rw [lowerEnvelope_credalInheritanceGamble_eq,
      upperEnvelope_credalInheritanceGamble_eq]
    rw [if_pos hPrecise, if_pos hJudgment]
    ring
  · by_cases hJudgment : credalInheritanceJudgment Γ M subConcept superConcept
    · have hImprecise : credallyImpreciseInheritance Γ M subConcept superConcept := by
        rcases hJudgment with ⟨hSubUpper, hSuperUpper⟩
        rw [credallyImpreciseInheritance_iff]
        refine ⟨hSubUpper, hSuperUpper, ?_⟩
        rw [credallyPreciseInheritance_iff] at hPrecise
        by_cases hSubLower : subConcept ∈ lowerConceptFamily Γ M
        · right
          intro hSuperLower
          exact hPrecise ⟨hSubLower, hSuperLower⟩
        · exact Or.inl hSubLower
      rw [if_pos hImprecise]
      unfold credalEnvelopeWidth
      rw [lowerEnvelope_credalInheritanceGamble_eq,
        upperEnvelope_credalInheritanceGamble_eq]
      rw [if_neg hPrecise, if_pos hJudgment]
      ring
    · have hNotImprecise :
        ¬ credallyImpreciseInheritance Γ M subConcept superConcept := by
        intro hImprecise
        exact hJudgment
          (credallyImpreciseInheritance_imp_judgment Γ M subConcept superConcept hImprecise)
      rw [if_neg hNotImprecise]
      unfold credalEnvelopeWidth
      rw [lowerEnvelope_credalInheritanceGamble_eq,
        upperEnvelope_credalInheritanceGamble_eq]
      rw [if_neg hPrecise, if_neg hJudgment]
      ring

omit [Nonempty Obj] in
theorem credalEnvelopeWidthComplement_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credalEnvelopeWidthComplement (gateCredalSet (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyImpreciseInheritance Γ M subConcept superConcept then 0 else 1 := by
  classical
  by_cases hImprecise : credallyImpreciseInheritance Γ M subConcept superConcept
  · rw [if_pos hImprecise]
    rw [credalEnvelopeWidthComplement,
      credalEnvelopeWidth_credalInheritanceGamble_eq, if_pos hImprecise]
    ring
  · rw [if_neg hImprecise]
    rw [credalEnvelopeWidthComplement,
      credalEnvelopeWidth_credalInheritanceGamble_eq, if_neg hImprecise]
    ring

omit [Nonempty Obj] in
theorem credalEnvelopeMidpoint_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    credalEnvelopeMidpoint (gateCredalSet (Gate := Gate × Gate))
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyPreciseInheritance Γ M subConcept superConcept then 1
      else if credalInheritanceJudgment Γ M subConcept superConcept then (1 / 2 : ℝ)
      else 0 := by
  classical
  by_cases hPrecise : credallyPreciseInheritance Γ M subConcept superConcept
  · have hJudgment :=
      credallyPreciseInheritance_imp_judgment Γ M subConcept superConcept hPrecise
    unfold credalEnvelopeMidpoint
    rw [lowerEnvelope_credalInheritanceGamble_eq,
      upperEnvelope_credalInheritanceGamble_eq]
    rw [if_pos hPrecise, if_pos hJudgment, if_pos hPrecise]
    ring
  · by_cases hJudgment : credalInheritanceJudgment Γ M subConcept superConcept
    · unfold credalEnvelopeMidpoint
      rw [lowerEnvelope_credalInheritanceGamble_eq,
        upperEnvelope_credalInheritanceGamble_eq]
      rw [if_neg hPrecise, if_pos hJudgment, if_neg hPrecise, if_pos hJudgment]
      ring
    · unfold credalEnvelopeMidpoint
      rw [lowerEnvelope_credalInheritanceGamble_eq,
        upperEnvelope_credalInheritanceGamble_eq]
      rw [if_neg hPrecise, if_neg hJudgment, if_neg hPrecise, if_neg hJudgment]
      ring

omit [Nonempty Obj] in
theorem globalEnvelopeWidth_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidth
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyImpreciseInheritance Γ M subConcept superConcept then 1 else 0 := by
  simp [gateCredalProjectiveSpec, ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    credalEnvelopeWidth_credalInheritanceGamble_eq]

omit [Nonempty Obj] in
theorem globalEnvelopeWidthComplement_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidthComplement
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyImpreciseInheritance Γ M subConcept superConcept then 0 else 1 := by
  simp [gateCredalProjectiveSpec, ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    credalEnvelopeWidthComplement_credalInheritanceGamble_eq]

omit [Nonempty Obj] in
theorem globalEnvelopeMidpoint_credalInheritanceGamble_eq
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeMidpoint
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyPreciseInheritance Γ M subConcept superConcept then 1
      else if credalInheritanceJudgment Γ M subConcept superConcept then (1 / 2 : ℝ)
      else 0 := by
  simp [gateCredalProjectiveSpec, ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    credalEnvelopeMidpoint_credalInheritanceGamble_eq]

/-- Review-facing package: the credal inheritance predicates read directly as
PLN-style midpoint and width-complement coordinates on the independent-gate
inheritance gamble. -/
structure CredalInheritanceTruthCoordinateCrown
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) where
  widthReadout :
    (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidth
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyImpreciseInheritance Γ M subConcept superConcept then 1 else 0
  widthComplementReadout :
    (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidthComplement
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyImpreciseInheritance Γ M subConcept superConcept then 0 else 1
  midpointReadout :
    (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeMidpoint
        (credalInheritanceGamble Γ M subConcept superConcept) =
      if credallyPreciseInheritance Γ M subConcept superConcept then 1
      else if credalInheritanceJudgment Γ M subConcept superConcept then (1 / 2 : ℝ)
      else 0
  imprecise_width_eq_one :
    credallyImpreciseInheritance Γ M subConcept superConcept →
      (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidth
          (credalInheritanceGamble Γ M subConcept superConcept) = 1
  imprecise_widthComplement_eq_zero :
    credallyImpreciseInheritance Γ M subConcept superConcept →
      (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidthComplement
          (credalInheritanceGamble Γ M subConcept superConcept) = 0
  imprecise_midpoint_eq_half :
    credallyImpreciseInheritance Γ M subConcept superConcept →
      (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeMidpoint
          (credalInheritanceGamble Γ M subConcept superConcept) = (1 / 2 : ℝ)
  precise_widthComplement_eq_one :
    credallyPreciseInheritance Γ M subConcept superConcept →
      (gateCredalProjectiveSpec (Gate := Gate × Gate)).globalEnvelopeWidthComplement
          (credalInheritanceGamble Γ M subConcept superConcept) = 1

omit [Nonempty Obj] in
theorem credalInheritanceTruthCoordinateCrown
    (Γ : Gate → EvidenceGate Q)
    (M : Obj → Attr → Q)
    (subConcept superConcept : DualConcept Obj Attr) :
    CredalInheritanceTruthCoordinateCrown Γ M subConcept superConcept where
  widthReadout :=
    globalEnvelopeWidth_credalInheritanceGamble_eq Γ M subConcept superConcept
  widthComplementReadout :=
    globalEnvelopeWidthComplement_credalInheritanceGamble_eq Γ M subConcept superConcept
  midpointReadout :=
    globalEnvelopeMidpoint_credalInheritanceGamble_eq Γ M subConcept superConcept
  imprecise_width_eq_one := by
    intro hImprecise
    rw [globalEnvelopeWidth_credalInheritanceGamble_eq, if_pos hImprecise]
  imprecise_widthComplement_eq_zero := by
    intro hImprecise
    rw [globalEnvelopeWidthComplement_credalInheritanceGamble_eq, if_pos hImprecise]
  imprecise_midpoint_eq_half := by
    intro hImprecise
    have hJudgment :=
      credallyImpreciseInheritance_imp_judgment Γ M subConcept superConcept hImprecise
    have hNotPrecise :
        ¬ credallyPreciseInheritance Γ M subConcept superConcept := by
      intro hPrecise
      exact not_credallyImpreciseInheritance_of_precise
        Γ M subConcept superConcept hPrecise hImprecise
    rw [globalEnvelopeMidpoint_credalInheritanceGamble_eq,
      if_neg hNotPrecise, if_pos hJudgment]
  precise_widthComplement_eq_one := by
    intro hPrecise
    have hNotImprecise :=
      not_credallyImpreciseInheritance_of_precise Γ M subConcept superConcept hPrecise
    rw [globalEnvelopeWidthComplement_credalInheritanceGamble_eq, if_neg hNotImprecise]

end RobustCredalFinitePairBridge

namespace EvidenceMembershipContext

section FinitePairBridge

variable {State Obj Con Q : Type*}
variable [Mettapedia.Logic.EvidenceClass.EvidenceType State] [AddCommMonoid Q] [Preorder Q]
variable [Fintype Obj] [Nonempty Obj]

theorem finitePriorProb_crispInterpretationAt_eq_veWeight_ratio
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (feature witness : Con) :
    Interpretation.finitePriorProb (crispInterpretationAt M G W) witness =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (crispInterpretationAt M G W) feature witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness) [] := by
  simpa using
    Interpretation.finitePriorProb_eq_veWeight_ratio
      (I := crispInterpretationAt M G W)
      (feature := feature) (witness := witness)

theorem finiteExtensionalProb_crispInterpretationAt_eq_veWeight_ratio
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (feature witness : Con) :
    Interpretation.finiteExtensionalProb (crispInterpretationAt M G W) feature witness =
      if FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness)
          [⟨MembershipConcept.feature, true⟩] = 0 then
        0
      else
        (FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness)
          [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
          FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (crispInterpretationAt M G W) feature witness)
            [⟨MembershipConcept.feature, true⟩] := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_veWeight_ratio
      (I := crispInterpretationAt M G W)
      (feature := feature) (witness := witness)

theorem finitePointwiseLogRatioBits_crispInterpretationAt_eq_ve_query_score
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (feature witness : Con) :
    Interpretation.finitePointwiseLogRatioBits
        (crispInterpretationAt M G W) feature witness =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (crispInterpretationAt M G W) feature witness)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (crispInterpretationAt M G W) feature witness)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (crispInterpretationAt M G W) feature witness)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (crispInterpretationAt M G W) feature witness) []) := by
  simpa using
    Interpretation.finitePointwiseLogRatioBits_eq_ve_query_score
      (I := crispInterpretationAt M G W)
      (feature := feature) (witness := witness)

theorem finitePriorProb_crispInterpretationAt_eq_bp_ratio
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (feature witness : Con) :
    Interpretation.finitePriorProb (crispInterpretationAt M G W) witness =
      (FiniteWitnessFeatureTable.witnessMessage
        (Interpretation.toFiniteWitnessFeatureTable
          (crispInterpretationAt M G W) feature witness) true : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness) [] := by
  simpa using
    Interpretation.finitePriorProb_eq_bp_ratio
      (I := crispInterpretationAt M G W)
      (feature := feature) (witness := witness)

theorem finiteExtensionalProb_crispInterpretationAt_eq_bp_ratio
    (M : Mettapedia.Logic.ConceptOntology.EvidenceMembershipContext State Obj Con Q)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate Q)
    (W : State) (feature witness : Con) :
    Interpretation.finiteExtensionalProb (crispInterpretationAt M G W) feature witness =
      if FiniteWitnessFeatureTable.featureMessage
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Interpretation.toFiniteWitnessFeatureTable
            (crispInterpretationAt M G W) feature witness)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Interpretation.toFiniteWitnessFeatureTable
              (crispInterpretationAt M G W) feature witness)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Interpretation.toFiniteWitnessFeatureTable
              (crispInterpretationAt M G W) feature witness) true := by
  simpa using
    Interpretation.finiteExtensionalProb_eq_bp_ratio
      (I := crispInterpretationAt M G W)
      (feature := feature) (witness := witness)

end FinitePairBridge

end EvidenceMembershipContext

section MembershipQueryBuilderFinitePairBridge

namespace MembershipQueryBuilderBridge

variable {State Obj Con Srt : Type*} {Query : Srt → Type*}
variable [Mettapedia.Logic.EvidenceClass.EvidenceType State]
variable [Mettapedia.Logic.PLNWorldModel.WorldModelSigma State Srt Query]
variable [Fintype Obj] [Nonempty Obj]

theorem finitePriorProb_toEvidenceMembershipContext_eq_veWeight_ratio
    (enc : Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder Obj Con Srt Query)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate BinaryEvidence)
    (W : State) (feature witness : Con) :
    Interpretation.finitePriorProb
        (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
          (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
            (State := State) enc) G W) witness =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
            (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
              (State := State) enc) G W) feature witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                (State := State) enc) G W) feature witness) [] := by
  simpa using
    EvidenceMembershipContext.finitePriorProb_crispInterpretationAt_eq_veWeight_ratio
      (M := Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
        (State := State) enc)
      (G := G) (W := W) (feature := feature) (witness := witness)

theorem finiteExtensionalProb_toEvidenceMembershipContext_eq_bp_ratio
    (enc : Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder Obj Con Srt Query)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate BinaryEvidence)
    (W : State) (feature witness : Con) :
    Interpretation.finiteExtensionalProb
        (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
          (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
            (State := State) enc) G W) feature witness =
      if FiniteWitnessFeatureTable.featureMessage
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                (State := State) enc) G W) feature witness) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                (State := State) enc) G W) feature witness)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                  (State := State) enc) G W) feature witness)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                  (State := State) enc) G W) feature witness) true := by
  simpa using
    EvidenceMembershipContext.finiteExtensionalProb_crispInterpretationAt_eq_bp_ratio
      (M := Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
        (State := State) enc)
      (G := G) (W := W) (feature := feature) (witness := witness)

theorem finitePointwiseLogRatioBits_toEvidenceMembershipContext_eq_ve_query_score
    (enc : Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder Obj Con Srt Query)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate BinaryEvidence)
    (W : State) (feature witness : Con) :
    Interpretation.finitePointwiseLogRatioBits
        (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
          (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
            (State := State) enc) G W) feature witness =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                  (State := State) enc) G W) feature witness)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                  (State := State) enc) G W) feature witness)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                  (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                    (State := State) enc) G W) feature witness)
                [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                (State := State) enc) G W) feature witness)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                  (Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
                    (State := State) enc) G W) feature witness) []) := by
  simpa using
    EvidenceMembershipContext.finitePointwiseLogRatioBits_crispInterpretationAt_eq_ve_query_score
      (M := Mettapedia.Logic.ConceptOntology.MembershipQueryBuilder.toEvidenceMembershipContext
        (State := State) enc)
      (G := G) (W := W) (feature := feature) (witness := witness)

end MembershipQueryBuilderBridge

end MembershipQueryBuilderFinitePairBridge

section ObservationSurfaceFinitePairBridge

namespace ObservationSurfaceBridge

variable {Obs Obj Con : Type*}
variable [Fintype Obj] [Nonempty Obj]

theorem finitePriorProb_inducedContext_eq_veWeight_ratio
    (S : Mettapedia.Logic.ConceptOntology.ObservationSurface Obs Obj Con BinaryEvidence)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate BinaryEvidence)
    (σ : Multiset Obs) (feature witness : Con) :
    letI : Mettapedia.Logic.EvidenceClass.EvidenceType (Multiset Obs) :=
      Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType Obs
    Interpretation.finitePriorProb
        (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
          (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ) witness =
      (FiniteWitnessFeatureTable.veWeight
        (Interpretation.toFiniteWitnessFeatureTable
          (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
            (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
          feature witness)
        [⟨MembershipConcept.witness, true⟩] : ℝ) /
        FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
            feature witness) [] := by
  letI : Mettapedia.Logic.EvidenceClass.EvidenceType (Multiset Obs) :=
    Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType Obs
  simpa using
    EvidenceMembershipContext.finitePriorProb_crispInterpretationAt_eq_veWeight_ratio
      (M := Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S)
      (G := G) (W := σ) (feature := feature) (witness := witness)

theorem finiteExtensionalProb_inducedContext_eq_bp_ratio
    (S : Mettapedia.Logic.ConceptOntology.ObservationSurface Obs Obj Con BinaryEvidence)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate BinaryEvidence)
    (σ : Multiset Obs) (feature witness : Con) :
    letI : Mettapedia.Logic.EvidenceClass.EvidenceType (Multiset Obs) :=
      Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType Obs
    Interpretation.finiteExtensionalProb
        (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
          (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
        feature witness =
      if FiniteWitnessFeatureTable.featureMessage
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
            feature witness) true = 0 then
        0
      else
        (FiniteWitnessFeatureTable.jointFactorBelief
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
            feature witness)
          (FiniteWitnessFeatureTable.ttJointAssign
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
              feature witness)) : ℝ) /
          FiniteWitnessFeatureTable.featureMessage
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
              feature witness) true := by
  letI : Mettapedia.Logic.EvidenceClass.EvidenceType (Multiset Obs) :=
    Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType Obs
  simpa using
    EvidenceMembershipContext.finiteExtensionalProb_crispInterpretationAt_eq_bp_ratio
      (M := Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S)
      (G := G) (W := σ) (feature := feature) (witness := witness)

theorem finitePointwiseLogRatioBits_inducedContext_eq_ve_query_score
    (S : Mettapedia.Logic.ConceptOntology.ObservationSurface Obs Obj Con BinaryEvidence)
    (G : Mettapedia.Logic.ConceptOntology.EvidenceGate BinaryEvidence)
    (σ : Multiset Obs) (feature witness : Con) :
    letI : Mettapedia.Logic.EvidenceClass.EvidenceType (Multiset Obs) :=
      Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType Obs
    Interpretation.finitePointwiseLogRatioBits
        (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
          (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
        feature witness =
      logRatioInformationGainFromEvidence
        (if FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
              feature witness)
            [⟨MembershipConcept.feature, true⟩] = 0 then
          0
        else
          (FiniteWitnessFeatureTable.veWeight
            (Interpretation.toFiniteWitnessFeatureTable
              (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
              feature witness)
            [⟨MembershipConcept.feature, true⟩, ⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                  (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
                feature witness)
              [⟨MembershipConcept.feature, true⟩])
        ((FiniteWitnessFeatureTable.veWeight
          (Interpretation.toFiniteWitnessFeatureTable
            (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
              (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
            feature witness)
          [⟨MembershipConcept.witness, true⟩] : ℝ) /
            FiniteWitnessFeatureTable.veWeight
              (Interpretation.toFiniteWitnessFeatureTable
                (Mettapedia.Logic.IntensionalInheritance.EvidenceMembershipContext.crispInterpretationAt
                  (Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S) G σ)
                feature witness) []) := by
  letI : Mettapedia.Logic.EvidenceClass.EvidenceType (Multiset Obs) :=
    Mettapedia.Logic.PLNWorldModelAdditive.multisetEvidenceType Obs
  simpa using
    EvidenceMembershipContext.finitePointwiseLogRatioBits_crispInterpretationAt_eq_ve_query_score
      (M := Mettapedia.Logic.ConceptOntology.ObservationSurface.inducedContext S)
      (G := G) (W := σ) (feature := feature) (witness := witness)

end ObservationSurfaceBridge

end ObservationSurfaceFinitePairBridge

end Mettapedia.Logic.IntensionalInheritance
