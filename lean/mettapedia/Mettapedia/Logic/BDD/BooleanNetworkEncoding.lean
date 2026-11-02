import Mettapedia.Logic.BDD.TseitinCounting
import Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.SeparatorFactorization
import Mettapedia.ProbabilityTheory.FiniteWeightedExtension
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Boolean Bayesian networks as independent chance bits and selection constraints

Each supplied CPT row supplies one Bernoulli chance bit. A full equivalence
selects the row matching the observed parents. Unused row bits keep their
original probability law. A division-free completion kernel proves the marginal
equals the original CPT product, even on zero-probability assignments.

Chance probabilities are genuine probabilities. State bits receive neutral
counting weight, separately from the Tseitin compiler's own auxiliary correction.
The encoding uses one chance bit per CPT row, not one bit per complete network
world. No bound on the resulting BDD size is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.BooleanNetworkEncoding

open scoped NNReal ENNReal BigOperators
open LO.Propositional (Formula)
open PropositionalTseitin TseitinCounting
open Mettapedia.ProbabilityTheory FiniteFunctionalExtension FiniteWeightedExtension
open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork.DiscreteCPT

variable {n : Nat}

/-- Boolean state spaces on the existing DAG carrier. -/
def network (graph : DirectedGraph (Fin n)) (acyclic : graph.IsAcyclic) : BayesianNetwork (Fin n) where
  graph := graph
  acyclic := acyclic
  stateSpace _ := Bool
  measurableSpace _ := inferInstance

variable (graph : DirectedGraph (Fin n)) (acyclic : graph.IsAcyclic) [DecidableRel graph.edges]

instance networkEdgesDecidable : DecidableRel (network graph acyclic).graph.edges :=
  inferInstanceAs (DecidableRel graph.edges)

def parents (v : Fin n) : Finset (Fin n) := Finset.univ.filter fun u => graph.edges u v

@[simp] theorem mem_parents (u v : Fin n) : u ∈ parents graph v ↔ graph.edges u v := by
  simp [parents]

abbrev Row (v : Fin n) := Fin (2 ^ (parents graph v).card)
abbrev Chance := (v : Fin n) × Row graph v
def chanceCount : Nat := ∑ v, 2 ^ (parents graph v).card

def chanceEquiv : Chance graph ≃ Fin (chanceCount graph) := finSigmaFinEquiv

/-- Parent indices increase; row bits use the existing little-endian convention. -/
def rowEquiv (v : Fin n) : Row graph v ≃ (network graph acyclic).ParentAssignment v where
  toFun row u hu := WMPLNBDDWMCExact.worldAssignmentEquiv _ row
    (((parents graph v).orderIsoOfFin rfl).symm ⟨u, (mem_parents graph u v).mpr hu⟩)
  invFun assignment := (WMPLNBDDWMCExact.worldAssignmentEquiv _).symm
    (fun i => assignment ((parents graph v).orderIsoOfFin rfl i).val
      ((mem_parents graph _ v).mp ((parents graph v).orderIsoOfFin rfl i).property))
  left_inv row := by
    apply (WMPLNBDDWMCExact.worldAssignmentEquiv _).injective
    simp only [Equiv.apply_symm_apply]
    funext i
    change WMPLNBDDWMCExact.worldAssignmentEquiv _ row
      (((parents graph v).orderIsoOfFin rfl).symm ((parents graph v).orderIsoOfFin rfl i)) = _
    rw [OrderIso.symm_apply_apply]
  right_inv assignment := by
    funext u hu
    refine (congrFun ((WMPLNBDDWMCExact.worldAssignmentEquiv _).apply_symm_apply
      (fun i => assignment ((parents graph v).orderIsoOfFin rfl i).val
        ((mem_parents graph _ v).mp ((parents graph v).orderIsoOfFin rfl i).property))) _).trans ?_
    change (fun p : parents graph v => assignment p.val ((mem_parents graph p.val v).mp p.property))
      ((parents graph v).orderIsoOfFin rfl
        (((parents graph v).orderIsoOfFin rfl).symm ⟨u, (mem_parents graph u v).mpr hu⟩)) = _
    rw [OrderIso.apply_symm_apply]

def parentRow (input : Fin n → Bool) (v : Fin n) : Row graph v :=
  (rowEquiv graph acyclic v).symm (fun u _ => input u)

@[simp] theorem rowEquiv_parentRow (input : Fin n → Bool) (v : Fin n) :
    rowEquiv graph acyclic v (parentRow graph acyclic input v) = (fun u _ => input u) :=
  (rowEquiv graph acyclic v).apply_symm_apply _

variable (cpt : (network graph acyclic).DiscreteCPT)

noncomputable def rowWeight (chance : Chance graph) (value : Bool) : ℝ≥0 :=
  (cpt.cpt chance.1 (rowEquiv graph acyclic chance.1 chance.2) value).toNNReal

@[simp] theorem coe_rowWeight (chance : Chance graph) (value : Bool) :
    (rowWeight graph acyclic cpt chance value : ℝ≥0∞) =
      cpt.cpt chance.1 (rowEquiv graph acyclic chance.1 chance.2) value := by
  exact ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)

theorem rowWeight_sum (chance : Chance graph) : ∑ value, rowWeight graph acyclic cpt chance value = 1 := by
  apply ENNReal.coe_injective
  push_cast
  simp only [coe_rowWeight]
  exact pmf_sum_eq_one _

noncomputable def chanceProbability (i : Fin (chanceCount graph)) : ℝ≥0 :=
  rowWeight graph acyclic cpt ((chanceEquiv graph).symm i) true

theorem rowWeight_le_one (chance : Chance graph) (value : Bool) :
    rowWeight graph acyclic cpt chance value ≤ 1 := by
  rw [← rowWeight_sum graph acyclic cpt chance]
  exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ value)

theorem rowWeight_eq (chance : Chance graph) (value : Bool) :
    rowWeight graph acyclic cpt chance value =
      if value then rowWeight graph acyclic cpt chance true else 1 - rowWeight graph acyclic cpt chance true := by
  cases value with
  | true => rfl
  | false =>
    have total := rowWeight_sum graph acyclic cpt chance
    rw [Fintype.sum_bool] at total
    exact eq_tsub_of_add_eq (by simpa only [add_comm] using total)

noncomputable def chanceWeight (bits : Chance graph → Bool) : ℝ≥0 :=
  ∏ chance, rowWeight graph acyclic cpt chance (bits chance)

theorem chanceWeight_total : ∑ bits, chanceWeight graph acyclic cpt bits = 1 := by
  unfold chanceWeight
  rw [← Fintype.prod_sum]
  simp only [rowWeight_sum, Finset.prod_const_one]

/-- This is the supplied CPT product expressed in finite nonnegative weights. -/
noncomputable def sourceWeight (input : Fin n → Bool) : ℝ≥0 :=
  ∏ v, rowWeight graph acyclic cpt ⟨v, parentRow graph acyclic input v⟩ (input v)

theorem coe_sourceWeight (input : Fin n → Bool) :
    (sourceWeight graph acyclic cpt input : ℝ≥0∞) = cpt.jointWeight input := by
  simp only [sourceWeight, jointWeight, nodeProb]
  push_cast
  simp only [coe_rowWeight, rowEquiv_parentRow]
  rfl

def Selects (input : Fin n → Bool) (bits : Chance graph → Bool) : Prop :=
  ∀ v, bits ⟨v, parentRow graph acyclic input v⟩ = input v

instance selectsDecidable (input : Fin n → Bool) (bits : Chance graph → Bool) :
    Decidable (Selects graph acyclic input bits) := by unfold Selects; infer_instance

/-- Selected rows are clamped; every unused row retains the supplied CPT law. -/
noncomputable def completionFactor (input : Fin n → Bool) (chance : Chance graph) (value : Bool) : ℝ≥0 :=
  if chance.2 = parentRow graph acyclic input chance.1 then (if value = input chance.1 then 1 else 0)
  else rowWeight graph acyclic cpt chance value

noncomputable def completionKernel (input : Fin n → Bool) (bits : Chance graph → Bool) : ℝ≥0 :=
  ∏ chance, completionFactor graph acyclic cpt input chance (bits chance)

theorem completionFactor_sum (input : Fin n → Bool) (chance : Chance graph) :
    ∑ value, completionFactor graph acyclic cpt input chance value = 1 := by
  unfold completionFactor
  split_ifs with selected
  · simp
  · exact rowWeight_sum graph acyclic cpt chance

theorem completionKernel_normalized (input : Fin n → Bool) :
    rowMass (completionKernel graph acyclic cpt) input = 1 := by
  unfold rowMass completionKernel
  rw [← Fintype.prod_sum]
  simp only [completionFactor_sum, Finset.prod_const_one]

private theorem selected_row_product (input : Fin n → Bool) (bits : Chance graph → Bool)
    (selected : Selects graph acyclic input bits) (v : Fin n) :
    rowWeight graph acyclic cpt ⟨v, parentRow graph acyclic input v⟩ (input v) *
        ∏ row, completionFactor graph acyclic cpt input ⟨v, row⟩ (bits ⟨v, row⟩) =
      ∏ row, rowWeight graph acyclic cpt ⟨v, row⟩ (bits ⟨v, row⟩) := by
  classical
  let chosen := parentRow graph acyclic input v
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Row graph v))
    (fun row => completionFactor graph acyclic cpt input ⟨v, row⟩ (bits ⟨v, row⟩)) (Finset.mem_univ chosen)]
  have atChosen : completionFactor graph acyclic cpt input ⟨v, chosen⟩ (bits ⟨v, chosen⟩) = 1 := by
    simp [completionFactor, chosen, selected v]
  rw [atChosen, one_mul]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Row graph v))
    (fun row => rowWeight graph acyclic cpt ⟨v, row⟩ (bits ⟨v, row⟩)) (Finset.mem_univ chosen)]
  rw [show bits ⟨v, chosen⟩ = input v from selected v]
  congr 1
  apply Finset.prod_congr rfl
  intro row member
  have different := (Finset.mem_erase.mp member).1
  simp [completionFactor, different, chosen] at *

/-- The independently constructed kernel agrees with the chance/constraint product. -/
theorem weighted_extension_eq_selection (input : Fin n → Bool) (bits : Chance graph → Bool) :
    sourceWeight graph acyclic cpt input * completionKernel graph acyclic cpt input bits =
      chanceWeight graph acyclic cpt bits * if Selects graph acyclic input bits then 1 else 0 := by
  classical
  by_cases selected : Selects graph acyclic input bits
  · simp only [selected, if_true, mul_one, sourceWeight, completionKernel, chanceWeight,
      Fintype.prod_sigma, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _ => selected_row_product graph acyclic cpt input bits selected v)
  · have failed : ∃ v, bits ⟨v, parentRow graph acyclic input v⟩ ≠ input v := by
      simpa only [Selects, not_forall] using selected
    obtain ⟨v, failed⟩ := failed
    have kernelZero : completionKernel graph acyclic cpt input bits = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ ⟨v, parentRow graph acyclic input v⟩)
      simp [completionFactor, failed]
    simp [selected, kernelZero]

noncomputable def selectionWeight (world : (Fin n → Bool) × (Chance graph → Bool)) : ℝ≥0 :=
  chanceWeight graph acyclic cpt world.2 * if Selects graph acyclic world.1 world.2 then 1 else 0

theorem selectionWeight_eq_extension :
    selectionWeight graph acyclic cpt =
      weightedExtend (completionKernel graph acyclic cpt) (sourceWeight graph acyclic cpt) := by
  funext world
  exact (weighted_extension_eq_selection graph acyclic cpt world.1 world.2).symm

/-- The marginal law is an application of the existing weighted-extension criterion. -/
theorem selection_mass :
    observationMass (selectionWeight graph acyclic cpt) Prod.fst =
      observationMass (sourceWeight graph acyclic cpt) id := by
  rw [selectionWeight_eq_extension]
  exact (weighted_mass_eq_for_all_iff _).mpr (completionKernel_normalized graph acyclic cpt) _

theorem selection_marginal : marginalize (selectionWeight graph acyclic cpt) = sourceWeight graph acyclic cpt :=
  (mass_eq_iff_marginal _ _).mp (selection_mass graph acyclic cpt)

theorem sourceWeight_total : ∑ input, sourceWeight graph acyclic cpt input = 1 := by
  apply ENNReal.coe_injective
  push_cast
  simp only [coe_sourceWeight]
  let : ∀ v, Fintype ((network graph acyclic).stateSpace v) := fun _ => inferInstanceAs (Fintype Bool)
  let : ∀ v, Nonempty ((network graph acyclic).stateSpace v) := fun _ => inferInstanceAs (Nonempty Bool)
  exact jointWeight_sum_eq_one cpt

/-- Freeze every CPT row to the corresponding supplied chance bit. -/
noncomputable def deterministicCPT (bits : Chance graph → Bool) : (network graph acyclic).DiscreteCPT where
  cpt v assignment := PMF.pure (bits ⟨v, (rowEquiv graph acyclic v).symm assignment⟩)

theorem deterministic_joint (bits : Chance graph → Bool) (input : Fin n → Bool) :
    (deterministicCPT graph acyclic bits).jointWeight input =
      if Selects graph acyclic input bits then 1 else 0 := by
  classical
  unfold jointWeight nodeProb deterministicCPT parentAssignOfConfig
  by_cases selected : Selects graph acyclic input bits
  · rw [if_pos selected]
    apply Finset.prod_eq_one
    intro v _
    change (PMF.pure (bits ⟨v, parentRow graph acyclic input v⟩)) (input v) = 1
    simp [selected v]
  · rw [if_neg selected]
    obtain ⟨v, failed⟩ : ∃ v, bits ⟨v, parentRow graph acyclic input v⟩ ≠ input v := by
      simpa only [Selects, not_forall] using selected
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    change (PMF.pure (bits ⟨v, parentRow graph acyclic input v⟩)) (input v) = 0
    simp [Ne.symm failed]

/-- Acyclicity gives exactly one selected state for every chance assignment,
by the existing normalization theorem applied to deterministic CPTs. -/
theorem selection_unique (bits : Chance graph → Bool) :
    ∃! input : Fin n → Bool, Selects graph acyclic input bits := by
  classical
  let models := Finset.univ.filter fun input : Fin n → Bool => Selects graph acyclic input bits
  have countOne : (models.card : ℝ≥0∞) = 1 := by
    have total := sourceWeight_total graph acyclic (deterministicCPT graph acyclic bits)
    have castTotal := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) total
    simp only [ENNReal.ofNNReal_finsetSum, coe_sourceWeight, ENNReal.coe_one,
      deterministic_joint] at castTotal
    simpa [models] using castTotal
  have cardOne : models.card = 1 := by exact_mod_cast countOne
  obtain ⟨input, same⟩ := Finset.card_eq_one.mp cardOne
  have member (other : Fin n → Bool) : Selects graph acyclic other bits ↔ other = input := by
    have equivalence : other ∈ models ↔ other = input := by rw [same, Finset.mem_singleton]
    simpa [models] using equivalence
  exact ⟨input, (member input).mpr rfl, fun other held => (member other).mp held⟩

/-! ## Actual Boolean selection formulas -/

def allFormulas {α : Type*} : List (Formula α) → Formula α
  | [] => .imp .falsum .falsum
  | formula :: rest => .and formula (allFormulas rest)

theorem eval_allFormulas {α : Type*} (world : α → Bool) (formulas : List (Formula α)) :
    eval world (allFormulas formulas) = true ↔ ∀ formula ∈ formulas, eval world formula = true := by
  induction formulas <;> simp_all [allFormulas, eval]

def bitFormula {α : Type*} (atom : α) (value : Bool) : Formula α :=
  if value then .atom atom else .imp (.atom atom) .falsum

theorem eval_bitFormula {α : Type*} (world : α → Bool) (atom : α) (value : Bool) :
    eval world (bitFormula atom value) = true ↔ world atom = value := by
  cases value <;> cases h : world atom <;> simp [bitFormula, eval, h]

def equivalenceFormula {α : Type*} (first second : Formula α) : Formula α :=
  .and (.imp first second) (.imp second first)

theorem eval_equivalenceFormula {α : Type*} (world : α → Bool) (first second : Formula α) :
    eval world (equivalenceFormula first second) = true ↔ eval world first = eval world second := by
  cases hf : eval world first <;> cases hs : eval world second <;> simp [equivalenceFormula, eval, hf, hs]

theorem eval_imp_true {α : Type*} (world : α → Bool) (first second : Formula α) :
    eval world (.imp first second) = true ↔ (eval world first = true → eval world second = true) := by
  cases hf : eval world first <;> cases hs : eval world second <;> simp [eval, hf, hs]

def parentFormula (v : Fin n) (row : Row graph v) : Formula (Fin (n + chanceCount graph)) :=
  allFormulas ((List.finRange (parents graph v).card).map fun i =>
    bitFormula (Fin.castAdd (chanceCount graph) ((parents graph v).orderIsoOfFin rfl i).val)
      (WMPLNBDDWMCExact.worldAssignmentEquiv _ row i))

theorem parentRow_eq_iff (input : Fin n → Bool) (v : Fin n) (row : Row graph v) :
    parentRow graph acyclic input v = row ↔
      ∀ i, input ((parents graph v).orderIsoOfFin rfl i).val =
        WMPLNBDDWMCExact.worldAssignmentEquiv _ row i := by
  change (WMPLNBDDWMCExact.worldAssignmentEquiv _).symm
    (fun i => input ((parents graph v).orderIsoOfFin rfl i).val) = row ↔ _
  rw [Equiv.symm_apply_eq]
  exact funext_iff

theorem parentFormula_correct (input : Fin n → Bool) (bits : Fin (chanceCount graph) → Bool)
    (v : Fin n) (row : Row graph v) :
    eval (joinedAssignment input bits) (parentFormula graph v row) = true ↔
      parentRow graph acyclic input v = row := by
  rw [parentRow_eq_iff]
  simp [parentFormula, eval_allFormulas, eval_bitFormula, joinedAssignment]

def selectionFormula : Formula (Fin (n + chanceCount graph)) :=
  allFormulas ((List.finRange n).flatMap fun v =>
    (List.finRange (2 ^ (parents graph v).card)).map fun row =>
      .imp (parentFormula graph v row)
        (equivalenceFormula (.atom (Fin.castAdd (chanceCount graph) v))
          (.atom (Fin.natAdd n (chanceEquiv graph ⟨v, row⟩)))))

theorem selectionFormula_correct (input : Fin n → Bool) (bits : Fin (chanceCount graph) → Bool) :
    eval (joinedAssignment input bits) (selectionFormula graph) = true ↔
      Selects graph acyclic input (bits ∘ chanceEquiv graph) := by
  simp only [selectionFormula, eval_allFormulas, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_finRange, forall_const, eval_imp_true, parentFormula_correct graph acyclic,
    eval_equivalenceFormula]
  simp only [eval, joinedAssignment, Fin.addCases_left, Fin.addCases_right]
  constructor
  · intro all v
    exact (all v (parentRow graph acyclic input v) rfl).symm
  · intro all v row selected
    subst row
    exact (all v).symm

def relabel {α β : Type*} (rename : α → β) : Formula α → Formula β
  | .atom atom => .atom (rename atom)
  | .falsum => .falsum
  | .and a b => .and (relabel rename a) (relabel rename b)
  | .or a b => .or (relabel rename a) (relabel rename b)
  | .imp a b => .imp (relabel rename a) (relabel rename b)

theorem eval_relabel {α β : Type*} (rename : α → β) (formula : Formula α) (world : β → Bool) :
    eval world (relabel rename formula) = eval (world ∘ rename) formula := by
  induction formula <;> simp_all [relabel, eval]

def encodedFormula (formula : Formula (Fin n)) : Formula (Fin (n + chanceCount graph)) :=
  .and (selectionFormula graph) (relabel (Fin.castAdd (chanceCount graph)) formula)

theorem encodedFormula_correct (formula : Formula (Fin n)) (input : Fin n → Bool)
    (bits : Fin (chanceCount graph) → Bool) :
    eval (joinedAssignment input bits) (encodedFormula graph formula) = true ↔
      Selects graph acyclic input (bits ∘ chanceEquiv graph) ∧ eval input formula = true := by
  have restricted : joinedAssignment input bits ∘ Fin.castAdd (chanceCount graph) = input := by
    funext i
    simp [joinedAssignment]
  simp only [encodedFormula, eval, Bool.and_eq_true, selectionFormula_correct graph acyclic,
    eval_relabel, restricted]

def chanceAssignmentEquiv : (Fin (chanceCount graph) → Bool) ≃ (Chance graph → Bool) where
  toFun bits := bits ∘ chanceEquiv graph
  invFun bits := bits ∘ (chanceEquiv graph).symm
  left_inv bits := by funext i; simp
  right_inv bits := by funext i; simp

theorem productWeight_chance (bits : Fin (chanceCount graph) → Bool) :
    productWeight (chanceProbability graph acyclic cpt) bits =
      chanceWeight graph acyclic cpt (bits ∘ chanceEquiv graph) := by
  unfold productWeight chanceWeight
  rw [← (chanceEquiv graph).prod_comp]
  apply Finset.prod_congr rfl
  intro chance _
  simp only [chanceProbability, Equiv.symm_apply_apply, Function.comp_apply]
  exact (rowWeight_eq graph acyclic cpt chance (bits (chanceEquiv graph chance))).symm

theorem productWeight_join {m k : Nat} (first : Fin m → ℝ≥0) (second : Fin k → ℝ≥0)
    (left : Fin m → Bool) (right : Fin k → Bool) :
    productWeight (Fin.addCases first second) (joinedAssignment left right) =
      productWeight first left * productWeight second right := by
  simp only [productWeight, joinedAssignment, Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]

/-- Chance probabilities are unchanged; state bits are neutral bookkeeping variables. -/
noncomputable def countingPrior : Fin (n + chanceCount graph) → ℝ≥0 :=
  Fin.addCases (fun _ => 1/2) (chanceProbability graph acyclic cpt)

theorem countingPrior_le_one (i : Fin (n + chanceCount graph)) : countingPrior graph acyclic cpt i ≤ 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    norm_num [countingPrior]
  · intro j
    simpa [countingPrior, chanceProbability] using
      rowWeight_le_one graph acyclic cpt ((chanceEquiv graph).symm j) true

theorem selection_query_sum (formula : Formula (Fin n)) :
    (∑ input, ∑ bits, if Selects graph acyclic input bits ∧ eval input formula = true
      then chanceWeight graph acyclic cpt bits else 0) =
      ∑ input, if eval input formula then sourceWeight graph acyclic cpt input else 0 := by
  have preserved := congrArg (fun mass => mass.queryMass (fun input => eval input formula))
    (selection_mass graph acyclic cpt)
  simp only [observationMass, selectionWeight, Fintype.sum_prod_type, id_eq] at preserved
  calc
    _ = ∑ input, ∑ bits, if eval input formula then
        chanceWeight graph acyclic cpt bits * (if Selects graph acyclic input bits then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro input _
      apply Finset.sum_congr rfl
      intro bits _
      split_ifs <;> simp_all
    _ = _ := ENNReal.coe_inj.mp preserved

theorem encoded_weight_sum (formula : Formula (Fin n)) :
    (∑ world, if eval world (encodedFormula graph formula) then
      productWeight (countingPrior graph acyclic cpt) world else 0) =
      (1/2 : ℝ≥0) ^ n * ∑ input, if eval input formula then sourceWeight graph acyclic cpt input else 0 := by
  rw [← (assignmentEquiv n (chanceCount graph)).sum_comp]
  change (∑ world : (Fin n → Bool) × (Fin (chanceCount graph) → Bool),
    if eval (joinedAssignment world.1 world.2) (encodedFormula graph formula) then
      productWeight (countingPrior graph acyclic cpt) (joinedAssignment world.1 world.2) else 0) = _
  simp only [Fintype.sum_prod_type, encodedFormula_correct graph acyclic]
  rw [← selection_query_sum graph acyclic cpt formula, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [← (chanceAssignmentEquiv graph).sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bits _
  unfold countingPrior
  rw [productWeight_join, productWeight_half, productWeight_chance]
  split_ifs <;> simp_all [chanceAssignmentEquiv]

/-- Correction for state bits only. Tseitin auxiliaries have their own correction in `tseitinCount`. -/
noncomputable def stateCountingFactor : ℝ≥0∞ := 2 ^ n

noncomputable def bnCount (formula : Formula (Fin n)) : ℝ≥0∞ :=
  stateCountingFactor (n := n) * tseitinCount (encodedFormula graph formula) (countingPrior graph acyclic cpt)

/-- One existing BDD counting call computes the original BN query mass. -/
theorem bnCount_correct (formula : Formula (Fin n)) :
    bnCount graph acyclic cpt formula = ∑ input, if eval input formula then cpt.jointWeight input else 0 := by
  rw [bnCount, tseitinCount_correct _ _ (countingPrior_le_one graph acyclic cpt)]
  have castSum := congrArg (fun value : ℝ≥0 => (value : ℝ≥0∞))
    (encoded_weight_sum graph acyclic cpt formula)
  simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat,
    apply_ite (fun value : ℝ≥0 => (value : ℝ≥0∞)), ENNReal.coe_zero, coe_sourceWeight] at castSum
  rw [castSum, stateCountingFactor]
  have cancel : (2 : ℝ≥0∞)^n * (1/2 : ℝ≥0∞)^n = 1 := by
    rw [← mul_pow]
    norm_num [ENNReal.mul_inv_cancel]
  rw [← mul_assoc, cancel, one_mul]

/-- Conditioning retains the existing absent answer for impossible evidence. -/
theorem bnCount_query (evidence query : Formula (Fin n)) :
    countQuery (bnCount graph acyclic cpt) evidence query =
      (observationMass (PropositionalTseitinMass.sourceWeight evidence (sourceWeight graph acyclic cpt)) id).query
        (fun input => eval input query) := by
  apply countQuery_correct
  intro formula
  simpa only [coe_sourceWeight] using bnCount_correct graph acyclic cpt formula

/-- The original CPT factor graph is retained as a second exact readout. -/
theorem bnCount_factorGraph (formula : Formula (Fin n)) :
    bnCount graph acyclic cpt formula =
      ∑ input : Fin n → Bool, if eval input formula then cpt.toFactorGraph.unnormalizedJoint input else 0 := by
  calc
    _ = ∑ input, if eval input formula then cpt.jointWeight input else 0 :=
      bnCount_correct graph acyclic cpt formula
    _ = _ := Finset.sum_congr rfl (fun input _ =>
      congrArg (fun value => if eval input formula then value else 0)
        (toFactorGraph_unnormalizedJoint_eq cpt input).symm)

theorem bnCount_normalized : bnCount graph acyclic cpt (.imp .falsum .falsum) = 1 := by
  rw [bnCount_correct]
  simp only [eval, Bool.not_false, Bool.true_or, if_true]
  let : ∀ v, Fintype ((network graph acyclic).stateSpace v) := fun _ => inferInstanceAs (Fintype Bool)
  let : ∀ v, Nonempty ((network graph acyclic).stateSpace v) := fun _ => inferInstanceAs (Nonempty Bool)
  exact jointWeight_sum_eq_one cpt

namespace Controls

/-- A parentless fair root with any finite number of children copying it. -/
def starGraph (children : Nat) : DirectedGraph (Fin (children + 1)) where
  edges u v := u = 0 ∧ v ≠ 0

instance starDecidable (children : Nat) : DecidableRel (starGraph children).edges :=
  fun u v => inferInstanceAs (Decidable (u = 0 ∧ v ≠ 0))

theorem starAcyclic (children : Nat) : (starGraph children).IsAcyclic := by
  intro v ⟨u, ⟨root, nonroot⟩, path⟩
  subst v
  cases path with
  | refl => exact nonroot rfl
  | step edge _ => exact nonroot edge.1

noncomputable def fairPMF : PMF Bool :=
  PMF.ofFintype (fun _ => 1/2) (by norm_num [Fintype.sum_bool, ENNReal.mul_inv_cancel])

noncomputable def starCPT (children : Nat) : (network (starGraph children) (starAcyclic children)).DiscreteCPT where
  cpt v assignment := if root : v = 0 then fairPMF
    else PMF.pure (assignment 0 ⟨rfl, root⟩)

theorem star_nodeProb (children : Nat) (input : Fin (children + 1) → Bool) (v : Fin (children + 1)) :
    (starCPT children).nodeProb input v =
      if v = 0 then 1/2 else if input v = input 0 then 1 else 0 := by
  change (if root : v = 0 then fairPMF else PMF.pure (input 0)) (input v) = _
  by_cases root : v = 0
  · subst v
    rfl
  · rw [dif_neg root, if_neg root]
    by_cases same : input v = input 0 <;> simp [PMF.pure_apply, same]

theorem star_joint (children : Nat) (input : Fin (children + 1) → Bool) :
    (starCPT children).jointWeight input = if ∀ v, input v = input 0 then 1/2 else 0 := by
  classical
  unfold jointWeight
  by_cases same : ∀ v, input v = input 0
  · rw [if_pos same, ← Finset.mul_prod_erase (Finset.univ : Finset (Fin (children + 1)))
      ((starCPT children).nodeProb input) (Finset.mem_univ 0)]
    rw [star_nodeProb]
    have rest : ∏ v ∈ (Finset.univ : Finset (Fin (children + 1))).erase 0,
        (starCPT children).nodeProb input v = 1 := by
      apply Finset.prod_eq_one
      intro v member
      rw [star_nodeProb, if_neg (Finset.mem_erase.mp member).1, if_pos (same v)]
    rw [rest, mul_one]
    simp
  · rw [if_neg same]
    obtain ⟨v, different⟩ := not_forall.mp same
    have nonroot : v ≠ 0 := by intro equal; exact different (congrArg input equal)
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [star_nodeProb, if_neg nonroot, if_neg different]

theorem parentless_has_one_chance_bit : chanceCount (starGraph 0) = 1 := by decide
theorem copy_has_three_chance_bits : chanceCount (starGraph 1) = 3 := by decide
theorem fork_has_five_chance_bits : chanceCount (starGraph 2) = 5 := by decide

theorem star_root_count (children : Nat) :
    bnCount (starGraph children) (starAcyclic children) (starCPT children) (.atom 0) = 1/2 := by
  rw [bnCount_correct]
  have term (input : Fin (children + 1) → Bool) :
      (if eval input (.atom 0) then (starCPT children).jointWeight input else 0) =
        if input = (fun _ => true) then (1/2 : ℝ≥0∞) else 0 := by
    by_cases allTrue : input = (fun _ => true)
    · subst input
      simp [star_joint, eval]
    · by_cases rootTrue : input 0 = true
      · have inconsistent : ¬ ∀ v, input v = input 0 := by
          intro allEqual
          apply allTrue
          funext v
          exact (allEqual v).trans rootTrue
        rw [star_joint, if_neg inconsistent]
        simp [allTrue]
      · simp [eval, rootTrue, allTrue]
  simp_rw [term]
  simp

theorem parentless_probability :
    bnCount (starGraph 0) (starAcyclic 0) (starCPT 0) (.atom 0) = 1/2 := star_root_count 0

/-- One call gives the correlated `00/11` law, including zero off-diagonal mass. -/
theorem correlated_copy_count :
    bnCount (starGraph 1) (starAcyclic 1) (starCPT 1) (.and (.atom 0) (.atom 1)) = 1/2 := by
  rw [bnCount_correct]
  have term (input : Fin 2 → Bool) :
      (if eval input (.and (.atom 0) (.atom 1)) then (starCPT 1).jointWeight input else 0) =
        if input = (fun _ => true) then (1/2 : ℝ≥0∞) else 0 := by
    cases h0 : input 0 <;> cases h1 : input 1 <;>
      simp [star_joint, eval, funext_iff, Fin.forall_fin_two, h0, h1]
  simp_rw [term]
  simp

theorem zero_table_entry_preserved : (starCPT 1).jointWeight ![false, true] = 0 := by
  simp [star_joint, Fin.forall_fin_two]

theorem fork_children_count :
    bnCount (starGraph 2) (starAcyclic 2) (starCPT 2) (.and (.atom 1) (.atom 2)) = 1/2 := by
  rw [bnCount_correct]
  have term (input : Fin 3 → Bool) :
      (if eval input (.and (.atom 1) (.atom 2)) then (starCPT 2).jointWeight input else 0) =
        if input = (fun _ => true) then (1/2 : ℝ≥0∞) else 0 := by
    cases h0 : input 0 <;> cases h1 : input 1 <;> cases h2 : input 2 <;>
      simp [star_joint, eval, funext_iff, Fin.forall_fin_succ, h0, h1, h2]
  simp_rw [term]
  simp

theorem positive_evidence_copy :
    countQuery (bnCount (starGraph 1) (starAcyclic 1) (starCPT 1)) (.atom 0) (.atom 1) = some 1 := by
  simp only [countQuery, star_root_count, correlated_copy_count]
  norm_num [ENNReal.div_self]

def copyProbability (privateBit separatorBit : Bool) : ℝ≥0 := if privateBit = separatorBit then 1 else 0

/-- The common-parent example uses exactly the same prior on both representations. -/
theorem fork_prior_factorization (x s y : Bool) :
    (starCPT 2).jointWeight ![s, x, y] =
      ((SeparatorFactorization.graph copyProbability (fun _ : Bool => (1/2 : ℝ≥0))
        (fun s y => copyProbability y s)).unnormalizedJoint
          (SeparatorFactorization.graphConfiguration copyProbability (fun _ : Bool => (1/2 : ℝ≥0))
            (fun s y => copyProbability y s) x s y) : ℝ≥0∞) := by
  rw [SeparatorFactorization.graph_joint]
  cases x <;> cases s <;> cases y <;>
    norm_num [star_joint, copyProbability, Fin.forall_fin_succ]

theorem fork_count_equals_separator :
    bnCount (starGraph 2) (starAcyclic 2) (starCPT 2) (.and (.atom 1) (.atom 2)) =
      ((SeparatorFactorization.graph SeparatorFactorization.Controls.copyTrue
        (fun _ : Bool => (1/2 : ℝ≥0)) (fun s y => SeparatorFactorization.Controls.copyTrue y s)).partitionFunction : ℝ≥0∞) := by
  rw [fork_children_count, SeparatorFactorization.Controls.common_parent_separator]
  norm_num

/-- One state bit and one genuine chance bit, with only the forward implication. -/
def oneWaySelection : Formula (Fin 2) := .imp (.atom 1) (.atom 0)
def fullSelection : Formula (Fin 2) := equivalenceFormula (.atom 0) (.atom 1)

theorem oneWay_count : tseitinCount oneWaySelection (fun _ => 1/2) = 3/4 := by
  rw [fair_count]
  have models : PropositionalTseitinMass.Controls.count
      (fun input => eval input oneWaySelection) = 3 := by decide
  norm_num [models]

theorem fullSelection_count : tseitinCount fullSelection (fun _ => 1/2) = 2/4 := by
  rw [fair_count]
  have models : PropositionalTseitinMass.Controls.count
      (fun input => eval input fullSelection) = 2 := by decide
  norm_num [models]

/-- After both bookkeeping corrections, the weak selection still invents mass. -/
theorem oneWay_mass_drift :
    stateCountingFactor (n := 1) * tseitinCount oneWaySelection (fun _ => 1/2) = 3/2 ∧
      stateCountingFactor (n := 1) * tseitinCount fullSelection (fun _ => 1/2) = 1 := by
  rw [oneWay_count, fullSelection_count]
  simp only [stateCountingFactor, pow_one]
  constructor
  · have finite : (2 : ℝ≥0) * (3/4) = 3/2 := by norm_num
    have lifted := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) finite
    simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using lifted
  · norm_num [div_eq_mul_inv, ← mul_assoc, ENNReal.mul_inv_cancel]

theorem oneWay_probability_drift :
    countQuery (fun formula => tseitinCount formula (fun _ => 1/2)) oneWaySelection (.atom 0) =
      some (2/3 : ℝ≥0∞) := by
  have joint : PropositionalTseitinMass.Controls.count
      (fun input : Fin 2 → Bool => eval input (.and oneWaySelection (.atom 0))) = 2 := by decide
  dsimp only [countQuery]
  simp only [oneWay_count]
  rw [fair_count, joint]
  norm_num
  have finite : ((2 : ℝ≥0) / 4) / (3/4) = 2/3 := by norm_num
  have lifted := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) finite
  simpa only [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3/4 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using lifted

end Controls

theorem impossible_evidence_absent (query : Formula (Fin n)) :
    countQuery (bnCount graph acyclic cpt) .falsum query = none := by
  simp [countQuery, bnCount_correct, eval]

end Mettapedia.Logic.BDDCore.BooleanNetworkEncoding
