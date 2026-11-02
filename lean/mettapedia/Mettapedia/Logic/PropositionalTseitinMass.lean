import Mettapedia.Logic.PropositionalTseitin
import Mettapedia.ProbabilityTheory.FiniteWeightedExtension

/-!
# Definitional clauses preserve world mass and mixture revision

Source weights are arbitrary finite nonnegative tables, including correlated
priors. The target multiplies the supplied source weight by the actual emitted
hard-clause potentials. Its auxiliary literals carry neutral counting weight.
Unique gate evaluation identifies this product with the existing deterministic
extension of the source table restricted by the asserted formula.

The resulting interpretation preserves every declared joint observation,
partition mass, conditioning and additive mixture revision. It does not turn
material implications into a logic program's least-model semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.PropositionalTseitinMass

open scoped NNReal ENNReal BigOperators
open LO.Propositional (Formula)
open PropositionalTseitin MarkovLogicClauseSemantics
open Mettapedia.ProbabilityTheory
open FiniteFunctionalExtension FiniteWeightedExtension
open Mettapedia.Logic.WorldModel

abbrev Input (n : Nat) := Fin n → Bool
abbrev Auxiliary {n : Nat} (formula : Formula (Fin n)) := Fin (auxCount formula) → Bool
abbrev World {n : Nat} (formula : Formula (Fin n)) := Input n × Auxiliary formula

/-- Actual multiplication of the hard-clause factors. -/
def clauseProduct {α : Type*} [DecidableEq α] : List (GroundClause α) → (α → Bool) → ℝ≥0
  | [], _ => 1
  | clause :: clauses, world =>
      (if evalClause world clause then 1 else 0) * clauseProduct clauses world

theorem clauseProduct_eq {α : Type*} [DecidableEq α]
    (clauses : List (GroundClause α)) (world : α → Bool) :
    clauseProduct clauses world = if evalCNF clauses world then 1 else 0 := by
  induction clauses with
  | nil => simp [clauseProduct, evalCNF]
  | cons clause clauses ih =>
    by_cases hc : evalClause world clause = true <;>
      by_cases ht : evalCNF clauses world = true <;>
      simp_all [clauseProduct, evalCNF]

/-- Assert the source formula without changing the relative weights of its models. -/
def sourceWeight {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0) : Input n → ℝ≥0 :=
  fun input => if eval input formula then weight input else 0

/-- The compiled weighted CNF, defined by its emitted clauses rather than by source evaluation. -/
def targetWeight {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0) : World formula → ℝ≥0 :=
  fun world => weight world.1 * clauseProduct (compile formula).asserted (read world.1 world.2)

theorem targetWeight_eq_extend {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0) :
    targetWeight formula weight = extend (fun input => realizeAux input formula) (sourceWeight formula weight) := by
  classical
  funext world
  simp only [targetWeight, clauseProduct_eq, asserted_correct, extend, sourceWeight]
  split_ifs <;> simp_all

theorem target_marginal {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0) :
    marginalize (targetWeight formula weight) = sourceWeight formula weight := by
  rw [targetWeight_eq_extend, marginalize_extend]

/-- Every query on source assignments, and total mass, agree before normalization. -/
theorem mass_eq_source {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0) :
    observationMass (targetWeight formula weight) Prod.fst =
      observationMass (sourceWeight formula weight) id :=
  (mass_eq_iff_marginal _ _).mpr (target_marginal formula weight)

/-- Auxiliary observations are licensed by their independently computed source meaning. -/
theorem observation_mass {n : Nat} {View : Type*} (formula : Formula (Fin n))
    (weight : Input n → ℝ≥0) (observe : World formula → View) :
    observationMass (targetWeight formula weight) observe =
      observationMass (sourceWeight formula weight)
        (fun input => observe (input, realizeAux input formula)) := by
  rw [targetWeight_eq_extend, extension_observation_mass]

theorem totalMass_eq {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0) :
    (observationMass (targetWeight formula weight) Prod.fst).totalMass =
      (observationMass (sourceWeight formula weight) id).totalMass :=
  congrArg MassSemantics.totalMass (mass_eq_source formula weight)

/-- Equality includes the absent answer when the asserted source mass is zero. -/
theorem query_eq {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0)
    (query : Input n → Bool) :
    (observationMass (targetWeight formula weight) Prod.fst).query query =
      (observationMass (sourceWeight formula weight) id).query query := by
  rw [mass_eq_source]

def conditionWeight {Ω : Type*} (event : Ω → Bool) (weight : Ω → ℝ≥0) : Ω → ℝ≥0 :=
  fun world => if event world then weight world else 0

theorem targetWeight_condition {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0)
    (event : Input n → Bool) :
    targetWeight formula (conditionWeight event weight) =
      conditionWeight (event ∘ Prod.fst) (targetWeight formula weight) := by
  funext world
  simp [targetWeight, conditionWeight, ite_mul]

theorem sourceWeight_condition {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0)
    (event : Input n → Bool) :
    sourceWeight formula (conditionWeight event weight) =
      conditionWeight event (sourceWeight formula weight) := by
  funext input
  unfold sourceWeight conditionWeight
  split_ifs <;> simp_all

theorem conditioned_mass {n : Nat} (formula : Formula (Fin n)) (weight : Input n → ℝ≥0)
    (event : Input n → Bool) :
    observationMass (conditionWeight (event ∘ Prod.fst) (targetWeight formula weight)) Prod.fst =
      observationMass (conditionWeight event (sourceWeight formula weight)) id := by
  rw [← targetWeight_condition, mass_eq_source, sourceWeight_condition]

theorem targetWeight_add {n : Nat} (formula : Formula (Fin n)) (first second : Input n → ℝ≥0) :
    targetWeight formula (first + second) = targetWeight formula first + targetWeight formula second := by
  funext world
  simp [targetWeight, add_mul]

@[simp] theorem targetWeight_zero {n : Nat} (formula : Formula (Fin n)) :
    targetWeight formula 0 = 0 := by
  funext world
  simp [targetWeight]

@[instance_reducible] noncomputable def sourceModel {n : Nat} (formula : Formula (Fin n)) :
    MonoidalWorldModel (Input n → ℝ≥0) (Input n → Bool) (Option ℝ≥0∞) where
  revise := (· + ·)
  empty := 0
  extract weight query := (observationMass (sourceWeight formula weight) id).query query
  revise_assoc := add_assoc
  revise_empty_left := zero_add
  revise_empty_right := add_zero

/-- Compilation is an interpretation of the existing WM query/revision interface. -/
noncomputable def compiledInterpretation {n : Nat} (formula : Formula (Fin n)) :
    @RevisionMap (Input n → ℝ≥0) (Input n → Bool) (Option ℝ≥0∞)
      (World formula → ℝ≥0) (Input n → Bool) (Option ℝ≥0∞)
      (sourceModel formula).toWorldModel (tableModel Prod.fst).toWorldModel := by
  letI := sourceModel formula
  letI := tableModel (Source := World formula) Prod.fst
  exact {
    state := targetWeight formula
    query := id
    value := id
    observe := query_eq formula
    empty := targetWeight_zero formula
    revise := targetWeight_add formula }

theorem compilation_chronology {n : Nat} (formula : Formula (Fin n))
    (updates : List (Input n → ℝ≥0)) (initial : Input n → ℝ≥0) :
    targetWeight formula (updates.foldl (· + ·) initial) =
      (updates.map (targetWeight formula)).foldl (· + ·) (targetWeight formula initial) := by
  let := sourceModel formula
  let := tableModel (Source := World formula) Prod.fst
  exact (compiledInterpretation formula).foldl_revise updates initial

namespace Controls

/-- Finite Boolean enumeration, independent of the real-valued mass evaluator. -/
def count {Ω : Type*} [Fintype Ω] (predicate : Ω → Bool) : Nat :=
  ∑ world, if predicate world then 1 else 0

def indicator {Ω : Type*} (predicate : Ω → Bool) : Ω → ℝ≥0 :=
  fun world => if predicate world then 1 else 0

theorem indicator_total {Ω View : Type*} [Fintype Ω] (predicate : Ω → Bool) (view : Ω → View) :
    (observationMass (indicator predicate) view).totalMass = (count predicate : ℝ≥0∞) := by
  simp [observationMass, indicator, count]

theorem indicator_queryMass {Ω View : Type*} [Fintype Ω] (predicate : Ω → Bool)
    (view : Ω → View) (query : View → Bool) :
    (observationMass (indicator predicate) view).queryMass query =
      (count (fun world => predicate world && query (view world)) : ℝ≥0∞) := by
  simp only [observationMass, indicator, count]
  push_cast
  apply Finset.sum_congr rfl
  intro world _
  by_cases hp : predicate world = true <;> by_cases hq : query (view world) = true <;>
    simp [hp, hq]

theorem indicator_query {Ω View : Type*} [Fintype Ω] (predicate : Ω → Bool)
    (view : Ω → View) (query : View → Bool) (positive : count predicate ≠ 0) :
    (observationMass (indicator predicate) view).query query =
      some ((count (fun world => predicate world && query (view world)) : ℝ≥0∞) / count predicate) := by
  simp only [MassSemantics.query, MassSemantics.queryProb, indicator_total,
    Nat.cast_eq_zero, positive, if_false, indicator_queryMass]

theorem condition_indicator {Ω : Type*} (predicate event : Ω → Bool) :
    conditionWeight event (indicator predicate) = indicator (fun world => predicate world && event world) := by
  funext world
  by_cases hp : predicate world = true <;> by_cases he : event world = true <;>
    simp [conditionWeight, indicator, hp, he]

def exampleFormula : Formula (Fin 3) := .or (.atom 0) (.and (.atom 1) (.atom 2))

def oneWayClauses : List (GroundClause (Wire 3 1)) :=
  [{.pos (.inl 0), .pos (.inr 0)}, {.neg (.inr 0), .pos (.inl 1)}, {.neg (.inr 0), .pos (.inl 2)}]

def sourceEvent (input : Input 3) : Bool := eval input exampleFormula
def oneWayEvent (world : Input 3 × Bool) : Bool :=
  evalCNF oneWayClauses (read world.1 (fun _ : Fin 1 => world.2))
def compiledEvent (world : World exampleFormula) : Bool :=
  evalCNF (compile exampleFormula).asserted (read world.1 world.2)

theorem oneWay_projects_exactly (input : Input 3) :
    (∃ auxiliary, oneWayEvent (input, auxiliary) = true) ↔ sourceEvent input = true := by
  cases h0 : input 0 <;> cases h1 : input 1 <;> cases h2 : input 2 <;>
    simp [oneWayEvent, oneWayClauses, sourceEvent, exampleFormula, eval,
      evalCNF, evalClause, evalLiteral, PropositionalTseitin.read, h0, h1, h2]

theorem source_models_five : count sourceEvent = 5 := by decide
theorem oneWay_models_six : count oneWayEvent = 6 := by decide
theorem compiled_models_five : count compiledEvent = 5 := by decide
theorem source_p_models_four : count (fun input => sourceEvent input && input 0) = 4 := by decide
theorem oneWay_p_models_five : count (fun world => oneWayEvent world && world.1 0) = 5 := by decide

/-- SAT preservation and projection correctness do not prevent normalization bias. -/
theorem oneWay_probability_bias :
    (observationMass (indicator sourceEvent) id).query (fun input => input 0) = some (4/5 : ℝ≥0∞) ∧
      (observationMass (indicator oneWayEvent) Prod.fst).query (fun input => input 0) =
        some (5/6 : ℝ≥0∞) := by
  constructor
  · rw [indicator_query _ _ _ (by rw [source_models_five]; decide)]
    norm_num [source_models_five, source_p_models_four]
  · rw [indicator_query _ _ _ (by rw [oneWay_models_six]; decide)]
    norm_num [oneWay_models_six, oneWay_p_models_five]

theorem compiled_probability_correct :
    (observationMass (targetWeight exampleFormula (fun _ => 1)) Prod.fst).query (fun input => input 0) =
      some (4/5 : ℝ≥0∞) := by
  rw [query_eq]
  exact oneWay_probability_bias.1

theorem further_conditioning_correct :
    (observationMass
      (conditionWeight ((fun input : Input 3 => input 0) ∘ Prod.fst)
        (targetWeight exampleFormula (fun _ => 1))) Prod.fst).query (fun input => input 0) =
      some (1 : ℝ≥0∞) := by
  rw [conditioned_mass exampleFormula (fun _ => 1) (fun input => input 0)]
  change (observationMass (conditionWeight (fun input => input 0) (indicator sourceEvent)) id).query
    (fun input => input 0) = _
  rw [condition_indicator, indicator_query _ _ _ (by rw [source_p_models_four]; decide)]
  simp only [Bool.and_assoc]
  norm_num [source_p_models_four, ENNReal.div_self]

def firstBit (input : Input 2) : Bool := input 0

theorem first_bit_models_two : count firstBit = 2 := by decide
theorem both_bits_models_one : count (fun input => firstBit input && input 1) = 1 := by decide

/-- A source variable unused by the asserted formula remains queryable. -/
theorem unused_source_bit_retained :
    (observationMass (targetWeight (.atom 0 : Formula (Fin 2)) (fun _ => 1)) Prod.fst).query
      (fun input => input 1) = some (1/2 : ℝ≥0∞) := by
  rw [query_eq]
  change (observationMass (indicator firstBit) id).query (fun input => input 1) = _
  rw [indicator_query _ _ _ (by rw [first_bit_models_two]; decide)]
  norm_num [first_bit_models_two, both_bits_models_one]

def correlatedEvent (input : Input 2) : Bool := input 0 == input 1
def assertedCorrelatedEvent (input : Input 2) : Bool := correlatedEvent input && input 0

theorem correlated_models_two : count correlatedEvent = 2 := by decide
theorem correlated_joint_models_one : count (fun input => correlatedEvent input && (input 0 && input 1)) = 1 := by decide
theorem asserted_correlated_models_one : count assertedCorrelatedEvent = 1 := by decide
theorem asserted_correlated_q_models_one : count (fun input => assertedCorrelatedEvent input && input 1) = 1 := by decide

/-- Conditioning a correlated prior on its first bit forces the second bit. -/
theorem correlated_prior_preserved :
    (observationMass (targetWeight (.atom 0) (indicator correlatedEvent)) Prod.fst).query
      (fun input => input 1) = some (1 : ℝ≥0∞) := by
  rw [query_eq]
  have weights : sourceWeight (.atom 0) (indicator correlatedEvent) = indicator assertedCorrelatedEvent := by
    funext input
    simp only [sourceWeight, eval, indicator, assertedCorrelatedEvent]
    by_cases hp : input 0 = true <;> by_cases hc : correlatedEvent input = true <;> simp [hp, hc]
  rw [weights, indicator_query _ _ _ (by rw [asserted_correlated_models_one]; decide)]
  norm_num [asserted_correlated_models_one, asserted_correlated_q_models_one]

theorem example_size : auxCount exampleFormula = 2 ∧ (compile exampleFormula).asserted.length = 7 := by decide

theorem repeated_atom_rejects_false_source :
    evalCNF (compile (.and (.atom 0) (.atom 0) : Formula (Fin 1))).asserted
      (read (fun _ => false) (fun _ => true)) = false := by decide

theorem truth_without_source_atoms_has_one_model :
    count (fun world : World (.imp .falsum .falsum : Formula (Fin 0)) =>
      evalCNF (compile (.imp .falsum .falsum : Formula (Fin 0))).asserted (read world.1 world.2)) = 1 := by decide

theorem contradiction_has_no_answer {n : Nat} (weight : Input n → ℝ≥0) (query : Input n → Bool) :
    (observationMass (targetWeight .falsum weight) Prod.fst).query query = none := by
  rw [query_eq]
  simp [sourceWeight, eval, observationMass, MassSemantics.query]

theorem zero_prior_has_no_answer {n : Nat} (formula : Formula (Fin n)) (query : Input n → Bool) :
    (observationMass (targetWeight formula 0) Prod.fst).query query = none := by
  simp [observationMass, MassSemantics.query]

theorem impossible_condition_has_no_answer {n : Nat} (formula : Formula (Fin n))
    (weight : Input n → ℝ≥0) (query : Input n → Bool) :
    (observationMass (conditionWeight (fun _ => false) (targetWeight formula weight)) Prod.fst).query query = none := by
  simp [conditionWeight, observationMass, MassSemantics.query]

end Controls

end Mettapedia.Logic.PropositionalTseitinMass
