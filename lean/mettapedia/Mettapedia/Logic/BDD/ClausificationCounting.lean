import Mettapedia.Logic.PropositionalPlaistedGreenbaum
import Mettapedia.Logic.BDD.Projection
import Mettapedia.Logic.BDD.TseitinCounting

/-!
# Clausification choices with explicit observation contracts

Full Tseitin has unique auxiliary extensions. Polarity-directed clauses preserve
satisfiability and projected models, but raw auxiliary counting can bias both
mass and normalized probability. Here the actual directed clauses pass through
the existing clause-to-BDD compiler, existential projection, and the existing
weighted counter. No source truth-table recompilation is used by that path.

Projection removes multiplicity before counting, so source counts, product
weights, finite mixtures and optional conditional answers agree with full
Tseitin. This is a correctness result; fewer clauses do not imply a smaller BDD.
Synthesis of source-independent factorized auxiliary weights is a separate
problem, as is compiling shared formula DAGs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.ClausificationCounting

open scoped NNReal ENNReal BigOperators
open LO.Propositional (Formula)
open MarkovLogicClauseSemantics PropositionalTseitin
open PropositionalPlaistedGreenbaum (Polarity)
open TseitinCounting
open Mettapedia.ProbabilityTheory FiniteFunctionalExtension

/-- Compile the emitted directed clauses, retaining the compiler's auxiliary names. -/
def directedBDD {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    BDD (n + auxCount formula) :=
  clausesBDD (renameCNF finSumFinEquiv (PropositionalPlaistedGreenbaum.asserted polarity formula))

theorem directedBDD_ordered {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (directedBDD polarity formula).Ordered none := clausesBDD_ordered _

theorem directedBDD_eval {n : Nat} (polarity : Polarity) (formula : Formula (Fin n))
    (input : Fin n → Bool) (auxiliary : Fin (auxCount formula) → Bool) :
    (directedBDD polarity formula).eval (Fin.addCases input auxiliary) =
      evalCNF (PropositionalPlaistedGreenbaum.asserted polarity formula) (read input auxiliary) := by
  have joined : (Fin.addCases input auxiliary : Fin (n + auxCount formula) → Bool) ∘ finSumFinEquiv =
      read input auxiliary := by
    funext wire
    cases wire <;> simp [PropositionalTseitin.read]
  simp only [directedBDD, clausesBDD_eval, evalCNF_rename, joined]

def projectedBDD {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) : BDD n :=
  Projection.projectAux (directedBDD polarity formula)

theorem projectedBDD_ordered {n : Nat} (polarity : Polarity) (formula : Formula (Fin n)) :
    (projectedBDD polarity formula).Ordered none :=
  Projection.projectAux_ordered _ none (directedBDD_ordered polarity formula)

/-- The projected BDD answers precisely the source observation, for either root polarity. -/
theorem projectedBDD_eval {n : Nat} (polarity : Polarity) (formula : Formula (Fin n))
    (input : Fin n → Bool) : (projectedBDD polarity formula).eval input = polarity.accepts (eval input formula) := by
  apply Bool.eq_iff_iff.mpr
  rw [projectedBDD, Projection.projectAux_eval _ (directedBDD_ordered polarity formula)]
  simp only [directedBDD_eval, PropositionalPlaistedGreenbaum.projection_exact]

/-- One certified BDD count, after existential elimination of the auxiliaries. -/
noncomputable def projectedCount {n : Nat} (polarity : Polarity) (formula : Formula (Fin n))
    (p : Fin n → ℝ≥0) : ℝ≥0∞ := bdd_wmc (projectedBDD polarity formula) (fun i => (p i : ℝ≥0∞))

theorem projectedCount_correct {n : Nat} (polarity : Polarity) (formula : Formula (Fin n))
    (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    projectedCount polarity formula p =
      ∑ input, if polarity.accepts (eval input formula) then (productWeight p input : ℝ≥0∞) else 0 := by
  rw [projectedCount, bdd_wmc_correct _ (projectedBDD_ordered polarity formula) _
    (fun i => ENNReal.coe_le_coe.mpr (hp i))]
  simp only [weightedSat, projectedBDD_eval, coe_productWeight]

theorem projectedCount_eq_tseitin {n : Nat} (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) : projectedCount .positive formula p = tseitinCount formula p := by
  rw [projectedCount_correct _ _ _ hp, tseitinCount_correct _ _ hp]
  rfl

inductive Method where
  | full | polarityDirected
  deriving DecidableEq, Repr

/-- Each method exposes its actual clause list, on the same source/auxiliary carrier. -/
def clauses {n : Nat} (method : Method) (formula : Formula (Fin n)) :
    List (GroundClause (Wire n (auxCount formula))) :=
  match method with
  | .full => (compile formula).asserted
  | .polarityDirected => PropositionalPlaistedGreenbaum.asserted .positive formula

theorem projected_models {n : Nat} (method : Method) (formula : Formula (Fin n)) (input : Fin n → Bool) :
    (∃ auxiliary, evalCNF (clauses method formula) (read input auxiliary) = true) ↔ eval input formula = true := by
  cases method with
  | full => simp [clauses, asserted_correct]
  | polarityDirected => exact PropositionalPlaistedGreenbaum.projection_exact .positive formula input

theorem satisfiability {n : Nat} (method : Method) (formula : Formula (Fin n)) :
    (∃ input auxiliary, evalCNF (clauses method formula) (read input auxiliary) = true) ↔
      ∃ input, eval input formula = true := by simp only [projected_models]

/-- Full encoding corrects fair auxiliary weights; directed encoding projects first. -/
noncomputable def count {n : Nat} (method : Method) (formula : Formula (Fin n)) (p : Fin n → ℝ≥0) : ℝ≥0∞ :=
  match method with
  | .full => tseitinCount formula p
  | .polarityDirected => projectedCount .positive formula p

theorem count_eq_tseitin {n : Nat} (method : Method) (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) : count method formula p = tseitinCount formula p := by
  cases method with
  | full => rfl
  | polarityDirected => exact projectedCount_eq_tseitin formula p hp

/-- Both certified routes preserve the weighted source observation. -/
theorem count_correct {n : Nat} (method : Method) (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) : count method formula p =
      ∑ input, if eval input formula then (productWeight p input : ℝ≥0∞) else 0 := by
  rw [count_eq_tseitin _ _ _ hp, tseitinCount_correct _ _ hp]

theorem model_count {n : Nat} (method : Method) (formula : Formula (Fin n)) :
    count method formula (fun _ => 1/2) =
      (PropositionalTseitinMass.Controls.count (fun input => eval input formula) : ℝ≥0∞) / 2 ^ n := by
  rw [count_eq_tseitin _ _ _ (fun _ => by norm_num), fair_count]

theorem normalized_probability {n : Nat} (method : Method) (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (evidence query : Formula (Fin n)) :
    countQuery (fun formula => count method formula p) evidence query =
      (observationMass (PropositionalTseitinMass.sourceWeight evidence (productWeight p)) id).query
        (fun input => eval input query) :=
  countQuery_correct _ _ (fun formula => count_correct method formula p hp) evidence query

/-- Correlated finite priors reuse the existing mixture semantics: one call per component. -/
noncomputable def countMixture {ι : Type*} [Fintype ι] {n : Nat} (method : Method)
    (formula : Formula (Fin n)) (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0) : ℝ≥0∞ :=
  ∑ i, (mass i : ℝ≥0∞) * count method formula (prior i)

theorem countMixture_eq {ι : Type*} [Fintype ι] {n : Nat} (method : Method)
    (formula : Formula (Fin n)) (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0)
    (hp : ∀ i j, prior i j ≤ 1) : countMixture method formula mass prior = mixtureCount formula mass prior := by
  simp only [countMixture, count_eq_tseitin _ _ _ (hp _), mixtureCount_eq_sum]

theorem arbitrary_source_mass {n : Nat} (method : Method) (formula : Formula (Fin n))
    (weight : (Fin n → Bool) → ℝ≥0) :
    countMixture method formula weight pointPrior =
      ∑ input, if eval input formula then (weight input : ℝ≥0∞) else 0 := by
  rw [countMixture_eq _ _ _ _ pointPrior_le_one, arbitrary_table_count]

theorem arbitrary_source_probability {n : Nat} (method : Method) (weight : (Fin n → Bool) → ℝ≥0)
    (evidence query : Formula (Fin n)) :
    countQuery (fun formula => countMixture method formula weight pointPrior) evidence query =
      (observationMass (PropositionalTseitinMass.sourceWeight evidence weight) id).query
        (fun input => eval input query) :=
  countQuery_correct _ _ (fun formula => arbitrary_source_mass method formula weight) evidence query

namespace Controls

open PropositionalTseitinMass (World)
open PropositionalTseitinMass.Controls (exampleFormula sourceEvent indicator indicator_query)

def directedEvent (world : World exampleFormula) : Bool :=
  evalCNF (PropositionalPlaistedGreenbaum.asserted .positive exampleFormula) (read world.1 world.2)

theorem four_clauses_instead_of_seven :
    (clauses .polarityDirected exampleFormula).length = 4 ∧ (clauses .full exampleFormula).length = 7 := by decide

theorem five_source_models_six_directed_models :
    PropositionalTseitinMass.Controls.count sourceEvent = 5 ∧
      PropositionalTseitinMass.Controls.count directedEvent = 6 := by decide

theorem five_directed_models_with_p :
    PropositionalTseitinMass.Controls.count (fun world => directedEvent world && world.1 0) = 5 := by decide

/-- The clauses actually emitted by the directed compiler exhibit the 5-versus-6 boundary. -/
theorem raw_directed_probability_biased :
    (observationMass (indicator directedEvent) Prod.fst).query (fun input => input 0) =
      some (5/6 : ℝ≥0∞) := by
  rw [indicator_query _ _ _ (by rw [five_source_models_six_directed_models.2]; decide)]
  norm_num [five_source_models_six_directed_models.2, five_directed_models_with_p]

theorem projected_probability_four_fifths :
    countQuery (fun formula => count .polarityDirected formula (fun _ => 1/2)) exampleFormula (.atom 0) =
      some (4/5 : ℝ≥0∞) := by
  simp only [count_eq_tseitin .polarityDirected _ (fun _ : Fin 3 => 1/2) (fun _ => by norm_num)]
  exact TseitinCounting.Controls.conditioned_four_fifths

theorem projected_count_five_eighths : count .polarityDirected exampleFormula (fun _ => 1/2) = 5/8 := by
  rw [count_eq_tseitin _ _ _ (fun _ => by norm_num)]
  exact TseitinCounting.Controls.source_five_eighths

/-- In this polarity the missing implication is forced by the asserted root. -/
theorem positive_conjunction_same_models : ∀ (input : Fin 2 → Bool) (auxiliary : Fin 1 → Bool),
    evalCNF (clauses .polarityDirected (.and (.atom 0) (.atom 1))) (read input auxiliary) =
      evalCNF (clauses .full (.and (.atom 0) (.atom 1))) (read input auxiliary) := by decide

theorem negative_disjunction_same_models : ∀ (input : Fin 2 → Bool) (auxiliary : Fin 1 → Bool),
    evalCNF (PropositionalPlaistedGreenbaum.asserted .negative (.or (.atom 0) (.atom 1))) (read input auxiliary) =
      evalCNF (PropositionalPlaistedGreenbaum.fullAsserted .negative (.or (.atom 0) (.atom 1)))
        (read input auxiliary) := by decide

def nestedImplication : Formula (Fin 2) := .imp (.imp (.atom 0) (.atom 1)) (.atom 0)

/-- Deliberately incorrect: the antecedent of an implication keeps positive polarity. -/
def wrongAntecedent : Encoding 2 2 :=
  PropositionalPlaistedGreenbaum.combine .imp .positive
    (PropositionalPlaistedGreenbaum.compile .positive (.imp (.atom 0) (.atom 1)))
    (PropositionalPlaistedGreenbaum.compile .positive (.atom 0))

theorem antecedent_polarity_matters :
    eval ![false, true] nestedImplication = false ∧
      evalCNF wrongAntecedent.asserted (read ![false, true] ![false, true]) = true ∧
      evalCNF (clauses .polarityDirected nestedImplication) (read ![false, true] ![false, true]) = false := by decide

theorem repeated_atom_no_false_model :
    ¬ ∃ auxiliary, evalCNF (clauses .polarityDirected (.and (.atom 0) (.atom 0) : Formula (Fin 1)))
      (read (fun _ => false) auxiliary) = true := by
  rw [projected_models]
  decide

theorem unused_bit_query_exact :
    countQuery (fun formula => count .polarityDirected formula (fun _ : Fin 2 => 1/2))
      (.atom 0) (.atom 1) = some (1/2 : ℝ≥0∞) := by
  have single : PropositionalTseitinMass.Controls.count (fun input : Fin 2 → Bool => eval input (.atom 0)) = 2 := by decide
  have joint : PropositionalTseitinMass.Controls.count
      (fun input : Fin 2 → Bool => eval input (.and (.atom 0) (.atom 1))) = 1 := by decide
  simp only [countQuery, model_count, single, joint]
  norm_num
  have ratio : ((1 : ℝ≥0) / 4) / (2/4) = 1/2 := by norm_num
  have castRatio := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) ratio
  simpa only [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2/4 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_one, ENNReal.coe_ofNat, one_div] using castRatio

theorem constants_without_source_atoms :
    count .polarityDirected (.imp .falsum .falsum : Formula (Fin 0)) (fun _ => 1/2) = 1 ∧
      projectedCount .negative (.falsum : Formula (Fin 0)) (fun _ => 1/2) = 1 := by
  constructor
  · rw [model_count]
    have one : PropositionalTseitinMass.Controls.count
        (fun input : Fin 0 → Bool => eval input (.imp .falsum .falsum)) = 1 := by decide
    norm_num [one]
  · rw [projectedCount_correct .negative .falsum (fun _ : Fin 0 => 1/2) (fun _ => by norm_num)]
    simp [eval, Polarity.accepts, productWeight]

theorem impossible_evidence_absent {n : Nat} (method : Method) (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (query : Formula (Fin n)) : countQuery (fun formula => count method formula p) .falsum query = none := by
  simp only [count_eq_tseitin _ _ _ hp]
  exact TseitinCounting.Controls.impossible_evidence_absent p hp query

theorem zero_prior_absent {n : Nat} (method : Method) (evidence query : Formula (Fin n)) :
    countQuery (fun formula => countMixture method formula (fun _ : Fin n → Bool => 0) pointPrior)
      evidence query = none := by
  simp [countQuery, countMixture]

end Controls

end Mettapedia.Logic.BDDCore.ClausificationCounting
