import Mettapedia.Logic.BDD.WMPLNBDDWMCExact
import Mettapedia.Logic.PropositionalTseitinMass
import Mathlib.Algebra.BigOperators.Fin

/-!+# From emitted definitional clauses to certified weighted counts

The clause compiler uses the existing BDD operations and counting algorithm.
Its input is the actual output of the propositional Tseitin compiler. Since
the BDD counter uses normalized Bernoulli weights, each auxiliary receives
probability one half; multiplying by `2 ^ auxCount` restores neutral counting
weight for its unique satisfying extension.

Finite mixtures reuse the same BDD with one counting call per component.
They express correlated priors without claiming an efficient correlated
counting algorithm or changing the independent-coordinate counter.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.TseitinCounting

open scoped NNReal ENNReal BigOperators
open LO.Propositional (Formula)
open MarkovLogicClauseSemantics PropositionalTseitin
open Mettapedia.ProbabilityTheory FiniteFunctionalExtension

/-- Enumerate only the literal alphabet, in atom order with positive first. -/
def clauseLiterals {n : Nat} (clause : GroundClause (Fin n)) : List (Literal (Fin n)) :=
  ((List.finRange n).flatMap fun i => [.pos i, .neg i]).filter fun literal => literal ∈ clause

@[simp] theorem mem_clauseLiterals {n : Nat} (clause : GroundClause (Fin n))
    (literal : Literal (Fin n)) : literal ∈ clauseLiterals clause ↔ literal ∈ clause := by
  cases literal <;> simp [clauseLiterals]

def literalBDD {n : Nat} : Literal (Fin n) → BDD n
  | .pos i => bddVar i
  | .neg i => bddNot (bddVar i)

@[simp] theorem literalBDD_eval {n : Nat} (literal : Literal (Fin n)) (world : Fin n → Bool) :
    (literalBDD literal).eval world = evalLiteral world literal := by
  cases literal <;> simp [literalBDD, evalLiteral]

theorem literalBDD_ordered {n : Nat} (literal : Literal (Fin n)) :
    (literalBDD literal).Ordered none := by
  cases literal with
  | pos i => exact bddVar_ordered i
  | neg i => exact bddNot_ordered _ _ (bddVar_ordered i)

def disjunctionBDD {n : Nat} : List (Literal (Fin n)) → BDD n
  | [] => .zero
  | literal :: rest => apply (· || ·) (literalBDD literal) (disjunctionBDD rest)

theorem disjunctionBDD_eval {n : Nat} (literals : List (Literal (Fin n))) (world : Fin n → Bool) :
    (disjunctionBDD literals).eval world = literals.any (evalLiteral world) := by
  induction literals <;> simp_all [disjunctionBDD]

theorem disjunctionBDD_ordered {n : Nat} (literals : List (Literal (Fin n))) :
    (disjunctionBDD literals).Ordered none := by
  induction literals with
  | nil => exact .zero
  | cons literal rest ih => exact apply_ordered _ _ _ _ (literalBDD_ordered literal) ih

def clauseBDD {n : Nat} (clause : GroundClause (Fin n)) : BDD n :=
  disjunctionBDD (clauseLiterals clause)

@[simp] theorem clauseBDD_eval {n : Nat} (clause : GroundClause (Fin n)) (world : Fin n → Bool) :
    (clauseBDD clause).eval world = evalClause world clause := by
  apply Bool.eq_iff_iff.mpr
  simp [clauseBDD, disjunctionBDD_eval, evalClause]

def clausesBDD {n : Nat} : List (GroundClause (Fin n)) → BDD n
  | [] => .one
  | clause :: rest => apply (· && ·) (clauseBDD clause) (clausesBDD rest)

@[simp] theorem clausesBDD_eval {n : Nat} (clauses : List (GroundClause (Fin n)))
    (world : Fin n → Bool) :
    (clausesBDD clauses).eval world = evalCNF clauses world := by
  induction clauses <;> simp_all [clausesBDD, evalCNF]

theorem clausesBDD_ordered {n : Nat} (clauses : List (GroundClause (Fin n))) :
    (clausesBDD clauses).Ordered none := by
  induction clauses with
  | nil => exact .one
  | cons clause rest ih =>
    exact apply_ordered _ _ _ _ (disjunctionBDD_ordered _) ih

/-- Source names precede auxiliary names; no names are identified. -/
def tseitinBDD {n : Nat} (formula : Formula (Fin n)) : BDD (n + auxCount formula) :=
  clausesBDD (renameCNF finSumFinEquiv (compile formula).asserted)

theorem tseitinBDD_ordered {n : Nat} (formula : Formula (Fin n)) :
    (tseitinBDD formula).Ordered none := clausesBDD_ordered _

def joinedAssignment {n k : Nat} (input : Fin n → Bool) (auxiliary : Fin k → Bool) :
    Fin (n + k) → Bool := Fin.addCases input auxiliary

theorem tseitinBDD_eval {n : Nat} (formula : Formula (Fin n)) (input : Fin n → Bool)
    (auxiliary : Fin (auxCount formula) → Bool) :
    (tseitinBDD formula).eval (joinedAssignment input auxiliary) = true ↔
      eval input formula = true ∧ auxiliary = realizeAux input formula := by
  have joined : joinedAssignment input auxiliary ∘ finSumFinEquiv = read input auxiliary := by
    funext wire
    cases wire <;> simp [joinedAssignment, PropositionalTseitin.read]
  simp only [tseitinBDD, clausesBDD_eval, evalCNF_rename, joined, asserted_correct]

def assignmentEquiv (n k : Nat) : ((Fin n → Bool) × (Fin k → Bool)) ≃ (Fin (n + k) → Bool) where
  toFun world := joinedAssignment world.1 world.2
  invFun world := (fun i => world (Fin.castAdd k i), fun i => world (Fin.natAdd n i))
  left_inv world := by ext i <;> simp [joinedAssignment]
  right_inv world := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [joinedAssignment]

/-- The finite source table associated with the existing Bernoulli weights. -/
noncomputable def productWeight {n : Nat} (p : Fin n → ℝ≥0) (world : Fin n → Bool) : ℝ≥0 :=
  ∏ i, if world i then p i else 1 - p i

theorem coe_productWeight {n : Nat} (p : Fin n → ℝ≥0) (world : Fin n → Bool) :
    (productWeight p world : ℝ≥0∞) = assignmentWeight (fun i => (p i : ℝ≥0∞)) world := by
  simp only [productWeight, assignmentWeight, varWeight]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [ENNReal.coe_sub]

noncomputable def countingEnv {n : Nat} (k : Nat) (p : Fin n → ℝ≥0) : Fin (n + k) → ℝ≥0∞ :=
  Fin.addCases (fun i => (p i : ℝ≥0∞)) (fun _ => 1 / 2)

theorem countingEnv_le_one {n : Nat} (k : Nat) (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (i : Fin (n + k)) : countingEnv k p i ≤ 1 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [countingEnv] using (ENNReal.coe_le_coe.mpr (hp j))
  · intro j
    norm_num [countingEnv]

theorem assignmentWeight_countingEnv {n k : Nat} (p : Fin n → ℝ≥0)
    (input : Fin n → Bool) (auxiliary : Fin k → Bool) :
    assignmentWeight (countingEnv k p) (joinedAssignment input auxiliary) =
      (productWeight p input : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ k := by
  rw [assignmentWeight, Fin.prod_univ_add]
  simp only [countingEnv, joinedAssignment, varWeight, Fin.addCases_left, Fin.addCases_right]
  have half : ∀ b : Bool, (if b then (1 / 2 : ℝ≥0∞) else 1 - 1 / 2) = 1 / 2 := by
    intro b
    cases b <;> norm_num
  simp only [half, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [coe_productWeight]
  rfl

/-- The uncorrected call pays one fair-bit factor for each auxiliary. -/
theorem raw_count {n : Nat} (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) :
    bdd_wmc (tseitinBDD formula) (countingEnv (auxCount formula) p) =
      (∑ input, if eval input formula then (productWeight p input : ℝ≥0∞) else 0) *
        (1 / 2 : ℝ≥0∞) ^ auxCount formula := by
  rw [bdd_wmc_correct _ (tseitinBDD_ordered formula) _ (countingEnv_le_one _ p hp)]
  unfold weightedSat
  rw [← (assignmentEquiv n (auxCount formula)).sum_comp]
  change (∑ world : (Fin n → Bool) × (Fin (auxCount formula) → Bool),
    if (tseitinBDD formula).eval (joinedAssignment world.1 world.2) then
      assignmentWeight (countingEnv (auxCount formula) p) (joinedAssignment world.1 world.2) else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro input _
  simp only [tseitinBDD_eval, assignmentWeight_countingEnv]
  by_cases holds : eval input formula = true <;> simp [holds]

/-- One call to the existing counter, followed by the proved auxiliary correction. -/
noncomputable def tseitinCount {n : Nat} (formula : Formula (Fin n)) (p : Fin n → ℝ≥0) : ℝ≥0∞ :=
  2 ^ auxCount formula * bdd_wmc (tseitinBDD formula) (countingEnv (auxCount formula) p)

/-- Formula-to-count exactness, with no assumed equivalence for the emitted BDD. -/
theorem tseitinCount_correct {n : Nat} (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) :
    tseitinCount formula p =
      ∑ input, if eval input formula then (productWeight p input : ℝ≥0∞) else 0 := by
  rw [tseitinCount, raw_count formula p hp]
  have cancel : (2 : ℝ≥0∞) ^ auxCount formula * (1 / 2 : ℝ≥0∞) ^ auxCount formula = 1 := by
    rw [← mul_pow]
    norm_num [ENNReal.mul_inv_cancel]
  calc
    _ = (∑ input, if eval input formula then (productWeight p input : ℝ≥0∞) else 0) *
        (2 ^ auxCount formula * (1 / 2 : ℝ≥0∞) ^ auxCount formula) := by ac_rfl
    _ = _ := by rw [cancel, mul_one]

theorem tseitinCount_eq_weightedSat {n : Nat} (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) :
    tseitinCount formula p = weightedSat (fun input => eval input formula) (fun i => (p i : ℝ≥0∞)) := by
  rw [tseitinCount_correct formula p hp]
  simp only [weightedSat, coe_productWeight]

/-- The exact numbered-world readout from the existing WM/ProbLog bridge. -/
theorem tseitinCount_eq_queryProb {n : Nat} (formula : Formula (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) :
    tseitinCount formula p =
      Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb
        (fun i => (p i : ℝ≥0∞))
        (fun world => eval (WMPLNBDDWMCExact.worldAssignmentEquiv n world) formula) := by
  rw [WMPLNBDDWMCExact.queryProb_eq_weightedSat _
    (fun i => by exact_mod_cast hp i), tseitinCount_eq_weightedSat formula p hp]
  simp

section Mixtures

variable {ι : Type*} [Fintype ι] {n : Nat}

/-- Supplied component masses need not sum to one: this is also a weight table. -/
noncomputable def mixtureWeight (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0) :
    (Fin n → Bool) → ℝ≥0 := fun input => ∑ i, mass i * productWeight (prior i) input

/-- The same compiled BDD is evaluated once per supplied product component. -/
noncomputable def mixtureCount (formula : Formula (Fin n))
    (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0) : ℝ≥0∞ :=
  let compiled := tseitinBDD formula
  ∑ i, (mass i : ℝ≥0∞) *
    (2 ^ auxCount formula * bdd_wmc compiled (countingEnv (auxCount formula) (prior i)))

theorem mixtureCount_eq_sum (formula : Formula (Fin n))
    (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0) :
    mixtureCount formula mass prior =
      ∑ i, (mass i : ℝ≥0∞) * tseitinCount formula (prior i) := rfl

theorem mixtureCount_correct (formula : Formula (Fin n))
    (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0) (hp : ∀ i j, prior i j ≤ 1) :
    mixtureCount formula mass prior =
      ∑ input, if eval input formula then (mixtureWeight mass prior input : ℝ≥0∞) else 0 := by
  simp only [mixtureCount_eq_sum, tseitinCount_correct _ _ (hp _), mixtureWeight, Finset.mul_sum]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  by_cases holds : eval input formula = true <;> simp [holds]

/-- A deterministic assignment is itself a product prior, including probabilities zero and one. -/
def pointPrior (point : Fin n → Bool) : Fin n → ℝ≥0 := fun i => if point i then 1 else 0

theorem pointPrior_le_one (point : Fin n → Bool) (i : Fin n) : pointPrior point i ≤ 1 := by
  unfold pointPrior
  split_ifs <;> norm_num

theorem productWeight_pointPrior (point input : Fin n → Bool) :
    productWeight (pointPrior point) input = if input = point then 1 else 0 := by
  classical
  by_cases same : input = point
  · subst input
    simp only [productWeight, if_true]
    apply Finset.prod_eq_one
    intro i _
    unfold pointPrior
    split_ifs <;> norm_num
  · obtain ⟨i, different⟩ := Function.ne_iff.mp same
    have factor : (if input i then pointPrior point i else 1 - pointPrior point i) = 0 := by
      cases h₁ : input i <;> cases h₂ : point i <;> simp_all [pointPrior]
    simp only [same, if_false, productWeight]
    exact Finset.prod_eq_zero (Finset.mem_univ i) factor

/-- Every finite table is a mixture; the full-table route has `2 ^ n` components. -/
theorem mixtureWeight_points (weight : (Fin n → Bool) → ℝ≥0) :
    mixtureWeight weight pointPrior = weight := by
  classical
  funext input
  simp [mixtureWeight, productWeight_pointPrior]

theorem point_count (formula : Formula (Fin n)) (point : Fin n → Bool) :
    tseitinCount formula (pointPrior point) = if eval point formula then 1 else 0 := by
  classical
  rw [tseitinCount_correct formula _ (pointPrior_le_one point)]
  simp only [productWeight_pointPrior]
  have term (input : Fin n → Bool) :
      (if eval input formula then ((if input = point then 1 else 0 : ℝ≥0) : ℝ≥0∞) else 0) =
        if input = point then (if eval point formula then 1 else 0) else 0 := by
    by_cases same : input = point <;> simp [same]
  simp_rw [term]
  simp

theorem arbitrary_table_count (formula : Formula (Fin n)) (weight : (Fin n → Bool) → ℝ≥0) :
    mixtureCount formula weight pointPrior =
      ∑ input, if eval input formula then (weight input : ℝ≥0∞) else 0 := by
  rw [mixtureCount_correct formula weight pointPrior pointPrior_le_one, mixtureWeight_points]

end Mixtures

/-- The finite-table mass interface used in tranche 1, with a formula asserted. -/
theorem source_total_eq_sum {n : Nat} (formula : Formula (Fin n)) (weight : (Fin n → Bool) → ℝ≥0) :
    (observationMass (PropositionalTseitinMass.sourceWeight formula weight) id).totalMass =
      ∑ input, if eval input formula then (weight input : ℝ≥0∞) else 0 := by
  simp only [observationMass, PropositionalTseitinMass.sourceWeight]
  push_cast
  apply Finset.sum_congr rfl
  intro input _
  split_ifs <;> simp

theorem source_query_eq_sum {n : Nat} (formula query : Formula (Fin n))
    (weight : (Fin n → Bool) → ℝ≥0) :
    (observationMass (PropositionalTseitinMass.sourceWeight formula weight) id).queryMass
        (fun input => eval input query) =
      ∑ input, if eval input (.and formula query) then (weight input : ℝ≥0∞) else 0 := by
  simp only [observationMass, PropositionalTseitinMass.sourceWeight, id_eq, eval]
  push_cast
  apply Finset.sum_congr rfl
  intro input _
  by_cases hf : eval input formula = true <;> by_cases hq : eval input query = true <;> simp [hf, hq]

/-- Normalize corrected counts, retaining absence for impossible evidence.
The numerator and denominator can have different auxiliary counts. -/
noncomputable def countQuery {n : Nat} (count : Formula (Fin n) → ℝ≥0∞)
    (evidence query : Formula (Fin n)) : Option ℝ≥0∞ :=
  if count evidence = 0 then none else some (count (.and evidence query) / count evidence)

theorem countQuery_correct {n : Nat} (count : Formula (Fin n) → ℝ≥0∞)
    (weight : (Fin n → Bool) → ℝ≥0)
    (correct : ∀ formula, count formula =
      ∑ input, if eval input formula then (weight input : ℝ≥0∞) else 0)
    (evidence query : Formula (Fin n)) :
    countQuery count evidence query =
      (observationMass (PropositionalTseitinMass.sourceWeight evidence weight) id).query
        (fun input => eval input query) := by
  simp only [countQuery, MassSemantics.query, MassSemantics.queryProb,
    source_query_eq_sum, source_total_eq_sum, correct]
  split_ifs <;> rfl

theorem product_query_correct {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (evidence query : Formula (Fin n)) :
    countQuery (fun formula => tseitinCount formula p) evidence query =
      (observationMass (PropositionalTseitinMass.sourceWeight evidence (productWeight p)) id).query
        (fun input => eval input query) :=
  countQuery_correct _ _ (fun formula => tseitinCount_correct formula p hp) evidence query

theorem mixture_query_correct {ι : Type*} [Fintype ι] {n : Nat}
    (mass : ι → ℝ≥0) (prior : ι → Fin n → ℝ≥0) (hp : ∀ i j, prior i j ≤ 1)
    (evidence query : Formula (Fin n)) :
    countQuery (fun formula => mixtureCount formula mass prior) evidence query =
      (observationMass (PropositionalTseitinMass.sourceWeight evidence (mixtureWeight mass prior)) id).query
        (fun input => eval input query) :=
  countQuery_correct _ _ (fun formula => mixtureCount_correct formula mass prior hp) evidence query

theorem productWeight_half {n : Nat} (input : Fin n → Bool) :
    productWeight (fun _ => 1/2) input = (1/2 : ℝ≥0) ^ n := by
  have each : ∀ i, (if input i then (1/2 : ℝ≥0) else 1 - 1/2) = 1/2 := by
    intro i
    cases input i with
    | true => rfl
    | false =>
      change (1 : ℝ≥0) - 1/2 = 1/2
      apply NNReal.coe_injective
      rw [NNReal.coe_sub (by norm_num : (1/2 : ℝ≥0) ≤ 1)]
      norm_num
  simp only [productWeight, each, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Fair product weights turn model counts into probabilities; this is a
corollary of the certified counter, not a separate enumeration algorithm. -/
theorem fair_count {n : Nat} (formula : Formula (Fin n)) :
    tseitinCount formula (fun _ => 1/2) =
      (PropositionalTseitinMass.Controls.count (fun input => eval input formula) : ℝ≥0∞) / 2 ^ n := by
  rw [tseitinCount_correct formula _ (fun _ => by norm_num)]
  have weights : ∀ input : Fin n → Bool,
      (productWeight (fun _ => 1/2) input : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro input
    rw [productWeight_half]
    norm_num
  simp only [weights]
  have collect : (∑ input : Fin n → Bool,
      if eval input formula then (2 : ℝ≥0∞)⁻¹ ^ n else 0) =
      (PropositionalTseitinMass.Controls.count (fun input => eval input formula) : ℝ≥0∞) * 2⁻¹ ^ n := by
    rw [← Finset.sum_filter]
    simp [PropositionalTseitinMass.Controls.count, nsmul_eq_mul]
  rw [collect]
  simp [div_eq_mul_inv, ENNReal.inv_pow]

namespace Controls

open PropositionalTseitinMass.Controls

theorem source_five_eighths : tseitinCount exampleFormula (fun _ => 1/2) = 5/8 := by
  rw [fair_count]
  change (count sourceEvent : ℝ≥0∞) / 2 ^ 3 = _
  norm_num [source_models_five]

/-- The raw call has a real normalization factor; omitting the correction is wrong. -/
theorem raw_five_thirtySeconds :
    bdd_wmc (tseitinBDD exampleFormula) (countingEnv (auxCount exampleFormula) (fun _ => 1/2)) = 5/32 := by
  rw [raw_count exampleFormula _ (fun _ => by norm_num)]
  rw [← tseitinCount_correct exampleFormula _ (fun _ => by norm_num), source_five_eighths]
  change (5/8 : ℝ≥0∞) * (1/2) ^ 2 = 5/32
  have finiteRatio : (5/8 : ℝ≥0) * (1/2) ^ 2 = 5/32 := by norm_num
  have castRatio := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) finiteRatio
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using castRatio

theorem conditioned_four_fifths :
    countQuery (fun formula => tseitinCount formula (fun _ => 1/2)) exampleFormula (.atom 0) =
      some (4/5 : ℝ≥0∞) := by
  have joint : count (fun input : Fin 3 → Bool => eval input (.and exampleFormula (.atom 0))) = 4 := by decide
  dsimp only [countQuery]
  simp only [source_five_eighths]
  rw [fair_count, joint]
  norm_num
  have finiteRatio : ((4 : ℝ≥0) / 8) / (5/8) = 4/5 := by norm_num
  have castRatio := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) finiteRatio
  simpa only [ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (5/8 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using castRatio

def correlatedPrior (component : Bool) : Fin 2 → ℝ≥0 := pointPrior (fun _ => component)

theorem correlated_mixture_not_product_marginals :
    mixtureCount (.and (.atom 0) (.atom 1)) (fun _ : Bool => 1/2) correlatedPrior = 1/2 ∧
      tseitinCount (.and (.atom 0) (.atom 1) : Formula (Fin 2)) (fun _ => 1/2) = 1/4 := by
  constructor
  · simp [mixtureCount_eq_sum, correlatedPrior, point_count, eval]
  · rw [fair_count]
    have models : count (fun input : Fin 2 → Bool => eval input (.and (.atom 0) (.atom 1))) = 1 := by decide
    norm_num [models]

theorem zero_mixture_absent {ι : Type*} [Fintype ι] {n : Nat}
    (prior : ι → Fin n → ℝ≥0) (evidence query : Formula (Fin n)) :
    countQuery (fun formula => mixtureCount formula (fun _ => 0) prior) evidence query = none := by
  simp [countQuery, mixtureCount]

theorem impossible_evidence_absent {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (query : Formula (Fin n)) : countQuery (fun formula => tseitinCount formula p) .falsum query = none := by
  simp [countQuery, tseitinCount_correct _ _ hp, eval]

end Controls

end Mettapedia.Logic.BDDCore.TseitinCounting
