import Mettapedia.Logic.ClarkCompletion
import Mettapedia.Logic.BDD.ClausificationCounting
import Mettapedia.Logic.BDD.ProbMeTTaSourceSyntax
import Mettapedia.PLN.Bridges.Languages.ProbLog.ExtensionControls

/-!
# From normalized ground programs to certified probability

The construction emits Clark completion, compiles actual clauses, projects
gate auxiliaries and program atoms, and calls the existing BDD counter on the
original independent choices. Tightness and stratification certify this route;
they are separate hypotheses with different semantic roles.

The comparison with the extensional normal-program BDD is an evaluation and
probability law, not a dependence of the structural compiler on an enumeration
of models. Derived atoms receive neutral weight in the equivalent weighted
completion formula. Conditioning keeps zero-evidence answers absent.

Reference: Fierens et al., *Inference and learning in probabilistic logic
programs using weighted Boolean formulas*, https://doi.org/10.1017/S1471068414000076.
Non-tight stratified programs use `BDD.RecursiveNormalCompilation`, which
adds the Lin–Zhao loop formulas; see https://cse.hkust.edu.hk/assat/.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.NormalCompletion

open scoped NNReal ENNReal BigOperators
open LP NormalProgramSemantics ClarkCompletion PropositionalTseitin TseitinCounting
open LO.Propositional (Formula)
open ClausificationCounting (Method)
open Mettapedia.ProbabilityTheory FiniteFunctionalExtension
open PropositionalTseitinMass (conditionWeight)

/-- Both paths compile clauses before removing the gate-variable block. -/
def formulaBDD {n : Nat} (method : Method) (formula : Formula (Fin n)) : BDD n :=
  match method with
  | .full => Projection.projectAux (tseitinBDD formula)
  | .polarityDirected => ClausificationCounting.projectedBDD .positive formula

theorem formulaBDD_ordered {n : Nat} (method : Method) (formula : Formula (Fin n)) :
    (formulaBDD method formula).Ordered none := by
  cases method with
  | full => exact Projection.projectAux_ordered _ none (tseitinBDD_ordered formula)
  | polarityDirected => exact ClausificationCounting.projectedBDD_ordered .positive formula

@[simp] theorem formulaBDD_eval {n : Nat} (method : Method) (formula : Formula (Fin n))
    (input : Fin n → Bool) : (formulaBDD method formula).eval input = eval input formula := by
  cases method with
  | full =>
    apply Bool.eq_iff_iff.mpr
    rw [formulaBDD, Projection.projectAux_eval _ (tseitinBDD_ordered formula)]
    change (∃ auxiliary, (tseitinBDD formula).eval (joinedAssignment input auxiliary) = true) ↔ _
    simp [tseitinBDD_eval]
  | polarityDirected => exact ClausificationCounting.projectedBDD_eval .positive formula input

variable {σ : LPSignature} [DecidableEq (GroundAtom σ)] {n : Nat}

/-- Program atoms form the second block; only original random choices survive. -/
def programBDD (method : Method) (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (goals : List (GoalLit σ)) : BDD n :=
  Projection.projectAux (formulaBDD method (completionQuery table facts rules goals))

theorem programBDD_ordered (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (goals : List (GoalLit σ)) :
    (programBDD method table facts rules goals).Ordered none :=
  Projection.projectAux_ordered _ none (formulaBDD_ordered method _)

theorem programBDD_correct (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (tight : Tight rules) (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    (programBDD method table facts rules goals).eval choice = true ↔
      ∀ g ∈ goals, goalLitHoldsIn (fullStratifiedModel rules (chosenFacts facts choice) s)
        (fullStratifiedModel rules (chosenFacts facts choice) s) g := by
  rw [programBDD, Projection.projectAux_eval _ (formulaBDD_ordered method _)]
  simp only [formulaBDD_eval, completionQuery_correct table facts rules covers tight s stratified]
  simp

omit [DecidableEq (GroundAtom σ)] in
/-- The normalized source carries a facts-only base, so no rule closure is frozen early. -/
theorem normalized_base (prog : ProbMeTTaSourceProgram σ n) (choice : Fin n → Bool) :
    leastHerbrandModel (residualKBa prog.toProbLogBase choice) = chosenFacts prog.probFacts choice := by
  apply Set.Subset.antisymm
  · apply leastHerbrandModel_least
    simp [T_P_LP, residualKBa, ProbMeTTaSourceProgram.toProbLogBase, residualDBa, chosenFacts]
  · intro a ha
    exact leastHerbrandModel_db (residualKBa prog.toProbLogBase choice) a ha

omit [DecidableEq (GroundAtom σ)] in
theorem source_goal (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (choice : Fin n → Bool) (g : GoalLit σ) :
    goalLitHoldsIn (fullStratifiedModel prog.normalRules (chosenFacts prog.probFacts choice) s)
      (fullStratifiedModel prog.normalRules (chosenFacts prog.probFacts choice) s) g ↔
        LP.GoalLit.holdsNormal prog.toNormalProbLogProgram s choice g := by
  cases g <;> simp only [goalLitHoldsIn, GoalLit.holdsNormal, queryHoldsNormalA,
    ProbMeTTaSourceProgram.toNormalProbLogProgram, normalized_base]

noncomputable def sourceEvent (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) : Bool := by
  classical
  exact decide (∀ g ∈ goals, LP.GoalLit.holdsNormal prog.toNormalProbLogProgram s choice g)

omit [DecidableEq (GroundAtom σ)] in
theorem sourceEvent_true (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    sourceEvent prog s goals choice = true ↔
      ∀ g ∈ goals, LP.GoalLit.holdsNormal prog.toNormalProbLogProgram s choice g := by
  classical
  simp only [sourceEvent, decide_eq_true_eq]

theorem programBDD_source (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification σ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit σ))
    (choice : Fin n → Bool) :
    (programBDD method table prog.probFacts prog.normalRules goals).eval choice = sourceEvent prog s goals choice := by
  apply Bool.eq_iff_iff.mpr
  rw [programBDD_correct method table prog.probFacts prog.normalRules covers tight s stratified]
  simp only [sourceEvent, decide_eq_true_eq, source_goal]

noncomputable def programCount (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ)) : ℝ≥0∞ :=
  bdd_wmc (programBDD method table prog.probFacts prog.normalRules goals) prog.probs

theorem programCount_correct (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification σ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit σ)) :
    programCount method table prog goals = weightedSat (sourceEvent prog s goals) prog.probs := by
  rw [programCount, bdd_wmc_correct _ (programBDD_ordered method table prog.probFacts prog.normalRules goals)
    _ prog.probs_le_one]
  simp only [weightedSat, programBDD_source method table prog covers tight s stratified]

/-- Direct agreement with ProbLog's normalized, numbered-total-choice probability. -/
theorem programCount_eq_queryProb (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification σ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit σ)) :
    programCount method table prog goals =
      Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent prog s goals (WMPLNBDDWMCExact.worldAssignmentEquiv n world)) :=
  WMPLNBDDWMCExact.bdd_wmc_eq_queryProb _
    (programBDD_ordered method table prog.probFacts prog.normalRules goals) _ prog.probs_le_one _
    (fun world => programBDD_source method table prog covers tight s stratified goals
      (WMPLNBDDWMCExact.worldAssignmentEquiv n world))

section ExistingSourceAPI

universe u v
variable {τ : LPSignature.{u, u, v, u}} [DecidableEq (GroundAtom τ)]
variable [IsEmpty τ.functionSymbols] [Nonempty (GroundTerm τ)]

omit [DecidableEq (GroundAtom τ)] in
/-- The existing exact source probability is the weighted source event, independently of a compiler. -/
theorem sourceEvent_eq_probExact (prog : ProbMeTTaSourceProgram τ n) (s : Stratification τ)
    (query : GroundAtom τ) :
    weightedSat (sourceEvent prog s [.pos query]) prog.probs = prog.probExact s query := by
  rw [ProbMeTTaSourceProgram.probExact_eq_weightedSat_query]
  classical
  have event : sourceEvent prog s [.pos query] =
      (fun a => decide (queryHoldsNormalA prog.toNormalProbLogProgram s query a)) := by
    funext choice
    apply Bool.eq_iff_iff.mpr
    rw [sourceEvent_true, decide_eq_true_eq]
    constructor
    · exact fun h => h (.pos query) (by simp)
    · intro h g hg
      have same : g = .pos query := List.mem_singleton.mp hg
      subst g
      exact h
  rw [event]
  rfl

/-- Agreement with the existing normalized source probability, including its extensional construction. -/
theorem programCount_eq_probExact (method : Method) (table : AtomTable (GroundAtom τ))
    (prog : ProbMeTTaSourceProgram τ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification τ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (query : GroundAtom τ) :
    programCount method table prog [.pos query] = prog.probExact s query := by
  rw [programCount_correct method table prog covers tight s stratified, sourceEvent_eq_probExact]

/-- The old existence theorem and the structural compiler denote the same function and count. -/
theorem agrees_with_extensional (method : Method) (table : AtomTable (GroundAtom τ))
    (prog : ProbMeTTaSourceProgram τ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification τ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit τ)) :
    ∃ f : BDD n, f.Ordered none ∧
      (∀ choice, f.eval choice = (programBDD method table prog.probFacts prog.normalRules goals).eval choice) ∧
      bdd_wmc f prog.probs = programCount method table prog goals := by
  obtain ⟨f, ordered, agrees⟩ := exists_ordered_normal_goal_semantic_bdd prog.toNormalProbLogProgram s goals
  have same : ∀ choice, f.eval choice = (programBDD method table prog.probFacts prog.normalRules goals).eval choice := by
    intro choice
    apply Bool.eq_iff_iff.mpr
    rw [programBDD_source method table prog covers tight s stratified]
    simpa [sourceEvent] using agrees choice
  refine ⟨f, ordered, same, ?_⟩
  rw [bdd_wmc_correct f ordered _ prog.probs_le_one,
    programCount, bdd_wmc_correct _ (programBDD_ordered method table prog.probFacts prog.normalRules goals)
      _ prog.probs_le_one]
  simp only [weightedSat, same]

end ExistingSourceAPI

noncomputable def neutralPrior (table : AtomTable (GroundAtom σ)) (p : Fin n → ℝ≥0) :
    Fin (n + table.atoms.length) → ℝ≥0 := Fin.addCases p (fun _ => 1/2)

omit [DecidableEq (GroundAtom σ)] in
theorem neutralPrior_le_one (table : AtomTable (GroundAtom σ)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) : ∀ i, neutralPrior table p i ≤ 1 := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [neutralPrior] using hp j
  · intro j
    norm_num [neutralPrior]

omit [DecidableEq (GroundAtom σ)] in
theorem neutral_assignment_weight (table : AtomTable (GroundAtom σ)) (p : Fin n → ℝ≥0)
    (choice : Fin n → Bool) (values : Fin table.atoms.length → Bool) :
    (productWeight (neutralPrior table p) (joinedAssignment choice values) : ℝ≥0∞) =
      (productWeight p choice : ℝ≥0∞) * (1/2 : ℝ≥0∞) ^ table.atoms.length := by
  rw [coe_productWeight]
  have env : (fun i => (neutralPrior table p i : ℝ≥0∞)) = countingEnv table.atoms.length p := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [neutralPrior, countingEnv]
  rw [env]
  exact assignmentWeight_countingEnv p choice values

omit [DecidableEq (GroundAtom σ)] in
/-- Count any supplied formula whose auxiliary block is a unique extension of its source event. -/
theorem uniqueExtension_raw_count (method : Method) (table : AtomTable (GroundAtom σ))
    (formula : Formula (Fin (n + table.atoms.length)))
    (realize : (Fin n → Bool) → Fin table.atoms.length → Bool) (event : (Fin n → Bool) → Bool)
    (contract : ∀ choice values, eval (joinedAssignment choice values) formula = true ↔
      values = realize choice ∧ event choice = true)
    (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    ClausificationCounting.count method formula (neutralPrior table p) =
      weightedSat event (fun i => (p i : ℝ≥0∞)) * (1/2 : ℝ≥0∞) ^ table.atoms.length := by
  classical
  rw [ClausificationCounting.count_correct _ _ _ (neutralPrior_le_one table p hp)]
  unfold weightedSat
  rw [← (assignmentEquiv n table.atoms.length).sum_comp]
  change (∑ world : (Fin n → Bool) × (Fin table.atoms.length → Bool),
    if eval (joinedAssignment world.1 world.2) formula
    then (productWeight (neutralPrior table p) (joinedAssignment world.1 world.2) : ℝ≥0∞) else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro choice _
  simp only [contract, neutral_assignment_weight table p]
  cases event choice <;> simp [coe_productWeight]

/-- A fair weight on each program atom contributes exactly one common factor. -/
theorem completion_raw_count (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (tight : Tight rules) (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (goals : List (GoalLit σ)) (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    ClausificationCounting.count method (completionQuery table facts rules goals) (neutralPrior table p) =
      bdd_wmc (programBDD method table facts rules goals) (fun i => (p i : ℝ≥0∞)) *
        (1/2 : ℝ≥0∞) ^ table.atoms.length := by
  rw [bdd_wmc_correct _ (programBDD_ordered method table facts rules goals) _
    (fun i => ENNReal.coe_le_coe.mpr (hp i))]
  refine uniqueExtension_raw_count method table _ (modelValues table facts rules s) _ ?_ p hp
  intro choice values
  rw [programBDD_correct method table facts rules covers tight s stratified]
  exact completionQuery_correct table facts rules covers tight s stratified choice values goals

theorem completion_weighted_count (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (tight : Tight rules) (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (goals : List (GoalLit σ)) (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    (2 : ℝ≥0∞) ^ table.atoms.length *
      ClausificationCounting.count method (completionQuery table facts rules goals) (neutralPrior table p) =
        bdd_wmc (programBDD method table facts rules goals) (fun i => (p i : ℝ≥0∞)) := by
  rw [completion_raw_count method table facts rules covers tight s stratified goals p hp]
  have cancel : (2 : ℝ≥0∞) ^ table.atoms.length * (1/2 : ℝ≥0∞) ^ table.atoms.length = 1 := by
    rw [← mul_pow]
    norm_num [ENNReal.mul_inv_cancel]
  rw [← mul_assoc, mul_comm _ (bdd_wmc _ _), mul_assoc, cancel, mul_one]

noncomputable def choiceProbability (prog : ProbMeTTaSourceProgram σ n) (i : Fin n) : ℝ≥0 :=
  (prog.probs i).toNNReal

omit [DecidableEq (GroundAtom σ)] in
@[simp] theorem coe_choiceProbability (prog : ProbMeTTaSourceProgram σ n) (i : Fin n) :
    (choiceProbability prog i : ℝ≥0∞) = prog.probs i :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (prog.probs_le_one i))

omit [DecidableEq (GroundAtom σ)] in
theorem choiceProbability_le_one (prog : ProbMeTTaSourceProgram σ n) (i : Fin n) :
    choiceProbability prog i ≤ 1 := by
  apply ENNReal.coe_le_coe.mp
  simpa using prog.probs_le_one i

theorem programCount_weighted_completion (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification σ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit σ)) :
    programCount method table prog goals = (2 : ℝ≥0∞) ^ table.atoms.length *
      ClausificationCounting.count method (completionQuery table prog.probFacts prog.normalRules goals)
        (neutralPrior table (choiceProbability prog)) := by
  simpa only [coe_choiceProbability, programCount] using
    (completion_weighted_count method table prog.probFacts prog.normalRules covers tight s stratified
      goals (choiceProbability prog) (choiceProbability_le_one prog)).symm

omit [DecidableEq (GroundAtom σ)] in
theorem sourceEvent_append (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (first second : List (GoalLit σ)) (choice : Fin n → Bool) :
    sourceEvent prog s (first ++ second) choice =
      (sourceEvent prog s first choice && sourceEvent prog s second choice) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, sourceEvent_true, List.forall_mem_append]

theorem sourceEvent_completion (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification σ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (goals : List (GoalLit σ))
    (choice : Fin n → Bool) :
    sourceEvent prog s goals choice = true ↔ ∃ values,
      eval (joinedAssignment choice values) (completionQuery table prog.probFacts prog.normalRules goals) = true := by
  rw [sourceEvent_true]
  constructor
  · intro holds
    refine ⟨modelValues table prog.probFacts prog.normalRules s choice, ?_⟩
    apply (completionQuery_correct table prog.probFacts prog.normalRules covers tight s stratified choice _ goals).mpr
    exact ⟨rfl, fun g hg => (source_goal prog s choice g).mpr (holds g hg)⟩
  · rintro ⟨values, holds⟩
    have body := (completionQuery_correct table prog.probFacts prog.normalRules covers tight s stratified choice values goals).mp holds
    exact fun g hg => (source_goal prog s choice g).mp (body.2 g hg)

noncomputable def sourceMass (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (evidence : List (GoalLit σ)) : MassSemantics ((Fin n → Bool) → Bool) :=
  observationMass (conditionWeight (sourceEvent prog s evidence) (productWeight (choiceProbability prog))) id

omit [DecidableEq (GroundAtom σ)] in
theorem sourceMass_total (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (evidence : List (GoalLit σ)) :
    (sourceMass prog s evidence).totalMass = weightedSat (sourceEvent prog s evidence) prog.probs := by
  simp only [sourceMass, observationMass, conditionWeight, weightedSat]
  push_cast
  apply Finset.sum_congr rfl
  intro choice _
  by_cases present : sourceEvent prog s evidence choice = true <;>
    simp [present, coe_productWeight]

omit [DecidableEq (GroundAtom σ)] in
theorem sourceMass_query (prog : ProbMeTTaSourceProgram σ n) (s : Stratification σ)
    (evidence query : List (GoalLit σ)) :
    (sourceMass prog s evidence).queryMass (sourceEvent prog s query) =
      weightedSat (sourceEvent prog s (evidence ++ query)) prog.probs := by
  simp only [sourceMass, observationMass, conditionWeight, weightedSat, sourceEvent_append, id_eq]
  push_cast
  apply Finset.sum_congr rfl
  intro choice _
  by_cases he : sourceEvent prog s evidence choice = true <;>
    by_cases hq : sourceEvent prog s query choice = true <;> simp [he, hq, coe_productWeight]

noncomputable def programConditional (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (evidence query : List (GoalLit σ)) : Option ℝ≥0∞ :=
  if programCount method table prog evidence = 0 then none else
    some (programCount method table prog (evidence ++ query) / programCount method table prog evidence)

theorem programConditional_correct (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (tight : Tight prog.normalRules) (s : Stratification σ)
    (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s) (evidence query : List (GoalLit σ)) :
    programConditional method table prog evidence query =
      (sourceMass prog s evidence).query (sourceEvent prog s query) := by
  simp only [programConditional, programCount_correct method table prog covers tight s stratified,
    MassSemantics.query, MassSemantics.queryProb, sourceMass_total, sourceMass_query]
  split_ifs <;> rfl

namespace Controls

def signature (A : Type) : LPSignature where
  constants := Unit
  vars := Empty
  relationSymbols := A
  relationArity _ := 0
  functionSymbols := Empty
  functionArity := Empty.elim

instance (A : Type) : IsEmpty (signature A).functionSymbols := inferInstanceAs (IsEmpty Empty)
instance (A : Type) : Nonempty (GroundTerm (signature A)) := ⟨.const ()⟩

def atom {A : Type} (a : A) : GroundAtom (signature A) := ⟨a, Fin.elim0⟩

@[simp] theorem atom_inj {A : Type} (a b : A) : atom a = atom b ↔ a = b :=
  ⟨congrArg GroundAtom.symbol, congrArg atom⟩

theorem atom_surjective {A : Type} (a : GroundAtom (signature A)) : ∃ b, atom b = a := by
  refine ⟨a.symbol, ?_⟩
  cases a with
  | mk symbol args =>
    have emptyArgs : args = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst args
    rfl

def atomEquiv (A : Type) : GroundAtom (signature A) ≃ A where
  toFun a := a.symbol
  invFun := atom
  left_inv a := by obtain ⟨a, rfl⟩ := atom_surjective a; rfl
  right_inv _ := rfl

instance (A : Type) [DecidableEq A] : DecidableEq (GroundAtom (signature A)) :=
  Equiv.decidableEq (atomEquiv A)

def zeroStratum (A : Type) : Stratification (signature A) := fun _ => 0

def readSet {A : Type} (S : Set (GroundAtom (signature A))) : Set A := {a | atom a ∈ S}

open Mettapedia.GSLT.OpenEnded.PrologContrasts (Atom)

def liarRules : List (NormalClause (signature Atom)) :=
  [⟨atom .p, [.neg (atom .p)]⟩]

def choiceRules : List (NormalClause (signature Atom)) :=
  [⟨atom .p, [.neg (atom .q)]⟩, ⟨atom .q, [.neg (atom .p)]⟩]

theorem liar_no_supported (S : Set (GroundAtom (signature Atom))) : ¬ SupportedModel liarRules ∅ S := by
  intro supported
  apply Mettapedia.GSLT.OpenEnded.PrologContrasts.liar_no_supported_model (readSet S)
  ext a
  have point := Set.ext_iff.mp supported (atom a)
  cases a <;> simp_all [readSet, T_normal, liarRules, normalClauseBodyHolds, goalLitHoldsIn,
    Mettapedia.GSLT.OpenEnded.PrologContrasts.nafStep, Mettapedia.GSLT.OpenEnded.PrologContrasts.liar]

theorem liar_tight : Tight liarRules := by
  apply (TightCertificate.sound (rules := liarRules))
  refine ⟨fun _ => 0, ?_⟩
  intro c hc a ha
  have same : c = ⟨atom .p, [.neg (atom .p)]⟩ := by simpa [liarRules] using hc
  subst c
  simp at ha

theorem liar_not_stratifiable : ¬ isStratifiable liarRules := by
  rintro ⟨s, respects⟩
  have loop : s (atom Atom.p) < s (atom Atom.p) :=
    respects ⟨atom .p, [.neg (atom .p)]⟩ (by simp [liarRules]) (.neg (atom .p)) (by simp)
  exact Nat.lt_irrefl _ loop

theorem liar_no_stable (S : Set (GroundAtom (signature Atom))) : ¬ StableModel liarRules ∅ S :=
  fun stable => liar_no_supported S (stable_supported stable)

theorem choice_supported_reading (S : Set (GroundAtom (signature Atom))) :
    SupportedModel choiceRules ∅ S ↔
      Mettapedia.GSLT.OpenEnded.PrologContrasts.nafStep Mettapedia.GSLT.OpenEnded.PrologContrasts.choice (readSet S) = readSet S := by
  constructor
  · intro supported
    ext a
    have point := Set.ext_iff.mp supported (atom a)
    cases a <;> simpa [readSet, T_normal, choiceRules, normalClauseBodyHolds, goalLitHoldsIn,
      Mettapedia.GSLT.OpenEnded.PrologContrasts.nafStep, Mettapedia.GSLT.OpenEnded.PrologContrasts.choice] using point
  · intro supported
    ext a
    obtain ⟨a, rfl⟩ := atom_surjective a
    have point := Set.ext_iff.mp supported a
    cases a <;> simpa [readSet, T_normal, choiceRules, normalClauseBodyHolds, goalLitHoldsIn,
      Mettapedia.GSLT.OpenEnded.PrologContrasts.nafStep, Mettapedia.GSLT.OpenEnded.PrologContrasts.choice] using point

theorem choice_tight : Tight choiceRules := by
  apply (TightCertificate.sound (rules := choiceRules))
  refine ⟨fun _ => 0, ?_⟩
  intro c hc a ha
  simp only [choiceRules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp at ha

theorem choice_two_stable : StableModel choiceRules ∅ {atom Atom.p} ∧ StableModel choiceRules ∅ {atom Atom.q} := by
  have readP : readSet {atom Atom.p} = {Atom.p} := by ext a; simp [readSet]
  have readQ : readSet {atom Atom.q} = {Atom.q} := by ext a; simp [readSet]
  constructor
  · rw [stable_iff_supported choice_tight, choice_supported_reading, readP]
    exact Mettapedia.GSLT.OpenEnded.PrologContrasts.choice_model_p
  · rw [stable_iff_supported choice_tight, choice_supported_reading, readQ]
    exact Mettapedia.GSLT.OpenEnded.PrologContrasts.choice_model_q

theorem choice_only_two (S : Set (GroundAtom (signature Atom))) :
    StableModel choiceRules ∅ S ↔ S = {atom Atom.p} ∨ S = {atom Atom.q} := by
  constructor
  · intro stable
    have supported := stable_supported stable
    have hp := Set.ext_iff.mp supported (atom Atom.p)
    have hq := Set.ext_iff.mp supported (atom Atom.q)
    simp only [Set.mem_union, Set.mem_empty_iff_false, false_or] at hp hq
    have p : (atom Atom.p ∈ S ↔ atom Atom.q ∉ S) := by
      simpa [T_normal, choiceRules, normalClauseBodyHolds, goalLitHoldsIn] using hp.symm
    have q : (atom Atom.q ∈ S ↔ atom Atom.p ∉ S) := by
      simpa [T_normal, choiceRules, normalClauseBodyHolds, goalLitHoldsIn] using hq.symm
    by_cases present : atom Atom.p ∈ S
    · left
      have absent := p.mp present
      ext a
      obtain ⟨a, rfl⟩ := atom_surjective a
      cases a <;> simp [present, absent]
    · right
      have other := q.mpr present
      ext a
      obtain ⟨a, rfl⟩ := atom_surjective a
      cases a <;> simp [present, other]
  · rintro (rfl | rfl)
    · exact choice_two_stable.1
    · exact choice_two_stable.2

theorem choice_not_stratifiable : ¬ isStratifiable choiceRules := by
  rintro ⟨s, respects⟩
  have pq : s (atom Atom.q) < s (atom Atom.p) :=
    respects ⟨atom .p, [.neg (atom .q)]⟩ (by simp [choiceRules]) (.neg (atom .q)) (by simp)
  have qp : s (atom Atom.p) < s (atom Atom.q) :=
    respects ⟨atom .q, [.neg (atom .p)]⟩ (by simp [choiceRules]) (.neg (atom .p)) (by simp)
  omega

def loopRules : List (NormalClause (signature Unit)) := [⟨atom (), [.pos (atom ())]⟩]

theorem loop_stratified : ∀ c ∈ loopRules, respectsStratification c (zeroStratum Unit) := by
  intro c hc
  have same : c = ⟨atom (), [.pos (atom ())]⟩ := by simpa [loopRules] using hc
  subst c
  simp [respectsStratification]

theorem loop_not_tight : ¬ Tight loopRules := by
  rw [tight_iff_acyclic]
  intro acyclic
  apply acyclic (atom ())
  exact Relation.TransGen.single ⟨⟨atom (), [.pos (atom ())]⟩, by simp [loopRules], rfl, by simp⟩

theorem loop_stable_empty : StableModel loopRules ∅ ∅ := by
  rw [stable_iff]
  apply Set.Subset.antisymm (Set.empty_subset _)
  apply OrderHom.lfp_le
  rintro a (absent | ⟨c, hc, _, body⟩)
  · exact absent.elim
  · have same : c = ⟨atom (), [.pos (atom ())]⟩ := by simpa [loopRules] using hc
    subst c
    exact body (.pos (atom ())) (by simp)

theorem loop_supported_nonempty : SupportedModel loopRules ∅ {atom ()} := by
  ext a
  obtain ⟨a, rfl⟩ := atom_surjective a
  cases a
  simp [T_normal, loopRules, normalClauseBodyHolds, goalLitHoldsIn]

def loopSource : ProbMeTTaSourceProgram (signature Unit) 0 where
  probFacts := Fin.elim0
  probs := Fin.elim0
  probs_le_one i := Fin.elim0 i
  normalRules := loopRules
  facts_injective i := Fin.elim0 i

def loopTable : AtomTable (GroundAtom (signature Unit)) := ⟨[atom ()], by simp⟩

def originalLoop : Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation.ProbLogProgram (signature Unit) 0 where
  probFacts := Fin.elim0
  probs := Fin.elim0
  rules := [⟨(atom ()).toAtom, [(atom ()).toAtom]⟩]
  facts_injective i := Fin.elim0 i

/-- Reuse the existing ProbLog recursion control on the same ground program. -/
theorem original_loop_absent (world : Fin (2 ^ 0)) :
    ¬ Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation.queryHolds originalLoop (atom ()) world :=
  Mettapedia.PLN.Bridges.Languages.ProbLog.ExtensionControls.recursive_query_absent world

theorem loop_source_probability_zero : loopSource.probExact (zeroStratum Unit) (atom ()) = 0 := by
  rw [ProbMeTTaSourceProgram.probExact_eq_weightedSat_query]
  have empty : fullStratifiedModel loopRules ∅ (zeroStratum Unit) = ∅ :=
    ((stable_iff_eq_full loopRules ∅ (zeroStratum Unit) loop_stratified ∅).mp loop_stable_empty).symm
  have base (choice : Fin 0 → Bool) : chosenFacts loopSource.probFacts choice = ∅ := by
    ext a
    simp [chosenFacts]
  have absent (choice : Fin 0 → Bool) :
      ¬ queryHoldsNormalA loopSource.toNormalProbLogProgram (zeroStratum Unit) (atom ()) choice := by
    change atom () ∉ fullStratifiedModel loopRules (leastHerbrandModel (residualKBa loopSource.toProbLogBase choice)) (zeroStratum Unit)
    rw [normalized_base, base, empty]
    simp
  simp [weightedSat, absent]

theorem loop_completion_model_counts :
    PropositionalTseitinMass.Controls.count (fun values : Fin 1 → Bool =>
      eval (joinedAssignment Fin.elim0 values) (completion loopTable loopSource.probFacts loopRules)) = 2 ∧
    PropositionalTseitinMass.Controls.count (fun values : Fin 1 → Bool =>
      eval (joinedAssignment Fin.elim0 values) (completionQuery loopTable loopSource.probFacts loopRules [.pos (atom ())])) = 1 := by decide

theorem loop_completion_probability_half (method : Method) :
    countQuery (fun formula => ClausificationCounting.count method formula (fun _ => 1/2))
      (completion loopTable loopSource.probFacts loopRules) (goalsFormula loopTable 0 [.pos (atom ())]) =
        some (1/2 : ℝ≥0∞) := by
  have total : PropositionalTseitinMass.Controls.count (fun world : Fin (0 + loopTable.atoms.length) → Bool =>
      eval world (completion loopTable loopSource.probFacts loopRules)) = 2 := by decide
  have joint : PropositionalTseitinMass.Controls.count (fun world : Fin (0 + loopTable.atoms.length) → Bool =>
      eval world (.and (completion loopTable loopSource.probFacts loopRules)
        (goalsFormula loopTable 0 [.pos (atom ())]))) = 1 := by decide
  simp only [countQuery, ClausificationCounting.model_count, total, joint]
  norm_num [loopTable, ENNReal.div_self]

def negativeRules : List (NormalClause (signature Bool)) := [⟨atom true, [.neg (atom false)]⟩]
def negativeFacts : Fin 1 → GroundAtom (signature Bool) := fun _ => atom false
def negativeTable : AtomTable (GroundAtom (signature Bool)) := ⟨[atom false, atom true], by simp⟩
def negativeStratum : Stratification (signature Bool) := fun a => match (a.symbol : Bool) with | false => 0 | true => 1

noncomputable def negativeSource (p : ℝ≥0) (hp : p ≤ 1) : ProbMeTTaSourceProgram (signature Bool) 1 where
  probFacts := negativeFacts
  probs _ := p
  probs_le_one _ := by exact_mod_cast hp
  normalRules := negativeRules
  facts_injective _ _ _ := Subsingleton.elim _ _

theorem negative_covers : Covers negativeTable negativeFacts negativeRules := by
  constructor
  · intro i
    simp [negativeTable, negativeFacts]
  · intro c hc
    have same : c = ⟨atom true, [.neg (atom false)]⟩ := by simpa [negativeRules] using hc
    subst c
    simp [negativeTable]

theorem negative_tight : Tight negativeRules := by
  apply (TightCertificate.sound (rules := negativeRules))
  refine ⟨fun _ => 0, ?_⟩
  intro c hc a ha
  have same : c = ⟨atom true, [.neg (atom false)]⟩ := by simpa [negativeRules] using hc
  subst c
  simp at ha

theorem negative_stratified : ∀ c ∈ negativeRules, respectsStratification c negativeStratum := by
  intro c hc
  have same : c = ⟨atom true, [.neg (atom false)]⟩ := by simpa [negativeRules] using hc
  subst c
  simp [respectsStratification, negativeStratum, atom]

theorem negative_completion_event : ∀ choice : Fin 1 → Bool,
    (∃ values : Fin 2 → Bool,
      eval (joinedAssignment choice values) (completionQuery negativeTable negativeFacts negativeRules [.pos (atom true)]) = true) ↔
        (!(choice 0)) = true := by decide

theorem negative_source_event (p : ℝ≥0) (hp : p ≤ 1) (choice : Fin 1 → Bool) :
    sourceEvent (negativeSource p hp) negativeStratum [.pos (atom true)] choice = !choice 0 := by
  apply Bool.eq_iff_iff.mpr
  rw [sourceEvent_completion negativeTable (negativeSource p hp) negative_covers negative_tight
    negativeStratum negative_stratified]
  exact negative_completion_event choice

theorem negative_probability (method : Method) (p : ℝ≥0) (hp : p ≤ 1) :
    programCount method negativeTable (negativeSource p hp) [.pos (atom true)] = 1 - (p : ℝ≥0∞) := by
  rw [programCount_correct method negativeTable (negativeSource p hp) negative_covers negative_tight
    negativeStratum negative_stratified]
  simp only [weightedSat, negative_source_event]
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp [assignmentWeight, varWeight, negativeSource]

theorem third_le_one : (1/3 : ℝ≥0) ≤ 1 := by
  exact_mod_cast (show (1/3 : ℝ) ≤ 1 by norm_num)

theorem negative_probability_two_thirds (method : Method) :
    programCount method negativeTable (negativeSource (1/3) third_le_one) [.pos (atom true)] = 2/3 := by
  rw [negative_probability]
  have ratio : (1 : ℝ≥0) - 1/3 = 2/3 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub third_le_one]
    norm_num
  rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ratio]
  norm_num

theorem zero_and_one_probabilities (method : Method) :
    programCount method negativeTable (negativeSource 0 (by norm_num)) [.pos (atom true)] = 1 ∧
      programCount method negativeTable (negativeSource 1 (by norm_num)) [.pos (atom true)] = 0 := by
  constructor <;> rw [negative_probability] <;> norm_num

theorem zero_evidence_absent (method : Method) :
    programConditional method negativeTable (negativeSource 1 (by norm_num))
      [.pos (atom true)] [.pos (atom false)] = none := by
  simp only [programConditional, negative_probability]
  norm_num

def derivedFactRules : List (NormalClause (signature Bool)) := [⟨atom false, []⟩]

theorem selected_fact_need_not_be_atom_truth :
    eval (joinedAssignment (fun _ : Fin 1 => false) ![true, false])
      (completion negativeTable negativeFacts derivedFactRules) = true := by decide

theorem missing_definition_closed :
    eval (joinedAssignment (fun _ : Fin 1 => false) ![true, true])
      (completion negativeTable negativeFacts derivedFactRules) = false := by decide

theorem guards_and_duplicate_rules :
    eval (joinedAssignment (fun _ : Fin 0 => false) ![false, false])
      (completion negativeTable Fin.elim0 [⟨atom true, [.neq (atom false) (atom false)]⟩]) = true ∧
    eval (joinedAssignment (fun _ : Fin 0 => false) ![false, true])
      (completion negativeTable Fin.elim0 [⟨atom true, [.neq (atom false) (atom true)]⟩]) = true ∧
    (∀ choice values, eval (joinedAssignment choice values)
      (completion negativeTable negativeFacts (negativeRules ++ negativeRules)) =
        eval (joinedAssignment choice values) (completion negativeTable negativeFacts negativeRules)) := by decide

def mixedNormal : List (NormalClause (signature (Fin 3))) := [⟨atom 1, [.neg (atom 0)]⟩]
def allNormal : List (NormalClause (signature (Fin 3))) := mixedNormal ++ [⟨atom 2, [.pos (atom 1)]⟩]
def mixedStratum : Stratification (signature (Fin 3)) := fun a => (a.symbol : Fin 3).val

def layeredProgram : NormalProbLogProgram (signature (Fin 3)) 0 where
  probFacts := Fin.elim0
  probs := Fin.elim0
  rules := [⟨(atom (2 : Fin 3)).toAtom, [(atom (1 : Fin 3)).toAtom]⟩]
  facts_injective i := Fin.elim0 i
  normalRules := mixedNormal

def normalizedProgram : ProbMeTTaSourceProgram (signature (Fin 3)) 0 where
  probFacts := Fin.elim0
  probs := Fin.elim0
  probs_le_one i := Fin.elim0 i
  facts_injective i := Fin.elim0 i
  normalRules := allNormal

theorem allNormal_tight : Tight allNormal := by
  apply TightCertificate.sound (rules := allNormal)
  refine ⟨mixedStratum, ?_⟩
  intro c hc a ha
  simp only [allNormal, mixedNormal, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp at ha
  · simp only [List.mem_singleton, GoalLit.pos.injEq] at ha
    subst a
    decide

theorem allNormal_stratified : ∀ c ∈ allNormal, respectsStratification c mixedStratum := by
  intro c hc
  simp only [allNormal, mixedNormal, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [respectsStratification, mixedStratum, atom]

theorem mixedNormal_tight : Tight mixedNormal := by
  apply allNormal_tight.mono
  rintro a b ⟨c, hc, head, body⟩
  exact ⟨c, List.mem_append_left _ hc, head, body⟩

theorem mixedNormal_stratified : ∀ c ∈ mixedNormal, respectsStratification c mixedStratum :=
  fun c hc => allNormal_stratified c (List.mem_append_left _ hc)

theorem mixed_supported_models : SupportedModel mixedNormal ∅ {atom (1 : Fin 3)} ∧
    SupportedModel allNormal ∅ {atom (1 : Fin 3), atom (2 : Fin 3)} := by
  constructor <;> ext a <;> obtain ⟨a, rfl⟩ := atom_surjective a <;> fin_cases a <;>
    simp [T_normal, mixedNormal, allNormal, normalClauseBodyHolds, goalLitHoldsIn]

theorem layered_base_empty (choice : Fin 0 → Bool) :
    leastHerbrandModel (residualKBa layeredProgram.toProbLogProgram choice) = ∅ := by
  apply Set.Subset.antisymm ?_ (Set.empty_subset _)
  apply leastHerbrandModel_least
  rw [T_P_LP_le_iff]
  constructor
  · rintro a ⟨i, _, _⟩
    exact Fin.elim0 i
  · intro c grounding member body
    have same : c = ⟨(atom (2 : Fin 3)).toAtom, [(atom (1 : Fin 3)).toAtom]⟩ := by
      simpa [residualKBa, layeredProgram] using member
    subst c
    exact (body (atom (1 : Fin 3)).toAtom (by simp)).elim

/-- Freezing `r ← q` before deriving `q ← ¬p` loses `r`; normalization derives both. -/
theorem frozen_base_diverges :
    ¬ queryHoldsNormalA layeredProgram mixedStratum (atom (2 : Fin 3)) Fin.elim0 ∧
      queryHoldsNormalA normalizedProgram.toNormalProbLogProgram mixedStratum (atom (2 : Fin 3)) Fin.elim0 := by
  have oldModel : fullStratifiedModel mixedNormal ∅ mixedStratum = {atom (1 : Fin 3)} :=
    ((supported_iff_eq_full mixedNormal ∅ mixedStratum mixedNormal_stratified mixedNormal_tight _).mp
      mixed_supported_models.1).symm
  have newModel : fullStratifiedModel allNormal ∅ mixedStratum = {atom (1 : Fin 3), atom (2 : Fin 3)} :=
    ((supported_iff_eq_full allNormal ∅ mixedStratum allNormal_stratified allNormal_tight _).mp
      mixed_supported_models.2).symm
  have noFacts : chosenFacts normalizedProgram.probFacts Fin.elim0 = ∅ := by ext a; simp [chosenFacts]
  constructor
  · change atom (2 : Fin 3) ∉ fullStratifiedModel mixedNormal
      (leastHerbrandModel (residualKBa layeredProgram.toProbLogProgram Fin.elim0)) mixedStratum
    rw [layered_base_empty, oldModel]
    simp
  · change atom (2 : Fin 3) ∈ fullStratifiedModel allNormal
      (leastHerbrandModel (residualKBa normalizedProgram.toProbLogBase Fin.elim0)) mixedStratum
    rw [normalized_base, noFacts, newModel]
    simp

def emptySource : ProbMeTTaSourceProgram (signature Unit) 0 := { loopSource with normalRules := [] }
def emptyTable : AtomTable (GroundAtom (signature Unit)) := programTable emptySource.probFacts [] []

theorem empty_program_count (method : Method) : programCount method emptyTable emptySource [] = 1 := by
  have tight : Tight ([] : List (NormalClause (signature Unit))) := by
    apply TightCertificate.sound
    exact ⟨fun _ => 0, fun _ h => by cases h⟩
  rw [programCount_correct method emptyTable emptySource (programTable_covers _ _ _) tight
    (zeroStratum Unit) (fun _ h => by cases h)]
  simp [weightedSat, sourceEvent, assignmentWeight]

end Controls

end Mettapedia.Logic.BDDCore.NormalCompletion
