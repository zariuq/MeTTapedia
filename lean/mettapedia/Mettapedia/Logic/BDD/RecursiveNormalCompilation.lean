import Mettapedia.Logic.NormalProgramLoops
import Mettapedia.Logic.BDD.NormalCompletion

/-!
# Certified probability for recursive stratified ground programs

Clark completion and all induced positive loop formulas are compiled through
the existing full Tseitin or polarity-directed route. Projection retains the
original random choices. Stable-model correspondence holds for all finite
ground normal programs; probability soundness additionally uses stratification
to give a unique model for each total choice. No tightness premise is needed.

For non-stratified programs, the projected Boolean observation means existence
of a stable model satisfying the goals. It does not select a distribution over
multiple stable models. Enumeration of loops may be exponential.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.RecursiveNormalCompilation

open scoped NNReal ENNReal BigOperators
open LP NormalProgramSemantics ClarkCompletion NormalProgramLoops PropositionalTseitin TseitinCounting
open NormalCompletion
open ClausificationCounting (Method)
open Mettapedia.ProbabilityTheory

variable {σ : LPSignature} [DecidableEq (GroundAtom σ)] {n : Nat}

def loopProgramBDD (method : Method) (table : AtomTable (GroundAtom σ)) (facts : Fin n → GroundAtom σ)
    (rules : List (NormalClause σ)) (goals : List (GoalLit σ)) : BDD n :=
  Projection.projectAux (formulaBDD method (loopQuery table facts rules goals))

theorem loopProgramBDD_ordered (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (goals : List (GoalLit σ)) :
    (loopProgramBDD method table facts rules goals).Ordered none :=
  Projection.projectAux_ordered _ none (formulaBDD_ordered method _)

/-- Without stratification this observation is existential stable-model satisfaction. -/
theorem loopProgramBDD_models (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    (loopProgramBDD method table facts rules goals).eval choice = true ↔
      ∃ S, StableModel rules (chosenFacts facts choice) S ∧ ∀ g ∈ goals, goalLitHoldsIn S S g := by
  classical
  rw [loopProgramBDD, Projection.projectAux_eval _ (formulaBDD_ordered method _)]
  simp only [formulaBDD_eval, loopQuery, eval, Bool.and_eq_true,
    loopCompletion_models table facts rules covers, eval_goalsFormula]
  constructor
  · rintro ⟨values, stable, goals⟩
    exact ⟨table.interpretation values, stable, goals⟩
  · rintro ⟨S, stable, goals⟩
    have supported := stable_supported stable
    have contained : S ⊆ {a | a ∈ table.atoms} := by
      rw [← supported]
      exact consequences_contained table facts rules covers choice S
    refine ⟨fun i => decide (table.atoms.get i ∈ S), ?_⟩
    rw [table.interpretation_realize S contained]
    exact ⟨stable, goals⟩

theorem loopProgramBDD_correct (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    (loopProgramBDD method table facts rules goals).eval choice = true ↔
      ∀ g ∈ goals, goalLitHoldsIn (fullStratifiedModel rules (chosenFacts facts choice) s)
        (fullStratifiedModel rules (chosenFacts facts choice) s) g := by
  rw [loopProgramBDD_models method table facts rules covers]
  simp only [stable_iff_eq_full rules (chosenFacts facts choice) s stratified, exists_eq_left]

theorem loopProgramBDD_source (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    (loopProgramBDD method table prog.probFacts prog.normalRules goals).eval choice = sourceEvent prog s goals choice := by
  apply Bool.eq_iff_iff.mpr
  rw [loopProgramBDD_correct method table prog.probFacts prog.normalRules covers s stratified, sourceEvent_true]
  simp only [source_goal]

theorem loopSourceEvent_formula (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) (choice : Fin n → Bool) :
    sourceEvent prog s goals choice = true ↔ ∃ values,
      eval (joinedAssignment choice values) (loopQuery table prog.probFacts prog.normalRules goals) = true := by
  rw [sourceEvent_true]
  constructor
  · intro holds
    refine ⟨modelValues table prog.probFacts prog.normalRules s choice, ?_⟩
    apply (loopQuery_correct table prog.probFacts prog.normalRules covers s stratified choice _ goals).mpr
    exact ⟨rfl, fun g hg => (source_goal prog s choice g).mpr (holds g hg)⟩
  · rintro ⟨values, holds⟩
    have body := (loopQuery_correct table prog.probFacts prog.normalRules covers s stratified choice values goals).mp holds
    exact fun g hg => (source_goal prog s choice g).mp (body.2 g hg)

noncomputable def loopProgramCount (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (goals : List (GoalLit σ)) : ℝ≥0∞ :=
  bdd_wmc (loopProgramBDD method table prog.probFacts prog.normalRules goals) prog.probs

theorem loopProgramCount_correct (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) :
    loopProgramCount method table prog goals = weightedSat (sourceEvent prog s goals) prog.probs := by
  rw [loopProgramCount, bdd_wmc_correct _ (loopProgramBDD_ordered method table prog.probFacts prog.normalRules goals)
    _ prog.probs_le_one]
  simp only [weightedSat, loopProgramBDD_source method table prog covers s stratified]

theorem loopProgramCount_eq_queryProb (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) :
    loopProgramCount method table prog goals =
      Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb prog.probs
        (fun world => sourceEvent prog s goals (WMPLNBDDWMCExact.worldAssignmentEquiv n world)) :=
  WMPLNBDDWMCExact.bdd_wmc_eq_queryProb _
    (loopProgramBDD_ordered method table prog.probFacts prog.normalRules goals) _ prog.probs_le_one _
    (fun world => loopProgramBDD_source method table prog covers s stratified goals
      (WMPLNBDDWMCExact.worldAssignmentEquiv n world))

theorem loop_raw_count (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (covers : Covers table facts rules)
    (s : Stratification σ) (stratified : ∀ c ∈ rules, respectsStratification c s)
    (goals : List (GoalLit σ)) (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    ClausificationCounting.count method (loopQuery table facts rules goals) (neutralPrior table p) =
      bdd_wmc (loopProgramBDD method table facts rules goals) (fun i => (p i : ℝ≥0∞)) *
        (1/2 : ℝ≥0∞) ^ table.atoms.length := by
  rw [bdd_wmc_correct _ (loopProgramBDD_ordered method table facts rules goals) _
    (fun i => ENNReal.coe_le_coe.mpr (hp i))]
  refine uniqueExtension_raw_count method table _ (modelValues table facts rules s) _ ?_ p hp
  intro choice values
  rw [loopProgramBDD_correct method table facts rules covers s stratified]
  exact loopQuery_correct table facts rules covers s stratified choice values goals

theorem loopProgramCount_weighted_completion (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit σ)) :
    loopProgramCount method table prog goals = (2 : ℝ≥0∞) ^ table.atoms.length *
      ClausificationCounting.count method (loopQuery table prog.probFacts prog.normalRules goals)
        (neutralPrior table (choiceProbability prog)) := by
  rw [loop_raw_count method table prog.probFacts prog.normalRules covers s stratified goals
    (choiceProbability prog) (choiceProbability_le_one prog)]
  simp only [coe_choiceProbability]
  have cancel : (2 : ℝ≥0∞) ^ table.atoms.length * (1/2 : ℝ≥0∞) ^ table.atoms.length = 1 := by
    rw [← mul_pow]
    norm_num [ENNReal.mul_inv_cancel]
  rw [← mul_assoc, mul_comm _ (bdd_wmc _ _), mul_assoc, cancel, mul_one]
  rfl

noncomputable def loopProgramConditional (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (evidence query : List (GoalLit σ)) : Option ℝ≥0∞ :=
  if loopProgramCount method table prog evidence = 0 then none else
    some (loopProgramCount method table prog (evidence ++ query) / loopProgramCount method table prog evidence)

theorem loopProgramConditional_correct (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification σ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (evidence query : List (GoalLit σ)) :
    loopProgramConditional method table prog evidence query =
      (sourceMass prog s evidence).query (sourceEvent prog s query) := by
  simp only [loopProgramConditional, loopProgramCount_correct method table prog covers s stratified,
    MassSemantics.query, MassSemantics.queryProb, sourceMass_total, sourceMass_query]
  split_ifs <;> rfl

theorem loopProgramBDD_eq_of_tight (method : Method) (table : AtomTable (GroundAtom σ))
    (facts : Fin n → GroundAtom σ) (rules : List (NormalClause σ)) (tight : Tight rules)
    (goals : List (GoalLit σ)) :
    loopProgramBDD method table facts rules goals = programBDD method table facts rules goals := by
  simp only [loopProgramBDD, programBDD, loopQuery, loopCompletion_eq_of_tight table facts rules tight, completionQuery]

theorem loopProgramCount_eq_of_tight (method : Method) (table : AtomTable (GroundAtom σ))
    (prog : ProbMeTTaSourceProgram σ n) (tight : Tight prog.normalRules) (goals : List (GoalLit σ)) :
    loopProgramCount method table prog goals = programCount method table prog goals := by
  rw [loopProgramCount, loopProgramBDD_eq_of_tight method table prog.probFacts prog.normalRules tight]
  rfl

section ExistingSourceAPI

universe u v
variable {τ : LPSignature.{u, u, v, u}} [DecidableEq (GroundAtom τ)]
variable [IsEmpty τ.functionSymbols] [Nonempty (GroundTerm τ)]

theorem loopProgramCount_eq_probExact (method : Method) (table : AtomTable (GroundAtom τ))
    (prog : ProbMeTTaSourceProgram τ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification τ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (query : GroundAtom τ) : loopProgramCount method table prog [.pos query] = prog.probExact s query := by
  rw [loopProgramCount_correct method table prog covers s stratified, sourceEvent_eq_probExact]

theorem loop_agrees_with_extensional (method : Method) (table : AtomTable (GroundAtom τ))
    (prog : ProbMeTTaSourceProgram τ n) (covers : Covers table prog.probFacts prog.normalRules)
    (s : Stratification τ) (stratified : ∀ c ∈ prog.normalRules, respectsStratification c s)
    (goals : List (GoalLit τ)) :
    ∃ f : BDD n, f.Ordered none ∧
      (∀ choice, f.eval choice = (loopProgramBDD method table prog.probFacts prog.normalRules goals).eval choice) ∧
      bdd_wmc f prog.probs = loopProgramCount method table prog goals := by
  obtain ⟨f, ordered, agrees⟩ := exists_ordered_normal_goal_semantic_bdd prog.toNormalProbLogProgram s goals
  have same : ∀ choice, f.eval choice = (loopProgramBDD method table prog.probFacts prog.normalRules goals).eval choice := by
    intro choice
    apply Bool.eq_iff_iff.mpr
    rw [loopProgramBDD_source method table prog covers s stratified, sourceEvent_true]
    exact agrees choice
  refine ⟨f, ordered, same, ?_⟩
  rw [bdd_wmc_correct f ordered _ prog.probs_le_one,
    loopProgramCount, bdd_wmc_correct _ (loopProgramBDD_ordered method table prog.probFacts prog.normalRules goals)
      _ prog.probs_le_one]
  simp only [weightedSat, same]

end ExistingSourceAPI

namespace Controls

open NormalCompletion.Controls
open Mettapedia.GSLT.OpenEnded.PrologContrasts (Atom)

theorem self_loop_emitted : loopSets loopTable loopRules = [{atom ()}] := by decide

theorem self_loop_probability_restored (method : Method) :
    countQuery (fun formula => ClausificationCounting.count method formula (fun _ => 1/2))
      (completion loopTable loopSource.probFacts loopRules) (goalsFormula loopTable 0 [.pos (atom ())]) =
        some (1/2 : ℝ≥0∞) ∧ loopProgramCount method loopTable loopSource [.pos (atom ())] = 0 := by
  refine ⟨loop_completion_probability_half method, ?_⟩
  have covers : Covers loopTable loopSource.probFacts loopRules := by
    constructor
    · intro i
      exact Fin.elim0 i
    · intro c hc
      have same : c = ⟨atom (), [.pos (atom ())]⟩ := by simpa [loopRules] using hc
      subst c
      simp [loopTable]
  rw [loopProgramCount_eq_probExact method loopTable loopSource covers (zeroStratum Unit) loop_stratified]
  exact loop_source_probability_zero

def supportFacts : Fin 1 → GroundAtom (signature (Fin 3)) := fun _ => atom 0
def supportRules : List (NormalClause (signature (Fin 3))) :=
  [⟨atom 1, [.pos (atom 2)]⟩, ⟨atom 2, [.pos (atom 1)]⟩, ⟨atom 1, [.pos (atom 0)]⟩]
def supportTable : AtomTable (GroundAtom (signature (Fin 3))) := ⟨[atom 0, atom 1, atom 2], by decide⟩

noncomputable def oneSource {A : Type} (fact : GroundAtom (signature A))
    (rules : List (NormalClause (signature A))) (p : ℝ≥0) (hp : p ≤ 1) : ProbMeTTaSourceProgram (signature A) 1 where
  probFacts _ := fact
  probs _ := p
  probs_le_one _ := by exact_mod_cast hp
  normalRules := rules
  facts_injective _ _ _ := Subsingleton.elim _ _

noncomputable def supportedCycle (p : ℝ≥0) (hp : p ≤ 1) : ProbMeTTaSourceProgram (signature (Fin 3)) 1 :=
  oneSource (atom 0) supportRules p hp

theorem support_covers : Covers supportTable supportFacts supportRules := by
  constructor
  · intro i
    simp [supportTable, supportFacts]
  · intro c hc
    simp only [supportRules, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [supportTable]

theorem support_stratified : ∀ c ∈ supportRules, respectsStratification c (zeroStratum (Fin 3)) := by
  intro c hc
  simp only [supportRules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [respectsStratification, zeroStratum]

theorem support_loop_family : loopSets supportTable supportRules = [{atom 1, atom 2}] := by decide

theorem support_not_tight : ¬ Tight supportRules := by
  intro tight
  have empty := loopSets_nil_of_tight supportTable supportRules tight
  rw [support_loop_family] at empty
  contradiction

theorem support_full_model : ∀ (choice : Fin 1 → Bool) (values : Fin 3 → Bool),
    eval (joinedAssignment choice values) (loopCompletion supportTable supportFacts supportRules) = true ↔
      values = fun _ => choice 0 := by decide

theorem support_formula_event : ∀ choice : Fin 1 → Bool,
    (∃ values : Fin 3 → Bool, eval (joinedAssignment choice values)
      (loopQuery supportTable supportFacts supportRules [.pos (atom 1)]) = true) ↔ choice 0 = true := by decide

theorem support_source_event (p : ℝ≥0) (hp : p ≤ 1) (choice : Fin 1 → Bool) :
    sourceEvent (supportedCycle p hp) (zeroStratum (Fin 3)) [.pos (atom 1)] choice = choice 0 := by
  apply Bool.eq_iff_iff.mpr
  rw [loopSourceEvent_formula supportTable (supportedCycle p hp) support_covers
    (zeroStratum (Fin 3)) support_stratified]
  exact support_formula_event choice

theorem external_support_probability (method : Method) (p : ℝ≥0) (hp : p ≤ 1) :
    loopProgramCount method supportTable (supportedCycle p hp) [.pos (atom 1)] = (p : ℝ≥0∞) := by
  rw [loopProgramCount_correct method supportTable (supportedCycle p hp) support_covers
    (zeroStratum (Fin 3)) support_stratified]
  simp only [weightedSat, support_source_event]
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp [assignmentWeight, varWeight, supportedCycle, oneSource]

theorem support_one_third (method : Method) :
    loopProgramCount method supportTable (supportedCycle (1/3) third_le_one) [.pos (atom 1)] = 1/3 := by
  rw [external_support_probability]
  norm_num

theorem support_zero_and_one (method : Method) :
    loopProgramCount method supportTable (supportedCycle 0 (by norm_num)) [.pos (atom 1)] = 0 ∧
      loopProgramCount method supportTable (supportedCycle 1 (by norm_num)) [.pos (atom 1)] = 1 := by
  constructor <;> rw [external_support_probability] <;> norm_num

theorem unsupported_evidence_absent (method : Method) :
    loopProgramConditional method supportTable (supportedCycle 0 (by norm_num))
      [.pos (atom 1)] [.pos (atom 2)] = none := by
  simp only [loopProgramConditional, external_support_probability]
  norm_num

def insideFacts : Fin 1 → GroundAtom (signature (Fin 3)) := fun _ => atom 1
def insideRules : List (NormalClause (signature (Fin 3))) :=
  [⟨atom 1, [.pos (atom 2)]⟩, ⟨atom 2, [.pos (atom 1)]⟩]
def insideTable : AtomTable (GroundAtom (signature (Fin 3))) := ⟨[atom 1, atom 2], by decide⟩
noncomputable def insideSource (p : ℝ≥0) (hp : p ≤ 1) := oneSource (atom (1 : Fin 3)) insideRules p hp

theorem inside_covers : Covers insideTable insideFacts insideRules := by
  constructor
  · intro i
    simp [insideTable, insideFacts]
  · intro c hc
    simp only [insideRules, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [insideTable]

theorem inside_stratified : ∀ c ∈ insideRules, respectsStratification c (zeroStratum (Fin 3)) := by
  intro c hc
  simp only [insideRules, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [respectsStratification, zeroStratum]

/-- A selected fact whose head is in the loop is external support, despite the cyclic rules. -/
theorem selected_fact_formula_event : ∀ choice : Fin 1 → Bool,
    (∃ values : Fin 2 → Bool, eval (joinedAssignment choice values)
      (loopQuery insideTable insideFacts insideRules [.pos (atom 2)]) = true) ↔ choice 0 = true := by decide

theorem selected_fact_support_probability (method : Method) (p : ℝ≥0) (hp : p ≤ 1) :
    loopProgramCount method insideTable (insideSource p hp) [.pos (atom 2)] = (p : ℝ≥0∞) := by
  have event (choice : Fin 1 → Bool) :
      sourceEvent (insideSource p hp) (zeroStratum (Fin 3)) [.pos (atom 2)] choice = choice 0 := by
    apply Bool.eq_iff_iff.mpr
    rw [loopSourceEvent_formula insideTable (insideSource p hp) inside_covers
      (zeroStratum (Fin 3)) inside_stratified]
    exact selected_fact_formula_event choice
  rw [loopProgramCount_correct method insideTable (insideSource p hp) inside_covers
    (zeroStratum (Fin 3)) inside_stratified]
  simp only [weightedSat, event]
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp [assignmentWeight, varWeight, insideSource, oneSource]

def threeCycle : List (NormalClause (signature (Fin 3))) :=
  [⟨atom 1, [.pos (atom 0)]⟩, ⟨atom 2, [.pos (atom 1)]⟩, ⟨atom 0, [.pos (atom 2)]⟩]

theorem induced_loop_boundaries :
    loopCheck threeCycle {atom 0, atom 1, atom 2} = true ∧
      loopCheck threeCycle {atom 0, atom 2} = false ∧
      loopCheck threeCycle {atom 0} = false ∧ loopCheck threeCycle ∅ = false := by decide

/-- The global path through vertex 1 does not make {0,2} an induced loop. -/
theorem outside_path_does_not_suffice :
    Relation.TransGen (PositiveDependency threeCycle) (atom 0) (atom 2) ∧
      loopCheck threeCycle {atom 0, atom 2} = false := by
  refine ⟨?_, induced_loop_boundaries.2.1⟩
  apply Relation.TransGen.tail (b := atom (1 : Fin 3))
  · exact .single ⟨⟨atom 1, [.pos (atom 0)]⟩, by simp [threeCycle], rfl, by simp⟩
  · exact ⟨⟨atom 2, [.pos (atom 1)]⟩, by simp [threeCycle], rfl, by simp⟩

def subloopTrap : List (NormalClause (signature (Fin 3))) :=
  [⟨atom 0, [.pos (atom 0)]⟩, ⟨atom 0, [.pos (atom 1), .pos (atom 2)]⟩,
   ⟨atom 1, [.pos (atom 0)]⟩, ⟨atom 1, []⟩]

/-- The largest loop has external support at vertex 1; the unsupported proper subloop is essential. -/
theorem maximal_loop_only_is_insufficient :
    loopSets supportTable subloopTrap = [{atom 0}, {atom 0, atom 1}] ∧
      eval (joinedAssignment (n := 0) Fin.elim0 ![true, true, false])
        (completion supportTable Fin.elim0 subloopTrap) = true ∧
      eval (joinedAssignment (n := 0) Fin.elim0 ![true, true, false])
        (loopFormula supportTable Fin.elim0 subloopTrap {atom 0, atom 1}) = true ∧
      eval (joinedAssignment (n := 0) Fin.elim0 ![true, true, false])
        (loopFormula supportTable Fin.elim0 subloopTrap {atom 0}) = false ∧
      eval (joinedAssignment (n := 0) Fin.elim0 ![true, true, false])
        (loopCompletion supportTable Fin.elim0 subloopTrap) = false := by decide

theorem undefined_atom_stays_closed :
    eval (joinedAssignment (n := 0) Fin.elim0 ![true, true, true])
      (loopCompletion supportTable Fin.elim0 subloopTrap) = false := by decide

def choiceTable : AtomTable (GroundAtom (signature Atom)) := ⟨[atom .p, atom .q], by simp⟩

/-- Loop formulas preserve both choice models; stratification, and hence a probability certificate, is absent. -/
theorem choice_remains_non_stratified :
    loopSets choiceTable choiceRules = [] ∧
      PropositionalTseitinMass.Controls.count (fun values : Fin 2 → Bool =>
        eval (joinedAssignment (n := 0) Fin.elim0 values) (loopCompletion choiceTable Fin.elim0 choiceRules)) = 2 ∧
      ¬ isStratifiable choiceRules := by
  refine ⟨loopSets_nil_of_tight choiceTable choiceRules choice_tight, ?_, choice_not_stratifiable⟩
  decide

theorem tight_route_unchanged (method : Method) :
    loopProgramCount method negativeTable (negativeSource (1/3) third_le_one) [.pos (atom true)] = 2/3 := by
  rw [loopProgramCount_eq_of_tight method negativeTable _ negative_tight]
  exact negative_probability_two_thirds method

theorem empty_program_still_one (method : Method) : loopProgramCount method emptyTable emptySource [] = 1 := by
  have tight : Tight emptySource.normalRules := by
    apply TightCertificate.sound
    exact ⟨fun _ => 0, fun _ h => by cases h⟩
  rw [loopProgramCount_eq_of_tight method emptyTable emptySource tight]
  exact empty_program_count method

def guardedSelfLoop : List (NormalClause (signature Unit)) :=
  [⟨atom (), [.pos (atom ()), .neq (atom ()) (atom ())]⟩]

theorem static_guard_does_not_remove_syntactic_loop :
    loopSets loopTable guardedSelfLoop = [{atom ()}] ∧
      eval (joinedAssignment (n := 0) Fin.elim0 (fun _ => false))
        (loopCompletion loopTable Fin.elim0 guardedSelfLoop) = true ∧
      eval (joinedAssignment (n := 0) Fin.elim0 (fun _ => true))
        (loopCompletion loopTable Fin.elim0 guardedSelfLoop) = false := by decide

theorem duplicated_rules_preserve_models : ∀ choice values,
    eval (joinedAssignment choice values) (loopCompletion supportTable supportFacts (supportRules ++ supportRules)) =
      eval (joinedAssignment choice values) (loopCompletion supportTable supportFacts supportRules) := by decide

end Controls

end Mettapedia.Logic.BDDCore.RecursiveNormalCompilation
