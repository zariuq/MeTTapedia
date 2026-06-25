import Mettapedia.Logic.BDD.FirstOrderADTranslation
import Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics

/-!
# ProbMeTTa Source Surface

This file lifts the proved ProbMeTTa runtime/query core to a normalized
source-level surface for the actual `lib_prob.metta` constructors:

- `prob-rule`
- `=>`
- `::`
- `::adr`
- `::=>`
- `prob-wmc-env`
- `?prob`
- `?prob-given`

The source surface is intentionally normalized:
- rule bodies are stored as explicit `GoalLit` lists
- probabilistic facts are stored directly as `ProbLogProgram.probFacts`
- top-level probabilities are exact `ENNReal` values, not decimal rounding

Positive example:
- `(:: p q)` really extends the probabilistic-fact environment with `q`
  at weight `p`.

Negative example:
- this file does **not** model `new-id` or mutable MeTTa spaces literally.
  Instead it formalizes the normalized source semantics they compute.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics

/-- Normalized source-level body syntax for `body-goals`. -/
inductive ProbMeTTaBody (σ : LPSignature) where
  | empty
  | single : GoalLit σ → ProbMeTTaBody σ
  | conj : List (GoalLit σ) → ProbMeTTaBody σ

/-- `body-goals`: normalize a source body to an explicit goal list. -/
def bodyGoals {σ : LPSignature} : ProbMeTTaBody σ → List (GoalLit σ)
  | .empty => []
  | .single g => [g]
  | .conj gs => gs

@[simp] theorem bodyGoals_empty {σ : LPSignature} :
    bodyGoals (σ := σ) .empty = [] := rfl

@[simp] theorem bodyGoals_single {σ : LPSignature} (g : GoalLit σ) :
    bodyGoals (.single g) = [g] := rfl

@[simp] theorem bodyGoals_conj {σ : LPSignature} (gs : List (GoalLit σ)) :
    bodyGoals (.conj gs) = gs := rfl

/-- Positive-body fragment used by the source `::adr` / `::=>` builders. -/
abbrev ProbMeTTaPositiveBody (σ : LPSignature) := List (GroundAtom σ)

/-- Coerce a positive body into a goal list. -/
def positiveBodyGoals {σ : LPSignature}
    (body : ProbMeTTaPositiveBody σ) : List (GoalLit σ) :=
  body.map GoalLit.pos

/-- A normalized ProbMeTTa source program: probabilistic facts plus normal
rules over explicit goal literals. -/
structure ProbMeTTaSourceProgram (σ : LPSignature) (n : ℕ) where
  probFacts : Fin n → GroundAtom σ
  probs : ProbAssignment n
  probs_le_one : ∀ i, probs i ≤ 1
  normalRules : List (NormalClause σ)
  facts_injective : Function.Injective probFacts

/-- The base ProbLog program carried by a source program: probabilistic facts
only, with the normal-rule layer kept separate. -/
def ProbMeTTaSourceProgram.toProbLogBase {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) : ProbLogProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  rules := []
  facts_injective := prog.facts_injective

/-- The normalized normal ProbLog program corresponding to a source surface
state. -/
def ProbMeTTaSourceProgram.toNormalProbLogProgram {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) : NormalProbLogProgram σ n where
  toProbLogProgram := prog.toProbLogBase
  normalRules := prog.normalRules

/-- `prob-rule`: add a normalized rule body to the source program. -/
def ProbMeTTaSourceProgram.probRule {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n)
    (body : ProbMeTTaBody σ) (head : GroundAtom σ) :
    ProbMeTTaSourceProgram σ n where
  probFacts := prog.probFacts
  probs := prog.probs
  probs_le_one := prog.probs_le_one
  normalRules := { head := head, body := bodyGoals body } :: prog.normalRules
  facts_injective := prog.facts_injective

/-- Backward-compatible alias for `prob-rule`. This formalizes the source
constructor `=>`. -/
def ProbMeTTaSourceProgram.arrowAlias {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n)
    (body : ProbMeTTaBody σ) (head : GroundAtom σ) :
    ProbMeTTaSourceProgram σ n :=
  prog.probRule body head

/-- Extend a finite family by one fresh final entry. -/
def extendFinFn {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) :
    Fin (n + 1) → α := fun i =>
  if h : i.1 < n then f ⟨i.1, h⟩ else x

@[simp] theorem extendFinFn_castSucc {α : Type*} {n : ℕ}
    (f : Fin n → α) (x : α) (i : Fin n) :
    extendFinFn f x i.castSucc = f i := by
  simp [extendFinFn, i.isLt]

@[simp] theorem extendFinFn_last {α : Type*} {n : ℕ}
    (f : Fin n → α) (x : α) :
    extendFinFn f x (Fin.last n) = x := by
  simp [extendFinFn]

/-- Fresh extension preserves injectivity. -/
theorem extendFinFn_injective {α : Type*} {n : ℕ}
    {f : Fin n → α} {x : α}
    (hf : Function.Injective f)
    (hfresh : ∀ i, f i ≠ x) :
    Function.Injective (extendFinFn f x) := by
  intro i j hij
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · have hEq :
          f ⟨i.1, hi⟩ = f ⟨j.1, hj⟩ := by
        simpa [extendFinFn, hi, hj] using hij
      have hFin : (⟨i.1, hi⟩ : Fin n) = ⟨j.1, hj⟩ := hf hEq
      apply Fin.ext
      simpa using congrArg Fin.val hFin
    · have hEq : f ⟨i.1, hi⟩ = x := by
        simpa [extendFinFn, hi, hj] using hij
      exact (hfresh ⟨i.1, hi⟩ hEq).elim
  · by_cases hj : j.1 < n
    · have hEq : x = f ⟨j.1, hj⟩ := by
        simpa [extendFinFn, hi, hj] using hij
      exact (hfresh ⟨j.1, hj⟩ hEq.symm).elim
    · apply Fin.ext
      omega

/-- Source constructor `(:: p goal)`: extend the probabilistic-fact surface by a
fresh new probabilistic atom. -/
def ProbMeTTaSourceProgram.addProbFact {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n)
    (p : ENNReal) (hp : p ≤ 1)
    (goal : GroundAtom σ)
    (hfresh : ∀ i, prog.probFacts i ≠ goal) :
    ProbMeTTaSourceProgram σ (n + 1) where
  probFacts := extendFinFn prog.probFacts goal
  probs := extendFinFn prog.probs p
  probs_le_one := by
    intro i
    by_cases hi : i.1 < n
    · simpa [extendFinFn, hi] using prog.probs_le_one ⟨i.1, hi⟩
    · simpa [extendFinFn, hi] using hp
  normalRules := prog.normalRules
  facts_injective := extendFinFn_injective prog.facts_injective hfresh

/-- `prob-wmc-env`: the normalized WMC environment is exactly the vector of
registered probabilistic weights. -/
def ProbMeTTaSourceProgram.probWmcEnv {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) : Fin n → ENNReal :=
  prog.probs

@[simp] theorem ProbMeTTaSourceProgram.probWmcEnv_apply {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) (i : Fin n) :
    prog.probWmcEnv i = prog.probs i := rfl

/-- Exact, non-rounded `?prob-bdd` witness for the normalized source surface. -/
noncomputable def ProbMeTTaSourceProgram.probQueryBDD
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) : BDD n :=
  Classical.choose <|
    normal_goal_wmc_semantic_equivalence
      prog.toNormalProbLogProgram s [.pos q] prog.probWmcEnv prog.probs_le_one

theorem ProbMeTTaSourceProgram.probQueryBDD_spec
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) :
    let f := prog.probQueryBDD s q
    f.Ordered none ∧
      bdd_wmc f prog.probWmcEnv = weightedSat f.eval prog.probWmcEnv ∧
      (∀ a, f.eval a = true ↔ queryHoldsNormalA prog.toNormalProbLogProgram s q a) := by
  classical
  unfold ProbMeTTaSourceProgram.probQueryBDD
  simpa [queryHoldsNormalA, GoalLit.holdsNormal] using
    Classical.choose_spec
      (normal_goal_wmc_semantic_equivalence
        prog.toNormalProbLogProgram s [.pos q] prog.probWmcEnv prog.probs_le_one)

/-- Exact, non-rounded `?prob-bdd-ev` witness for a positive evidence list on
the normalized source surface. -/
noncomputable def ProbMeTTaSourceProgram.probEvidenceBDD
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (evidence : List (GroundAtom σ)) : BDD n :=
  Classical.choose <|
    normal_goal_wmc_semantic_equivalence
      prog.toNormalProbLogProgram s (evidence.map GoalLit.pos)
      prog.probWmcEnv prog.probs_le_one

theorem ProbMeTTaSourceProgram.probEvidenceBDD_spec_goals
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (evidence : List (GroundAtom σ)) :
    let f := prog.probEvidenceBDD s evidence
    f.Ordered none ∧
      bdd_wmc f prog.probWmcEnv = weightedSat f.eval prog.probWmcEnv ∧
      (∀ a, f.eval a = true ↔
        ∀ g ∈ evidence.map GoalLit.pos,
          GoalLit.holdsNormal prog.toNormalProbLogProgram s a g) := by
  classical
  unfold ProbMeTTaSourceProgram.probEvidenceBDD
  simpa using
    Classical.choose_spec
      (normal_goal_wmc_semantic_equivalence
        prog.toNormalProbLogProgram s (evidence.map GoalLit.pos)
        prog.probWmcEnv prog.probs_le_one)

theorem ProbMeTTaSourceProgram.probEvidenceBDD_spec
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (evidence : List (GroundAtom σ)) :
    let f := prog.probEvidenceBDD s evidence
    f.Ordered none ∧
      bdd_wmc f prog.probWmcEnv = weightedSat f.eval prog.probWmcEnv ∧
      (∀ a, f.eval a = true ↔
        ∀ q ∈ evidence,
          queryHoldsNormalA prog.toNormalProbLogProgram s q a) := by
  classical
  rcases prog.probEvidenceBDD_spec_goals s evidence with ⟨hord, hwmc, hiff⟩
  refine ⟨hord, hwmc, ?_⟩
  intro a
  constructor
  · intro hf q hq
    exact (hiff a).1 hf (.pos q) (by exact List.mem_map.mpr ⟨q, hq, rfl⟩)
  · intro hall
    exact (hiff a).2 (by
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact hall q hq)

/-- The explicit source-level `?prob-bdd-ev`/query conjunction used by
`?prob-given`. -/
noncomputable def ProbMeTTaSourceProgram.probQueryEvidenceBDD
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) : BDD n :=
  apply (· && ·) (prog.probQueryBDD s q) (prog.probEvidenceBDD s evidence)

theorem ProbMeTTaSourceProgram.probQueryEvidenceBDD_spec
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    let f := prog.probQueryEvidenceBDD s q evidence
    f.Ordered none ∧
      bdd_wmc f prog.probWmcEnv = weightedSat f.eval prog.probWmcEnv ∧
      (∀ a, f.eval a = true ↔
        queryHoldsNormalA prog.toNormalProbLogProgram s q a ∧
          ∀ e ∈ evidence, queryHoldsNormalA prog.toNormalProbLogProgram s e a) := by
  classical
  dsimp [ProbMeTTaSourceProgram.probQueryEvidenceBDD]
  rcases prog.probQueryBDD_spec s q with ⟨hordQ, _hwmcQ, hiffQ⟩
  rcases prog.probEvidenceBDD_spec s evidence with ⟨hordE, _hwmcE, hiffE⟩
  refine ⟨apply_ordered _ _ _ _ hordQ hordE,
    bdd_wmc_correct _ (apply_ordered _ _ _ _ hordQ hordE) _ prog.probs_le_one, ?_⟩
  intro a
  rw [apply_eval]
  simp [hiffQ a, hiffE a]

/-- Exact, non-rounded `?prob` value on the normalized source surface. -/
noncomputable def ProbMeTTaSourceProgram.probExact
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) : ENNReal :=
  bdd_wmc (prog.probQueryBDD s q) prog.probWmcEnv

theorem ProbMeTTaSourceProgram.probExact_eq_weightedSat_query
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) :
    prog.probExact s q =
      weightedSat
        (fun a => by
          classical
          exact decide (queryHoldsNormalA prog.toNormalProbLogProgram s q a))
        prog.probWmcEnv := by
  classical
  have hspec := prog.probQueryBDD_spec s q
  rcases hspec with ⟨_, hwmc, hiff⟩
  unfold ProbMeTTaSourceProgram.probExact
  rw [hwmc]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hq : queryHoldsNormalA prog.toNormalProbLogProgram s q a
  · simp [hiff a, hq]
  · simp [hiff a, hq]

/-- Exact, non-rounded `?prob-given` value computed from the explicit source
operators `?prob-bdd`, `?prob-bdd-ev`, and `apply-bdd bdd-and`. -/
noncomputable def ProbMeTTaSourceProgram.probGivenViaOperatorsExact
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) : ENNReal :=
  let fQE := prog.probQueryEvidenceBDD s q evidence
  let fE := prog.probEvidenceBDD s evidence
  bdd_wmc fQE prog.probWmcEnv / bdd_wmc fE prog.probWmcEnv

theorem ProbMeTTaSourceProgram.probGivenViaOperatorsExact_eq_weightedSat_ratio
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    let fQE := prog.probQueryEvidenceBDD s q evidence
    let fE := prog.probEvidenceBDD s evidence
    prog.probGivenViaOperatorsExact s q evidence =
      weightedSat fQE.eval prog.probWmcEnv /
        weightedSat fE.eval prog.probWmcEnv := by
  classical
  rcases prog.probQueryEvidenceBDD_spec s q evidence with ⟨_hordQE, hwmcQE, _⟩
  rcases prog.probEvidenceBDD_spec s evidence with ⟨_hordE, hwmcE, _⟩
  unfold ProbMeTTaSourceProgram.probGivenViaOperatorsExact
  simp [hwmcQE, hwmcE]

/-- Evidence positivity for the exact source-level `?prob-given` semantics. -/
def ProbMeTTaSourceProgram.EvidencePositive
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (goalsE : List (GoalLit σ)) : Prop :=
  ∃ a : Fin n → Bool,
    (∀ g ∈ goalsE, GoalLit.holdsNormal prog.toNormalProbLogProgram s a g) ∧
    assignmentWeight prog.probWmcEnv a ≠ 0

/-- Exact, non-rounded BDD witnesses for `?prob-given`. -/
noncomputable def ProbMeTTaSourceProgram.probGivenBDDs
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (hEpos : prog.EvidencePositive s goalsE) :
    BDD n × BDD n :=
  let h :=
    normal_conditional_probability
      prog.toNormalProbLogProgram s goalsQ goalsE prog.probWmcEnv prog.probs_le_one hEpos
  let fQE := Classical.choose h
  let h' := Classical.choose_spec h
  let fE := Classical.choose h'
  (fQE, fE)

theorem ProbMeTTaSourceProgram.probGivenBDDs_spec
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (hEpos : prog.EvidencePositive s goalsE) :
    let fs := prog.probGivenBDDs s goalsQ goalsE hEpos
    fs.1.Ordered none ∧ fs.2.Ordered none ∧
      bdd_wmc fs.2 prog.probWmcEnv ≠ 0 ∧
      bdd_wmc fs.1 prog.probWmcEnv / bdd_wmc fs.2 prog.probWmcEnv =
        weightedSat fs.1.eval prog.probWmcEnv /
          weightedSat fs.2.eval prog.probWmcEnv ∧
      (∀ a, fs.1.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          GoalLit.holdsNormal prog.toNormalProbLogProgram s a g) ∧
      (∀ a, fs.2.eval a = true ↔
        ∀ g ∈ goalsE,
          GoalLit.holdsNormal prog.toNormalProbLogProgram s a g) := by
  classical
  unfold ProbMeTTaSourceProgram.probGivenBDDs
  let h :=
    normal_conditional_probability
      prog.toNormalProbLogProgram s goalsQ goalsE prog.probWmcEnv prog.probs_le_one hEpos
  let fQE := Classical.choose h
  let h' := Classical.choose_spec h
  let fE := Classical.choose h'
  have hs : fQE.Ordered none ∧
      fE.Ordered none ∧
      bdd_wmc fE prog.probWmcEnv ≠ 0 ∧
      bdd_wmc fQE prog.probWmcEnv / bdd_wmc fE prog.probWmcEnv =
        weightedSat fQE.eval prog.probWmcEnv /
          weightedSat fE.eval prog.probWmcEnv ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          GoalLit.holdsNormal prog.toNormalProbLogProgram s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          GoalLit.holdsNormal prog.toNormalProbLogProgram s a g) := by
    exact Classical.choose_spec h'
  simpa [h, fQE, h', fE] using hs

/-- Exact, non-rounded `?prob-given` value on the normalized source surface. -/
noncomputable def ProbMeTTaSourceProgram.probGivenExact
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (hEpos : prog.EvidencePositive s goalsE) : ENNReal :=
  let fs := prog.probGivenBDDs s goalsQ goalsE hEpos
  bdd_wmc fs.1 prog.probWmcEnv / bdd_wmc fs.2 prog.probWmcEnv

theorem ProbMeTTaSourceProgram.probGivenExact_eq_weightedSat_ratio
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (hEpos : prog.EvidencePositive s goalsE) :
    let fs := prog.probGivenBDDs s goalsQ goalsE hEpos
    prog.probGivenExact s goalsQ goalsE hEpos =
      weightedSat fs.1.eval prog.probWmcEnv /
        weightedSat fs.2.eval prog.probWmcEnv := by
  classical
  unfold ProbMeTTaSourceProgram.probGivenExact
  simpa using (prog.probGivenBDDs_spec s goalsQ goalsE hEpos).2.2.2.1

/-- Rule heads available to the nonground fallback branch of `?prob` /
`?prob-given`: probabilistic facts contribute `pf` rules, and normal rules
contribute their explicit heads. -/
def ProbMeTTaSourceProgram.ruleHeads {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) : List (GroundAtom σ) :=
  List.ofFn prog.probFacts ++ prog.normalRules.map NormalClause.head

/-- A normalized witness for the nonground source fallback:
`(match &self (rule $goal $_) $goal)`. -/
abbrev ProbMeTTaSourceProgram.HeadWitness {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) := { q : GroundAtom σ // q ∈ prog.ruleHeads }

theorem ProbMeTTaSourceProgram.probFact_mem_ruleHeads
    {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) (i : Fin n) :
    prog.probFacts i ∈ prog.ruleHeads := by
  unfold ProbMeTTaSourceProgram.ruleHeads
  apply List.mem_append.mpr
  left
  rw [List.mem_ofFn', Set.mem_range]
  exact ⟨i, rfl⟩

theorem ProbMeTTaSourceProgram.normalRuleHead_mem_ruleHeads
    {σ : LPSignature} {n : ℕ}
    (prog : ProbMeTTaSourceProgram σ n) (c : NormalClause σ)
    (hc : c ∈ prog.normalRules) :
    c.head ∈ prog.ruleHeads := by
  unfold ProbMeTTaSourceProgram.ruleHeads
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨c, hc, rfl⟩

/-- Normalized nonground fallback for `?prob`: once `match &self` has selected
a concrete rule head witness, recursion continues on that head. -/
noncomputable def ProbMeTTaSourceProgram.probExactMatchedHead
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : prog.HeadWitness) : ENNReal :=
  prog.probExact s q.1

@[simp] theorem ProbMeTTaSourceProgram.probExactMatchedHead_eq
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : prog.HeadWitness) :
    prog.probExactMatchedHead s q = prog.probExact s q.1 := rfl

/-- Normalized nonground fallback for `?prob-given`: after `match &self` picks a
concrete head witness, evaluation continues with the explicit source operators. -/
noncomputable def ProbMeTTaSourceProgram.probGivenViaOperatorsMatchedHead
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : prog.HeadWitness) (evidence : List (GroundAtom σ)) : ENNReal :=
  prog.probGivenViaOperatorsExact s q.1 evidence

@[simp] theorem ProbMeTTaSourceProgram.probGivenViaOperatorsMatchedHead_eq
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : prog.HeadWitness) (evidence : List (GroundAtom σ)) :
    prog.probGivenViaOperatorsMatchedHead s q evidence =
      prog.probGivenViaOperatorsExact s q.1 evidence := rfl

/-- The source-level `::adr` payload: a weighted ground annotated disjunction
with a positive ground body. -/
def probADR {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    WeightedAnnotatedDisjunction σ where
  heads := alts.map Prod.snd
  probs := fun i => (alts.get (i.cast (by simp))).1
  body := body

/-- `(::=> p head body)` normalized as a singleton-head AD. -/
def probColonImpliesSingle {σ : LPSignature}
    (p : ENNReal) (head : GroundAtom σ)
    (body : ProbMeTTaPositiveBody σ) :
    WeightedAnnotatedDisjunction σ :=
  probADR [(p, head)] body

/-- `(::=> heads body)` normalized as a weighted ground AD with positive body. -/
def probColonImpliesMany {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    WeightedAnnotatedDisjunction σ :=
  probADR alts body

/-- The `::adr` source builder forgets probabilities exactly by
`toAnnotatedDisjunction`. -/
@[simp] theorem probADR_toAnnotatedDisjunction {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ) :
    (probADR alts body).toAnnotatedDisjunction =
      { heads := alts.map Prod.snd, body := body } := by
  rfl

/-- Expanded normal rules generated by the normalized source-level `::adr`
builder. -/
def probADRRules {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ) :
    List (NormalClause σ) :=
  expandAD (probADR alts body).toAnnotatedDisjunction auxAtoms

@[simp] theorem probADRRules_eq_expandAD {σ : LPSignature}
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ) :
    probADRRules alts body auxAtoms =
      expandAD (probADR alts body).toAnnotatedDisjunction auxAtoms := rfl

/-- The normalized source-level `::adr` builder plugs directly into the
existing AD-to-WMC bridge. -/
theorem probADR_wmc_correct {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (base : ProbMeTTaSourceProgram σ n)
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ)
    (s : Stratification σ)
    (goals : List (GoalLit σ)) :
    ∃ f : BDD n, f.Ordered none ∧
      bdd_wmc f base.probWmcEnv = weightedSat f.eval base.probWmcEnv ∧
      (∀ a, f.eval a = true ↔
        ∀ g ∈ goals,
          GoalLit.holdsNormal
            ({ toProbLogProgram := base.toProbLogBase
               normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
              NormalProbLogProgram σ n) s a g) := by
  simpa [ProbMeTTaSourceProgram.probWmcEnv, probADRRules] using
    ad_program_wmc_correct base.toProbLogBase
      (base.normalRules ++ expandAD (probADR alts body).toAnnotatedDisjunction auxAtoms)
      s goals base.probWmcEnv base.probs_le_one

/-- The normalized source-level `::adr` / `::=>` builders also plug directly
into the existing conditioning bridge. -/
theorem probADR_conditioning_correct {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (base : ProbMeTTaSourceProgram σ n)
    (alts : List (ENNReal × GroundAtom σ))
    (body : ProbMeTTaPositiveBody σ)
    (auxAtoms : Fin ((alts.map Prod.snd).length) → GroundAtom σ)
    (s : Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE,
        GoalLit.holdsNormal
          ({ toProbLogProgram := base.toProbLogBase
             normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
            NormalProbLogProgram σ n) s a g) ∧
      assignmentWeight base.probWmcEnv a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE base.probWmcEnv ≠ 0 ∧
      bdd_wmc fQE base.probWmcEnv / bdd_wmc fE base.probWmcEnv =
        weightedSat fQE.eval base.probWmcEnv /
          weightedSat fE.eval base.probWmcEnv ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE,
          GoalLit.holdsNormal
            ({ toProbLogProgram := base.toProbLogBase
               normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
              NormalProbLogProgram σ n) s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE,
          GoalLit.holdsNormal
            ({ toProbLogProgram := base.toProbLogBase
               normalRules := base.normalRules ++ probADRRules alts body auxAtoms } :
              NormalProbLogProgram σ n) s a g) := by
  simpa [ProbMeTTaSourceProgram.probWmcEnv, probADRRules] using
    ad_program_conditioning_correct base.toProbLogBase
      (base.normalRules ++ expandAD (probADR alts body).toAnnotatedDisjunction auxAtoms)
      s goalsQ goalsE base.probWmcEnv base.probs_le_one hEpos

end Mettapedia.Logic.BDDCore
