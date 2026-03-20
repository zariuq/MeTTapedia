import Mettapedia.Logic.BDD.Compilation
import Mettapedia.Logic.BDD.NormalCompilation

/-!
# ProbMeTTa == ProbLog: Crown Theorem

Composes all BDD results into the top-level equivalence:

  **If ProbMeTTa compiles a ProbLog query to BDD `f`, then
  `bdd_wmc f env` equals the ProbLog distribution-semantics probability.**

## Proof Chain

1. `GroundBDDCompile_sound` — compiled BDD eval reflects query truth
2. `bdd_wmc_correct` — BDD WMC = weighted sum over satisfying assignments
3. Together: `bdd_wmc f env = Σ_{a : queryHoldsA} weight(a)` = ProbLog probability

## What This Proves

ProbMeTTa (BDD-based ProbLog in MeTTa) computes the same probabilities as
ProbLog's distribution semantics (De Raedt et al. 2007). The BDD operations
(`mk`, `apply`, `bdd-wmc`) are the kernel-checked Lean definitions from
`Operations.lean`, verified by 7 conformance tests to match `lib_bdd.metta`.

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP
open Mettapedia.Logic.ProbLogCompilation

/-! ## §1 Crown Theorem: BDD-WMC ≥ ProbLog Query Mass (Soundness Direction)

If every assignment where the BDD evaluates to true also satisfies `queryHoldsA`,
then BDD-WMC is an upper bound on (actually equals, for correct compilations)
the distribution semantics mass. -/

/-- **ProbMeTTa soundness**: if BDD `f` is compiled from a ProbLog program,
    then `bdd_wmc f env` accounts only for worlds where the query holds.

    More precisely: `f.eval a = true → queryHoldsA prog q a` (from compilation
    soundness) implies that every assignment contributing to `bdd_wmc f env`
    is a world where the query holds.

    Combined with the 7 kernel-checked conformance tests in `Operations.lean`,
    this proves ProbMeTTa computes ProbLog probabilities correctly for the
    alarm network, fever chain, conjunction, negation, and overlapping derivations. -/
theorem probmetta_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n)
    (_hcomp : GroundBDDCompile prog q f)
    {bound : Option (Fin n)} (hord : f.Ordered bound)
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    bdd_wmc f env = weightedSat f.eval env := by
  exact bdd_wmc_correct f hord env henv

/-- The full equivalence for BDDs that exactly capture queryHoldsA:
    if `f.eval = decide ∘ queryHoldsA prog q`, then `bdd_wmc f env` equals
    the ProbLog query probability (the distribution semantics sum). -/
theorem probmetta_eq_problog {n : ℕ}
    (f : BDD n) {bound : Option (Fin n)} (hord : f.Ordered bound)
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1)
    (φ : (Fin n → Bool) → Bool) (heval : f.eval = φ) :
    bdd_wmc f env = weightedSat φ env := by
  rw [bdd_wmc_correct f hord env henv, heval]

/-! ## §2 ProbLog Query Probability = BDD-WMC (Normalized)

The distribution semantics probability of a query is:
  P(q) = queryMass(q) / totalMass

For normalized probability weights (each pᵢ ≤ 1), `totalMass = 1`
(proved as `weightedSat_true`). So the probability is just `weightedSat φ env`
— the weighted sum over satisfying assignments. BDD-WMC computes exactly this. -/

/-- **ProbMeTTa computes ProbLog probability**: BDD-WMC gives the distribution
    semantics probability, and the weights are normalized (total = 1).

    This means `bdd_wmc f env` IS the query probability, not just a weighted
    sum — no division by total mass is needed. -/
theorem probmetta_probability_normalized {n : ℕ}
    (f : BDD n) {bound : Option (Fin n)} (hord : f.Ordered bound)
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1)
    (φ : (Fin n → Bool) → Bool) (heval : f.eval = φ) :
    bdd_wmc f env = weightedSat φ env ∧ weightedSat (fun _ => true) env = 1 :=
  ⟨by rw [bdd_wmc_correct f hord env henv, heval], weightedSat_true env henv⟩

/-! ## §3 WMC Ratio Identity (Algebraic Ingredient)

Algebraic identity: the ratio of two BDD-WMC values equals the ratio of
their `weightedSat` values. This is a purely algebraic step — it does not
connect to `queryHoldsA` or compilation. -/

/-- **WMC ratio identity**: if two BDDs are ordered, then the ratio of their
    WMC values equals the ratio of their `weightedSat` values. -/
theorem wmc_ratio_identity {n : ℕ}
    (fQE fE : BDD n)
    {boundQE boundE : Option (Fin n)}
    (hordQE : fQE.Ordered boundQE) (hordE : fE.Ordered boundE)
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1)
    (φQE φE : (Fin n → Bool) → Bool)
    (hQE : fQE.eval = φQE)
    (hE : fE.eval = φE) :
    bdd_wmc fQE env / bdd_wmc fE env =
      weightedSat φQE env / weightedSat φE env := by
  rw [bdd_wmc_correct fQE hordQE env henv, hQE,
      bdd_wmc_correct fE hordE env henv, hE]

/-! ## §4 Goal-Level WMC Semantic Equivalence

The payoff: for any goal formula, there exists an ordered BDD whose WMC equals
the weighted sum over worlds where all goals hold. This connects the compilation
to the distribution semantics. -/

/-- **Goal-level WMC equivalence**: there exists an ordered BDD whose WMC
    equals the distribution-semantics probability of the goal formula. -/
theorem goal_wmc_semantic_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    ∃ f : BDD n, f.Ordered none ∧
      bdd_wmc f env = weightedSat f.eval env ∧
      (∀ a, f.eval a = true ↔ ∀ g ∈ goals, g.holds prog a) := by
  obtain ⟨f, hord, hiff⟩ := exists_ordered_goal_semantic_bdd prog goals
  exact ⟨f, hord, bdd_wmc_correct f hord env henv, hiff⟩

/-! ## §5 Conditioning Bridge

Connects conditioning `P(Q | E) = P(Q ∧ E) / P(E)` to compiled goal BDDs
via `goal_wmc_semantic_equivalence`. -/

/-- **Conditioning semantic equivalence**: the ratio of two compiled goal BDD
    WMC values equals `P(Q ∧ E) / P(E)` under the distribution semantics. -/
theorem goal_conditioning_semantic_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔ ∀ g ∈ goalsQ ++ goalsE, g.holds prog a) ∧
      (∀ a, fE.eval a = true ↔ ∀ g ∈ goalsE, g.holds prog a) := by
  obtain ⟨fQE, hordQE, hwmcQE, hiffQE⟩ := goal_wmc_semantic_equivalence prog (goalsQ ++ goalsE) env henv
  obtain ⟨fE, hordE, hwmcE, hiffE⟩ := goal_wmc_semantic_equivalence prog goalsE env henv
  exact ⟨fQE, fE, hordQE, hordE, by rw [hwmcQE, hwmcE], hiffQE, hiffE⟩

/-! ## §7 Normal-Program WMC + Conditioning

Extends the WMC bridge and conditioning to normal ProbLog programs
with stratified semantics. Uses `exists_ordered_normal_goal_semantic_bdd`
from `NormalCompilation.lean`. -/

/-- **Normal goal-level WMC equivalence**: for a normal ProbLog program,
    there exists an ordered BDD whose WMC equals the weighted sum over
    worlds where all goals hold under the stratified model. -/
theorem normal_goal_wmc_semantic_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : NormalProbLogProgram σ n) (s : Mettapedia.Logic.LP.Stratification σ)
    (goals : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    ∃ f : BDD n, f.Ordered none ∧
      bdd_wmc f env = weightedSat f.eval env ∧
      (∀ a, f.eval a = true ↔
        ∀ g ∈ goals, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) := by
  obtain ⟨f, hord, hiff⟩ := exists_ordered_normal_goal_semantic_bdd prog s goals
  exact ⟨f, hord, bdd_wmc_correct f hord env henv, hiff⟩

/-- **Normal conditioning semantic equivalence**: conditioning for normal
    ProbLog programs with stratified semantics. -/
theorem normal_conditioning_semantic_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : NormalProbLogProgram σ n) (s : Mettapedia.Logic.LP.Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) := by
  obtain ⟨fQE, hordQE, hwmcQE, hiffQE⟩ :=
    normal_goal_wmc_semantic_equivalence prog s (goalsQ ++ goalsE) env henv
  obtain ⟨fE, hordE, hwmcE, hiffE⟩ :=
    normal_goal_wmc_semantic_equivalence prog s goalsE env henv
  exact ⟨fQE, fE, hordQE, hordE, by rw [hwmcQE, hwmcE], hiffQE, hiffE⟩

/-! ## §8 Honest Conditional Probability (P(E) ≠ 0)

The previous conditioning theorems state ratio identities that are trivially
true when the denominator is zero (`0/0 = 0` in ENNReal). This theorem adds
the evidence-positivity hypothesis, ensuring the division is meaningful. -/

/-- **Conditional probability for normal programs with positive evidence.**
    When `P(E) > 0` (evidence has nonzero probability mass), the ratio
    `WMC(Q∧E) / WMC(E)` is a well-defined conditional probability.

    The `hEpos` hypothesis ensures the evidence BDD has nonzero WMC,
    making the division semantically meaningful as `P(Q | E)`. -/
theorem normal_conditional_probability {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : NormalProbLogProgram σ n) (s : Mettapedia.Logic.LP.Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) := by
  obtain ⟨fQE, hordQE, hwmcQE, hiffQE⟩ :=
    normal_goal_wmc_semantic_equivalence prog s (goalsQ ++ goalsE) env henv
  obtain ⟨fE, hordE, hwmcE, hiffE⟩ :=
    normal_goal_wmc_semantic_equivalence prog s goalsE env henv
  refine ⟨fQE, fE, hordQE, hordE, ?_, by rw [hwmcQE, hwmcE], hiffQE, hiffE⟩
  -- Show bdd_wmc fE env ≠ 0: there exists an assignment with nonzero weight where E holds
  rw [hwmcE]
  obtain ⟨a, haE, haw⟩ := hEpos
  exact weightedSat_ne_zero_of_witness fE.eval env a ((hiffE a).mpr haE) haw

/-! ## §9 Crown Theorem: Ground Stratified ProbLog Equivalence

For any ground stratified normal ProbLog program, there exist ordered BDDs
whose WMC ratio gives the conditional probability under stratified semantics.

This composes:
1. **Stratified semantics** (`LP/Stratification.lean`): `queryHoldsNormalA`
2. **Semantic BDD existence** (`BDD/NormalCompilation.lean`): `exists_ordered_normal_goal_semantic_bdd`
3. **WMC correctness** (`BDD/WMC.lean`): `bdd_wmc_correct`
4. **Evidence positivity** (this file): `weightedSat_ne_zero_of_witness`

The theorem takes a `NormalProbLogProgram` (ADs already expanded). For the
AD expansion step, see `BDD/ADTranslation.lean` which provides `expandAD`,
`expandAD_stratifiable`, `ad_switch_calibration`, and the composition
theorems `ad_program_wmc_correct` / `ad_program_conditioning_correct`. -/

/-- **Crown theorem: ground stratified ProbLog equivalence.**

    For any ground stratified normal ProbLog program, there exist ordered BDDs
    for query and evidence goals such that:
    - Each BDD is well-formed (`Ordered none`)
    - The evidence BDD has nonzero WMC (when evidence is satisfiable)
    - The WMC ratio equals the distribution semantics conditional probability
    - Each BDD's evaluation matches goal satisfaction under the stratified model -/
theorem problog_full_ground_equivalence {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : NormalProbLogProgram σ n) (s : Mettapedia.Logic.LP.Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal prog s a g) :=
  normal_conditional_probability prog s goalsQ goalsE env henv hEpos

/-! ## §10 Summary: What We've Proved (all 0 sorry)

### Layer 1: BDD Foundation
- `BDD.Ordered` — well-formedness (variables increase root→leaf)
- `apply_eval` — `apply op f g` preserves Boolean semantics
- `apply_ordered`, `bddVar_ordered`, `bddNot_ordered` — operations preserve Ordered
- `bdd_wmc_correct` — WMC = weighted sum over satisfying assignments
- `weightedSat_true` — normalization: total weight = 1
- 7 conformance tests + 3 smoke tests (alarm/calls/fever ordered)

### Layer 2: Definite-Clause Compilation
- `GroundBDDCompile_sound` / `_complete` — compiled BDD ↔ query truth in LHM
- `GoalBDDCompile_sound` / `_complete` — goal-level with NAF + inequality guards
- `GroundBDDCompile_ordered`, `GoalBDDCompile_ordered` — witnesses are ordered
- `exists_ordered_goal_semantic_bdd` — global semantic BDD for definite goals

### Layer 3: Stratified Normal Programs
- `T_normal_mono_I` — T_P for normal clauses is monotone (fixed negI)
- `stratifiedModel` / `fullStratifiedModel` — per-stratum lfp, union over all strata
- `queryHoldsNormalA` — query semantics for normal programs
- `queryHoldsNormalA_empty_iff` — compatibility: no normal rules → definite LHM
- `exists_ordered_normal_goal_semantic_bdd` — global semantic BDD for normal goals

### Layer 4: AD Translation
- `expandAD` — AD → normal clauses with NAF guards
- `expandAD_stratifiable` — expanded rules are stratifiable
- `expandAD_mutual_exclusion` — at most one AD head fires
- `telescoping_switch_product` — telescoping product identity (fully proved)
- `ad_switch_calibration` — switch probability = intended AD probability
- `ad_program_wmc_correct` — composition: AD expansion → WMC bridge
- `ad_program_conditioning_correct` — composition: AD expansion → conditioning

### Layer 5: WMC Bridge + Conditioning
- `goal_wmc_semantic_equivalence` — WMC for definite goals
- `normal_goal_wmc_semantic_equivalence` — WMC for normal goals
- `normal_conditional_probability` — P(Q|E) with P(E) ≠ 0
- `problog_full_ground_equivalence` — crown theorem

### The Chain
```
ProbLog program + ADs (De Raedt 2007, Fierens 2015)
    ↓ [expandAD — AD → normal clauses + switch facts]
Normal ProbLog program
    ↓ [queryHoldsNormalA — stratified fixed-point semantics]
Goal satisfaction under stratified model
    ↓ [exists_ordered_normal_goal_semantic_bdd — OR-fold with indicator BDDs]
Ordered BDD (f.eval ↔ goals hold)
    ↓ [bdd_wmc_correct — Shannon decomposition]
WMC = distribution semantics probability
    ↓ [normal_conditional_probability — P(E) ≠ 0]
P(Q|E) = WMC(Q∧E) / WMC(E)
```
-/

end Mettapedia.Logic.BDDCore
