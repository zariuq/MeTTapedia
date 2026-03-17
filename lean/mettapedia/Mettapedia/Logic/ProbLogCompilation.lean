/-
LLM Context:
- T_P_K_LP at ℝ≥0∞ ≠ distribution semantics (bag vs set semantics)
- Correct architecture: total-choice → residual KB → least Herbrand model → queryHolds
- For function-free signatures: g.groundAtom ga.toAtom = ga (ground atoms are invariant)
- leastHerbrandModel_least: pre-fixpoint ⊇ least model
- T_P_LP_le_iff: I is pre-fixpoint ↔ contains EDB + closed under rules
- worldToAssignment is in Mettapedia.Logic.CompletePLN
-/
import Mettapedia.Logic.ProbLogDistributionSemantics
import Mettapedia.Logic.PLNBioHypothesisGeneration
import Mettapedia.Logic.LP.Core
import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.Logic.LP.FunctionFreeEvaluation
import Mettapedia.Logic.LP.Provenance
import Provenance.Semirings.Which

/-!
# ProbLog Syntactic Compilation to WM-PLN

This module formalizes the **syntactic compilation** from ProbLog programs to WM-PLN
objects, proving that the compilation preserves distribution-semantics probabilities.

## Architecture

A ProbLog program has:
- `n` independent probabilistic facts with probabilities `p_i`
- Definite clauses (rules) that derive atoms from facts

For each "total choice" (world `w : Fin (2^n)`), the chosen facts form a residual
knowledge base. The query holds in world `w` iff it is in the least Herbrand model
of the residual KB. The query probability is the weighted sum over worlds.

## Important: T_P_K_LP at ℝ≥0∞ ≠ Distribution Semantics

The provenance operator `T_P_K_LP` at `K = ℝ≥0∞` computes **bag semantics**
(sum-of-products), not distribution semantics (set semantics). For programs with
overlapping derivations (e.g., `q :- f_1. q :- f_2.`), bag semantics gives
`p_1 + p_2` while distribution semantics gives `1 - (1-p_1)(1-p_2)`.

The correct compilation routes through total-choice → residual model → `queryProb`.

## Scope

This module covers the **finite ground, definite (no negation), OR-pattern** fragment:
programs where each rule derives a single query atom from a single probabilistic fact.
This covers the rejuve-bio benchmark and a large class of practical ProbLog programs.

**Not covered**: recursion, negation-as-failure, overlapping non-OR derivations,
knowledge compilation (BDD/SDD), the provenance polynomial approach.

## References

- De Raedt, Kimmig, Toivonen, "ProbLog: A Probabilistic Prolog", IJCAI 2007
- Green, Karvounarakis, Tannen, "Provenance Semirings", PODS 2007
-/

namespace Mettapedia.Logic.ProbLogCompilation

open scoped ENNReal
open Mettapedia.Logic.LP
open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.ProbLogDistributionSemantics
open Mettapedia.Logic.PLNBioHypothesisGeneration
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.PLNNoisyOr
open Which

/-! ## §1 Ground Atom Invariance (Function-Free)

For function-free signatures, ground atoms are invariant under grounding:
applying any grounding to a ground atom (lifted to `Atom`) returns the same atom. -/

/-- In a function-free signature, grounding a ground term lifted to `Term` recovers
    the original ground term. -/
theorem Grounding.groundTerm_toTerm_self {σ : LPSignature} [IsEmpty σ.functionSymbols]
    (g : Grounding σ) (gt : GroundTerm σ) : g.groundTerm gt.toTerm = gt :=
  @GroundTerm.casesOn σ (fun gt => g.groundTerm gt.toTerm = gt) gt
    (fun _ => rfl)
    (fun f _ => (IsEmpty.false f).elim)

/-- In a function-free signature, grounding a ground atom (lifted to `Atom`) recovers
    the original ground atom. -/
theorem Grounding.groundAtom_toAtom_self {σ : LPSignature} [IsEmpty σ.functionSymbols]
    (g : Grounding σ) (ga : GroundAtom σ) : g.groundAtom ga.toAtom = ga := by
  cases ga
  simp [Grounding.groundAtom, GroundAtom.toAtom, Grounding.groundTerm_toTerm_self]

/-! ## §2 ProbLog Program Syntax -/

/-- A ProbLog program with `n` independent probabilistic facts over LP signature `σ`.

    - `probFacts`: the `n` ground atoms that serve as probabilistic facts
    - `probs`: their probabilities (values in ℝ≥0∞)
    - `rules`: definite clauses (no negation, no probability annotations)
    - `facts_injective`: the probabilistic facts are distinct atoms -/
structure ProbLogProgram (σ : LPSignature) (n : ℕ) where
  probFacts      : Fin n → GroundAtom σ
  probs          : ProbAssignment n
  rules          : Program σ
  facts_injective : Function.Injective probFacts

/-! ## §3 Total-Choice Semantics

For each world `w : Fin (2^n)`, the "total choice" selects which probabilistic facts
are true. The residual knowledge base has the chosen facts as EDB and the original
rules as the intensional program. -/

/-- The residual EDB for world `w`: the set of probabilistic facts chosen true. -/
def residualDB {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (w : Fin (2 ^ n)) : Set (GroundAtom σ) :=
  { a | ∃ i : Fin n, worldToAssignment n w i = true ∧ prog.probFacts i = a }

/-- The residual knowledge base for world `w`. -/
def residualKB {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (w : Fin (2 ^ n)) : KnowledgeBase σ where
  prog := prog.rules
  db := residualDB prog w

/-- A query atom holds in world `w` iff it is in the least Herbrand model of
    the residual knowledge base. -/
def queryHolds {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (q : GroundAtom σ) (w : Fin (2 ^ n)) : Prop :=
  q ∈ leastHerbrandModel (residualKB prog w)

/-! ## §4 OR-Pattern Programs

An OR-pattern program has rules of the form `q :- f_i` for each probabilistic fact `f_i`,
deriving a single query atom `q` from individual facts. This covers the rejuve-bio
gene–SNP relevance model:
```
  relevant_gene :- regulatory_effect.
  relevant_gene :- eqtl_association.
  relevant_gene :- activity_by_contact.
``` -/

/-- An OR-pattern ProbLog program: all rules derive query `q` from a single fact. -/
structure IsORPattern {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) : Prop where
  /-- Each probabilistic fact has a rule deriving `q`. -/
  has_rule : ∀ i : Fin n, (⟨q.toAtom, [(prog.probFacts i).toAtom]⟩ : Clause σ) ∈ prog.rules
  /-- Every rule is of this form. -/
  only_rules : ∀ c ∈ prog.rules,
    ∃ i : Fin n, c = ⟨q.toAtom, [(prog.probFacts i).toAtom]⟩
  /-- `q` is not a probabilistic fact. -/
  q_not_fact : ∀ i : Fin n, prog.probFacts i ≠ q

/-! ## §5 OR-Pattern Structural Theorem

The key theorem: for OR-pattern programs, `queryHolds prog q w` iff some fact is
chosen in world `w`. -/

/-- Forward direction: if fact `i` is chosen, `q` holds. -/
theorem queryHolds_or_forward {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (w : Fin (2 ^ n)) (i : Fin n) (hi : worldToAssignment n w i = true) :
    queryHolds prog q w := by
  -- probFacts i is in the residual EDB
  have hmem : prog.probFacts i ∈ (residualKB prog w).db :=
    ⟨i, hi, rfl⟩
  -- Use any grounding; ground atoms are invariant under it (function-free)
  let g : Grounding σ := fun _ => Classical.arbitrary (GroundTerm σ)
  have hhead : g.groundAtom q.toAtom = q := Grounding.groundAtom_toAtom_self g q
  have hbody_eq : g.groundAtom (prog.probFacts i).toAtom = prog.probFacts i :=
    Grounding.groundAtom_toAtom_self g (prog.probFacts i)
  -- The body atom is in the EDB, hence in the least Herbrand model
  have hbody_model : g.groundAtom (prog.probFacts i).toAtom ∈
      leastHerbrandModel (residualKB prog w) := by
    rw [hbody_eq]; exact leastHerbrandModel_db _ _ hmem
  -- Apply the clause rule
  have := leastHerbrandModel_clause (residualKB prog w)
    ⟨q.toAtom, [(prog.probFacts i).toAtom]⟩ (hor.has_rule i) g
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rw [hb]; exact hbody_model)
  rw [hhead] at this
  exact this

/-- Backward direction: if `q` holds, some fact must be chosen.
    Uses the pre-fixpoint technique: construct a set S ⊇ leastHerbrandModel that
    only contains `q` when some fact is chosen. -/
theorem queryHolds_or_backward {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    [IsEmpty σ.functionSymbols]
    (w : Fin (2 ^ n)) (hq : queryHolds prog q w) :
    ∃ i : Fin n, worldToAssignment n w i = true := by
  -- Define the candidate pre-fixpoint:
  -- S = residualDB ∪ { a | a = q ∧ ∃ i, worldToAssignment w i = true }
  let S : Set (GroundAtom σ) :=
    residualDB prog w ∪ { a | a = q ∧ ∃ i : Fin n, worldToAssignment n w i = true }
  -- Show S is a pre-fixpoint (model) of the residual KB
  have hS : T_P_LP (residualKB prog w) S ⊆ S := by
    rw [T_P_LP_le_iff]
    constructor
    · -- EDB ⊆ S
      exact Set.subset_union_left
    · -- Closed under rules
      intro c g hc hbody
      -- By only_rules, c = ⟨q.toAtom, [(probFacts j).toAtom]⟩ for some j
      obtain ⟨j, hcj⟩ := hor.only_rules c hc
      subst hcj
      -- The grounded head is q (since function-free)
      have hhead : g.groundAtom q.toAtom = q := Grounding.groundAtom_toAtom_self g q
      rw [hhead]
      -- The body atom (probFacts j) is in S
      have hbj := hbody ((prog.probFacts j).toAtom) (List.mem_cons_self ..)
      have hbj_eq : g.groundAtom (prog.probFacts j).toAtom = prog.probFacts j :=
        Grounding.groundAtom_toAtom_self g (prog.probFacts j)
      rw [hbj_eq] at hbj
      -- probFacts j ∈ S: either in residualDB or in {a | a = q ∧ ...}
      rcases hbj with hdb | ⟨heq, _⟩
      · -- Case 1: probFacts j ∈ residualDB → some fact is chosen
        obtain ⟨k, hk, _⟩ := hdb
        exact Set.mem_union_right _ ⟨rfl, k, hk⟩
      · -- Case 2: probFacts j = q → contradicts q_not_fact
        exact absurd heq (hor.q_not_fact j)
  -- leastHerbrandModel ⊆ S
  have hle := leastHerbrandModel_least (residualKB prog w) S hS
  -- q ∈ leastHerbrandModel, so q ∈ S
  have hqS := hle hq
  -- q is not in residualDB (q is not a probabilistic fact)
  rcases hqS with hdb | ⟨_, hexists⟩
  · obtain ⟨k, _, hk⟩ := hdb
    exact absurd hk (hor.q_not_fact k)
  · exact hexists

/-- **OR-Pattern Structural Theorem**: For an OR-pattern ProbLog program, query `q`
    holds in world `w` if and only if some probabilistic fact is chosen. -/
theorem queryHolds_or_pattern {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (w : Fin (2 ^ n)) :
    queryHolds prog q w ↔ ∃ i : Fin n, worldToAssignment n w i = true :=
  ⟨queryHolds_or_backward prog q hor w, fun ⟨i, hi⟩ =>
    queryHolds_or_forward prog q hor w i hi⟩

/-! ## §6 Connection to anyTrue and Noisy-OR

The existential `∃ i, worldToAssignment w i = true` is equivalent to
`anyTrue (List.finRange n) w = true`, connecting the LP characterization
to the ProbLog distribution-semantics machinery. -/

/-- `anyTrue (List.finRange n) w = true` iff some fact assignment is true. -/
theorem anyTrue_finRange_iff (n : ℕ) (w : Fin (2 ^ n)) :
    anyTrue (List.finRange n) w = true ↔ ∃ i : Fin n, worldToAssignment n w i = true := by
  simp [anyTrue, List.any_eq_true, List.mem_finRange]

/-- For OR-pattern programs, `queryHolds` holds iff `anyTrue` is true. This is the
    compiled query predicate: the LP-derived query equals the Boolean predicate. -/
theorem queryHolds_iff_anyTrue {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (w : Fin (2 ^ n)) :
    queryHolds prog q w ↔ (anyTrue (List.finRange n) w = true) := by
  rw [anyTrue_finRange_iff]
  exact queryHolds_or_pattern prog q hor w

/-- **Compilation Noisy-OR Theorem**: For an OR-pattern ProbLog program with
    probabilities `p_i ≤ 1`, the distribution-semantics query probability equals
    the noisy-OR formula `1 - Π(1 - p_i)`.

    The query predicate `anyTrue (List.finRange n)` is the **compiled query**:
    by `queryHolds_iff_anyTrue`, it equals `true` in exactly those worlds where
    the LP-derived query `q` holds in the least Herbrand model. -/
theorem compilation_or_noisyOr {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (_ : IsORPattern prog q)
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (hp : ∀ i, prog.probs i ≤ 1) (hn : 0 < 2 ^ n) :
    queryProb prog.probs (anyTrue (List.finRange n)) =
      1 - Finset.univ.prod (fun i : Fin n => 1 - prog.probs i) :=
  queryProb_anyTrue_full prog.probs hp hn

/-- **toReal corollary**: The compiled probability, as a real number, equals
    `noisyOrMulti` of the real-valued probabilities. -/
theorem compilation_or_toReal {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (_ : IsORPattern prog q)
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (hp : ∀ i, prog.probs i ≤ 1) (hn : 0 < 2 ^ n) :
    (queryProb prog.probs (anyTrue (List.finRange n))).toReal =
      noisyOrMulti (List.ofFn (fun i : Fin n => (prog.probs i).toReal)) :=
  queryProb_anyTrue_toReal_eq_noisyOrMulti prog.probs hp hn

/-! ## §7 WM-PLN Strictly Extends the Compiled Fragment

ProbLog's `queryProb` is a pure function of fixed weights. WM-PLN adds:
- **BinaryEvidence revision** via `BinaryEvidence.hplus` (aggregate new observations)
- **Heterogeneous combination** (frequentist + expert + analogical)
- **Higher-order evidence** (evidence about evidence)

We demonstrate the first: for a compiled ProbLog program, adding new evidence
produces a strictly different WM state. -/

/-- WM-PLN extends ProbLog: given a compiled ProbLog state with finite world weights
    and nonzero new evidence, the revised WM state differs from the original.
    This shows ProbLog cannot express evidence revision natively. -/
theorem wm_pln_revision_changes_evidence
    (p : ProbAssignment n) (E_new : JointEvidence n)
    (w₀ : Fin (2 ^ n))
    (hp : probLogToJointEvidence p w₀ ≠ ⊤)
    (hne : E_new w₀ ≠ 0) :
    probLogToJointEvidence p + E_new ≠ probLogToJointEvidence p := by
  intro h
  have h₀ := congr_fun h w₀
  simp only [Pi.add_apply] at h₀
  -- h₀ : p_w₀ + e_w₀ = p_w₀. Rearrange to use WithTop.add_right_cancel.
  have h₁ : E_new w₀ + probLogToJointEvidence p w₀ =
      0 + probLogToJointEvidence p w₀ := by
    rw [add_comm, h₀, zero_add]
  exact hne (WithTop.add_right_cancel hp h₁)

/-! ## §8 Bag vs Set Semantics: Formal Separation

The provenance operator `T_P_K_LP` at `K = ℝ≥0∞` computes **bag semantics** (sum of
probabilities), while distribution semantics computes the **noisy-OR** (set semantics).

For OR-pattern programs:
- Bag semantics: `∑ p_i`
- Set semantics: `1 - ∏ (1 - p_i)`

These are provably different whenever ≥ 2 probabilities are positive.
The relationship is given by **Boole's inequality**: bag ≥ set (always),
with strict inequality when derivations overlap. -/

/-- **Boole's inequality (additive form, Finset version)**: `∑_s p + ∏_s (1-p) ≥ 1`.
    Works for any Finset, enabling decomposition over subsets. -/
theorem sum_add_prod_compl_ge_one_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (hp : ∀ i ∈ s, p i ≤ 1) :
    1 ≤ s.sum p + s.prod (fun i => 1 - p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has]
    set S := s.sum p
    set P := s.prod (fun i => 1 - p i)
    set q := p a
    have hq : q ≤ 1 := hp a (Finset.mem_insert_self a s)
    have hih : 1 ≤ S + P := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
    have hP : P ≤ 1 :=
      Finset.prod_le_one' (fun i _ => tsub_le_self)
    -- Key: q + P*(1-q) ≥ P, so S + q + P*(1-q) ≥ S + P ≥ 1
    have hP_split : P * (1 - q) + P * q = P := by
      rw [← mul_add, tsub_add_cancel_of_le hq, mul_one]
    calc 1 ≤ S + P := hih
      _ = S + (P * (1 - q) + P * q) := by rw [hP_split]
      _ = S + P * (1 - q) + P * q := by rw [add_assoc]
      _ ≤ S + P * (1 - q) + q := by
          gcongr; exact mul_le_of_le_one_left (zero_le _) hP
      _ = q + S + (1 - q) * P := by rw [mul_comm]; ring

/-- Boole's inequality for `Fin n`. -/
theorem sum_add_prod_compl_ge_one {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) :
    1 ≤ Finset.univ.sum p + Finset.univ.prod (fun i => 1 - p i) :=
  sum_add_prod_compl_ge_one_finset Finset.univ p (fun i _ => hp i)

/-- **Boole's inequality (subtraction form)**: `1 - ∏(1-p) ≤ ∑ p`.
    The noisy-OR is at most the sum of probabilities. -/
theorem noisyOr_le_sum {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) :
    1 - Finset.univ.prod (fun i => 1 - p i) ≤ Finset.univ.sum p := by
  rw [tsub_le_iff_right]
  exact sum_add_prod_compl_ge_one p hp

/-- Identity in NNReal: `x + y + (1-x)(1-y) = 1 + xy` when `x, y ≤ 1`. -/
private theorem nnreal_two_sum_prod (x y : NNReal) (hx : x ≤ 1) (hy : y ≤ 1) :
    x + y + (1 - x) * (1 - y) = 1 + x * y := by
  apply NNReal.coe_injective
  push_cast [NNReal.coe_sub hx, NNReal.coe_sub hy]
  ring

/-- Key identity for two probabilities in ENNReal:
    `x + y + (1-x)(1-y) = 1 + xy` when `x, y ≤ 1`. -/
theorem two_sum_prod_eq_one_add_mul {x y : ℝ≥0∞} (hx : x ≤ 1) (hy : y ≤ 1) :
    x + y + (1 - x) * (1 - y) = 1 + x * y := by
  have hx_ne : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx
  have hy_ne : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hy
  lift x to NNReal using hx_ne
  lift y to NNReal using hy_ne
  rw [ENNReal.coe_le_one_iff] at hx hy
  have := nnreal_two_sum_prod x y hx hy
  exact_mod_cast this

/-- **Strict Boole's inequality**: when ≥ 2 probabilities are positive (and ≤ 1),
    the bag sum strictly exceeds the noisy-OR.
    Equivalently: `∑ p + ∏(1-p) > 1`.

    Proof: split Finset.univ into {a,b} and the complement. The sum decomposes as
    `(pa + pb + S') + P · P'` where S' and P' are the complement sum/product.
    By `two_sum_prod_eq`: `pa + pb + P = 1 + pa·pb` where `P = (1-pa)(1-pb)`.
    By Boole on the complement: `S' + P' ≥ 1`, so `S' ≥ 1 - P' ≥ P(1-P')`,
    giving `S' + P·P' ≥ P`. Therefore `∑ p + ∏(1-p) ≥ 1 + pa·pb > 1`. -/
theorem sum_add_prod_compl_gt_one {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) (a b : Fin n) (hab : a ≠ b)
    (ha : 0 < p a) (hb : 0 < p b) :
    1 < Finset.univ.sum p + Finset.univ.prod (fun i => 1 - p i) := by
  -- Decompose into {a,b} and complement
  set ab := ({a, b} : Finset (Fin n))
  set rest := Finset.univ \ ab
  have hdisj : Disjoint ab rest := Finset.disjoint_sdiff
  have hunion : ab ∪ rest = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ ab)
  -- Split sum and product
  have hsum : Finset.univ.sum p = ab.sum p + rest.sum p := by
    rw [← hunion, Finset.sum_union hdisj]
  have hprod : Finset.univ.prod (fun i => 1 - p i) =
      ab.prod (fun i => 1 - p i) * rest.prod (fun i => 1 - p i) := by
    rw [← hunion, Finset.prod_union hdisj]
  rw [hsum, hprod]
  -- Simplify the {a,b} parts
  have hab_sum : ab.sum p = p a + p b := Finset.sum_pair hab
  have hab_prod : ab.prod (fun i => 1 - p i) = (1 - p a) * (1 - p b) :=
    Finset.prod_pair hab
  rw [hab_sum, hab_prod]
  set S' := rest.sum p
  set P' := rest.prod (fun i => 1 - p i)
  set P := (1 - p a) * (1 - p b)
  -- Key identity: pa + pb + P = 1 + pa * pb
  have hident : p a + p b + P = 1 + p a * p b :=
    two_sum_prod_eq_one_add_mul (hp a) (hp b)
  -- P ≤ 1
  have hP_le : P ≤ 1 := by
    calc P = (1 - p a) * (1 - p b) := rfl
      _ ≤ 1 * 1 := by gcongr <;> exact tsub_le_self
      _ = 1 := mul_one 1
  -- Boole on complement: S' + P' ≥ 1
  have hboole_rest : 1 ≤ S' + P' :=
    sum_add_prod_compl_ge_one_finset rest p (fun i _ => hp i)
  -- S' ≥ P(1 - P'), hence S' + P·P' ≥ P
  have hrest_ge : P ≤ S' + P * P' := by
    have hP' : P' ≤ 1 :=
      Finset.prod_le_one' (fun i _ => tsub_le_self)
    have hS'_ge : 1 - P' ≤ S' := by rwa [tsub_le_iff_right]
    have hP1P' : P * (1 - P') ≤ S' :=
      le_trans (mul_le_of_le_one_left (zero_le _) hP_le) hS'_ge
    calc P = P * 1 := (mul_one P).symm
      _ = P * (P' + (1 - P')) := by rw [add_tsub_cancel_of_le hP']
      _ = P * P' + P * (1 - P') := by rw [mul_add]
      _ ≤ P * P' + S' := by gcongr
      _ = S' + P * P' := add_comm _ _
  -- Now combine: pa + pb + S' + P·P' ≥ pa + pb + P = 1 + pa·pb > 1
  have hpab_pos : (0 : ℝ≥0∞) < p a * p b := ENNReal.mul_pos ha.ne' hb.ne'
  calc 1 < 1 + p a * p b := ENNReal.lt_add_right ENNReal.one_ne_top hpab_pos.ne'
    _ = p a + p b + P := hident.symm
    _ ≤ p a + p b + (S' + P * P') := by gcongr
    _ = p a + p b + S' + P * P' := by ring

/-- **Strict Boole's inequality (subtraction form)**: when ≥ 2 probabilities are positive,
    the noisy-OR is strictly less than the sum of probabilities. This is the formal
    separation between set semantics (distribution semantics) and bag semantics (T_P_K_LP). -/
theorem noisyOr_lt_sum {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) (a b : Fin n) (hab : a ≠ b)
    (ha : 0 < p a) (hb : 0 < p b) :
    1 - Finset.univ.prod (fun i => 1 - p i) < Finset.univ.sum p := by
  set P := Finset.univ.prod (fun i => 1 - p i)
  have hP_le : P ≤ 1 := Finset.prod_le_one' (fun i _ => tsub_le_self)
  have hP_ne : P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hP_le
  rw [ENNReal.sub_lt_iff_lt_right hP_ne hP_le]
  exact sum_add_prod_compl_gt_one p hp a b hab ha hb

/-- **Bag-Set Separation Theorem**: For an OR-pattern ProbLog program where at least
    two mechanisms have positive probability, the bag semantics (∑ p_i, which is what
    T_P_K_LP at ℝ≥0∞ computes) strictly exceeds the set semantics (1 - ∏(1 - p_i),
    which is what distribution semantics / queryProb computes).

    This formally proves that the naive provenance semiring approach at ℝ≥0∞ gives the
    WRONG answer for ProbLog programs with overlapping derivations. -/
theorem bag_set_separation {n : ℕ} (p : ProbAssignment n)
    (hp : ∀ i, p i ≤ 1) (hn : 0 < 2 ^ n)
    (a b : Fin n) (hab : a ≠ b) (ha : 0 < p a) (hb : 0 < p b) :
    queryProb p (anyTrue (List.finRange n)) <
      Finset.univ.sum (fun i : Fin n => p i) := by
  rw [queryProb_anyTrue_full p hp hn]
  exact noisyOr_lt_sum p hp a b hab ha hb

/-- **Quantitative Boole bound**: `∑pᵢ + ∏(1-pᵢ) ≥ 1 + pₐ·pᵦ` for any two distinct
    indices a, b. This strengthens `sum_add_prod_compl_gt_one` from qualitative (> 1)
    to quantitative (≥ 1 + pₐpᵦ). -/
theorem sum_add_prod_ge_one_add_mul {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) (a b : Fin n) (hab : a ≠ b) :
    1 + p a * p b ≤ Finset.univ.sum p + Finset.univ.prod (fun i => 1 - p i) := by
  set ab := ({a, b} : Finset (Fin n))
  set rest := Finset.univ \ ab
  have hdisj : Disjoint ab rest := Finset.disjoint_sdiff
  have hunion : ab ∪ rest = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ ab)
  have hsum : Finset.univ.sum p = ab.sum p + rest.sum p := by
    rw [← hunion, Finset.sum_union hdisj]
  have hprod : Finset.univ.prod (fun i => 1 - p i) =
      ab.prod (fun i => 1 - p i) * rest.prod (fun i => 1 - p i) := by
    rw [← hunion, Finset.prod_union hdisj]
  rw [hsum, hprod]
  have hab_sum : ab.sum p = p a + p b := Finset.sum_pair hab
  have hab_prod : ab.prod (fun i => 1 - p i) = (1 - p a) * (1 - p b) :=
    Finset.prod_pair hab
  rw [hab_sum, hab_prod]
  set S' := rest.sum p
  set P' := rest.prod (fun i => 1 - p i)
  set P := (1 - p a) * (1 - p b)
  have hident : p a + p b + P = 1 + p a * p b :=
    two_sum_prod_eq_one_add_mul (hp a) (hp b)
  have hP_le : P ≤ 1 := by
    calc P = (1 - p a) * (1 - p b) := rfl
      _ ≤ 1 * 1 := by gcongr <;> exact tsub_le_self
      _ = 1 := mul_one 1
  have hboole_rest : 1 ≤ S' + P' :=
    sum_add_prod_compl_ge_one_finset rest p (fun i _ => hp i)
  have hrest_ge : P ≤ S' + P * P' := by
    have hP' : P' ≤ 1 := Finset.prod_le_one' (fun i _ => tsub_le_self)
    have hS'_ge : 1 - P' ≤ S' := by rwa [tsub_le_iff_right]
    have hP1P' : P * (1 - P') ≤ S' :=
      le_trans (mul_le_of_le_one_left (zero_le _) hP_le) hS'_ge
    calc P = P * 1 := (mul_one P).symm
      _ = P * (P' + (1 - P')) := by rw [add_tsub_cancel_of_le hP']
      _ = P * P' + P * (1 - P') := by rw [mul_add]
      _ ≤ P * P' + S' := by gcongr
      _ = S' + P * P' := add_comm _ _
  calc 1 + p a * p b = p a + p b + P := hident.symm
    _ ≤ p a + p b + (S' + P * P') := by gcongr
    _ = p a + p b + S' + P * P' := by ring

/-- **Quantitative Boole bound (gap form)**: the gap between bag semantics (∑ pᵢ) and
    set semantics (1 - ∏(1-pᵢ)) is at least pₐ · pᵦ for any two distinct indices.
    This strengthens `noisyOr_lt_sum` from a qualitative separation to a quantitative one. -/
theorem noisyOr_gap_ge_prod_pair {n : ℕ} (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, p i ≤ 1) (a b : Fin n) (hab : a ≠ b) :
    p a * p b ≤ Finset.univ.sum p - (1 - Finset.univ.prod (fun i => 1 - p i)) := by
  set prod_val := Finset.univ.prod (fun i => 1 - p i)
  set sum_val := Finset.univ.sum p
  set noisyOr := 1 - prod_val
  have hprod_le : prod_val ≤ 1 := Finset.prod_le_one' (fun i _ => tsub_le_self)
  have hnor_ne_top : noisyOr ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hprod_ne : prod_val ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hprod_le
  -- Quantitative bound: 1 + pa*pb ≤ sum + prod
  have hquant := sum_add_prod_ge_one_add_mul p hp a b hab
  -- Rewrite 1 as noisyOr + prod_val, then cancel prod_val
  have h1eq : noisyOr + prod_val = 1 := tsub_add_cancel_of_le hprod_le
  have h1_rw : 1 + p a * p b = (noisyOr + p a * p b) + prod_val := by
    rw [← h1eq]; ring
  rw [h1_rw] at hquant
  -- Cancel prod_val from both sides
  have hsge : noisyOr + p a * p b ≤ sum_val :=
    (ENNReal.add_le_add_iff_right hprod_ne).mp hquant
  -- noisyOr + pa*pb ≤ sum → pa*pb ≤ sum - noisyOr
  have hnor_le_sum : noisyOr ≤ sum_val := le_self_add.trans hsge
  rw [← tsub_add_cancel_of_le hnor_le_sum] at hsge
  exact (ENNReal.add_le_add_iff_right hnor_ne_top).mp (by rwa [add_comm] at hsge)

/-! ## §9 Bridge to T_P_K_LP: Bag Semantics Operator

For a ProbLog program viewed as an LP knowledge base with probability annotations,
one step of T_P_K_LP at ℝ≥0∞ computes the bag-semantics sum. We define the bridge
from ProbLogProgram to FinKnowledgeBase and the initial annotation. -/

/-- Convert a ProbLogProgram to a FinKnowledgeBase. The probabilistic facts are NOT
    in the EDB (they are handled by the annotation); only rules are present. -/
def ProbLogProgram.toFinKB {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) : FinKnowledgeBase σ where
  prog := prog.rules
  db := ∅

/-- Initial probability annotation: each probabilistic fact maps to its probability.
    All other atoms map to 0. -/
noncomputable def ProbLogProgram.initialAnnotation {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) [DecidableEq (GroundAtom σ)] : KRelation σ ℝ≥0∞ :=
  fun a => Finset.univ.sum (fun i => if prog.probFacts i = a then prog.probs i else 0)

/-- The initial annotation correctly assigns probabilities to probabilistic facts. -/
theorem ProbLogProgram.initialAnnotation_at_fact {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) [DecidableEq (GroundAtom σ)] (i : Fin n) :
    prog.initialAnnotation (prog.probFacts i) = prog.probs i := by
  simp only [initialAnnotation]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [prog.facts_injective.ne hji]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The initial annotation is 0 at the query atom (which is not a probabilistic fact). -/
theorem ProbLogProgram.initialAnnotation_zero_at_query {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) [DecidableEq (GroundAtom σ)]
    (q : GroundAtom σ) (hq : ∀ i, prog.probFacts i ≠ q) :
    prog.initialAnnotation q = 0 := by
  simp only [initialAnnotation]
  apply Finset.sum_eq_zero
  intro i _
  simp [hq i]

/-! ## §10 T_P_K_LP Computes Bag Semantics for OR-Pattern Programs

For a variable-free, function-free OR-pattern program, one step of `T_P_K_LP` at `ℝ≥0∞`
from the initial annotation equals the sum of all probabilities (bag semantics).
Combined with §8, this formally proves that T_P_K_LP gives the WRONG answer for
distribution semantics whenever ≥ 2 mechanisms are active.

The proof requires:
- `GroundTerm.toTerm` and `GroundAtom.toAtom` are injective (function-free)
- `Unique (Grounding σ)` when `σ.vars` is empty (collapses the sum over groundings)
- The rules list is a permutation of the canonical rules `⟨q.toAtom, [(probFacts i).toAtom]⟩`
- `convert_to` to bridge lambda-elaboration mismatches with `(f ∘ g)` vs `fun x => f (g x)` -/

/-! ## §11 Which-Provenance: Support Profiles as Semiring Lineage

The `Which` semiring does not try to recover ProbLog distribution semantics.
Instead, it tracks *which* probabilistic facts support a query. For the OR-pattern
fragment, one step of `T_P_K_LP` at `Which (Fin n)` computes the exact active
support profile.

This is the principled role of semiring provenance in the current architecture:
it recovers the static support-profile quotient, while the WM/evidence layer
retains richer multiplicity and revision information. -/

/-- A `Which`-valued annotation marking exactly the active probabilistic facts by
their indices. Inactive facts contribute `0`; active facts contribute the singleton
lineage `{i}`. -/
noncomputable def ProbLogProgram.whichInitialAnnotation {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (active : Finset (Fin n))
    [DecidableEq (GroundAtom σ)] : KRelation σ (Which (Fin n)) :=
  fun a =>
    ∑ i : Fin n,
      if i ∈ active ∧ prog.probFacts i = a
      then Which.wset {i}
      else 0

/-- On a probabilistic fact, `whichInitialAnnotation` returns the singleton lineage
for that fact exactly when the fact is active. -/
theorem ProbLogProgram.whichInitialAnnotation_at_fact {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (active : Finset (Fin n))
    [DecidableEq (GroundAtom σ)] (i : Fin n) :
    prog.whichInitialAnnotation active (prog.probFacts i) =
      if i ∈ active then Which.wset ({i} : Finset (Fin n)) else 0 := by
  classical
  unfold ProbLogProgram.whichInitialAnnotation
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hneq : prog.probFacts j ≠ prog.probFacts i := by
      intro h
      exact hji (prog.facts_injective h)
    simp [hneq]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Away from probabilistic facts, `whichInitialAnnotation` is zero. -/
theorem ProbLogProgram.whichInitialAnnotation_zero_at_query {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (active : Finset (Fin n))
    [DecidableEq (GroundAtom σ)] (q : GroundAtom σ)
    (hq : ∀ i : Fin n, prog.probFacts i ≠ q) :
    prog.whichInitialAnnotation active q = 0 := by
  classical
  unfold ProbLogProgram.whichInitialAnnotation
  apply Finset.sum_eq_zero
  intro i _
  simp [hq i]

/-- Summing singleton `Which` lineages over a finite set recovers the set itself. -/
private theorem sum_which_singletons_eq_wset {α : Type} [DecidableEq α]
    (s : Finset α) :
    s.sum (fun a => (Which.wset ({a} : Finset α) : Which α)) =
      if s.Nonempty then Which.wset s else 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, ih]
    have hins : (insert a s).Nonempty := ⟨a, by simp⟩
    rw [if_pos hins]
    by_cases hs : s.Nonempty
    · rw [if_pos hs]
      change Which.wset ({a} ∪ s) = Which.wset (insert a s)
      rw [Finset.insert_eq]
    · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      rw [if_neg hs]
      subst hs'
      simp [HAdd.hAdd, Add.add]

/-- Indicator-summing singleton `Which` lineages over the whole type recovers the
chosen active profile. -/
private theorem sum_ite_which_singletons_eq_wset {α : Type} [Fintype α] [DecidableEq α]
    (s : Finset α) :
    Finset.univ.sum
      (fun a => if a ∈ s then (Which.wset ({a} : Finset α) : Which α) else 0) =
      if s.Nonempty then Which.wset s else 0 := by
  classical
  rw [Fintype.sum_ite_mem]
  exact sum_which_singletons_eq_wset s

/-- In a function-free signature, `GroundTerm.toTerm` is injective. -/
theorem GroundTerm.toTerm_injective {σ : LPSignature} [IsEmpty σ.functionSymbols] :
    Function.Injective (GroundTerm.toTerm : GroundTerm σ → Term σ) := by
  intro a b h
  rw [← GroundTerm.ofConst_toConst a, ← GroundTerm.ofConst_toConst b]
  suffices a.toConst = b.toConst by rw [this]
  have h' : (GroundTerm.ofConst a.toConst).toTerm = (GroundTerm.ofConst b.toConst).toTerm := by
    rwa [GroundTerm.ofConst_toConst, GroundTerm.ofConst_toConst]
  change (GroundTerm.const a.toConst).toTerm = (GroundTerm.const b.toConst).toTerm at h'
  exact Term.const.inj h'

/-- In a function-free signature, `GroundAtom.toAtom` is injective. -/
theorem GroundAtom.toAtom_injective {σ : LPSignature} [IsEmpty σ.functionSymbols] :
    Function.Injective (GroundAtom.toAtom : GroundAtom σ → Atom σ) := by
  intro ⟨s, a⟩ ⟨s', b⟩ h
  have hsym : s = s' := congrArg Atom.symbol h
  subst hsym; congr 1; funext i
  exact GroundTerm.toTerm_injective (congrFun (eq_of_heq (Atom.ext_iff.mp h).2) i)

/-- When `σ.vars` is empty, there is a unique grounding (the empty function). -/
noncomputable instance uniqueGroundingOfVarsEmpty {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [IsEmpty σ.vars] [Fintype σ.constants] :
    Unique (Grounding σ) where
  default := isEmptyElim
  uniq _ := funext isEmptyElim

/-- The canonical rule for index `i` in an OR-pattern program: `q :- probFacts i`. -/
private def canonicalRule {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (i : Fin n) : Clause σ :=
  ⟨q.toAtom, [(prog.probFacts i).toAtom]⟩

/-- `canonicalRule` is injective when probabilistic facts are injective. -/
private theorem canonicalRule_injective {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) :
    Function.Injective (canonicalRule prog q) := by
  intro i j h
  simp only [canonicalRule, Clause.mk.injEq] at h
  simp only [List.cons.injEq, and_true] at h
  exact prog.facts_injective (GroundAtom.toAtom_injective h.2)

/-- The rules list of an OR-pattern program is a permutation of the canonical rules. -/
private theorem rules_perm_canonical {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    (hnodup : prog.rules.Nodup) :
    prog.rules.Perm ((List.finRange n).map (canonicalRule prog q)) := by
  rw [List.perm_ext_iff_of_nodup (d₁ := hnodup)
      (d₂ := (List.nodup_finRange n).map (canonicalRule_injective prog q))]
  intro c
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := hor.only_rules c hc
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, hi ▸ rfl⟩
  · intro hc
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hc
    exact hi ▸ hor.has_rule i

/-- **T_P_K_LP = Bag Sum**: For a variable-free, function-free OR-pattern program with
    no duplicate rules, one step of `T_P_K_LP` from the initial annotation at query `q`
    equals the sum of all probabilities.

    This is the formal statement that T_P_K_LP at `ℝ≥0∞` computes **bag semantics**.
    Combined with `bag_set_separation` (§8), it proves that T_P_K_LP gives the wrong
    answer for ProbLog distribution semantics whenever ≥ 2 mechanisms are active. -/
theorem T_P_K_LP_or_eq_sum {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    [IsEmpty σ.vars] [Fintype σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.vars]
    [DecidableEq σ.relationSymbols]
    [DecidableEq (GroundAtom σ)]
    (hnodup : prog.rules.Nodup) :
    T_P_K_LP ℝ≥0∞ prog.toFinKB prog.initialAnnotation q =
      Finset.univ.sum (fun i : Fin n => prog.probs i) := by
  simp only [T_P_K_LP, ProbLogProgram.toFinKB]
  simp only [show ¬(q ∈ (∅ : Finset (GroundAtom σ))) from by simp, ite_false, zero_add]
  haveI : Unique (Grounding σ) := uniqueGroundingOfVarsEmpty
  rw [Fintype.sum_unique]
  have hg : ∀ ga : GroundAtom σ, (default : Grounding σ).groundAtom ga.toAtom = ga :=
    Grounding.groundAtom_toAtom_self default
  have hperm := rules_perm_canonical prog q hor hnodup
  rw [(hperm.map _).sum_eq, List.map_map]
  -- Bridge the lambda-elaboration gap between `(f ∘ g)` and `fun i => f (g i)`
  convert_to ((List.finRange n).map (fun i => prog.probs i)).sum = _
  · congr 1
    apply List.map_congr_left; intro i _
    simp only [Function.comp_apply, canonicalRule, hg q, ite_true,
               List.map_cons, List.map_nil, hg (prog.probFacts i),
               List.prod_cons, List.prod_nil, mul_one]
    exact ProbLogProgram.initialAnnotation_at_fact prog i
  · rw [← List.ofFn_eq_map]; simp [Finset.sum]

/-- **T_P_K_LP = Which-Style Support Profile**: For the OR-pattern fragment, one
step of `T_P_K_LP` at the `WhichProfile` semiring computes the exact active fact
profile, with `0` for the empty profile and `pset active` otherwise.

This is the principled provenance result complementary to `T_P_K_LP_or_eq_sum`:
`ℝ≥0∞` yields bag weights, while `Which` yields the support-profile
quotient. -/
theorem T_P_K_LP_or_eq_which_profile {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (hor : IsORPattern prog q)
    [IsEmpty σ.vars] [Fintype σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.vars]
    [DecidableEq σ.relationSymbols]
    [DecidableEq (GroundAtom σ)]
    (active : Finset (Fin n))
    (hnodup : prog.rules.Nodup) :
    T_P_K_LP (Which (Fin n)) prog.toFinKB (prog.whichInitialAnnotation active) q =
      if active.Nonempty then Which.wset active else 0 := by
  simp only [T_P_K_LP, ProbLogProgram.toFinKB]
  simp only [show ¬(q ∈ (∅ : Finset (GroundAtom σ))) from by simp, ite_false, zero_add]
  haveI : Unique (Grounding σ) := uniqueGroundingOfVarsEmpty
  rw [Fintype.sum_unique]
  have hg : ∀ ga : GroundAtom σ, (default : Grounding σ).groundAtom ga.toAtom = ga :=
    Grounding.groundAtom_toAtom_self default
  have hperm := rules_perm_canonical prog q hor hnodup
  rw [(hperm.map _).sum_eq, List.map_map]
  convert_to
    ((List.finRange n).map
      (fun i =>
        if i ∈ active
        then (Which.wset ({i} : Finset (Fin n)) : Which (Fin n))
        else 0)).sum =
      _ 
  · congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, canonicalRule, hg q, ite_true,
      List.map_cons, List.map_nil, hg (prog.probFacts i),
      List.prod_cons, List.prod_nil, mul_one]
    exact ProbLogProgram.whichInitialAnnotation_at_fact prog active i
  · rw [← List.ofFn_eq_map]
    simpa [Finset.sum] using (sum_ite_which_singletons_eq_wset active)

#check @queryHolds_or_pattern
#check @compilation_or_noisyOr
#check @compilation_or_toReal
#check @wm_pln_revision_changes_evidence
#check @bag_set_separation
#check @T_P_K_LP_or_eq_sum
#check @T_P_K_LP_or_eq_which_profile
#check @noisyOr_gap_ge_prod_pair

-- Axiom footprint for key theorems
#print axioms T_P_K_LP_or_eq_sum
#print axioms bag_set_separation
#print axioms compilation_or_noisyOr
#print axioms noisyOr_gap_ge_prod_pair

end Mettapedia.Logic.ProbLogCompilation
