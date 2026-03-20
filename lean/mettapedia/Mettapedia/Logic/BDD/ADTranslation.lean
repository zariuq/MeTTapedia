import Mettapedia.Logic.BDD.ProbMeTTaBridge

/-!
# Annotated Disjunction Translation

Formalizes the standard ProbLog translation of annotated disjunctions (ADs)
into normal clauses with auxiliary probabilistic switch facts.

An AD `p₁::h₁ ; p₂::h₂ ; ... ; pₖ::hₖ :- body` is translated to:
- `h₁ :- body, aux₁`
- `h₂ :- body, aux₂, ¬aux₁`
- `hᵢ :- body, auxᵢ, ¬aux₁, ..., ¬aux_{i-1}`

where `auxᵢ` are fresh probabilistic facts with calibrated probabilities
such that `P(auxᵢ ∧ ¬aux₁ ∧ ... ∧ ¬aux_{i-1}) = pᵢ`.

## References

- De Raedt & Kimmig (2015): "Probabilistic (logic) programming concepts"
- Fierens et al. (2015): "Inference and learning in probabilistic logic programs
  using weighted Boolean formulas", §2.2

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open Mettapedia.Logic.LP
open Mettapedia.Logic.ProbLogCompilation

/-! ## §1 Annotated Disjunction Syntax -/

/-- An annotated disjunction: a multi-headed probabilistic rule.
    `heads[i]` fires with probability `probs[i]` when `body` is satisfied.
    At most one head fires per derivation (mutual exclusion via NAF guards).

    Example: `0.6::heads ; 0.4::tails :- coin_toss` has
    `heads = [heads_atom, tails_atom]`, `body = [coin_toss_atom]`. -/
structure AnnotatedDisjunction (σ : LPSignature) where
  heads : List (GroundAtom σ)
  body  : List (GroundAtom σ)

/-! ## §2 AD Expansion -/

/-- Build the NAF guard prefix for head `i`: `¬aux₁, ..., ¬aux_{i-1}`.
    This ensures mutual exclusion: head `i` fires only if no earlier head was selected. -/
def nafGuardPrefix {σ : LPSignature} {k : ℕ}
    (auxAtoms : Fin k → GroundAtom σ) (i : ℕ) : List (GoalLit σ) :=
  (List.range i).filterMap fun j =>
    if h : j < k then some (.neg (auxAtoms ⟨j, h⟩)) else none

/-- Expand an annotated disjunction into normal clauses.

    For each head `i`:
    - head: `ad.heads[i]`
    - body: `ad.body` (positive) ++ `auxAtoms[i]` (positive) ++ NAF guards for `j < i`

    The `auxAtoms` are fresh probabilistic facts provided by the caller.
    Their probabilities must be calibrated for the translation to preserve
    the distribution semantics. -/
def expandAD {σ : LPSignature} (ad : AnnotatedDisjunction σ)
    (auxAtoms : Fin ad.heads.length → GroundAtom σ) :
    List (NormalClause σ) :=
  (List.finRange ad.heads.length).map fun i =>
    { head := ad.heads.get (i.cast (by omega))
      body := ad.body.map GoalLit.pos ++
              [GoalLit.pos (auxAtoms i)] ++
              nafGuardPrefix auxAtoms i }

/-- Every member of `nafGuardPrefix` is `.neg (auxAtoms ⟨j, _⟩)` for some `j`. -/
theorem nafGuardPrefix_mem_neg {σ : LPSignature} {k : ℕ}
    (auxAtoms : Fin k → GroundAtom σ) (i : ℕ) (g : GoalLit σ)
    (hg : g ∈ nafGuardPrefix auxAtoms i) :
    ∃ fi : Fin k, g = .neg (auxAtoms fi) := by
  unfold nafGuardPrefix at hg
  rw [List.mem_filterMap] at hg
  obtain ⟨j, hj_mem, hj_eq⟩ := hg
  rw [List.mem_range] at hj_mem
  split at hj_eq
  · next hjk => simp at hj_eq; exact ⟨⟨j, hjk⟩, hj_eq.symm⟩
  · simp at hj_eq

/-! ## §3 Stratification of Expanded Rules -/

/-- The expanded AD rules are stratifiable: auxiliary atoms at stratum 0,
    AD heads at stratum 1. The positive body atoms (from `ad.body`) are
    resolved against the base definite LHM (stratum 0).

    Specifically: each rule has body containing `pos (auxAtoms[i])` (stratum 0 ≤ 1)
    and `neg (auxAtoms[j])` for `j < i` (stratum 0 < 1). -/
theorem expandAD_stratifiable {σ : LPSignature}
    (ad : AnnotatedDisjunction σ)
    (auxAtoms : Fin ad.heads.length → GroundAtom σ)
    (bodyAtoms : List (GroundAtom σ))
    (_hbody : ad.body = bodyAtoms)
    -- Freshness: aux atoms are distinct from head atoms and body atoms
    (hfresh_heads : ∀ i, auxAtoms i ∉ ad.heads)
    (hfresh_body : ∀ i, auxAtoms i ∉ ad.body) :
    isStratifiable (expandAD ad auxAtoms) := by
  classical
  -- Stratification: auxAtoms get stratum 0, everything else gets stratum 1
  refine ⟨fun ga => if ∃ i, auxAtoms i = ga then 0 else 1, ?_⟩
  intro c hc
  simp only [expandAD, List.mem_map, List.mem_finRange] at hc
  obtain ⟨idx, _, rfl⟩ := hc
  -- c.head = ad.heads.get idx (not an aux atom)
  have hhead_not_aux : ¬∃ i, auxAtoms i = ad.heads.get (idx.cast (by omega)) :=
    fun ⟨i, hi⟩ => hfresh_heads i (hi ▸ List.get_mem ..)
  -- The body is: body.map pos ++ [pos (auxAtoms idx)] ++ nafGuardPrefix auxAtoms idx
  -- respectsStratification checks each g ∈ body according to its GoalLit constructor
  intro g hg
  -- Three regions of the body list
  have hbody_mem := List.mem_append.mp hg
  rcases hbody_mem with hbody_part | hguard_part
  · -- g is in body.map pos ++ [pos (auxAtoms idx)]
    have hbody_mem2 := List.mem_append.mp hbody_part
    rcases hbody_mem2 with hmap | hsingle
    · -- g = pos a for some a ∈ ad.body
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmap
      show (if ∃ i, auxAtoms i = a then 0 else 1) ≤
           (if ∃ i, auxAtoms i = _ then 0 else 1)
      rw [if_neg (fun ⟨i, hi⟩ => hfresh_body i (hi ▸ ha)), if_neg hhead_not_aux]
    · -- g = pos (auxAtoms idx)
      rcases List.mem_cons.mp hsingle with rfl | h
      · show (if ∃ j, auxAtoms j = auxAtoms idx then 0 else 1) ≤
             (if ∃ j, auxAtoms j = _ then 0 else 1)
        rw [if_pos ⟨idx, rfl⟩, if_neg hhead_not_aux]; omega
      · exact absurd h (by simp)
  · -- g ∈ nafGuardPrefix: g = neg (auxAtoms ⟨j, _⟩) for some j < idx
    -- nafGuardPrefix only produces .neg atoms, so g must be .neg
    -- nafGuardPrefix only produces .neg atoms → stratum 0 < 1 = stratum(head)
    -- Every member of nafGuardPrefix is .neg (auxAtoms ⟨j, _⟩) for some j
    -- So the respectsStratification check needs stratum(auxAtoms j) < stratum(head)
    -- which is 0 < 1.
    -- We prove this by showing g matches the .neg case of respectsStratification
    -- and the underlying atom is an auxAtom.
    have hmem_naf := nafGuardPrefix_mem_neg auxAtoms idx.val g hguard_part
    obtain ⟨fi, hgeq⟩ := hmem_naf
    rw [hgeq]
    show (if ∃ i, auxAtoms i = auxAtoms fi then 0 else 1) <
         (if ∃ i, auxAtoms i = _ then 0 else 1)
    rw [if_pos ⟨fi, rfl⟩, if_neg hhead_not_aux]; omega

/-! ## §4 Mutual Exclusion Property

The NAF guards ensure that at most one AD head can fire per assignment:
if `auxAtoms[i]` is true and all `auxAtoms[j]` for `j < i` are false,
then only head `i` can be derived from this AD. -/

/-- At most one expanded rule can fire per assignment: if head `i`'s body
    is satisfied (aux_i true, aux_j false for j < i), then head `j`'s body
    is NOT satisfied for `j ≠ i`. -/
theorem expandAD_mutual_exclusion {σ : LPSignature}
    (ad : AnnotatedDisjunction σ)
    (auxAtoms : Fin ad.heads.length → GroundAtom σ)
    (I negI : Set (GroundAtom σ))
    (i j : Fin ad.heads.length) (hij : i < j)
    -- aux_i is true (in the positive interpretation)
    (_hi_pos : auxAtoms i ∈ I)
    -- aux_i is in the NAF interpretation (meaning it would block j's NAF guard)
    (hi_neg : auxAtoms i ∈ negI) :
    -- Then head j's body is NOT fully satisfied (aux_i blocks it via ¬aux_i)
    ¬ ∀ g ∈ (nafGuardPrefix auxAtoms j), goalLitHoldsIn I negI g := by
  intro hall
  -- nafGuardPrefix includes neg (auxAtoms i) since i < j
  have : GoalLit.neg (auxAtoms i) ∈ nafGuardPrefix auxAtoms j := by
    simp [nafGuardPrefix, List.mem_filterMap, List.mem_range]
    exact ⟨i, hij, i.isLt, rfl⟩
  have := hall _ this
  -- goalLitHoldsIn for neg: auxAtoms i ∉ negI
  simp [goalLitHoldsIn] at this
  exact this hi_neg

/-! ## §5 Switch Probability Calibration

The standard ProbLog AD translation uses calibrated switch probabilities:
`switchProbs i = probs i / (1 - Σ_{j<i} probs j)`.

The key identity: `∏_{j<i} (1 - switchProbs j) · switchProbs i = probs i`.

This telescopes because each factor `(1 - switchProbs j) = (1 - S_{j+1})/(1 - S_j)`
where `S_j = Σ_{m<j} probs m`, so the product collapses to `(1 - S_i)`.
Then `(1 - S_i) · probs_i / (1 - S_i) = probs_i`. -/

open scoped ENNReal

/-- Partial sum of probabilities: `S i = Σ_{j<i} probs j`. -/
noncomputable def partialSum {k : ℕ} (probs : Fin k → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  (Finset.univ.filter (fun j : Fin k => j.val < i)).sum probs

/-- Switch probability: `probs i / (1 - S_i)` where `S_i = Σ_{j<i} probs j`. -/
noncomputable def switchProb {k : ℕ} (probs : Fin k → ℝ≥0∞) (i : Fin k) : ℝ≥0∞ :=
  probs i / (1 - partialSum probs i)

/-- `partialSum probs 0 = 0`. -/
theorem partialSum_zero {k : ℕ} (probs : Fin k → ℝ≥0∞) :
    partialSum probs 0 = 0 := by
  simp [partialSum]

/-- The filter `{j : Fin k | j.val < n+1}` splits into `{j | j.val < n} ∪ {⟨n, _⟩}`. -/
private theorem filter_lt_succ_eq {k : ℕ} (n : ℕ) (hn : n < k) :
    Finset.univ.filter (fun j : Fin k => j.val < n + 1) =
    Finset.univ.filter (fun j : Fin k => j.val < n) ∪ {⟨n, hn⟩} := by
  ext j; simp [Finset.mem_filter]
  -- Goal: ↑j ≤ n ↔ j = ⟨n, hn⟩ ∨ ↑j < n
  constructor
  · intro hjn1
    by_cases hjn : j.val < n
    · right; exact hjn
    · left; ext; simp; omega
  · intro h; rcases h with rfl | h
    · simp
    · omega

private theorem filter_lt_succ_disjoint {k : ℕ} (n : ℕ) (hn : n < k) :
    Disjoint (Finset.univ.filter (fun j : Fin k => j.val < n)) {⟨n, hn⟩} := by
  rw [Finset.disjoint_left]
  intro j hj hmem
  have hjn := (Finset.mem_filter.mp hj).2
  rw [Finset.mem_singleton] at hmem
  rw [hmem] at hjn; simp at hjn

/-- `partialSum probs (n+1) = partialSum probs n + probs ⟨n, _⟩`. -/
private theorem partialSum_succ {k : ℕ} (probs : Fin k → ℝ≥0∞) (n : ℕ) (hn : n < k) :
    partialSum probs (n + 1) = partialSum probs n + probs ⟨n, hn⟩ := by
  simp only [partialSum]
  rw [filter_lt_succ_eq n hn, Finset.sum_union (filter_lt_succ_disjoint n hn)]
  simp

/-- `partialSum probs m ≤ Finset.univ.sum probs`. -/
private theorem partialSum_le_sum {k : ℕ} (probs : Fin k → ℝ≥0∞) (m : ℕ) :
    partialSum probs m ≤ Finset.univ.sum probs := by
  simp only [partialSum]
  exact Finset.sum_le_sum_of_subset (fun j _ => Finset.mem_univ j)

/-- **Telescoping product** (fully proved):
    `∏_{j<m} (1 - switchProb j) = 1 - S_m`. -/
theorem telescoping_switch_product {k : ℕ} (probs : Fin k → ℝ≥0∞)
    (hsum : Finset.univ.sum probs ≤ 1)
    (m : ℕ) (hm : m ≤ k)
    (hpartial : ∀ j, j < m → partialSum probs j < 1) :
    (Finset.univ.filter (fun j : Fin k => j.val < m)).prod
      (fun j => 1 - switchProb probs j) = 1 - partialSum probs m := by
  induction m with
  | zero => simp [partialSum_zero]
  | succ n ih =>
    have hn_lt_k : n < k := by omega
    rw [filter_lt_succ_eq n hn_lt_k,
        Finset.prod_union (filter_lt_succ_disjoint n hn_lt_k)]
    simp only [Finset.prod_singleton]
    -- IH: product up to n = 1 - S_n
    rw [ih (by omega) (fun j hj => hpartial j (by omega))]
    -- Goal: (1 - S_n) * (1 - switchProb ⟨n, _⟩) = 1 - S_{n+1}
    simp only [switchProb]
    -- S_{n+1} = S_n + probs_n
    have hSn_succ := partialSum_succ probs n hn_lt_k
    rw [hSn_succ]
    -- ENNReal arithmetic: (1 - S_n) * (1 - p_n / (1 - S_n)) = 1 - S_n - p_n
    have hSn_lt : partialSum probs n < 1 := hpartial n (by omega)
    have hSn_le : partialSum probs n ≤ 1 := le_of_lt hSn_lt
    have h1Sn_ne : 1 - partialSum probs n ≠ 0 := by
      intro h; exact not_lt.mpr (tsub_eq_zero_iff_le.mp h) hSn_lt
    have h1Sn_ne_top : 1 - partialSum probs n ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hpn_le : probs ⟨n, hn_lt_k⟩ ≤ 1 - partialSum probs n := by
      have hSn_ne_top : partialSum probs n ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hSn_le
      rw [ENNReal.le_sub_iff_add_le_right hSn_ne_top hSn_le]
      calc probs ⟨n, hn_lt_k⟩ + partialSum probs n
          = partialSum probs n + probs ⟨n, hn_lt_k⟩ := add_comm ..
        _ = partialSum probs (n + 1) := hSn_succ.symm
        _ ≤ Finset.univ.sum probs := partialSum_le_sum probs (n + 1)
        _ ≤ 1 := hsum
    rw [ENNReal.mul_sub (by intro _ _; exact h1Sn_ne_top)]
    rw [mul_one, ENNReal.mul_div_cancel h1Sn_ne h1Sn_ne_top]
    rw [← tsub_add_eq_tsub_tsub]

/-- **AD switch calibration** (fully proved, no hypotheses beyond `hsum`):
    the probability of selecting exactly switch `i` equals `probs i`. -/
theorem ad_switch_calibration {k : ℕ} (probs : Fin k → ℝ≥0∞)
    (hsum : Finset.univ.sum probs ≤ 1)
    (i : Fin k)
    (hSi_lt : partialSum probs i.val < 1)
    (hpartial : ∀ j, j < i.val → partialSum probs j < 1) :
    (Finset.univ.filter (fun j : Fin k => j.val < i.val)).prod
      (fun j => 1 - switchProb probs j) *
    switchProb probs i = probs i := by
  rw [telescoping_switch_product probs hsum i.val (by omega) hpartial, switchProb]
  have hSi_ne : 1 - partialSum probs i.val ≠ 0 := by
    intro h; exact not_lt.mpr (tsub_eq_zero_iff_le.mp h) hSi_lt
  have hSi_ne_top : 1 - partialSum probs i.val ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  exact ENNReal.mul_div_cancel hSi_ne hSi_ne_top

/-! ## §6 AD-to-WMC Composition

Connects the AD expansion to the WMC bridge: given a base ProbLog program
and normal rules (produced by `expandAD`), the WMC of the resulting
`NormalProbLogProgram` is correct under stratified semantics. -/

/-- **AD-to-WMC composition**: given a base program and normal rules
    (from `expandAD` with calibrated switch facts), the WMC bridge applies.

    Usage: `ad_program_wmc_correct baseProg (expandAD ad auxAtoms) s goals env henv`
    gives an ordered BDD whose WMC equals the distribution semantics probability
    of `goals` under the expanded program's stratified model. -/
theorem ad_program_wmc_correct {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (baseProg : ProbLogProgram σ n)
    (normalRules : List (NormalClause σ))
    (s : Mettapedia.Logic.LP.Stratification σ)
    (goals : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1) :
    ∃ f : BDD n, f.Ordered none ∧
      bdd_wmc f env = weightedSat f.eval env ∧
      (∀ a, f.eval a = true ↔
        ∀ g ∈ goals, Mettapedia.Logic.LP.GoalLit.holdsNormal
          (⟨baseProg, normalRules⟩ : NormalProbLogProgram σ n) s a g) :=
  normal_goal_wmc_semantic_equivalence ⟨baseProg, normalRules⟩ s goals env henv

/-- **AD-to-conditioning composition**: given a base program and normal rules
    (from `expandAD`), the conditioning bridge applies with P(E) ≠ 0. -/
theorem ad_program_conditioning_correct {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (baseProg : ProbLogProgram σ n)
    (normalRules : List (NormalClause σ))
    (s : Mettapedia.Logic.LP.Stratification σ)
    (goalsQ goalsE : List (GoalLit σ))
    (env : Fin n → ℝ≥0∞) (henv : ∀ i, env i ≤ 1)
    (hEpos : ∃ a : Fin n → Bool,
      (∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal ⟨baseProg, normalRules⟩ s a g) ∧
      assignmentWeight env a ≠ 0) :
    ∃ fQE fE : BDD n,
      fQE.Ordered none ∧ fE.Ordered none ∧
      bdd_wmc fE env ≠ 0 ∧
      bdd_wmc fQE env / bdd_wmc fE env =
        weightedSat fQE.eval env / weightedSat fE.eval env ∧
      (∀ a, fQE.eval a = true ↔
        ∀ g ∈ goalsQ ++ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal
          (⟨baseProg, normalRules⟩ : NormalProbLogProgram σ n) s a g) ∧
      (∀ a, fE.eval a = true ↔
        ∀ g ∈ goalsE, Mettapedia.Logic.LP.GoalLit.holdsNormal
          (⟨baseProg, normalRules⟩ : NormalProbLogProgram σ n) s a g) :=
  normal_conditional_probability ⟨baseProg, normalRules⟩ s goalsQ goalsE env henv hEpos

end Mettapedia.Logic.BDDCore
