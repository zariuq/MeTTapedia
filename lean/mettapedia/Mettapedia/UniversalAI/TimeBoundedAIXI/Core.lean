import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mettapedia.UniversalAI.BayesianAgents.Core
import Mettapedia.UniversalAI.BayesianAgents.InfiniteHistoryCompat
import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration

/-!
# Chapter 7 (core-generic): AIXItl convergence schema

This module factors out the **Chapter 7 best-vote + proof-enumeration convergence schema** from
`Mettapedia.UniversalAI.TimeBoundedAIXI`, but in terms of the **generic**
`Mettapedia.UniversalAI.BayesianAgents.Core` API (arbitrary finite action/percept alphabets).

It intentionally does **not** re-develop step-counting semantics (`ToPartrec`, etc.); it packages the
logical prerequisites needed for AIXItl→AIXI-style ε-optimality results.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI.Core

open scoped BigOperators
open scoped Classical

universe uA uP

/-! ## Programs outputting `(claimed value, action)` -/

/-- A binary program code with a recorded length. -/
structure Program where
  code : List Bool
  length : ℕ := code.length

/-- A (total) extended chronological program: returns a real-valued self-estimate and an action. -/
structure ExtendedChronologicalProgram (Action : Type uA) (Percept : Type uP) where
  code : Program
  compute : BayesianAgents.Core.History Action Percept → ℝ × Action

instance {Action : Type uA} {Percept : Type uP} [Inhabited Action] :
    Inhabited (ExtendedChronologicalProgram Action Percept) :=
  ⟨{ code := { code := [] }, compute := fun _ => (0, default) }⟩

/-! ## Deterministic agents induced by programs -/

/-- A deterministic agent that always chooses `act h`. -/
noncomputable def deterministicAgent {Action : Type uA} {Percept : Type uP} [Fintype Action]
    (act : BayesianAgents.Core.History Action Percept → Action) : BayesianAgents.Core.Agent Action Percept where
  policy h a := if a = act h then 1 else 0
  policy_sum_one h _hw := by
    classical
    simp

/-- View an extended chronological program as a deterministic agent (it outputs an action). -/
noncomputable def ExtendedChronologicalProgram.toAgent {Action : Type uA} {Percept : Type uP} [Fintype Action]
    (p : ExtendedChronologicalProgram Action Percept) : BayesianAgents.Core.Agent Action Percept :=
  deterministicAgent fun h => (p.compute h).2

/-! ## Best-vote utilities -/

/-- Select the candidate with strictly larger claimed value, keeping `acc` on ties. -/
noncomputable def selectBetter {Action : Type uA} (acc cand : ℝ × Action) : ℝ × Action :=
  if cand.1 > acc.1 then cand else acc

theorem selectBetter_fst_ge_acc {Action : Type uA} (acc cand : ℝ × Action) :
    acc.1 ≤ (selectBetter acc cand).1 := by
  by_cases h : cand.1 > acc.1
  · have : acc.1 ≤ cand.1 := le_of_lt h
    simp [selectBetter, h, this]
  · simp [selectBetter, h]

theorem selectBetter_fst_ge_cand_of_ge {Action : Type uA} (acc cand : ℝ × Action) (hge : cand.1 ≤ acc.1) :
    cand.1 ≤ (selectBetter acc cand).1 := by
  have hnot : ¬cand.1 > acc.1 := by
    exact not_lt.mpr hge
  simp [selectBetter, hnot, hge]

theorem selectBetter_fst_ge_cand_of_gt {Action : Type uA} (acc cand : ℝ × Action) (hgt : cand.1 > acc.1) :
    cand.1 ≤ (selectBetter acc cand).1 := by
  simp [selectBetter, hgt]

/-- Fold over programs, keeping the `(claimed value, action)` pair with maximal claimed value. -/
noncomputable def bestByValueAux {Action : Type uA} {Percept : Type uP} (acc : ℝ × Action)
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) : ℝ × Action :=
  programs.foldl (fun acc p => selectBetter acc (ExtendedChronologicalProgram.compute p h)) acc

theorem bestByValueAux_fst_ge_acc {Action : Type uA} {Percept : Type uP} (acc : ℝ × Action)
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) : acc.1 ≤ (bestByValueAux acc programs h).1 := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux]
  | cons p ps ih =>
      simp [bestByValueAux, List.foldl_cons]
      exact
        le_trans (selectBetter_fst_ge_acc acc (ExtendedChronologicalProgram.compute p h))
          (ih (acc := selectBetter acc (ExtendedChronologicalProgram.compute p h)))

theorem bestByValueAux_fst_ge_of_mem {Action : Type uA} {Percept : Type uP} (acc : ℝ × Action)
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) {p : ExtendedChronologicalProgram Action Percept}
    (hp : p ∈ programs) :
    (ExtendedChronologicalProgram.compute p h).1 ≤ (bestByValueAux acc programs h).1 := by
  induction programs generalizing acc with
  | nil =>
      cases hp
  | cons q qs ih =>
      simp [bestByValueAux, List.mem_cons] at hp ⊢
      rcases hp with rfl | hp
      · have hstep :
            (ExtendedChronologicalProgram.compute p h).1 ≤
              (selectBetter acc (ExtendedChronologicalProgram.compute p h)).1 := by
          by_cases hgt : (ExtendedChronologicalProgram.compute p h).1 > acc.1
          · exact selectBetter_fst_ge_cand_of_gt acc (ExtendedChronologicalProgram.compute p h) hgt
          · have hge : (ExtendedChronologicalProgram.compute p h).1 ≤ acc.1 := le_of_not_gt hgt
            exact selectBetter_fst_ge_cand_of_ge acc (ExtendedChronologicalProgram.compute p h) hge
        have hmon :
            (selectBetter acc (ExtendedChronologicalProgram.compute p h)).1 ≤
              (bestByValueAux (selectBetter acc (ExtendedChronologicalProgram.compute p h)) qs h).1 :=
          bestByValueAux_fst_ge_acc
            (acc := selectBetter acc (ExtendedChronologicalProgram.compute p h)) (programs := qs) (h := h)
        exact le_trans hstep hmon
      · simpa [bestByValueAux, List.foldl_cons] using
          ih (acc := selectBetter acc (ExtendedChronologicalProgram.compute q h)) (hp := hp)

/-- Best `(claimed value, action)` among a list of programs, defaulting to `(0, default)` on `[]`. -/
noncomputable def bestByValue {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) : ℝ × Action :=
  match programs with
  | [] => (0, default)
  | p0 :: ps => bestByValueAux (ExtendedChronologicalProgram.compute p0 h) ps h

theorem bestByValue_fst_ge_of_mem {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) {p : ExtendedChronologicalProgram Action Percept}
    (hp : p ∈ programs) : (p.compute h).1 ≤ (bestByValue programs h).1 := by
  cases programs with
  | nil =>
      cases hp
  | cons head tail =>
      simp [bestByValue, List.mem_cons] at hp ⊢
      rcases hp with rfl | hp
      · exact
          bestByValueAux_fst_ge_acc (acc := ExtendedChronologicalProgram.compute p h) (programs := tail) (h := h)
      · exact
          bestByValueAux_fst_ge_of_mem (acc := ExtendedChronologicalProgram.compute head h) (programs := tail) (h := h) hp

theorem bestByValueAux_eq_acc_or_eq_compute_of_mem {Action : Type uA} {Percept : Type uP} (acc : ℝ × Action)
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) :
    bestByValueAux acc programs h = acc ∨
      ∃ p ∈ programs, bestByValueAux acc programs h = p.compute h := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux]
  | cons p ps ih =>
      have hsel : selectBetter acc (p.compute h) = acc ∨ selectBetter acc (p.compute h) = p.compute h := by
        by_cases hgt : (p.compute h).1 > acc.1
        · right
          simp [selectBetter, hgt]
        · left
          simp [selectBetter, hgt]
      have := ih (acc := selectBetter acc (p.compute h))
      rcases this with hEq | ⟨q, hq, hEq⟩
      · rcases hsel with hacc | hp
        · left
          simpa [bestByValueAux, List.foldl_cons, hacc] using hEq
        · right
          refine ⟨p, by simp, ?_⟩
          simpa [bestByValueAux, List.foldl_cons, hp] using hEq
      · right
        refine ⟨q, by simp [hq], ?_⟩
        simpa [bestByValueAux, List.foldl_cons] using hEq

theorem bestByValue_eq_compute_of_mem {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (programs : List (ExtendedChronologicalProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) (hne : programs ≠ []) :
    ∃ p ∈ programs, bestByValue programs h = p.compute h := by
  cases programs with
  | nil =>
      cases hne rfl
  | cons p0 ps =>
      have hmem : p0 ∈ (p0 :: ps) := by simp
      have hcases := bestByValueAux_eq_acc_or_eq_compute_of_mem (acc := p0.compute h) (programs := ps) (h := h)
      rcases hcases with hEq | ⟨p, hp, hEq⟩
      · refine ⟨p0, by simp, ?_⟩
        simp [bestByValue, hEq]
      · refine ⟨p, by simp [hp], ?_⟩
        simp [bestByValue, hEq]

/-! ## AIXItl as “best vote” over validated programs -/

/-- Time-bounded AIXI (AIXItl): keep a finite validated program list, then choose the best claim. -/
structure AIXItl (Action : Type uA) (Percept : Type uP) where
  timeBound : ℕ
  lengthBound : ℕ
  proofLengthBound : ℕ
  validatedPrograms : List (ExtendedChronologicalProgram Action Percept)

/-- The best `(claimed value, action)` among the agent's validated programs for a given history. -/
noncomputable def aixitlBestResult {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (agent : AIXItl Action Percept) (h : BayesianAgents.Core.History Action Percept) : ℝ × Action :=
  bestByValue agent.validatedPrograms h

/-- Steps 4-9: the AIXItl cycle output action. -/
noncomputable def aixitl_cycle {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (agent : AIXItl Action Percept) (h : BayesianAgents.Core.History Action Percept) : Action :=
  (aixitlBestResult agent h).2

theorem aixitlBestResult_eq_compute_of_mem {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (agent : AIXItl Action Percept) (h : BayesianAgents.Core.History Action Percept)
    (hne : agent.validatedPrograms ≠ []) :
    ∃ p ∈ agent.validatedPrograms, aixitlBestResult agent h = p.compute h := by
  simpa [aixitlBestResult] using bestByValue_eq_compute_of_mem (programs := agent.validatedPrograms) (h := h) hne

theorem aixitlBestResult_fst_ge_of_mem {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (agent : AIXItl Action Percept) (h : BayesianAgents.Core.History Action Percept)
    {p : ExtendedChronologicalProgram Action Percept} (hp : p ∈ agent.validatedPrograms) :
    (p.compute h).1 ≤ (aixitlBestResult agent h).1 := by
  simpa [aixitlBestResult] using bestByValue_fst_ge_of_mem (programs := agent.validatedPrograms) (h := h) hp

/-! ## A “real” VA predicate: claims are lower bounds on true value -/

/-- A program's claimed value is a lower bound on its *true* finite-horizon value in environment `μ`. -/
def ValidValueLowerBound {Action : Type uA} {Percept : Type uP} [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (horizon : ℕ)
    (p : ExtendedChronologicalProgram Action Percept) : Prop :=
  ∀ h : BayesianAgents.Core.History Action Percept,
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
      (p.compute h).1 ≤ BayesianAgents.Core.value μ p.toAgent γ h horizon

theorem value_deterministicAgent_succ {Action : Type uA} {Percept : Type uP} [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (act : BayesianAgents.Core.History Action Percept → Action)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h) :
    BayesianAgents.Core.value μ (deterministicAgent act) γ h (n + 1) =
      BayesianAgents.Core.qValue μ (deterministicAgent act) γ h (act h) n := by
  classical
  -- Expand `value` and use the Dirac distribution over actions.
  rw [BayesianAgents.Core.value_succ]
  -- Reduce to a finite sum.
  simp [deterministicAgent, hwf]
  -- Rewrite the summand from an indicator-weighted product to an `ite`.
  have hrewrite :
      (∑ a : Action,
          (if a = act h then (1 : ENNReal) else 0).toReal *
            BayesianAgents.Core.qValue μ (deterministicAgent act) γ h a n) =
        ∑ a : Action, if a = act h then BayesianAgents.Core.qValue μ (deterministicAgent act) γ h a n else 0 := by
    classical
    apply Fintype.sum_congr
    intro a
    by_cases ha : a = act h
    · simp [ha]
    · simp [ha]
  -- Finish by evaluating the `ite` sum.
  calc
    (∑ a : Action,
        (if a = act h then (1 : ENNReal) else 0).toReal *
          BayesianAgents.Core.qValue μ (deterministicAgent act) γ h a n)
        =
        ∑ a : Action, if a = act h then BayesianAgents.Core.qValue μ (deterministicAgent act) γ h a n else 0 := hrewrite
    _ = BayesianAgents.Core.qValue μ (deterministicAgent act) γ h (act h) n := by
        simp

theorem claimed_le_optimalQValue_of_validValueLowerBound {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [Inhabited Action] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    {p : ExtendedChronologicalProgram Action Percept}
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (hvalid : ValidValueLowerBound μ γ (n + 1) p) :
    (p.compute h).1 ≤ BayesianAgents.Core.optimalQValue μ γ h (p.compute h).2 n := by
  -- Start from the validity bound to the program's actual value.
  have hle_value : (p.compute h).1 ≤ BayesianAgents.Core.value μ p.toAgent γ h (n + 1) :=
    hvalid h hwf
  -- Reduce `value` of the induced deterministic policy to a `qValue`.
  have hval :
      BayesianAgents.Core.value μ p.toAgent γ h (n + 1) =
        BayesianAgents.Core.qValue μ p.toAgent γ h (p.compute h).2 n := by
    simpa [ExtendedChronologicalProgram.toAgent, deterministicAgent] using
      (value_deterministicAgent_succ (μ := μ) (γ := γ) (act := fun h' => (p.compute h').2) (h := h) (n := n)
        (hwf := hwf))
  have hle_q : (p.compute h).1 ≤ BayesianAgents.Core.qValue μ p.toAgent γ h (p.compute h).2 n := by
    simpa [hval] using hle_value
  -- Any policy's `qValue` is ≤ the optimal `Q*` value.
  have hq_le :
      BayesianAgents.Core.qValue μ p.toAgent γ h (p.compute h).2 n ≤
        BayesianAgents.Core.optimalQValue μ γ h (p.compute h).2 n := by
    have ih :
        ∀ k, k < n → ∀ h', BayesianAgents.Core.value μ p.toAgent γ h' k ≤ BayesianAgents.Core.optimalValue μ γ h' k := by
      intro k _hk h'
      exact BayesianAgents.Core.value_le_optimalValue (μ := μ) (π := p.toAgent) (γ := γ) (h := h') (n := k)
    exact
      BayesianAgents.Core.qValue_le_optimalQValue_strong (μ := μ) (π := p.toAgent) (γ := γ) (h := h)
        (a := (p.compute h).2) (n := n) ih
  exact le_trans hle_q hq_le

/-! ## ε-optimality of AIXItl’s chosen action (core-generic) -/

theorem aixitl_cycle_eps_optimal {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] [Inhabited Action] [BayesianAgents.Core.PerceptReward Percept]
    (agent : AIXItl Action Percept) (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (hne : agent.validatedPrograms ≠ [])
    (hall : ∀ p ∈ agent.validatedPrograms, ValidValueLowerBound μ γ (n + 1) p)
    (hex :
      ∃ p ∈ agent.validatedPrograms,
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤ (p.compute h).1) :
    BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
      BayesianAgents.Core.optimalQValue μ γ h (aixitl_cycle agent h) n := by
  rcases hex with ⟨p0, hp0, hp0_ge⟩
  have hbest_ge : (p0.compute h).1 ≤ (aixitlBestResult agent h).1 :=
    aixitlBestResult_fst_ge_of_mem (agent := agent) (h := h) hp0
  have hbest_ge' :
      BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
        (aixitlBestResult agent h).1 :=
    le_trans hp0_ge hbest_ge
  rcases aixitlBestResult_eq_compute_of_mem (agent := agent) (h := h) hne with ⟨p, hp, hpEq⟩
  have hvalid : ValidValueLowerBound μ γ (n + 1) p := hall p hp
  have hleQ : (p.compute h).1 ≤ BayesianAgents.Core.optimalQValue μ γ h (p.compute h).2 n :=
    claimed_le_optimalQValue_of_validValueLowerBound (μ := μ) (γ := γ) (h := h) (n := n) (hwf := hwf) hvalid
  have hbest_leQ :
      (aixitlBestResult agent h).1 ≤ BayesianAgents.Core.optimalQValue μ γ h (aixitl_cycle agent h) n := by
    simpa [aixitl_cycle, hpEq] using hleQ
  exact le_trans hbest_ge' hbest_leQ

/-!
## Proof-enumeration scaffolding (Chapter 7, Step 1)

Bitstring enumeration and the basic proof-checker interfaces (`ProofChecker`, `CompleteProofChecker`)
are shared with the toy development and live in `Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration`.
-/

/-! ### AIXItl from a proof checker (abstract Step 1+2 semantics) -/

/-- Step 2: filter programs by the length bound `l` (Step 3 is assumed to be baked into `compute`). -/
def filterAndModify {Action : Type uA} {Percept : Type uP}
    (programs : List (ExtendedChronologicalProgram Action Percept)) (l _t : ℕ) :
    List (ExtendedChronologicalProgram Action Percept) :=
  programs.filter fun p => p.code.length ≤ l

noncomputable def aixitlFromProofChecker {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (horizon : ℕ)
    (checker : ProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ horizon))
    (l l_p t : ℕ) : AIXItl Action Percept :=
  { timeBound := t
    lengthBound := l
    proofLengthBound := l_p
    validatedPrograms := filterAndModify (findValidPrograms checker.decode l_p) l t }

theorem validValueLowerBound_of_mem_aixitlFromProofChecker {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (horizon : ℕ)
    (checker : ProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ horizon))
    (l l_p t : ℕ) {p : ExtendedChronologicalProgram Action Percept}
    (hp : p ∈ (aixitlFromProofChecker μ γ horizon checker l l_p t).validatedPrograms) :
    ValidValueLowerBound μ γ horizon p := by
  have hp' : p ∈ findValidPrograms checker.decode l_p := by
    simp [aixitlFromProofChecker, filterAndModify] at hp
    exact hp.1
  exact ProofChecker.sound_of_mem_findValidPrograms (checker := checker) (ha := hp')

/-! ### ε-optimality from completeness + existence of a good program -/

theorem aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually_of_exists_good_program
    {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (l t : ℕ) (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (checker : CompleteProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ (n + 1)))
    (hex :
      ∃ p : ExtendedChronologicalProgram Action Percept,
        p.code.length ≤ l ∧
          ValidValueLowerBound μ γ (n + 1) p ∧
            BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
              (p.compute h).1) :
    ∃ N, ∀ l_p ≥ N,
      BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
        BayesianAgents.Core.optimalQValue μ γ h
          (aixitl_cycle (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t) h) n := by
  classical
  rcases hex with ⟨p0, hp0_len, hp0_valid, hp0_ge⟩
  rcases checker.exists_bound_forall_mem_findValidPrograms (a := p0) hp0_valid with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro l_p hlp
  -- Show `p0` is in the validated list for this `l_p`.
  have hp0_mem_find : p0 ∈ findValidPrograms checker.decode l_p := hN l_p hlp
  have hp0_mem_validated :
      p0 ∈ (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t).validatedPrograms := by
    simp [aixitlFromProofChecker, filterAndModify, hp0_mem_find, hp0_len]
  have hne :
      (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t).validatedPrograms ≠ [] := by
    intro hnil
    have hp0_mem_validated' := hp0_mem_validated
    simp [hnil] at hp0_mem_validated'
  have hall :
      ∀ p ∈ (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t).validatedPrograms,
        ValidValueLowerBound μ γ (n + 1) p := by
    intro p hp
    exact validValueLowerBound_of_mem_aixitlFromProofChecker (μ := μ) (γ := γ) (horizon := n + 1)
      (checker := checker.toProofChecker) (l := l) (l_p := l_p) (t := t) hp
  have hex' :
      ∃ p ∈ (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t).validatedPrograms,
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
          (p.compute h).1 := ⟨p0, hp0_mem_validated, hp0_ge⟩
  exact
    aixitl_cycle_eps_optimal (agent := aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t)
      (μ := μ) (γ := γ) (h := h) (n := n) (ε := ε) (hwf := hwf) (hne := hne) (hall := hall) (hex := hex')

/-- Convenience wrapper: choose `l := p.code.length` for the good program. -/
theorem aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually_of_exists_good_program'
    {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (t : ℕ) (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (checker : CompleteProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ (n + 1)))
    (hex :
      ∃ p : ExtendedChronologicalProgram Action Percept,
        ValidValueLowerBound μ γ (n + 1) p ∧
          BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤ (p.compute h).1) :
    ∃ l N, ∀ l_p ≥ N,
      BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
        BayesianAgents.Core.optimalQValue μ γ h
          (aixitl_cycle (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t) h) n := by
  classical
  rcases hex with ⟨p, hvalid, hclaim⟩
  refine ⟨p.code.length, ?_⟩
  simpa using
    (aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually_of_exists_good_program (μ := μ) (γ := γ) (l := p.code.length)
      (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
      (hex := ⟨p, le_rfl, hvalid, hclaim⟩))

/-
## Near-optimal verified-program scaffolding (Chapter 7 “long pole”)

Full AIXItl→AIXI convergence needs external assumptions connecting:

- existence of near-optimal *valid* programs (VA/`ValidValueLowerBound`)
- completeness of the proof system (captured here by `CompleteProofChecker`)

The definitions below package those hypotheses in a reusable form for Chapter 6/7 instantiations.
-/

/-- There exists a *verified* program whose claimed value is within `ε` of the optimal value at history `h`. -/
def ExistsNearOptimalVerifiedProgram {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ p : ExtendedChronologicalProgram Action Percept,
    ValidValueLowerBound μ γ (n + 1) p ∧
      BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤ (p.compute h).1

/-- For every `ε > 0`, there exists a verified program that is `ε`-close to optimal at history `h`. -/
def HasNearOptimalVerifiedPrograms {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ExistsNearOptimalVerifiedProgram μ γ h n ε

/-- A global version of `HasNearOptimalVerifiedPrograms`: near-optimal verified programs exist for every well-formed history. -/
def HasNearOptimalVerifiedProgramsForAllHistories {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (n : ℕ) : Prop :=
  ∀ h : BayesianAgents.Core.History Action Percept,
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
      HasNearOptimalVerifiedPrograms μ γ h n

/-- Packaged assumptions for the “AIXItl is `ε`-optimal” schema at fixed horizon `n+1`. -/
structure AIXItlConvergenceAssumptions {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (n : ℕ) where
  checker :
    CompleteProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ (n + 1))
  nearOptimal : HasNearOptimalVerifiedProgramsForAllHistories μ γ n

/-- Convergence assumptions packaged uniformly for all horizons `n`. -/
structure AIXItlConvergenceAssumptionsAllHorizons {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) where
  assumptions : ∀ n : ℕ, AIXItlConvergenceAssumptions (μ := μ) (γ := γ) n

/-- Convergence schema (core-generic): with a complete proof checker and near-optimal verified programs,
there exist bounds `l,l_p` making AIXItl `ε`-optimal at `h`. -/
theorem aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually
    {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (t : ℕ) (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (checker : CompleteProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ (n + 1)))
    (hex : HasNearOptimalVerifiedPrograms μ γ h n) :
    0 < ε →
      ∃ l N, ∀ l_p ≥ N,
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
          BayesianAgents.Core.optimalQValue μ γ h
            (aixitl_cycle (aixitlFromProofChecker μ γ (n + 1) checker.toProofChecker l l_p t) h) n := by
  intro hε
  rcases hex ε hε with ⟨p, hpValid, hpClaim⟩
  exact
    aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually_of_exists_good_program'
      (μ := μ) (γ := γ) (t := t) (h := h) (n := n) (ε := ε) (hwf := hwf) (checker := checker)
      (hex := ⟨p, hpValid, hpClaim⟩)

/-- Convenience: derive ε-optimality from packaged convergence assumptions. -/
theorem aixitlFromAIXItlConvergenceAssumptions_cycle_eps_optimal_eventually
    {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (t : ℕ) (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (assumptions : AIXItlConvergenceAssumptions (μ := μ) (γ := γ) n) :
    0 < ε →
      ∃ l N, ∀ l_p ≥ N,
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
          BayesianAgents.Core.optimalQValue μ γ h
            (aixitl_cycle
              (aixitlFromProofChecker μ γ (n + 1) assumptions.checker.toProofChecker l l_p t) h) n := by
  intro hε
  have hex : HasNearOptimalVerifiedPrograms μ γ h n :=
    assumptions.nearOptimal h hwf
  exact
    aixitlFromCompleteProofChecker_cycle_eps_optimal_eventually (μ := μ) (γ := γ) (t := t) (h := h) (n := n)
      (ε := ε) (hwf := hwf) (checker := assumptions.checker) (hex := hex) hε

/-! ## Infinite-horizon limit (measure-theoretic core) -/

section InfiniteHorizon

universe u

theorem valueFromMeasure_tendsto
    {Action Percept : Type u} [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (π : BayesianAgents.Core.Agent Action Percept)
    (γ : BayesianAgents.Core.DiscountFactor)
    (h_stoch : Mettapedia.UniversalAI.BayesianAgents.Core.InfiniteHistoryCompat.isStochastic μ)
    (h_lt : γ.val < 1) :
    Filter.Tendsto
        (fun t =>
          Mettapedia.UniversalAI.BayesianAgents.Core.InfiniteHistoryCompat.valueFromMeasure
            (Action := Action) (Percept := Percept) μ π γ h_stoch t)
        Filter.atTop
        (nhds
          (Mettapedia.UniversalAI.BayesianAgents.Core.InfiniteHistoryCompat.valueFromMeasureInf
            (Action := Action) (Percept := Percept) μ π γ h_stoch)) := by
  simpa using
    (Mettapedia.UniversalAI.BayesianAgents.Core.InfiniteHistoryCompat.tendsto_valueFromMeasure
      (Action := Action) (Percept := Percept) (μ := μ) (π := π) (γ := γ)
      (h_stoch := h_stoch) (h_lt := h_lt))

end InfiniteHorizon

end Mettapedia.UniversalAI.TimeBoundedAIXI.Core
