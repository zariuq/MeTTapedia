import Mettapedia.InformationTheory.KnowledgeQuantification.Entropic
import Mettapedia.GSLT.Causality.StructuralModels

/-!
# Causal knowledge

D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6: 181055
(2019), §2.3.3, values causal knowledge with eq. 2.27: the input is set rather than
measured, so it costs no information, while the method of setting it, `τ_do`, adds to the
theory.  Eq. 2.27 keeps the observational conditional entropy `H(Y | X, τ)` in the
numerator.  Under confounding that is the wrong quantity: the numerator of causal knowledge
is the information the *interventional* law carries, the mutual information of the design
law of the set input and the kernel `x ↦ P(Y | do(X = x))`.

* `FiniteSystem.intervention`: the interventional system, with no input cost and theory
  length `L(τ) + L(τ_do)`.
* `FiniteSystem.intervention_knowledge_eq_zero_of_const`: an intervention that never moves
  the explanandum gives zero causal knowledge.
* `FiniteSystem.knowledge_lt_intervention_iff`: when the interventional law is the
  observational one, setting beats measuring exactly when the method is shorter than the
  input it replaces; with as many inputs as explananda this is the paper's threshold
  `n_Y > L(τ_do) / H(X)` (`knowledge_lt_intervention_iff_uses`).

The interventional kernel of a structural model is the exogenous law pushed through the
solution of the surgical model (`StructuralModels.surgery`, the `do` of the causal
development, which `DoCalculus.TruncatedFactorization` identifies with the truncated
factorization):

* `doKernel`, with `solveUnder_isSolution`: the pushed store solves the surgical model;
* `intervention_knowledge_eq_zero_of_not_cause`: if setting the source never changes the
  solved target, causal knowledge is zero, whatever the observational dependence;
* `confounded_correlation_without_causation`: one exogenous bit drives both treatment and
  outcome.  The observational joint law is an exact copy of a fair bit, with positive
  knowledge, and causal knowledge is zero;
* `direct_causal_knowledge`: when the outcome copies the treatment, the interventional
  kernel is the identity and causal knowledge is positive.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.GSLT.Causality.StructuralModels

namespace FiniteSystem

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- **The interventional system** (eq. 2.27, with the interventional kernel).  The input is
set by the design law rather than measured, so it costs nothing; the method of setting it
costs `methodLength` beyond the theory. -/
def intervention (design : Prob X) (doKernel : X → Prob Y)
    (explananda theoryLength methodLength : ℝ) : FiniteSystem X Y :=
  ⟨design, doKernel, explananda, 0, theoryLength + methodLength⟩

theorem intervention_budget_input (design : Prob X) (doKernel : X → Prob Y)
    (explananda theoryLength methodLength : ℝ) :
    (intervention design doKernel explananda theoryLength methodLength).budget.input = 0 := by
  simp [intervention, budget]

/-- An intervention that never moves the explanandum gives zero causal knowledge. -/
theorem intervention_knowledge_eq_zero_of_const (design : Prob X) (r : Prob Y)
    (explananda theoryLength methodLength : ℝ) :
    (intervention design (fun _ => r) explananda theoryLength methodLength).knowledge = 0 :=
  (intervention design (fun _ => r) explananda theoryLength methodLength).knowledge_eq_zero_of_const
    r rfl

/-- **Setting against measuring** (eq. 2.27).  When the interventional law is the
observational one, the interventional system holds more knowledge exactly when the method
of setting the input is shorter than the input it replaces. -/
theorem knowledge_lt_intervention_iff (s : FiniteSystem X Y) {methodLength : ℝ}
    (hexpl : 0 < s.budget.explained) (htot : 0 < s.budget.total)
    (htot' : 0 < (intervention s.inputLaw s.kernel s.explananda s.theoryLength
      methodLength).budget.total) :
    s.knowledge <
        (intervention s.inputLaw s.kernel s.explananda s.theoryLength methodLength).knowledge ↔
      methodLength < s.inputs * shannonEntropyFin X s.inputLaw := by
  have hexpl' : (intervention s.inputLaw s.kernel s.explananda s.theoryLength
      methodLength).budget.explained = s.budget.explained := rfl
  unfold knowledge Budget.knowledge
  rw [hexpl', div_lt_div_iff_of_pos_left hexpl htot htot']
  unfold Budget.total budget intervention explanandumLaw
  dsimp only
  constructor <;> intro h <;> linarith

/-- The paper's threshold: with as many inputs as explananda, setting beats measuring
exactly when `n_Y > L(τ_do) / H(X)`. -/
theorem knowledge_lt_intervention_iff_uses (s : FiniteSystem X Y) {methodLength : ℝ}
    (huses : s.inputs = s.explananda) (hH : 0 < shannonEntropyFin X s.inputLaw)
    (hexpl : 0 < s.budget.explained) (htot : 0 < s.budget.total)
    (htot' : 0 < (intervention s.inputLaw s.kernel s.explananda s.theoryLength
      methodLength).budget.total) :
    s.knowledge <
        (intervention s.inputLaw s.kernel s.explananda s.theoryLength methodLength).knowledge ↔
      methodLength / shannonEntropyFin X s.inputLaw < s.explananda := by
  rw [s.knowledge_lt_intervention_iff hexpl htot htot', huses, div_lt_iff₀ hH]

end FiniteSystem

/-! ## Interventions on structural models -/

section Structural

variable {Ω Key Value : Type} [Fintype Ω] [Fintype Value] [DecidableEq Value]
  [DecidableEq Key]

/-- The store solving a recursive model after the surgery `assignment`, reached by
updating as many times as the rank bound. -/
def solveUnder {mech : Mechanisms Key Value} (rec : Recursive mech)
    (assignment : Key → Option Value) (seed : Key → Value) : Key → Value :=
  (update (surgery assignment mech))^[rec.bound] seed

omit [Fintype Value] [DecidableEq Value] [DecidableEq Key] in
theorem solveUnder_isSolution {mech : Mechanisms Key Value} (rec : Recursive mech)
    (assignment : Key → Option Value) (seed : Key → Value) :
    IsSolution (surgery assignment mech) (solveUnder rec assignment seed) :=
  iterate_isSolution (recursive_surgery rec assignment) seed

omit [Fintype Value] [DecidableEq Value] [DecidableEq Key] in
/-- The solved store does not depend on the seed. -/
theorem solveUnder_seed {mech : Mechanisms Key Value} (rec : Recursive mech)
    (assignment : Key → Option Value) (seed seed' : Key → Value) :
    solveUnder rec assignment seed = solveUnder rec assignment seed' :=
  solution_unique (recursive_surgery rec assignment) (solveUnder_isSolution rec assignment seed)
    (solveUnder_isSolution rec assignment seed')

omit [Fintype Value] [DecidableEq Value] in
/-- The assignment setting one key. -/
def setKey (key : Key) (v : Value) : Key → Option Value :=
  fun k => if k = key then some v else none

/-- **The interventional kernel** of a structural model with exogenous law `noise`: the law
of `target` under `do(source = v)`. -/
def doKernel (noise : Prob Ω) {mech : Ω → Mechanisms Key Value}
    (rec : ∀ ω, Recursive (mech ω)) (seed : Key → Value) (source target : Key) (v : Value) :
    Prob Value :=
  Prob.coarsen noise fun ω => solveUnder (rec ω) (setKey source v) seed target

/-- The observational law of `target`: the solution without surgery. -/
def observedLaw (noise : Prob Ω) {mech : Ω → Mechanisms Key Value}
    (rec : ∀ ω, Recursive (mech ω)) (seed : Key → Value) (target : Key) : Prob Value :=
  Prob.coarsen noise fun ω => solveUnder (rec ω) (fun _ => none) seed target

/-- **Not a cause, no causal knowledge.**  If setting `source` never changes the solved
`target`, every interventional law is the observational law of `target`, so causal
knowledge is zero, whatever the observational dependence. -/
theorem intervention_knowledge_eq_zero_of_not_cause (noise : Prob Ω)
    {mech : Ω → Mechanisms Key Value} (rec : ∀ ω, Recursive (mech ω)) (seed : Key → Value)
    (source target : Key) (design : Prob Value) (explananda theoryLength methodLength : ℝ)
    (notCause : ∀ ω v, solveUnder (rec ω) (setKey source v) seed target =
      solveUnder (rec ω) (fun _ => none) seed target) :
    (FiniteSystem.intervention design (doKernel noise rec seed source target) explananda
      theoryLength methodLength).knowledge = 0 := by
  have hconst : doKernel noise rec seed source target =
      fun _ => observedLaw noise rec seed target := by
    funext v
    unfold doKernel observedLaw
    congr 1
    funext ω
    exact notCause ω v
  rw [hconst]
  exact FiniteSystem.intervention_knowledge_eq_zero_of_const design _ explananda theoryLength
    methodLength

/-- A constant view pushes every law to the point mass. -/
theorem coarsen_const (noise : Prob Ω) (v : Value) :
    Prob.coarsen noise (fun _ => v) = Prob.dirac v := by
  apply Subtype.ext
  funext a
  rw [Prob.coarsen_apply, pushforward_eq_sum_ite, Prob.dirac_apply]
  by_cases h : v = a
  · subst h
    simp [noise.2.2]
  · have h' : a ≠ v := fun e => h e.symm
    simp [h, h']

end Structural

/-! ## Two structural models on one exogenous bit -/

/-- The endogenous keys: a treatment and an outcome. -/
inductive PairKey where
  | treatment
  | outcome
  deriving DecidableEq

/-- A common cause: the exogenous bit sets both treatment and outcome. -/
def confounded (u : Fin 2) : Mechanisms PairKey (Fin 2) := fun _ _ => u

def confoundedRecursive (u : Fin 2) : Recursive (confounded u) where
  rank _ := 0
  bound := 1
  rank_lt _ := Nat.zero_lt_one
  depends _ _ _ _ := rfl

theorem confounded_solve (u : Fin 2) (assignment : PairKey → Option (Fin 2))
    (seed : PairKey → Fin 2) (key : PairKey) :
    solveUnder (confoundedRecursive u) assignment seed key = (assignment key).getD u := rfl

/-- In the confounded pair the treatment does not cause the outcome. -/
theorem confounded_not_cause (u : Fin 2) (v : Fin 2) (seed : PairKey → Fin 2) :
    solveUnder (confoundedRecursive u) (setKey .treatment v) seed .outcome =
      solveUnder (confoundedRecursive u) (fun _ => none) seed .outcome := by
  rw [confounded_solve, confounded_solve]
  rfl

/-- The observational joint law of treatment and outcome in the confounded pair is an exact
copy of a fair bit. -/
theorem confounded_observational_joint (seed : PairKey → Fin 2) :
    Prob.coarsen binaryUniform (fun u =>
        (solveUnder (confoundedRecursive u) (fun _ => none) seed .treatment,
          solveUnder (confoundedRecursive u) (fun _ => none) seed .outcome)) =
      joint binaryUniform Prob.dirac := by
  apply Subtype.ext
  funext ab
  obtain ⟨a, b⟩ := ab
  simp only [confounded_solve, Option.getD_none]
  rw [Prob.coarsen_apply, pushforward_eq_sum_ite, joint_apply, Prob.dirac_apply,
    Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;>
    simp [binaryUniform_apply_zero, binaryUniform_apply_one]

/-- **Correlation without causation** (§2.3.3).  One exogenous bit sets treatment and outcome.
The observational joint law is the exact copy of a fair bit, whose knowledge is positive;
setting the treatment never moves the outcome, so causal knowledge is zero. -/
theorem confounded_correlation_without_causation (seed : PairKey → Fin 2) {L : ℝ} (hL : 0 ≤ L)
    (methodLength : ℝ) :
    Prob.coarsen binaryUniform (fun u =>
        (solveUnder (confoundedRecursive u) (fun _ => none) seed .treatment,
          solveUnder (confoundedRecursive u) (fun _ => none) seed .outcome)) =
        joint (copyBit L).inputLaw (copyBit L).kernel ∧
      0 < (copyBit L).knowledge ∧
      (FiniteSystem.intervention binaryUniform
        (doKernel binaryUniform confoundedRecursive seed .treatment .outcome) 1 L
          methodLength).knowledge = 0 :=
  ⟨confounded_observational_joint seed, copyBit_knowledge_pos hL,
    intervention_knowledge_eq_zero_of_not_cause binaryUniform confoundedRecursive seed
      .treatment .outcome binaryUniform 1 L methodLength
      (fun u v => confounded_not_cause u v seed)⟩

/-- A direct effect: the exogenous bit sets the treatment and the outcome copies it. -/
def direct (u : Fin 2) : Mechanisms PairKey (Fin 2)
  | .treatment => fun _ => u
  | .outcome => fun store => store .treatment

def directRank : PairKey → ℕ
  | .treatment => 0
  | .outcome => 1

def directRecursive (u : Fin 2) : Recursive (direct u) where
  rank := directRank
  bound := 2
  rank_lt key := by cases key <;> decide
  depends key store store' agree := by
    cases key with
    | treatment => rfl
    | outcome =>
        exact agree .treatment (by
          change directRank PairKey.treatment < directRank PairKey.outcome
          decide)

theorem direct_solve_outcome (u v : Fin 2) (seed : PairKey → Fin 2) :
    solveUnder (directRecursive u) (setKey .treatment v) seed .outcome = v := rfl

/-- The interventional kernel of the direct effect is the identity. -/
theorem direct_doKernel (seed : PairKey → Fin 2) :
    doKernel binaryUniform directRecursive seed .treatment .outcome = Prob.dirac := by
  funext v
  unfold doKernel
  simp only [direct_solve_outcome]
  exact coarsen_const binaryUniform v

/-- **A cause gives causal knowledge.**  Setting the treatment fixes the outcome, so the
interventional system is an exact copy with no input cost. -/
theorem direct_causal_knowledge (seed : PairKey → Fin 2) {L methodLength : ℝ} (hL : 0 ≤ L)
    (hm : 0 ≤ methodLength) :
    (FiniteSystem.intervention binaryUniform
        (doKernel binaryUniform directRecursive seed .treatment .outcome) 1 L
          methodLength).knowledge =
      Real.log 2 / (Real.log 2 + (L + methodLength)) ∧
    0 < (FiniteSystem.intervention binaryUniform
        (doKernel binaryUniform directRecursive seed .treatment .outcome) 1 L
          methodLength).knowledge := by
  rw [direct_doKernel]
  have hbudget : (FiniteSystem.intervention binaryUniform Prob.dirac 1 L methodLength).budget =
      ⟨Real.log 2, 0, 0, L + methodLength⟩ := by
    have hlaw : (FiniteSystem.intervention binaryUniform Prob.dirac 1 L
        methodLength).explanandumLaw = binaryUniform :=
      Prob.bind_dirac_right binaryUniform
    have hcond : conditionalEntropy binaryUniform (Prob.dirac : Fin 2 → Prob (Fin 2)) = 0 := by
      unfold conditionalEntropy
      simp [shannonEntropyFin_dirac]
    unfold FiniteSystem.budget
    rw [hlaw]
    simp [FiniteSystem.intervention, hcond, shannonEntropy_binaryUniform]
  have hK : (FiniteSystem.intervention binaryUniform Prob.dirac 1 L methodLength).knowledge =
      Real.log 2 / (Real.log 2 + (L + methodLength)) := by
    unfold FiniteSystem.knowledge
    rw [hbudget]
    unfold Budget.knowledge Budget.explained Budget.total
    dsimp only
    ring_nf
  refine ⟨hK, ?_⟩
  rw [hK]
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact div_pos hlog (by linarith)

end Mettapedia.InformationTheory.KnowledgeQuantification
