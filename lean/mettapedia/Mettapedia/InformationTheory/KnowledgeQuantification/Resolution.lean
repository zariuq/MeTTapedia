import Mettapedia.InformationTheory.KnowledgeQuantification.Entropic

/-!
# Resolution and data processing

D. Fanelli, *A theory and methodology to quantify knowledge*, R. Soc. open sci. 6: 181055
(2019), §§2.3.5–2.3.6 and appendices D–E, studies how knowledge changes when the resolution
of a system changes or the system drifts away from the one a theory was fitted to.

* `shannonEntropyFin_coarsen_le` and `shannonEntropyFin_le_coarsen_add_log`: observing a
  variable through a map whose fibres have at most `q` points lowers its entropy by at most
  `log q`, and never raises it (eq. E 1).
* `shannonEntropyFin_coarsen_dirac`: the lower bound is attained: refining a point mass adds
  no entropy, so the strict inequality `0 < H(X^{a'}) − H(X^a)` of eq. E 1 is false in
  general.
* The resolution conditions themselves (eqs. E 5–E 7) are `Budget.knowledge_lt_iff_residual_change`.
* `FiniteSystem.coarsenExplanandum_explained_le`: observing the explanandum through a map
  cannot raise the explained information (the data processing inequality of appendix D,
  through the tree's `expectedInformationGain_coarsen_le`);
  `FiniteSystem.coarsenExplanandum_knowledge_le`: if the explanandum keeps its entropy, `K`
  does not rise.

The paper's further claims that every empirical system has a unique optimal resolution
(eq. 2.31, appendix E) and that knowledge declines exponentially with distance (eq. 2.29,
appendix D) are not theorems: over finitely many resolutions a best one exists trivially but
need not be unique, and eq. 2.29 defines the decline rate `λ` rather than proving a law.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Finset Real
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.BayesianInference

/-! ## Entropy under coarsening -/

/-- Merging outcomes cannot raise their total `negMulLog`. -/
theorem negMulLog_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, negMulLog (f i) := by
  rw [Real.negMulLog, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Real.negMulLog, neg_mul, neg_le_neg_iff]
  rcases (hf i hi).lt_or_eq with hpos | hzero
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hpos (Finset.single_le_sum hf hi)) hpos.le
  · rw [← hzero]
    simp

/-- Splitting a mass over `|s|` outcomes raises its `negMulLog` by at most the mass times
`log |s|`. -/
theorem sum_negMulLog_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, negMulLog (f i) ≤
      negMulLog (∑ i ∈ s, f i) + (∑ i ∈ s, f i) * Real.log s.card := by
  rcases (Finset.sum_nonneg hf).lt_or_eq with hP | hP
  · have hne : s.Nonempty := Finset.nonempty_of_sum_ne_zero hP.ne'
    have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.2 hne
    have hls := sum_mul_log_le_klSumOn s f (fun _ => 1) hf (fun _ _ => zero_le_one)
      (fun _ _ _ => one_pos)
    simp only [klSumOn, div_one, Finset.sum_const, nsmul_eq_mul, mul_one] at hls
    rw [Real.log_div hP.ne' hcard.ne', mul_sub] at hls
    have hneg : ∑ i ∈ s, negMulLog (f i) = -∑ i ∈ s, f i * Real.log (f i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.negMulLog, neg_mul]
    rw [hneg, Real.negMulLog]
    linarith
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg hf).1 hP.symm
    rw [← hP]
    simp only [negMulLog_zero, zero_mul, add_zero]
    exact le_of_eq (Finset.sum_eq_zero fun i hi => by rw [hall i hi, negMulLog_zero])

variable {Y C : Type*} [Fintype Y] [Fintype C] [DecidableEq C]

/-- **Coarsening cannot raise entropy.** -/
theorem shannonEntropyFin_coarsen_le (p : Prob Y) (view : Y → C) :
    shannonEntropyFin C (Prob.coarsen p view) ≤ shannonEntropyFin Y p := by
  unfold shannonEntropyFin
  rw [← Finset.sum_fiberwise Finset.univ view (fun y => negMulLog (p.1 y))]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Prob.coarsen_apply]
  exact negMulLog_sum_le _ _ fun y _ => p.2.1 y

/-- **Refining a resolution `q`-fold adds at most `log q`** (eq. E 1). -/
theorem shannonEntropyFin_le_coarsen_add_log (p : Prob Y) (view : Y → C) {q : ℕ}
    (hq : ∀ c, (Finset.univ.filter fun y => view y = c).card ≤ q) :
    shannonEntropyFin Y p ≤ shannonEntropyFin C (Prob.coarsen p view) + Real.log q := by
  unfold shannonEntropyFin
  rw [← Finset.sum_fiberwise Finset.univ view (fun y => negMulLog (p.1 y))]
  have hfiber : ∀ c, ∑ y ∈ Finset.univ.filter (fun y => view y = c), negMulLog (p.1 y) ≤
      negMulLog ((Prob.coarsen p view).1 c) + (Prob.coarsen p view).1 c * Real.log q := by
    intro c
    refine (sum_negMulLog_le _ _ fun y _ => p.2.1 y).trans ?_
    rw [Prob.coarsen_apply]
    change negMulLog (pushforward p.1 view c) +
        pushforward p.1 view c * Real.log (Finset.univ.filter fun y => view y = c).card ≤
      negMulLog (pushforward p.1 view c) + pushforward p.1 view c * Real.log q
    have hlog : Real.log (Finset.univ.filter fun y => view y = c).card ≤ Real.log q := by
      rcases Nat.eq_zero_or_pos (Finset.univ.filter fun y => view y = c).card with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg q
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hq c)
    have := mul_le_mul_of_nonneg_left hlog (pushforward_nonneg p.1 p.2.1 view c)
    linarith
  calc ∑ c, ∑ y ∈ Finset.univ.filter (fun y => view y = c), negMulLog (p.1 y)
      ≤ ∑ c, (negMulLog ((Prob.coarsen p view).1 c) +
          (Prob.coarsen p view).1 c * Real.log q) := Finset.sum_le_sum fun c _ => hfiber c
    _ = ∑ c, negMulLog ((Prob.coarsen p view).1 c) + Real.log q := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, (Prob.coarsen p view).2.2, one_mul]

/-- **The lower bound is attained**: a point mass gains no entropy from refinement, so the
strict lower bound of eq. E 1 fails. -/
theorem shannonEntropyFin_coarsen_dirac [DecidableEq Y] (y : Y) (view : Y → C) :
    shannonEntropyFin C (Prob.coarsen (Prob.dirac y) view) =
      shannonEntropyFin Y (Prob.dirac y) := by
  rw [Prob.coarsen_dirac, shannonEntropyFin_dirac, shannonEntropyFin_dirac]

/-! ## Data processing -/

namespace FiniteSystem

variable {X : Type*} [Fintype X]

/-- The system with its explanandum observed through `view`. -/
def coarsenExplanandum (s : FiniteSystem X Y) (view : Y → C) : FiniteSystem X C :=
  ⟨s.inputLaw, fun x => Prob.coarsen (s.kernel x) view, s.explananda, s.inputs,
    s.theoryLength⟩

theorem coarsenExplanandum_explanandumLaw (s : FiniteSystem X Y) (view : Y → C) :
    (s.coarsenExplanandum view).explanandumLaw = Prob.coarsen s.explanandumLaw view :=
  (Prob.coarsen_bind s.inputLaw s.kernel view).symm

/-- **Data processing** (appendix D): observing the explanandum through a map cannot raise
the explained information. -/
theorem coarsenExplanandum_explained_le (s : FiniteSystem X Y) (view : Y → C)
    (hY : 0 ≤ s.explananda) :
    (s.coarsenExplanandum view).budget.explained ≤ s.budget.explained := by
  classical
  rw [budget_explained, budget_explained]
  exact mul_le_mul_of_nonneg_left
    (expectedInformationGain_coarsen_le s.inputLaw s.kernel view) hY

/-- If the coarsened explanandum keeps its entropy, knowledge does not rise. -/
theorem coarsenExplanandum_knowledge_le (s : FiniteSystem X Y) (view : Y → C)
    (hY : 0 < s.explananda) (htot : 0 < s.budget.total)
    (hentropy : shannonEntropyFin C (s.coarsenExplanandum view).explanandumLaw =
      shannonEntropyFin Y s.explanandumLaw) :
    (s.coarsenExplanandum view).knowledge ≤ s.knowledge := by
  have hexpl := s.coarsenExplanandum_explained_le view hY.le
  have hnonneg : 0 ≤ (s.coarsenExplanandum view).budget.explained := by
    classical
    rw [budget_explained]
    exact mul_nonneg hY.le (expectedInformationGain_nonneg _ _)
  have htotal : (s.coarsenExplanandum view).budget.total = s.budget.total := by
    unfold Budget.total budget
    dsimp only
    rw [hentropy]
    rfl
  exact Budget.knowledge_le_knowledge_of_le htot hnonneg hexpl htotal.ge

end FiniteSystem

end Mettapedia.InformationTheory.KnowledgeQuantification
