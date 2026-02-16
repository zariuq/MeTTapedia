import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNBayesNetWorldModel
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

/-!
# Exact BN Query Answering from PLN CPT Evidence (Boolean Case)

This module connects the PLN BN world-model sublayer (CPT evidence counts)
to **exact BN query answering** via variable elimination.

Key idea:
* CPT evidence is stored as `Evidence` per CPT entry.
* Convert each CPT entry into a Bernoulli PMF using `Evidence.toStrength`.
* Use the existing VE engine to answer prop/link queries exactly for the BN class.

This is the first concrete instance of the “BN sublayer = tractable WM class” story.
-/

namespace Mettapedia.Logic.PLNBayesNetInference

open scoped Classical BigOperators ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNBayesNetWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

/-! ## Bernoulli PMF from ENNReal probability -/

noncomputable def bernoulliPMF (p : ℝ≥0∞) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => if b then p else 1 - p) (by
    classical
    have hsum : (∑ b : Bool, (if b then p else 1 - p)) = p + (1 - p) := by
      simp
    have hsum' : p + (1 - p) = 1 := by
      simpa [add_comm] using (tsub_add_cancel_of_le hp)
    simp [hsum'])

/-! ## Binary Naive Bayes as Evidence-Product -/

section NaiveBayes

variable {ι : Type*}

/-- Binary NB in evidence form: prior evidence multiplied by per-feature likelihood evidence. -/
noncomputable def nbEvidence [Fintype ι] (prior : Evidence) (likelihood : ι → Evidence) : Evidence :=
  prior * ∏ i, likelihood i

/-- Textbook binary NB posterior from class masses and conditionally-independent features. -/
noncomputable def nbPosterior
    [Fintype ι]
    (priorPos priorNeg : ℝ≥0∞) (likePos likeNeg : ι → ℝ≥0∞) : ℝ≥0∞ :=
  let numPos := priorPos * ∏ i, likePos i
  let numNeg := priorNeg * ∏ i, likeNeg i
  if numPos + numNeg = 0 then 0 else numPos / (numPos + numNeg)

private lemma prod_pos (s : Finset ι) (f : ι → Evidence) :
    (Finset.prod s f).pos = Finset.prod s (fun i => (f i).pos) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rfl
  | @insert a s ha ih =>
      simp [ha, ih, Evidence.tensor_def]

private lemma prod_neg (s : Finset ι) (f : ι → Evidence) :
    (Finset.prod s f).neg = Finset.prod s (fun i => (f i).neg) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rfl
  | @insert a s ha ih =>
      simp [ha, ih, Evidence.tensor_def]

theorem nbEvidence_pos [Fintype ι] (prior : Evidence) (likelihood : ι → Evidence) :
    (nbEvidence prior likelihood).pos =
      prior.pos * Finset.univ.prod (fun i => (likelihood i).pos) := by
  classical
  unfold nbEvidence
  simp [Evidence.tensor_def, prod_pos]

theorem nbEvidence_neg [Fintype ι] (prior : Evidence) (likelihood : ι → Evidence) :
    (nbEvidence prior likelihood).neg =
      prior.neg * Finset.univ.prod (fun i => (likelihood i).neg) := by
  classical
  unfold nbEvidence
  simp [Evidence.tensor_def, prod_neg]

private lemma toOdds_prod_finset
    (s : Finset ι) (likelihood : ι → Evidence)
    (hneg : ∀ i, i ∈ s → (likelihood i).neg ≠ 0) :
    Evidence.toOdds (Finset.prod s (fun i => likelihood i)) =
      Finset.prod s (fun i => Evidence.toOdds (likelihood i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      change Evidence.toOdds ({ pos := 1, neg := 1 } : Evidence) = 1
      simp [Evidence.toOdds]
  | @insert a s ha ih =>
      have ha_neg : (likelihood a).neg ≠ 0 := hneg a (by simp)
      have hs_neg : ∀ i, i ∈ s → (likelihood i).neg ≠ 0 := by
        intro i hi
        exact hneg i (by simp [hi])
      have hprod_neg : (Finset.prod s (fun i => likelihood i)).neg ≠ 0 := by
        have hs_prod_ne_zero : Finset.prod s (fun i => (likelihood i).neg) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr ?_
          intro i hi
          exact hs_neg i hi
        simpa [prod_neg] using hs_prod_ne_zero
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [Evidence.toOdds_tensor_mul
        (x := likelihood a)
        (y := Finset.prod s (fun i => likelihood i))
        ha_neg hprod_neg]
      rw [ih hs_neg]

private lemma toLogOdds_prod_finset
    (s : Finset ι) (likelihood : ι → Evidence)
    (hneg : ∀ i, i ∈ s → (likelihood i).neg ≠ 0)
    (hodds0 : ∀ i, i ∈ s → Evidence.toOdds (likelihood i) ≠ 0)
    (hoddsTop : ∀ i, i ∈ s → Evidence.toOdds (likelihood i) ≠ ⊤) :
    Evidence.toLogOdds (Finset.prod s (fun i => likelihood i)) =
      Finset.sum s (fun i => Evidence.toLogOdds (likelihood i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      change Evidence.toLogOdds ({ pos := 1, neg := 1 } : Evidence) = 0
      simp [Evidence.toLogOdds, Evidence.toOdds]
  | @insert a s ha ih =>
      have ha_neg : (likelihood a).neg ≠ 0 := hneg a (by simp)
      have ha_odds0 : Evidence.toOdds (likelihood a) ≠ 0 := hodds0 a (by simp)
      have ha_oddsTop : Evidence.toOdds (likelihood a) ≠ ⊤ := hoddsTop a (by simp)
      have hs_neg : ∀ i, i ∈ s → (likelihood i).neg ≠ 0 := by
        intro i hi
        exact hneg i (by simp [hi])
      have hs_odds0 : ∀ i, i ∈ s → Evidence.toOdds (likelihood i) ≠ 0 := by
        intro i hi
        exact hodds0 i (by simp [hi])
      have hs_oddsTop : ∀ i, i ∈ s → Evidence.toOdds (likelihood i) ≠ ⊤ := by
        intro i hi
        exact hoddsTop i (by simp [hi])
      have hprod_neg : (Finset.prod s (fun i => likelihood i)).neg ≠ 0 := by
        have hs_prod_ne_zero : Finset.prod s (fun i => (likelihood i).neg) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr ?_
          intro i hi
          exact hs_neg i hi
        simpa [prod_neg] using hs_prod_ne_zero
      have hprod_odds :
          Evidence.toOdds (Finset.prod s (fun i => likelihood i))
            = Finset.prod s (fun i => Evidence.toOdds (likelihood i)) :=
        toOdds_prod_finset (s := s) (likelihood := likelihood) hs_neg
      have hprod_odds0 : Evidence.toOdds (Finset.prod s (fun i => likelihood i)) ≠ 0 := by
        rw [hprod_odds]
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro i hi
        exact hs_odds0 i hi
      have hprod_oddsTop : Evidence.toOdds (Finset.prod s (fun i => likelihood i)) ≠ ⊤ := by
        rw [hprod_odds]
        exact ENNReal.prod_ne_top (by
          intro i hi
          exact hs_oddsTop i hi)
      calc
        Evidence.toLogOdds (Finset.prod (insert a s) (fun i => likelihood i))
            = Evidence.toLogOdds (likelihood a * (Finset.prod s (fun i => likelihood i))) := by
                simp [Finset.prod_insert, ha]
        _ = Evidence.toLogOdds (likelihood a) + Evidence.toLogOdds (Finset.prod s (fun i => likelihood i)) := by
              exact Evidence.toLogOdds_tensor_add
                (x := likelihood a) (y := Finset.prod s (fun i => likelihood i))
                ha_neg hprod_neg ha_odds0 hprod_odds0 ha_oddsTop hprod_oddsTop
        _ = Evidence.toLogOdds (likelihood a) + Finset.sum s (fun i => Evidence.toLogOdds (likelihood i)) := by
              rw [ih hs_neg hs_odds0 hs_oddsTop]
        _ = Finset.sum (insert a s) (fun i => Evidence.toLogOdds (likelihood i)) := by
              simp [Finset.sum_insert, ha]

/-- Odds decomposition for binary NB evidence:
prior odds times product of per-feature odds. -/
theorem toOdds_nbEvidence_mul
    [Fintype ι]
    (prior : Evidence) (likelihood : ι → Evidence)
    (hprior_neg : prior.neg ≠ 0)
    (hlik_neg : ∀ i, (likelihood i).neg ≠ 0) :
    Evidence.toOdds (nbEvidence prior likelihood)
      = Evidence.toOdds prior * ∏ i, Evidence.toOdds (likelihood i) := by
  classical
  unfold nbEvidence
  have hprod_neg : (∏ i, likelihood i).neg ≠ 0 := by
    have hs_prod_ne_zero : (∏ i : ι, (likelihood i).neg) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i hi
      exact hlik_neg i
    simpa [prod_neg] using hs_prod_ne_zero
  rw [Evidence.toOdds_tensor_mul (x := prior) (y := ∏ i, likelihood i) hprior_neg hprod_neg]
  rw [toOdds_prod_finset (s := Finset.univ) (likelihood := likelihood) (by
    intro i hi
    exact hlik_neg i)]

/-- Log-odds decomposition for binary NB evidence:
prior log-odds plus sum of per-feature log-odds. -/
theorem toLogOdds_nbEvidence_add
    [Fintype ι]
    (prior : Evidence) (likelihood : ι → Evidence)
    (hprior_neg : prior.neg ≠ 0)
    (hprior_odds0 : Evidence.toOdds prior ≠ 0)
    (hprior_oddsTop : Evidence.toOdds prior ≠ ⊤)
    (hlik_neg : ∀ i, (likelihood i).neg ≠ 0)
    (hlik_odds0 : ∀ i, Evidence.toOdds (likelihood i) ≠ 0)
    (hlik_oddsTop : ∀ i, Evidence.toOdds (likelihood i) ≠ ⊤) :
    Evidence.toLogOdds (nbEvidence prior likelihood)
      = Evidence.toLogOdds prior + ∑ i, Evidence.toLogOdds (likelihood i) := by
  classical
  unfold nbEvidence
  have hprod_neg : (∏ i, likelihood i).neg ≠ 0 := by
    have hs_prod_ne_zero : (∏ i : ι, (likelihood i).neg) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i hi
      exact hlik_neg i
    simpa [prod_neg] using hs_prod_ne_zero
  have hprod_odds :
      Evidence.toOdds (∏ i, likelihood i) = ∏ i, Evidence.toOdds (likelihood i) :=
    toOdds_prod_finset (s := Finset.univ) (likelihood := likelihood) (by
      intro i hi
      exact hlik_neg i)
  have hprod_odds0 : Evidence.toOdds (∏ i, likelihood i) ≠ 0 := by
    rw [hprod_odds]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact hlik_odds0 i
  have hprod_oddsTop : Evidence.toOdds (∏ i, likelihood i) ≠ ⊤ := by
    rw [hprod_odds]
    exact ENNReal.prod_ne_top (by
      intro i hi
      exact hlik_oddsTop i)
  calc
    Evidence.toLogOdds (prior * ∏ i, likelihood i)
        = Evidence.toLogOdds prior + Evidence.toLogOdds (∏ i, likelihood i) := by
            exact Evidence.toLogOdds_tensor_add
              (x := prior) (y := ∏ i, likelihood i)
              hprior_neg hprod_neg hprior_odds0 hprod_odds0 hprior_oddsTop hprod_oddsTop
    _ = Evidence.toLogOdds prior + ∑ i, Evidence.toLogOdds (likelihood i) := by
      rw [toLogOdds_prod_finset
            (s := Finset.univ) (likelihood := likelihood)
            (hneg := by intro i hi; exact hlik_neg i)
            (hodds0 := by intro i hi; exact hlik_odds0 i)
            (hoddsTop := by intro i hi; exact hlik_oddsTop i)]

/-- Likelihood-only specialization (`prior = 1`):
NB log-odds become the pure sum of feature log-odds. -/
theorem toLogOdds_nbEvidence_likelihoodOnly
    [Fintype ι]
    (likelihood : ι → Evidence)
    (hlik_neg : ∀ i, (likelihood i).neg ≠ 0)
    (hlik_odds0 : ∀ i, Evidence.toOdds (likelihood i) ≠ 0)
    (hlik_oddsTop : ∀ i, Evidence.toOdds (likelihood i) ≠ ⊤) :
    Evidence.toLogOdds (nbEvidence ({ pos := 1, neg := 1 } : Evidence) likelihood)
      = ∑ i, Evidence.toLogOdds (likelihood i) := by
  have hone_neg : ({ pos := 1, neg := 1 } : Evidence).neg ≠ 0 := by simp
  have hone_odds0 : Evidence.toOdds ({ pos := 1, neg := 1 } : Evidence) ≠ 0 := by
    simp [Evidence.toOdds]
  have hone_oddsTop : Evidence.toOdds ({ pos := 1, neg := 1 } : Evidence) ≠ ⊤ := by
    simp [Evidence.toOdds]
  have hone_log : Evidence.toLogOdds ({ pos := 1, neg := 1 } : Evidence) = 0 := by
    simp [Evidence.toLogOdds, Evidence.toOdds]
  have hmain :=
    toLogOdds_nbEvidence_add
      (prior := ({ pos := 1, neg := 1 } : Evidence)) (likelihood := likelihood)
      (hprior_neg := hone_neg)
      (hprior_odds0 := hone_odds0)
      (hprior_oddsTop := hone_oddsTop)
      (hlik_neg := hlik_neg)
      (hlik_odds0 := hlik_odds0)
      (hlik_oddsTop := hlik_oddsTop)
  simpa [hone_log] using hmain

/-- Equivalence theorem (math sketch):

Write
- `prior = (p+, p-)`,
- `likelihood i = (li+, li-)`,
- `nbEvidence prior likelihood = (p+ * Π_i li+, p- * Π_i li-)`.

Then
`toStrength(nbEvidence prior likelihood)`
`= (p+ * Π_i li+) / ((p+ * Π_i li+) + (p- * Π_i li-))`.

The right-hand side is exactly
`nbPosterior p+ p- (fun i => li+) (fun i => li-)`.
-/
theorem toStrength_nbEvidence_eq_nbPosterior
    [Fintype ι]
    (prior : Evidence) (likelihood : ι → Evidence) :
    Evidence.toStrength (nbEvidence prior likelihood) =
      nbPosterior prior.pos prior.neg
        (fun i => (likelihood i).pos) (fun i => (likelihood i).neg) := by
  classical
  unfold Evidence.toStrength nbPosterior
  simp [Evidence.total, nbEvidence_pos, nbEvidence_neg]

/-! ### Core/bridge alias names (non-breaking)

These aliases expose theorem names used by selector-side theorem maps while
keeping existing names stable.
-/

/-- `PLN.tensorStrength_eq_nbPosterior` (math sketch):

Let
- `prior = (p+, p-)`
- each feature evidence be `likelihood i = (li+, li-)`
- tensor-composed NB evidence be
  `nbEvidence prior likelihood = (p+ * Π_i li+, p- * Π_i li-)`.

PLN strength is
`toStrength(x+, x-) = x+ / (x+ + x-)`.

So
`toStrength (nbEvidence prior likelihood)`
`= (p+ * Π_i li+) / ((p+ * Π_i li+) + (p- * Π_i li-))`,
which is exactly `nbPosterior p+ p- (fun i => li+) (fun i => li-)`.
-/
theorem PLN_tensorStrength_eq_nbPosterior
    [Fintype ι]
    (prior : Evidence) (likelihood : ι → Evidence) :
    Evidence.toStrength (nbEvidence prior likelihood) =
      nbPosterior prior.pos prior.neg
        (fun i => (likelihood i).pos) (fun i => (likelihood i).neg) := by
  exact toStrength_nbEvidence_eq_nbPosterior prior likelihood

end NaiveBayes

end Mettapedia.Logic.PLNBayesNetInference

/-! ## BoolBayesNet → BayesianNetwork -/

namespace Mettapedia.Logic.PLNBayesNetWorldModel.BoolBayesNet

variable {n : ℕ} (bn : BoolBayesNet n)

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale

noncomputable def toBayesianNetwork :
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork (Fin n) :=
  { graph := bn.graph
    acyclic := bn.acyclic
    stateSpace := fun _ => Bool
    measurableSpace := fun _ => by infer_instance }

variable [DecidableRel bn.graph.edges]

/-! ## Parent-configuration bridge -/

abbrev ParentAssignment (v : Fin n) :=
  (toBayesianNetwork bn).ParentAssignment v

def parentConfigOfAssignment (v : Fin n) (pa : ParentAssignment (bn := bn) v) :
    ParentConfig (bn := bn) v :=
  fun u => pa u.val u.property

/-! ## CPT evidence → CPT probabilities -/

noncomputable def cptEvidenceOfState (W : CPTState (bn := bn)) (v : Fin n)
    (pa : ParentAssignment (bn := bn) v) : Evidence :=
  W ⟨v, parentConfigOfAssignment (bn := bn) v pa⟩

noncomputable def cptOfState (W : CPTState (bn := bn)) :
    (toBayesianNetwork bn).DiscreteCPT :=
  { cpt := fun v pa =>
      let e := cptEvidenceOfState (bn := bn) W v pa
      Mettapedia.Logic.PLNBayesNetInference.bernoulliPMF
        (Evidence.toStrength e) (Evidence.toStrength_le_one e) }

/-! ## Exact BN query answering via VE (prop/link) -/

noncomputable def propProbVE (W : CPTState (bn := bn)) (v : Fin n) (val : Bool) : ℝ≥0∞ := by
  classical
  let _ : ∀ v, Fintype ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  let _ : ∀ v, DecidableEq ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  exact
    Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination.BayesianNetwork.propProbVE
      (bn := toBayesianNetwork bn) (cpt := cptOfState (bn := bn) W) v val

noncomputable def linkProbVE (W : CPTState (bn := bn)) (a b : Fin n) (valA valB : Bool) : ℝ≥0∞ := by
  classical
  let _ : ∀ v, Fintype ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  let _ : ∀ v, DecidableEq ((toBayesianNetwork bn).stateSpace v) := by
    intro v
    dsimp [toBayesianNetwork]
    infer_instance
  exact
    Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination.BayesianNetwork.linkProbVE
      (bn := toBayesianNetwork bn) (cpt := cptOfState (bn := bn) W) a b valA valB

end Mettapedia.Logic.PLNBayesNetWorldModel.BoolBayesNet
