import Mettapedia.Logic.PremiseSelectionKNN
import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN Bridge for k-NN Premise Selection

This file connects the k-NN relevance formula to PLN evidence combination.
We show that a natural PLN evidence aggregation (using hplus) produces a
positive-evidence total equal to the k-NN relevance score (ENNReal version).
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal
open Mettapedia.Logic.EvidenceQuantale

/-! ## ENNReal k-NN (nonnegative scores) -/

noncomputable def knnNearENN {Fact Feature : Type*} [DecidableEq Feature]
    (F : FeatureSet Fact Feature) (w : Feature -> ℝ≥0∞) (tau1 : Nat)
    (phi chi : Fact) : ℝ≥0∞ :=
  Finset.sum (F phi ∩ F chi) (fun f => (w f) ^ tau1)

/-- k-NN relevance score (ENNReal version), with tau2 distributed into neighbor contributions. -/
noncomputable def knnRelevanceENN {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) : ℝ≥0∞ :=
  let depTerm :=
    Finset.sum N (fun chi =>
      if phi ∈ deps chi then
        tau2 * (near chi goal / ((deps chi).card : ℝ≥0∞))
      else 0)
  (if phi ∈ N then near phi goal else 0) + depTerm

/-- Paper-style k-NN relevance: tau2 factored outside the neighbor-dependency sum. -/
noncomputable def knnRelevanceENN_paper {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) : ℝ≥0∞ :=
  let depTerm :=
    Finset.sum N (fun chi =>
      if phi ∈ deps chi then
        near chi goal / ((deps chi).card : ℝ≥0∞)
      else 0)
  (if phi ∈ N then near phi goal else 0) + tau2 * depTerm

theorem knnRelevanceENN_eq_paper {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) :
    knnRelevanceENN goal N near deps tau2 phi =
      knnRelevanceENN_paper goal N near deps tau2 phi := by
  classical
  simp [knnRelevanceENN, knnRelevanceENN_paper, Finset.mul_sum, mul_ite, mul_zero]

/-! ## PLN evidence aggregation -/

noncomputable def posEvidence (w : ℝ≥0∞) : Evidence :=
  ⟨w, 0⟩

@[simp] lemma posEvidence_pos (w : ℝ≥0∞) : (posEvidence w).pos = w := rfl
@[simp] lemma posEvidence_neg (w : ℝ≥0∞) : (posEvidence w).neg = 0 := rfl

@[simp] lemma evidence_pos_add (x y : Evidence) : (x + y).pos = x.pos + y.pos := by
  simp [Evidence.hplus_def]

@[simp] lemma evidence_neg_add (x y : Evidence) : (x + y).neg = x.neg + y.neg := by
  simp [Evidence.hplus_def]

@[simp] lemma evidence_pos_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Evidence) :
    (Finset.sum s f).pos = Finset.sum s (fun a => (f a).pos) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · rfl
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs]

@[simp] lemma evidence_neg_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Evidence) :
    (Finset.sum s f).neg = Finset.sum s (fun a => (f a).neg) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · rfl
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs]

/-- PLN-style evidence aggregation for k-NN relevance. -/
noncomputable def plnKnnEvidence {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) : Evidence :=
  let depEv :=
    Finset.sum N (fun chi =>
      posEvidence
        (if phi ∈ deps chi then
          tau2 * (near chi goal / ((deps chi).card : ℝ≥0∞))
        else 0))
  let selfEv : Evidence :=
    if phi ∈ N then posEvidence (near phi goal) else 0
  depEv + selfEv

theorem plnKnnEvidence_pos_eq_knnRelevanceENN {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) :
    (plnKnnEvidence goal N near deps tau2 phi).pos =
      knnRelevanceENN goal N near deps tau2 phi := by
  classical
  by_cases h : phi ∈ N
  · simp [plnKnnEvidence, knnRelevanceENN, posEvidence, h, add_comm]
  · simp [plnKnnEvidence, knnRelevanceENN, posEvidence, h, add_comm]

/-! ### Core/bridge alias names (non-breaking) -/

/-- Alias exposing the k-NN bridge in theorem-map naming. -/
theorem PLN_hplusPos_eq_knnRelevance {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) :
    (plnKnnEvidence goal N near deps tau2 phi).pos =
      knnRelevanceENN goal N near deps tau2 phi := by
  exact plnKnnEvidence_pos_eq_knnRelevanceENN goal N near deps tau2 phi

theorem plnKnnEvidence_neg_eq_zero {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (phi : Fact) :
    (plnKnnEvidence goal N near deps tau2 phi).neg = 0 := by
  classical
  by_cases h : phi ∈ N
  · simp [plnKnnEvidence, posEvidence, h]
  · simp [plnKnnEvidence, posEvidence, h]

/-! ## MaSh instance (ENNReal) -/

noncomputable def idfWeightENN {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (F : FeatureSet Fact Feature) (f : Feature) : ℝ≥0∞ :=
  ENNReal.ofReal (idfWeight facts F f)

noncomputable def mashNearENN {Fact Feature : Type*} [DecidableEq Fact] [DecidableEq Feature]
    (facts : Finset Fact) (F : FeatureSet Fact Feature) (tau1 : Nat)
    (phi chi : Fact) : ℝ≥0∞ :=
  knnNearENN F (idfWeightENN facts F) tau1 phi chi

end Mettapedia.Logic.PremiseSelection
