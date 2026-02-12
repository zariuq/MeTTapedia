import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic
import Mettapedia.Logic.PremiseSelectionKNN_PLNBridge
import Mettapedia.Logic.PremiseSelectionFusion
import Mettapedia.Logic.PremiseSelectionExternalBayesianity

/-!
# Optimality Transfer Lemmas for Premise Selection

This file records minimal, assumption-explicit lemmas that let us transfer
optimality results for NB and k-NN to their PLN-emulated counterparts.

We keep the statements intentionally structural:
* "NB is optimal if its score is Bayes posterior (or a strict monotone transform)."
* "Ranking optimality transfers across pointwise score equality."
* "PLN emulation inherits optimality when its score equals the classical score."

These are the small, sound bridges that connect the external theory papers
to the existing PLN emulation lemmas in this repo.
-/

namespace Mettapedia.Logic.PremiseSelectionOptimality

open scoped Classical ENNReal
open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.EvidenceQuantale

/-! ## Basic notions -/

def scoreClassAt {X : Type*} (s : X -> ℝ) (t : ℝ) : X -> Prop := fun x => s x ≥ t

def BayesClass {X : Type*} (η : X -> ℝ) : X -> Prop := scoreClassAt η (1 / 2)

def BayesOptimalClassifier {X : Type*} (η : X -> ℝ) (c : X -> Prop) : Prop :=
  ∀ x, c x ↔ η x ≥ (1 / 2)

def BayesOptimalRanking {X : Type*} (η : X -> ℝ) (s : X -> ℝ) : Prop :=
  ∀ x y, s x ≤ s y ↔ η x ≤ η y

def BayesOptimalRankingENN {X : Type*} (η : X -> ℝ≥0∞) (s : X -> ℝ≥0∞) : Prop :=
  ∀ x y, s x ≤ s y ↔ η x ≤ η y

def ZhangNBOptimalityAssumption {X : Type*} (η s : X -> ℝ) : Prop :=
  ∀ x, s x = η x

def ZhangNBRankingAssumption {X : Type*} (η s : X -> ℝ) : Prop :=
  ∃ f : ℝ -> ℝ, StrictMono f ∧ s = fun x => f (η x)

def KNNConsistencyAssumption {X : Type*} (η s : X -> ℝ) : Prop :=
  ∀ x, s x = η x

def PLNEmulates {X : Type*} (s_pln s_base : X -> ℝ) : Prop := s_pln = s_base

/-! ## NB optimality under exactness assumptions -/

lemma bayesOptimal_of_score_eq {X : Type*} (η s : X -> ℝ) (h : s = η) :
    BayesOptimalClassifier η (scoreClassAt s (1 / 2)) := by
  intro x
  simp [scoreClassAt, h]

lemma nb_optimal_of_zhang {X : Type*} (η s : X -> ℝ)
    (h : ZhangNBOptimalityAssumption η s) :
    BayesOptimalClassifier η (scoreClassAt s (1 / 2)) := by
  apply bayesOptimal_of_score_eq η s
  funext x; exact h x

lemma bayesOptimal_of_strictMono_threshold {X : Type*} (η s : X -> ℝ) (f : ℝ -> ℝ)
    (h : s = fun x => f (η x)) (hf : StrictMono f) :
    BayesOptimalClassifier η (scoreClassAt s (f (1 / 2))) := by
  intro x
  subst h
  have hmono := (StrictMono.le_iff_le hf (a := (1 / 2)) (b := η x))
  -- f (η x) ≥ f (1/2) ↔ η x ≥ 1/2
  simpa [scoreClassAt, ge_iff_le] using hmono

lemma ranking_optimal_of_strictMono {X : Type*} (η s : X -> ℝ) (f : ℝ -> ℝ)
    (h : s = fun x => f (η x)) (hf : StrictMono f) :
    BayesOptimalRanking η s := by
  intro x y
  subst h
  simpa using (StrictMono.le_iff_le hf (a := η x) (b := η y))

lemma nb_ranking_of_zhang_su {X : Type*} (η s : X -> ℝ)
    (h : ZhangNBRankingAssumption η s) :
    BayesOptimalRanking η s := by
  rcases h with ⟨f, hf, hs⟩
  exact ranking_optimal_of_strictMono η s f hs hf

lemma knn_ranking_of_consistency {X : Type*} (η s : X -> ℝ)
    (h : KNNConsistencyAssumption η s) :
    BayesOptimalRanking η s := by
  intro x y
  simp [h x, h y]

/-! ## Transfer lemmas (PLN inherits from base scores) -/

lemma ranking_transfer {X : Type*} (η s₁ s₂ : X -> ℝ)
    (h : s₁ = s₂) (hopt : BayesOptimalRanking η s₂) :
    BayesOptimalRanking η s₁ := by
  intro x y
  simpa [h] using hopt x y

lemma rankingENN_transfer {X : Type*} (η s₁ s₂ : X -> ℝ≥0∞)
    (h : s₁ = s₂) (hopt : BayesOptimalRankingENN η s₂) :
    BayesOptimalRankingENN η s₁ := by
  intro x y
  simpa [h] using hopt x y

lemma rankingENN_toReal {X : Type*} (η s : X -> ℝ≥0∞)
    (hη : ∀ x, η x ≠ ∞) (hs : ∀ x, s x ≠ ∞)
    (hopt : BayesOptimalRankingENN η s) :
    BayesOptimalRanking (fun x => (η x).toReal) (fun x => (s x).toReal) := by
  intro x y
  have h1 := (ENNReal.toReal_le_toReal (hs x) (hs y))
  have h2 := (ENNReal.toReal_le_toReal (hη x) (hη y))
  have h := hopt x y
  constructor
  · intro hxy
    have : s x ≤ s y := (h1).1 hxy
    exact (h2).2 ((h).1 this)
  · intro hxy
    have : η x ≤ η y := (h2).1 hxy
    exact (h1).2 ((h).2 this)

lemma classifier_transfer {X : Type*} (η : X -> ℝ) (c₁ c₂ : X -> Prop)
    (h : c₁ = c₂) (hopt : BayesOptimalClassifier η c₂) :
    BayesOptimalClassifier η c₁ := by
  intro x
  simpa [h] using hopt x

lemma scoreClassAt_congr {X : Type*} (s₁ s₂ : X -> ℝ) (t : ℝ) (h : s₁ = s₂) :
    scoreClassAt s₁ t = scoreClassAt s₂ t := by
  ext x
  simp [scoreClassAt, h]

lemma strictMono_linear_combo {X : Type*} [Preorder X] {f g : X -> ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (fun x => a * f x + b * g x) := by
  intro x y hxy
  have hf' : f x < f y := hf hxy
  have hg' : g x < g y := hg hxy
  have h1 : a * f x < a * f y := mul_lt_mul_of_pos_left hf' ha
  have h2 : b * g x < b * g y := mul_lt_mul_of_pos_left hg' hb
  exact add_lt_add h1 h2

lemma ranking_optimal_of_linear_combo {X : Type*} (η : X -> ℝ) (f g : ℝ -> ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf : StrictMono f) (hg : StrictMono g) :
    BayesOptimalRanking η (fun x => a * f (η x) + b * g (η x)) := by
  -- positive linear combination of two monotone transforms of η
  have hmono : StrictMono (fun x => a * f x + b * g x) :=
    strictMono_linear_combo (X := ℝ) (f := f) (g := g) ha hb hf hg
  apply ranking_optimal_of_strictMono η (fun x => a * f (η x) + b * g (η x))
    (fun x => a * f x + b * g x) rfl hmono

lemma ranking_optimal_of_linear_combo_scores {X : Type*} (η s₁ s₂ : X -> ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : ∃ f, StrictMono f ∧ s₁ = fun x => f (η x))
    (h₂ : ∃ g, StrictMono g ∧ s₂ = fun x => g (η x)) :
    BayesOptimalRanking η (fun x => a * s₁ x + b * s₂ x) := by
  rcases h₁ with ⟨f, hf, hs₁⟩
  rcases h₂ with ⟨g, hg, hs₂⟩
  subst hs₁
  subst hs₂
  exact ranking_optimal_of_linear_combo η f g ha hb hf hg

lemma fusion_ranking_of_linear_combo {X : Type*} (η s₁ s₂ s_fuse : X -> ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : ∃ f, StrictMono f ∧ s₁ = fun x => f (η x))
    (h₂ : ∃ g, StrictMono g ∧ s₂ = fun x => g (η x))
    (h_fuse : s_fuse = fun x => a * s₁ x + b * s₂ x) :
    BayesOptimalRanking η s_fuse := by
  subst h_fuse
  exact ranking_optimal_of_linear_combo_scores η s₁ s₂ ha hb h₁ h₂

/-! ## Fusion after normalization (explicit hypothesis) -/

lemma fusion_ranking_after_normalization
    {X : Type*} (η s₁ s₂ s_fuse : X -> ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : ∃ f, StrictMono f ∧ s₁ = fun x => f (η x))
    (h₂ : ∃ g, StrictMono g ∧ s₂ = fun x => g (η x))
    (h_fuse : s_fuse = fun x => a * s₁ x + b * s₂ x) :
    BayesOptimalRanking η s_fuse := by
  -- This lemma is identical to fusion_ranking_of_linear_combo, but its name
  -- makes explicit the intended use: apply after normalizing evidence totals.
  exact fusion_ranking_of_linear_combo η s₁ s₂ s_fuse ha hb h₁ h₂ h_fuse

/-! ## Fusion with normalized evidence totals -/

lemma fusion_ranking_after_normalization_toReal
    {Goal Fact : Type*} (η : Fact -> ℝ) (s₁ s₂ : Scorer Goal Fact) (g : Goal)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ⊤)
    (hw : 0 < (t / (t + t)).toReal)
    (h₁ : ∃ f, StrictMono f ∧
      (fun x =>
        (Evidence.toStrength ((normalizeScorer t s₁).score g x)).toReal)
        = fun x => f (η x))
    (h₂ : ∃ f, StrictMono f ∧
      (fun x =>
        (Evidence.toStrength ((normalizeScorer t s₂).score g x)).toReal)
        = fun x => f (η x)) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((fuse (normalizeScorer t s₁) (normalizeScorer t s₂)).score g x)).toReal) := by
  -- rewrite fused strength to a positive linear combination of normalized strengths
  set w : ℝ := (t / (t + t)).toReal
  have h_fuse :
      (fun x =>
        (Evidence.toStrength
          ((fuse (normalizeScorer t s₁) (normalizeScorer t s₂)).score g x)).toReal)
        = fun x =>
          w * (Evidence.toStrength ((normalizeScorer t s₁).score g x)).toReal
          + w * (Evidence.toStrength ((normalizeScorer t s₂).score g x)).toReal := by
    funext x
    have hbase :=
      fuse_toStrength_normalized_const_toReal
        (s₁ := s₁) (s₂ := s₂) (g := g) (f := x) t ht htop
    simpa [w] using hbase
  -- apply the generic fusion optimality lemma
  exact fusion_ranking_after_normalization η
    (s₁ := fun x => (Evidence.toStrength ((normalizeScorer t s₁).score g x)).toReal)
    (s₂ := fun x => (Evidence.toStrength ((normalizeScorer t s₂).score g x)).toReal)
    (s_fuse := fun x =>
      (Evidence.toStrength
        ((fuse (normalizeScorer t s₁) (normalizeScorer t s₂)).score g x)).toReal)
    (a := w) (b := w) hw hw h₁ h₂ h_fuse

lemma fusion_ranking_after_normalization_toReal_one
    {Goal Fact : Type*} (η : Fact -> ℝ) (s₁ s₂ : Scorer Goal Fact) (g : Goal)
    (h₁ : ∃ f, StrictMono f ∧
      (fun x =>
        (Evidence.toStrength ((normalizeScorer 1 s₁).score g x)).toReal)
        = fun x => f (η x))
    (h₂ : ∃ f, StrictMono f ∧
      (fun x =>
        (Evidence.toStrength ((normalizeScorer 1 s₂).score g x)).toReal)
        = fun x => f (η x)) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((fuse (normalizeScorer 1 s₁) (normalizeScorer 1 s₂)).score g x)).toReal) := by
  have ht : (1:ℝ≥0∞) ≠ 0 := by simp
  have htop : (1:ℝ≥0∞) ≠ ⊤ := by simp
  have hw : 0 < ((1:ℝ≥0∞) / (1 + 1)).toReal := by
    apply ENNReal.toReal_pos
    · -- numerator is nonzero and denominator is finite
      simp
    · exact ENNReal.div_ne_top (by simp) (by simp)
  simpa using
    (fusion_ranking_after_normalization_toReal
      (η := η) (s₁ := s₁) (s₂ := s₂) (g := g)
      (t := 1) ht htop hw h₁ h₂)

lemma fusion_ranking_after_normalization_toReal_totals
    {Goal Fact : Type*} (η : Fact -> ℝ) (s₁ s₂ : Scorer Goal Fact) (g : Goal)
    (t₁ t₂ : ℝ≥0∞)
    (h₁_ne : t₁ ≠ 0) (h₂_ne : t₂ ≠ 0) (h₁₂_ne : t₁ + t₂ ≠ 0)
    (h₁_top : t₁ ≠ ⊤) (h₂_top : t₂ ≠ ⊤)
    (hw₁ : 0 < (t₁ / (t₁ + t₂)).toReal)
    (hw₂ : 0 < (t₂ / (t₁ + t₂)).toReal)
    (h₁ : ∃ f, StrictMono f ∧
      (fun x =>
        (Evidence.toStrength ((normalizeScorer t₁ s₁).score g x)).toReal)
        = fun x => f (η x))
    (h₂ : ∃ f, StrictMono f ∧
      (fun x =>
        (Evidence.toStrength ((normalizeScorer t₂ s₂).score g x)).toReal)
        = fun x => f (η x)) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((fuse (normalizeScorer t₁ s₁) (normalizeScorer t₂ s₂)).score g x)).toReal) := by
  set w₁ : ℝ := (t₁ / (t₁ + t₂)).toReal
  set w₂ : ℝ := (t₂ / (t₁ + t₂)).toReal
  have h_fuse :
      (fun x =>
        (Evidence.toStrength
          ((fuse (normalizeScorer t₁ s₁) (normalizeScorer t₂ s₂)).score g x)).toReal)
        = fun x =>
          w₁ * (Evidence.toStrength ((normalizeScorer t₁ s₁).score g x)).toReal
          + w₂ * (Evidence.toStrength ((normalizeScorer t₂ s₂).score g x)).toReal := by
    funext x
    have hbase :=
      fuse_toStrength_normalized_totals_toReal
        (s₁ := s₁) (s₂ := s₂) (g := g) (f := x)
        (t₁ := t₁) (t₂ := t₂)
        h₁_ne h₂_ne h₁₂_ne h₁_top h₂_top
    simpa [w₁, w₂] using hbase
  exact fusion_ranking_after_normalization η
    (s₁ := fun x => (Evidence.toStrength ((normalizeScorer t₁ s₁).score g x)).toReal)
    (s₂ := fun x => (Evidence.toStrength ((normalizeScorer t₂ s₂).score g x)).toReal)
    (s_fuse := fun x =>
      (Evidence.toStrength
        ((fuse (normalizeScorer t₁ s₁) (normalizeScorer t₂ s₂)).score g x)).toReal)
    (a := w₁) (b := w₂) hw₁ hw₂ h₁ h₂ h_fuse

/-! ## Commutation + normalization preserves ranking assumptions -/

lemma ranking_after_commutation_normalization_iff
    {Goal Fact : Type*} (η : Fact -> ℝ)
    (p₁ p₂ likelihood : Scorer Goal Fact) (g : Goal) (t : ℝ≥0∞) :
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer t (update (fuse p₁ p₂) likelihood)).score g x)).toReal)
      ↔
    BayesOptimalRanking η
      (fun x =>
        (Evidence.toStrength
          ((normalizeScorer t (fuse (update p₁ likelihood) (update p₂ likelihood))).score g x)).toReal) := by
  let sPoolThenUpdate : Fact → ℝ :=
    fun x =>
      (Evidence.toStrength
        ((normalizeScorer t (update (fuse p₁ p₂) likelihood)).score g x)).toReal
  let sUpdateThenPool : Fact → ℝ :=
    fun x =>
      (Evidence.toStrength
        ((normalizeScorer t (fuse (update p₁ likelihood) (update p₂ likelihood))).score g x)).toReal
  have hs :
      sPoolThenUpdate = sUpdateThenPool := by
    funext x
    simp [sPoolThenUpdate, sUpdateThenPool, externalBayesianity_hplus_tensor]
  constructor
  · intro h
    exact ranking_transfer η sUpdateThenPool sPoolThenUpdate hs.symm h
  · intro h
    exact ranking_transfer η sPoolThenUpdate sUpdateThenPool hs h

/-! ## PLN inheritance (structural) -/

lemma pln_inherits_nb_optimal {X : Type*} (η s_nb s_pln : X -> ℝ)
    (hnb : ZhangNBOptimalityAssumption η s_nb)
    (hpln : PLNEmulates s_pln s_nb) :
    BayesOptimalClassifier η (scoreClassAt s_pln (1 / 2)) := by
  have hopt : BayesOptimalClassifier η (scoreClassAt s_nb (1 / 2)) :=
    nb_optimal_of_zhang η s_nb hnb
  apply classifier_transfer η (scoreClassAt s_pln (1 / 2)) (scoreClassAt s_nb (1 / 2))
  · exact scoreClassAt_congr s_pln s_nb (1 / 2) hpln
  · exact hopt

lemma pln_inherits_nb_ranking {X : Type*} (η s_nb s_pln : X -> ℝ)
    (hnb : ZhangNBRankingAssumption η s_nb)
    (hpln : PLNEmulates s_pln s_nb) :
    BayesOptimalRanking η s_pln := by
  have hopt : BayesOptimalRanking η s_nb := nb_ranking_of_zhang_su η s_nb hnb
  exact ranking_transfer η s_pln s_nb hpln hopt

lemma pln_inherits_knn_ranking {X : Type*} (η s_knn s_pln : X -> ℝ)
    (hknn : KNNConsistencyAssumption η s_knn)
    (hpln : PLNEmulates s_pln s_knn) :
    BayesOptimalRanking η s_pln := by
  have hopt : BayesOptimalRanking η s_knn := knn_ranking_of_consistency η s_knn hknn
  exact ranking_transfer η s_pln s_knn hpln hopt

/-! ## k-NN / PLN equality (ranking transfer) -/

lemma pln_knn_ranking_eq
    {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) (a b : Fact) :
    (plnKnnEvidence goal N near deps tau2 a).pos ≤
      (plnKnnEvidence goal N near deps tau2 b).pos
      ↔
    knnRelevanceENN goal N near deps tau2 a ≤ knnRelevanceENN goal N near deps tau2 b := by
  -- direct by rewriting both sides with the PLN-kNN bridge
  simp [plnKnnEvidence_pos_eq_knnRelevanceENN]

end Mettapedia.Logic.PremiseSelectionOptimality
