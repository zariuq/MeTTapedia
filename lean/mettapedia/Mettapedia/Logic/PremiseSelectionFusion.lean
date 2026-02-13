import Mettapedia.Logic.PremiseSelectionKNN_PLNBridge
import Mettapedia.Logic.EvidenceQuantale

/-!
# Fusion of Premise Selectors via PLN Revision

This file defines a generic Evidence-valued premise selector and a fusion
operator that combines two selectors by PLN revision (hplus).

It also records the exact strength formula (weighted average) for the fusion,
reusing `Evidence.toStrength_hplus`.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal BigOperators
open Mettapedia.Logic.EvidenceQuantale

/-- Evidence-valued scoring for a goal/fact pair. -/
structure Scorer (Goal Fact : Type*) where
  score : Goal -> Fact -> Evidence

/-- Fuse two scorers by PLN revision (hplus). -/
noncomputable def fuse {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) : Scorer Goal Fact :=
  ⟨fun g f => s₁.score g f + s₂.score g f⟩

@[simp] lemma fuse_score {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (fuse s₁ s₂).score g f = s₁.score g f + s₂.score g f := rfl

@[simp] lemma fuse_pos {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((fuse s₁ s₂).score g f).pos = (s₁.score g f).pos + (s₂.score g f).pos := by
  simp [fuse, Evidence.hplus_def]

@[simp] lemma fuse_neg {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((fuse s₁ s₂).score g f).neg = (s₁.score g f).neg + (s₂.score g f).neg := by
  simp [fuse, Evidence.hplus_def]

@[simp] lemma evidence_total_add (x y : Evidence) :
    (x + y).total = x.total + y.total := by
  simp [Evidence.total, Evidence.hplus_def, add_left_comm, add_comm]

@[simp] lemma fuse_total {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((fuse s₁ s₂).score g f).total = (s₁.score g f).total + (s₂.score g f).total := by
  simp [fuse, evidence_total_add]

/-- The fusion strength is the weighted average of strengths (PLN revision rule). -/
theorem fuse_toStrength
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (h₁ : (s₁.score g f).total ≠ 0)
    (h₂ : (s₂.score g f).total ≠ 0)
    (h₁₂ : ((s₁.score g f + s₂.score g f).total) ≠ 0)
    (h₁_top : (s₁.score g f).total ≠ ⊤)
    (h₂_top : (s₂.score g f).total ≠ ⊤) :
    Evidence.toStrength ((fuse s₁ s₂).score g f) =
      ((s₁.score g f).total / (s₁.score g f + s₂.score g f).total) * Evidence.toStrength (s₁.score g f)
      + ((s₂.score g f).total / (s₁.score g f + s₂.score g f).total) * Evidence.toStrength (s₂.score g f) := by
  simpa [fuse] using
    (Evidence.toStrength_hplus (s₁.score g f) (s₂.score g f) h₁ h₂ h₁₂ h₁_top h₂_top)

/-! ### Core/bridge alias names (non-breaking) -/

/-- Alias exposing revision strength as linear pooling in theorem-map naming. -/
theorem PLN_revisionStrength_eq_linearPool
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (h₁ : (s₁.score g f).total ≠ 0)
    (h₂ : (s₂.score g f).total ≠ 0)
    (h₁₂ : ((s₁.score g f + s₂.score g f).total) ≠ 0)
    (h₁_top : (s₁.score g f).total ≠ ⊤)
    (h₂_top : (s₂.score g f).total ≠ ⊤) :
    Evidence.toStrength ((fuse s₁ s₂).score g f) =
      ((s₁.score g f).total / (s₁.score g f + s₂.score g f).total) * Evidence.toStrength (s₁.score g f)
      + ((s₂.score g f).total / (s₁.score g f + s₂.score g f).total) * Evidence.toStrength (s₂.score g f) := by
  exact fuse_toStrength s₁ s₂ g f h₁ h₂ h₁₂ h₁_top h₂_top

/-! ## Constant-weight specialization -/

theorem fuse_toStrength_const_weights
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (t₁ t₂ : ℝ≥0∞)
    (h₁ : ∀ f, (s₁.score g f).total = t₁)
    (h₂ : ∀ f, (s₂.score g f).total = t₂)
    (h₁_ne : t₁ ≠ 0) (h₂_ne : t₂ ≠ 0) (h₁₂_ne : t₁ + t₂ ≠ 0)
    (h₁_top : t₁ ≠ ⊤) (h₂_top : t₂ ≠ ⊤) :
    Evidence.toStrength ((fuse s₁ s₂).score g f) =
      (t₁ / (t₁ + t₂)) * Evidence.toStrength (s₁.score g f) +
      (t₂ / (t₁ + t₂)) * Evidence.toStrength (s₂.score g f) := by
  have hx : (s₁.score g f).total ≠ 0 := by simpa [h₁ f] using h₁_ne
  have hy : (s₂.score g f).total ≠ 0 := by simpa [h₂ f] using h₂_ne
  have hsum : (s₁.score g f + s₂.score g f).total = t₁ + t₂ := by
    simp [evidence_total_add, h₁ f, h₂ f]
  have hxy : ((s₁.score g f + s₂.score g f).total) ≠ 0 := by
    intro h
    apply h₁₂_ne
    simpa [hsum] using h
  have hx_top : (s₁.score g f).total ≠ ⊤ := by simpa [h₁ f] using h₁_top
  have hy_top : (s₂.score g f).total ≠ ⊤ := by simpa [h₂ f] using h₂_top
  have hmain := fuse_toStrength s₁ s₂ g f hx hy hxy hx_top hy_top
  -- rewrite the weights as constants
  simpa [hsum, h₁ f, h₂ f] using hmain

theorem fuse_toStrength_proportional_weights
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (t : Fact -> ℝ≥0∞) (a b : ℝ≥0∞)
    (h₁ : ∀ f, (s₁.score g f).total = a * t f)
    (h₂ : ∀ f, (s₂.score g f).total = b * t f)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (ht : ∀ f, t f ≠ 0)
    (ha_top : a ≠ ⊤) (hb_top : b ≠ ⊤) (ht_top : ∀ f, t f ≠ ⊤) :
    Evidence.toStrength ((fuse s₁ s₂).score g f) =
      (a / (a + b)) * Evidence.toStrength (s₁.score g f) +
      (b / (a + b)) * Evidence.toStrength (s₂.score g f) := by
  have hx : (s₁.score g f).total ≠ 0 := by
    have : a * t f ≠ 0 := by
      exact mul_ne_zero ha (ht f)
    simpa [h₁ f] using this
  have hy : (s₂.score g f).total ≠ 0 := by
    have : b * t f ≠ 0 := by
      exact mul_ne_zero hb (ht f)
    simpa [h₂ f] using this
  have hx_top : (s₁.score g f).total ≠ ⊤ := by
    have : a * t f ≠ ⊤ := by
      exact ENNReal.mul_ne_top ha_top (ht_top f)
    simpa [h₁ f] using this
  have hy_top : (s₂.score g f).total ≠ ⊤ := by
    have : b * t f ≠ ⊤ := by
      exact ENNReal.mul_ne_top hb_top (ht_top f)
    simpa [h₂ f] using this
  have hsum : (s₁.score g f + s₂.score g f).total = (a + b) * t f := by
    simp [evidence_total_add, h₁ f, h₂ f, add_mul]
  have hxy : ((s₁.score g f + s₂.score g f).total) ≠ 0 := by
    intro h
    have : (a + b) * t f = 0 := by simpa [hsum] using h
    have hab : a + b = 0 := by
      apply (mul_eq_zero.mp this).resolve_right
      exact (ht f)
    have ha0 : a = 0 := by
      apply le_antisymm
      · have : a ≤ a + b := le_self_add
        simpa [hab] using this
      · exact bot_le
    exact ha ha0
  have hmain := fuse_toStrength s₁ s₂ g f hx hy hxy hx_top hy_top
  -- cancel the common factor t f in the weights
  have hwt1 :
      (a * t f) / ((a + b) * t f) = a / (a + b) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (ENNReal.mul_div_mul_right a (a + b) (ht f) (ht_top f))
  have hwt2 :
      (b * t f) / ((a + b) * t f) = b / (a + b) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (ENNReal.mul_div_mul_right b (a + b) (ht f) (ht_top f))
  simpa [hsum, h₁ f, h₂ f, hwt1, hwt2] using hmain

/-! ## Canonical scorers -/

/-- k-NN scorer from the PLN bridge. -/
noncomputable def knnScorer {Fact : Type*} [DecidableEq Fact]
    (goal : Fact) (N : Finset Fact) (near : Fact -> Fact -> ℝ≥0∞)
    (deps : DepSet Fact) (tau2 : ℝ≥0∞) : Scorer Fact Fact :=
  ⟨fun _ phi => plnKnnEvidence goal N near deps tau2 phi⟩

/-- Generic NB-style scorer: user supplies a precomputed Evidence score. -/
def nbScorer {Goal Fact : Type*} (score : Goal -> Fact -> Evidence) : Scorer Goal Fact :=
  ⟨score⟩

/-! ## Normalization wrapper -/

/-- Normalize evidence to a fixed total `t` while preserving strength. -/
noncomputable def normalizeEvidence (t : ℝ≥0∞) (e : Evidence) : Evidence :=
  let s := Evidence.toStrength e
  ⟨t * s, t * (1 - s)⟩

lemma normalizeEvidence_total (t : ℝ≥0∞) (e : Evidence) :
    (normalizeEvidence t e).total = t := by
  classical
  have hs : Evidence.toStrength e ≤ 1 := Evidence.toStrength_le_one e
  unfold normalizeEvidence Evidence.total
  -- total = t * s + t * (1 - s) = t * (s + (1 - s)) = t
  have hsum : Evidence.toStrength e + (1 - Evidence.toStrength e) = 1 := by
    simpa using (add_tsub_cancel_of_le hs)
  calc
    t * Evidence.toStrength e + t * (1 - Evidence.toStrength e)
        = t * (Evidence.toStrength e + (1 - Evidence.toStrength e)) := by
            simp [mul_add]
    _ = t * 1 := by simp [hsum]
    _ = t := by simp

lemma normalizeEvidence_toStrength (t : ℝ≥0∞) (e : Evidence)
    (ht : t ≠ 0) (htop : t ≠ ⊤) :
    Evidence.toStrength (normalizeEvidence t e) = Evidence.toStrength e := by
  classical
  set s : ℝ≥0∞ := Evidence.toStrength e
  have hpos : (normalizeEvidence t e).pos = t * s := by
    simp [normalizeEvidence, s]
  have htot : (normalizeEvidence t e).total = t := normalizeEvidence_total t e
  have htot_ne : (normalizeEvidence t e).total ≠ 0 := by
    simpa [htot] using ht
  calc
    Evidence.toStrength (normalizeEvidence t e)
        = (normalizeEvidence t e).pos / (normalizeEvidence t e).total := by
            simp [Evidence.toStrength, htot_ne]
    _ = (t * s) / t := by
            simp [hpos, htot]
    _ = s := by
            simpa [mul_comm] using (ENNReal.mul_div_cancel_right (a := s) (b := t) ht htop)
    _ = Evidence.toStrength e := by rfl

/-- Normalize a scorer so that every evidence total is fixed to `t`. -/
noncomputable def normalizeScorer {Goal Fact : Type*}
    (t : ℝ≥0∞) (s : Scorer Goal Fact) : Scorer Goal Fact :=
  ⟨fun g f => normalizeEvidence t (s.score g f)⟩

lemma normalizeScorer_total {Goal Fact : Type*} (t : ℝ≥0∞) (s : Scorer Goal Fact)
    (g : Goal) (f : Fact) :
    ((normalizeScorer t s).score g f).total = t := by
  simpa [normalizeScorer] using normalizeEvidence_total t (s.score g f)

lemma normalizeScorer_toStrength {Goal Fact : Type*} (t : ℝ≥0∞) (s : Scorer Goal Fact)
    (g : Goal) (f : Fact) (ht : t ≠ 0) (htop : t ≠ ⊤) :
    Evidence.toStrength ((normalizeScorer t s).score g f) =
      Evidence.toStrength (s.score g f) := by
  simpa [normalizeScorer] using normalizeEvidence_toStrength t (s.score g f) ht htop

theorem fuse_toStrength_normalized_const
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ⊤) :
    Evidence.toStrength
        ((fuse (normalizeScorer t s₁) (normalizeScorer t s₂)).score g f)
      =
      (t / (t + t)) * Evidence.toStrength ((normalizeScorer t s₁).score g f)
      + (t / (t + t)) * Evidence.toStrength ((normalizeScorer t s₂).score g f) := by
  -- totals are constant t after normalization
  have h₁ : ∀ f, ((normalizeScorer t s₁).score g f).total = t := by
    intro f; simpa using normalizeScorer_total t s₁ g f
  have h₂ : ∀ f, ((normalizeScorer t s₂).score g f).total = t := by
    intro f; simpa using normalizeScorer_total t s₂ g f
  have h₁₂ : t + t ≠ 0 := by
    intro h
    have : (2:ℝ≥0∞) * t = 0 := by simpa [two_mul] using h
    have ht0 : t = 0 := (mul_eq_zero.mp this).resolve_left (by simp)
    exact ht ht0
  have h₁_top : t ≠ ⊤ := htop
  have h₂_top : t ≠ ⊤ := htop
  simpa using
    (fuse_toStrength_const_weights
      (s₁ := normalizeScorer t s₁) (s₂ := normalizeScorer t s₂)
      (g := g) (f := f)
      (t₁ := t) (t₂ := t)
      h₁ h₂ ht ht h₁₂ h₁_top h₂_top)

theorem fuse_toStrength_normalized_const_toReal
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ⊤) :
    (Evidence.toStrength
        ((fuse (normalizeScorer t s₁) (normalizeScorer t s₂)).score g f)).toReal
      =
      (t / (t + t)).toReal *
          (Evidence.toStrength ((normalizeScorer t s₁).score g f)).toReal
      + (t / (t + t)).toReal *
          (Evidence.toStrength ((normalizeScorer t s₂).score g f)).toReal := by
  have hbase :=
    fuse_toStrength_normalized_const (s₁ := s₁) (s₂ := s₂)
      (g := g) (f := f) t ht htop
  have hden : t + t ≠ 0 := by
    intro h
    have : (2:ℝ≥0∞) * t = 0 := by simpa [two_mul] using h
    have ht0 : t = 0 := (mul_eq_zero.mp this).resolve_left (by simp)
    exact ht ht0
  have hw_ne_top : t / (t + t) ≠ ⊤ := ENNReal.div_ne_top htop hden
  have h₁_ne_top :
      Evidence.toStrength ((normalizeScorer t s₁).score g f) ≠ ⊤ := by
    have hle : Evidence.toStrength ((normalizeScorer t s₁).score g f) ≤ 1 :=
      Evidence.toStrength_le_one _
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  have h₂_ne_top :
      Evidence.toStrength ((normalizeScorer t s₂).score g f) ≠ ⊤ := by
    have hle : Evidence.toStrength ((normalizeScorer t s₂).score g f) ≤ 1 :=
      Evidence.toStrength_le_one _
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  have hleft_ne_top :
      (t / (t + t)) * Evidence.toStrength ((normalizeScorer t s₁).score g f) ≠ ⊤ :=
    ENNReal.mul_ne_top hw_ne_top h₁_ne_top
  have hright_ne_top :
      (t / (t + t)) * Evidence.toStrength ((normalizeScorer t s₂).score g f) ≠ ⊤ :=
    ENNReal.mul_ne_top hw_ne_top h₂_ne_top
  have hbase' := congrArg ENNReal.toReal hbase
  -- rewrite the sum/mul on ENNReal into ℝ
  simpa [ENNReal.toReal_add hleft_ne_top hright_ne_top, ENNReal.toReal_mul] using hbase'

theorem fuse_toStrength_normalized_const_toReal_one
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (Evidence.toStrength
        ((fuse (normalizeScorer 1 s₁) (normalizeScorer 1 s₂)).score g f)).toReal
      =
      ((1:ℝ≥0∞) / (1 + 1)).toReal *
          (Evidence.toStrength ((normalizeScorer 1 s₁).score g f)).toReal
      + ((1:ℝ≥0∞) / (1 + 1)).toReal *
          (Evidence.toStrength ((normalizeScorer 1 s₂).score g f)).toReal := by
  have ht : (1:ℝ≥0∞) ≠ 0 := by simp
  have htop : (1:ℝ≥0∞) ≠ ⊤ := by simp
  simpa using
    (fuse_toStrength_normalized_const_toReal
      (s₁ := s₁) (s₂ := s₂) (g := g) (f := f) (t := 1) ht htop)

/-- Normalization with possibly different target totals gives explicitly controlled
mixing weights `t₁/(t₁+t₂)` and `t₂/(t₁+t₂)`, independent of raw evidence magnitudes. -/
theorem fuse_toStrength_normalized_totals
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (t₁ t₂ : ℝ≥0∞)
    (h₁_ne : t₁ ≠ 0) (h₂_ne : t₂ ≠ 0) (h₁₂_ne : t₁ + t₂ ≠ 0)
    (h₁_top : t₁ ≠ ⊤) (h₂_top : t₂ ≠ ⊤) :
    Evidence.toStrength
        ((fuse (normalizeScorer t₁ s₁) (normalizeScorer t₂ s₂)).score g f)
      =
      (t₁ / (t₁ + t₂)) * Evidence.toStrength ((normalizeScorer t₁ s₁).score g f)
      + (t₂ / (t₁ + t₂)) * Evidence.toStrength ((normalizeScorer t₂ s₂).score g f) := by
  have h₁ : ∀ f, ((normalizeScorer t₁ s₁).score g f).total = t₁ := by
    intro f
    simpa using normalizeScorer_total t₁ s₁ g f
  have h₂ : ∀ f, ((normalizeScorer t₂ s₂).score g f).total = t₂ := by
    intro f
    simpa using normalizeScorer_total t₂ s₂ g f
  simpa using
    (fuse_toStrength_const_weights
      (s₁ := normalizeScorer t₁ s₁) (s₂ := normalizeScorer t₂ s₂)
      (g := g) (f := f)
      (t₁ := t₁) (t₂ := t₂)
      h₁ h₂ h₁_ne h₂_ne h₁₂_ne h₁_top h₂_top)

theorem fuse_toStrength_normalized_totals_toReal
    {Goal Fact : Type*} (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact)
    (t₁ t₂ : ℝ≥0∞)
    (h₁_ne : t₁ ≠ 0) (h₂_ne : t₂ ≠ 0) (h₁₂_ne : t₁ + t₂ ≠ 0)
    (h₁_top : t₁ ≠ ⊤) (h₂_top : t₂ ≠ ⊤) :
    (Evidence.toStrength
        ((fuse (normalizeScorer t₁ s₁) (normalizeScorer t₂ s₂)).score g f)).toReal
      =
      (t₁ / (t₁ + t₂)).toReal *
          (Evidence.toStrength ((normalizeScorer t₁ s₁).score g f)).toReal
      + (t₂ / (t₁ + t₂)).toReal *
          (Evidence.toStrength ((normalizeScorer t₂ s₂).score g f)).toReal := by
  have hbase :=
    fuse_toStrength_normalized_totals
      (s₁ := s₁) (s₂ := s₂) (g := g) (f := f)
      (t₁ := t₁) (t₂ := t₂) h₁_ne h₂_ne h₁₂_ne h₁_top h₂_top
  have hw₁_ne_top : t₁ / (t₁ + t₂) ≠ ⊤ := ENNReal.div_ne_top h₁_top h₁₂_ne
  have hw₂_ne_top : t₂ / (t₁ + t₂) ≠ ⊤ := ENNReal.div_ne_top h₂_top h₁₂_ne
  have hs₁_ne_top :
      Evidence.toStrength ((normalizeScorer t₁ s₁).score g f) ≠ ⊤ := by
    have hle : Evidence.toStrength ((normalizeScorer t₁ s₁).score g f) ≤ 1 :=
      Evidence.toStrength_le_one _
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  have hs₂_ne_top :
      Evidence.toStrength ((normalizeScorer t₂ s₂).score g f) ≠ ⊤ := by
    have hle : Evidence.toStrength ((normalizeScorer t₂ s₂).score g f) ≤ 1 :=
      Evidence.toStrength_le_one _
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  have hleft_ne_top :
      (t₁ / (t₁ + t₂)) * Evidence.toStrength ((normalizeScorer t₁ s₁).score g f) ≠ ⊤ :=
    ENNReal.mul_ne_top hw₁_ne_top hs₁_ne_top
  have hright_ne_top :
      (t₂ / (t₁ + t₂)) * Evidence.toStrength ((normalizeScorer t₂ s₂).score g f) ≠ ⊤ :=
    ENNReal.mul_ne_top hw₂_ne_top hs₂_ne_top
  have hbase' := congrArg ENNReal.toReal hbase
  simpa [ENNReal.toReal_add hleft_ne_top hright_ne_top, ENNReal.toReal_mul] using hbase'

/-! ## N-expert normalized pooling (finite family) -/

/-- Fuse a finite family of scorers by pointwise evidence sum. -/
noncomputable def fuseFamily {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) : Scorer Goal Fact :=
  ⟨fun g f => ∑ i, (s i).score g f⟩

@[simp] lemma fuseFamily_score {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (g : Goal) (f : Fact) :
    (fuseFamily s).score g f = ∑ i, (s i).score g f := rfl

@[simp] lemma fuseFamily_pos {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((fuseFamily s).score g f).pos = ∑ i, ((s i).score g f).pos := by
  simp [fuseFamily]

@[simp] lemma fuseFamily_neg {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((fuseFamily s).score g f).neg = ∑ i, ((s i).score g f).neg := by
  simp [fuseFamily]

@[simp] lemma fuseFamily_total {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((fuseFamily s).score g f).total = ∑ i, ((s i).score g f).total := by
  simp [Evidence.total, fuseFamily, Finset.sum_add_distrib]

@[simp] lemma normalizeScorer_pos {Goal Fact : Type*}
    (t : ℝ≥0∞) (s : Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((normalizeScorer t s).score g f).pos = t * Evidence.toStrength (s.score g f) := by
  simp [normalizeScorer, normalizeEvidence]

/-- Finite `N`-expert normalized pooling law:
the fused strength equals the weighted average of expert strengths with weights `t i`. -/
theorem fuseFamily_toStrength_normalized_totals
    {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (t : ι → ℝ≥0∞) (g : Goal) (f : Fact)
    (htsum : (∑ i, t i) ≠ 0) :
    Evidence.toStrength
      ((fuseFamily (fun i => normalizeScorer (t i) (s i))).score g f)
      =
    (∑ i, t i * Evidence.toStrength ((s i).score g f)) / (∑ i, t i) := by
  let sn : ι → Scorer Goal Fact := fun i => normalizeScorer (t i) (s i)
  have hpos :
      ((fuseFamily sn).score g f).pos
        = ∑ i, t i * Evidence.toStrength ((s i).score g f) := by
    simp [sn, fuseFamily, normalizeScorer, normalizeEvidence]
  have htot :
      ((fuseFamily sn).score g f).total = ∑ i, t i := by
    calc
      ((fuseFamily sn).score g f).total
          = ∑ i, ((sn i).score g f).total := by
              simpa using (fuseFamily_total (s := sn) (g := g) (f := f))
      _ = ∑ i, t i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [sn] using (normalizeScorer_total (t := t i) (s := s i) (g := g) (f := f))
  have htot_ne :
      ((fuseFamily sn).score g f).total ≠ 0 := by
    intro h0
    apply htsum
    rw [← htot]
    exact h0
  have houter :
      Evidence.toStrength ((fuseFamily sn).score g f)
        = ((fuseFamily sn).score g f).pos / ((fuseFamily sn).score g f).total := by
    unfold Evidence.toStrength
    exact if_neg htot_ne
  calc
    Evidence.toStrength ((fuseFamily sn).score g f)
        = ((fuseFamily sn).score g f).pos / ((fuseFamily sn).score g f).total := houter
    _ = (∑ i, t i * Evidence.toStrength ((s i).score g f)) / (∑ i, t i) := by
          rw [hpos, htot]

end Mettapedia.Logic.PremiseSelection
