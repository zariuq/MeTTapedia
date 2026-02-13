import Mettapedia.Logic.PremiseSelectionFusion

/-!
# External-Bayesianity Style Commutation for Premise Selection

This file formalizes the core algebraic commutation property behind a PLN-style
pool/update architecture:

- **Pool** independent prior experts with `hplus` (`fuse`).
- **Update** with shared likelihood evidence via tensor (`update`).

For evidence counts, tensor is coordinatewise multiplication and hplus is coordinatewise
addition, so update distributes over pooling. This yields an exact commutation law:

`update (fuse s₁ s₂) ℓ = fuse (update s₁ ℓ) (update s₂ ℓ)`.

This is the finite algebraic core of an external-Bayesianity style statement.
-/

namespace Mettapedia.Logic.PremiseSelection

open scoped Classical ENNReal
open Mettapedia.Logic.EvidenceQuantale

/-- Extensionality for premise scorers. -/
@[ext] theorem Scorer.ext {Goal Fact : Type*}
    {s t : Scorer Goal Fact}
    (h : ∀ g f, s.score g f = t.score g f) : s = t := by
  cases s
  cases t
  simp at h
  exact congrArg Scorer.mk (funext (fun g => funext (fun f => h g f)))

/-- Update a scorer with likelihood evidence via tensor product. -/
noncomputable def update {Goal Fact : Type*}
    (prior likelihood : Scorer Goal Fact) : Scorer Goal Fact :=
  ⟨fun g f => prior.score g f * likelihood.score g f⟩

@[simp] lemma update_score {Goal Fact : Type*}
    (prior likelihood : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (update prior likelihood).score g f = prior.score g f * likelihood.score g f := rfl

/-- Scale an evidence value coordinatewise. -/
noncomputable def scaleEvidence (w : ℝ≥0∞) (e : Evidence) : Evidence :=
  ⟨w * e.pos, w * e.neg⟩

@[simp] lemma scaleEvidence_pos (w : ℝ≥0∞) (e : Evidence) :
    (scaleEvidence w e).pos = w * e.pos := rfl

@[simp] lemma scaleEvidence_neg (w : ℝ≥0∞) (e : Evidence) :
    (scaleEvidence w e).neg = w * e.neg := rfl

/-- Regraduation via coordinatewise scaling preserves odds (finite nonzero scale). -/
theorem toOdds_scaleEvidence (w : ℝ≥0∞) (e : Evidence)
    (hw0 : w ≠ 0) (hwTop : w ≠ ⊤) (hneg : e.neg ≠ 0) :
    Evidence.toOdds (scaleEvidence w e) = Evidence.toOdds e := by
  have hscaled_neg : w * e.neg ≠ 0 := mul_ne_zero hw0 hneg
  rw [Evidence.toOdds_eq_div _ hscaled_neg, Evidence.toOdds_eq_div _ hneg]
  have hcancel :
      (e.pos * w) / (e.neg * w) = e.pos / e.neg := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (ENNReal.mul_div_mul_right (a := e.pos) (b := e.neg) (c := w) hw0 hwTop)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel

/-- Log-odds are invariant under finite nonzero coordinatewise regraduation. -/
theorem toLogOdds_scaleEvidence (w : ℝ≥0∞) (e : Evidence)
    (hw0 : w ≠ 0) (hwTop : w ≠ ⊤) (hneg : e.neg ≠ 0) :
    Evidence.toLogOdds (scaleEvidence w e) = Evidence.toLogOdds e := by
  simp [Evidence.toLogOdds, toOdds_scaleEvidence (w := w) (e := e) hw0 hwTop hneg]

/-- Scale all outputs of a scorer by a fixed evidence weight. -/
noncomputable def scaleScorer {Goal Fact : Type*}
    (w : ℝ≥0∞) (s : Scorer Goal Fact) : Scorer Goal Fact :=
  ⟨fun g f => scaleEvidence w (s.score g f)⟩

@[simp] lemma scaleScorer_score {Goal Fact : Type*}
    (w : ℝ≥0∞) (s : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (scaleScorer w s).score g f = scaleEvidence w (s.score g f) := rfl

/-- Weighted pooling family (linear pool in evidence space). -/
noncomputable def weightedFuse {Goal Fact : Type*}
    (w₁ w₂ : ℝ≥0∞) (s₁ s₂ : Scorer Goal Fact) : Scorer Goal Fact :=
  fuse (scaleScorer w₁ s₁) (scaleScorer w₂ s₂)

@[simp] lemma weightedFuse_score {Goal Fact : Type*}
    (w₁ w₂ : ℝ≥0∞) (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (weightedFuse w₁ w₂ s₁ s₂).score g f =
      scaleEvidence w₁ (s₁.score g f) + scaleEvidence w₂ (s₂.score g f) := rfl

/-- Zero scorer (no evidence). -/
def zeroScorer {Goal Fact : Type*} : Scorer Goal Fact := ⟨fun _ _ => Evidence.zero⟩

@[simp] lemma zeroScorer_score {Goal Fact : Type*} (g : Goal) (f : Fact) :
    (zeroScorer : Scorer Goal Fact).score g f = 0 := rfl

/-- Unit scorer (unit evidence `(1,1)` everywhere). -/
noncomputable def oneScorer {Goal Fact : Type*} : Scorer Goal Fact := ⟨fun _ _ => Evidence.one⟩

@[simp] lemma oneScorer_score {Goal Fact : Type*} (g : Goal) (f : Fact) :
    (oneScorer : Scorer Goal Fact).score g f = 1 := rfl

/-- Constant scorer helper (same evidence for all goal/fact pairs). -/
def constScorer {Goal Fact : Type*} (e : Evidence) : Scorer Goal Fact := ⟨fun _ _ => e⟩

@[simp] lemma constScorer_score {Goal Fact : Type*}
    (e : Evidence) (g : Goal) (f : Fact) :
    (constScorer (Goal := Goal) (Fact := Fact) e).score g f = e := rfl

/-- Coordinatewise max on evidence (counterexample pooling kernel). -/
noncomputable def maxEvidence (x y : Evidence) : Evidence :=
  ⟨max x.pos y.pos, max x.neg y.neg⟩

/-- Pointwise max pooling on scorers. -/
noncomputable def maxPool {Goal Fact : Type*}
    (s₁ s₂ : Scorer Goal Fact) : Scorer Goal Fact :=
  ⟨fun g f => maxEvidence (s₁.score g f) (s₂.score g f)⟩

@[simp] lemma maxPool_score {Goal Fact : Type*}
    (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    (maxPool s₁ s₂).score g f = maxEvidence (s₁.score g f) (s₂.score g f) := rfl

@[simp] lemma maxPool_pos {Goal Fact : Type*}
    (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((maxPool s₁ s₂).score g f).pos = max (s₁.score g f).pos (s₂.score g f).pos := by
  simp [maxPool, maxEvidence]

@[simp] lemma maxPool_neg {Goal Fact : Type*}
    (s₁ s₂ : Scorer Goal Fact) (g : Goal) (f : Fact) :
    ((maxPool s₁ s₂).score g f).neg = max (s₁.score g f).neg (s₂.score g f).neg := by
  simp [maxPool, maxEvidence]

/-- Updating after pooling equals pooling updated experts (left distributivity form). -/
theorem update_fuse_commute_left {Goal Fact : Type*}
    (s₁ s₂ likelihood : Scorer Goal Fact) :
    update (fuse s₁ s₂) likelihood = fuse (update s₁ likelihood) (update s₂ likelihood) := by
  apply Scorer.ext
  intro g f
  apply Evidence.ext'
  · simp [update, fuse, Evidence.hplus_def, Evidence.tensor_def, add_mul]
  · simp [update, fuse, Evidence.hplus_def, Evidence.tensor_def, add_mul]

/-- Updating after pooling equals pooling updated experts (right distributivity form). -/
theorem update_fuse_commute_right {Goal Fact : Type*}
    (prior l₁ l₂ : Scorer Goal Fact) :
    update prior (fuse l₁ l₂) = fuse (update prior l₁) (update prior l₂) := by
  apply Scorer.ext
  intro g f
  apply Evidence.ext'
  · simp [update, fuse, Evidence.hplus_def, Evidence.tensor_def, mul_add]
  · simp [update, fuse, Evidence.hplus_def, Evidence.tensor_def, mul_add]

/-- External-Bayesianity style commutation (pool and update commute for common likelihood). -/
theorem externalBayesianity_hplus_tensor {Goal Fact : Type*}
    (s₁ s₂ likelihood : Scorer Goal Fact) :
    fuse (update s₁ likelihood) (update s₂ likelihood) =
      update (fuse s₁ s₂) likelihood := by
  simp [update_fuse_commute_left (s₁ := s₁) (s₂ := s₂) (likelihood := likelihood)]

/-- External-Bayesianity also holds for weighted linear pooling. -/
theorem externalBayesianity_weighted_hplus_tensor {Goal Fact : Type*}
    (w₁ w₂ : ℝ≥0∞) (s₁ s₂ likelihood : Scorer Goal Fact) :
    weightedFuse w₁ w₂ (update s₁ likelihood) (update s₂ likelihood) =
      update (weightedFuse w₁ w₂ s₁ s₂) likelihood := by
  apply Scorer.ext
  intro g f
  apply Evidence.ext'
  · simp [weightedFuse, update, scaleScorer, scaleEvidence, Evidence.hplus_def, Evidence.tensor_def,
      add_mul, mul_assoc]
  · simp [weightedFuse, update, scaleScorer, scaleEvidence, Evidence.hplus_def, Evidence.tensor_def,
      add_mul, mul_assoc]

/-- Updating after finite-family pooling equals pooling updated experts. -/
theorem update_fuseFamily_commute_left {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (likelihood : Scorer Goal Fact) :
    update (fuseFamily s) likelihood = fuseFamily (fun i => update (s i) likelihood) := by
  apply Scorer.ext
  intro g f
  apply Evidence.ext'
  · simp [update, fuseFamily, Evidence.tensor_def, Finset.sum_mul]
  · simp [update, fuseFamily, Evidence.tensor_def, Finset.sum_mul]

/-- Updating a prior with finite pooled likelihood experts equals pooling individual updates. -/
theorem update_fuseFamily_commute_right {Goal Fact ι : Type*} [Fintype ι]
    (prior : Scorer Goal Fact) (l : ι → Scorer Goal Fact) :
    update prior (fuseFamily l) = fuseFamily (fun i => update prior (l i)) := by
  apply Scorer.ext
  intro g f
  apply Evidence.ext'
  · simp [update, fuseFamily, Evidence.tensor_def, Finset.mul_sum]
  · simp [update, fuseFamily, Evidence.tensor_def, Finset.mul_sum]

/-- External-Bayesianity style commutation for finite expert families. -/
theorem externalBayesianity_fuseFamily_tensor {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (likelihood : Scorer Goal Fact) :
    fuseFamily (fun i => update (s i) likelihood) = update (fuseFamily s) likelihood := by
  simp [update_fuseFamily_commute_left (s := s) (likelihood := likelihood)]

/-- Restricted characterization: in the weighted-linear family, two-sided neutrality forces
`w₁ = w₂ = 1`, hence the pool is exactly `fuse`. -/
theorem weightedFuse_unique_under_two_sided_neutrality
    {Goal Fact : Type*} (w₁ w₂ : ℝ≥0∞) (g0 : Goal) (f0 : Fact)
    (hL : ∀ s : Scorer Goal Fact, weightedFuse w₁ w₂ s zeroScorer = s)
    (hR : ∀ s : Scorer Goal Fact, weightedFuse w₁ w₂ zeroScorer s = s) :
    w₁ = 1 ∧ w₂ = 1 := by
  have hLpos := congrArg (fun sc => (sc.score g0 f0).pos) (hL oneScorer)
  have hRpos := congrArg (fun sc => (sc.score g0 f0).pos) (hR oneScorer)
  have hw₁ : w₁ = 1 := by
    simpa [weightedFuse, scaleScorer, scaleEvidence, zeroScorer, oneScorer,
      Evidence.hplus_def, Evidence.one, Evidence.zero] using hLpos
  have hw₂ : w₂ = 1 := by
    simpa [weightedFuse, scaleScorer, scaleEvidence, zeroScorer, oneScorer,
      Evidence.hplus_def, Evidence.one, Evidence.zero] using hRpos
  exact ⟨hw₁, hw₂⟩

theorem weightedFuse_eq_fuse_of_two_sided_neutrality
    {Goal Fact : Type*} (w₁ w₂ : ℝ≥0∞) (g0 : Goal) (f0 : Fact)
    (hL : ∀ s : Scorer Goal Fact, weightedFuse w₁ w₂ s zeroScorer = s)
    (hR : ∀ s : Scorer Goal Fact, weightedFuse w₁ w₂ zeroScorer s = s) :
    weightedFuse w₁ w₂ = (fuse : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact) := by
  rcases weightedFuse_unique_under_two_sided_neutrality
      (w₁ := w₁) (w₂ := w₂) (g0 := g0) (f0 := f0) hL hR with ⟨hw₁, hw₂⟩
  funext s₁ s₂
  simp [weightedFuse, hw₁, hw₂, scaleScorer, scaleEvidence, fuse, Evidence.hplus_def]

/-- Abstract pooling operator for premise scorers. -/
structure PoolingOperator (Goal Fact : Type*) where
  pool : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact
  comm :
    ∀ s₁ s₂, pool s₁ s₂ = pool s₂ s₁
  assoc :
    ∀ s₁ s₂ s₃, pool (pool s₁ s₂) s₃ = pool s₁ (pool s₂ s₃)
  neutral_left :
    ∀ s, pool zeroScorer s = s
  neutral_right :
    ∀ s, pool s zeroScorer = s
  external_bayes :
    ∀ s₁ s₂ likelihood,
      pool (update s₁ likelihood) (update s₂ likelihood) =
        update (pool s₁ s₂) likelihood

/-- `maxPool` is a genuine pooling operator under the current axioms.
This gives a concrete non-additive counterexample to uniqueness. -/
noncomputable def maxPoolingOperator {Goal Fact : Type*} :
    PoolingOperator Goal Fact := by
  refine
    { pool := maxPool
      comm := ?_
      assoc := ?_
      neutral_left := ?_
      neutral_right := ?_
      external_bayes := ?_ }
  · intro s₁ s₂
    apply Scorer.ext
    intro g f
    apply Evidence.ext'
    · simp [maxPool, maxEvidence, max_comm]
    · simp [maxPool, maxEvidence, max_comm]
  · intro s₁ s₂ s₃
    apply Scorer.ext
    intro g f
    apply Evidence.ext'
    · simp [maxPool, maxEvidence, max_assoc]
    · simp [maxPool, maxEvidence, max_assoc]
  · intro s
    apply Scorer.ext
    intro g f
    apply Evidence.ext'
    · simp [maxPool, maxEvidence, zeroScorer, Evidence.zero]
    · simp [maxPool, maxEvidence, zeroScorer, Evidence.zero]
  · intro s
    apply Scorer.ext
    intro g f
    apply Evidence.ext'
    · simp [maxPool, maxEvidence, zeroScorer, Evidence.zero]
    · simp [maxPool, maxEvidence, zeroScorer, Evidence.zero]
  · intro s₁ s₂ likelihood
    apply Scorer.ext
    intro g f
    apply Evidence.ext'
    · simp [maxPool, maxEvidence, update, Evidence.tensor_def, max_mul_mul_right]
    · simp [maxPool, maxEvidence, update, Evidence.tensor_def, max_mul_mul_right]

/-- The current pooling axioms do not characterize `fuse`: `maxPool` is different. -/
theorem maxPoolingOperator_ne_fuse
    {Goal Fact : Type*} [Nonempty Goal] [Nonempty Fact] :
    (maxPoolingOperator (Goal := Goal) (Fact := Fact)).pool ≠ fuse := by
  intro hEq
  let g0 : Goal := Classical.choice ‹Nonempty Goal›
  let f0 : Fact := Classical.choice ‹Nonempty Fact›
  let s2 : Scorer Goal Fact := constScorer ⟨(2 : ℝ≥0∞), 0⟩
  let s3 : Scorer Goal Fact := constScorer ⟨(3 : ℝ≥0∞), 0⟩
  have hAt :=
    congrArg
      (fun F : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact =>
        (F s2 s3).score g0 f0)
      hEq
  have hPosRaw :
      max (2 : ℝ≥0∞) 3 = ((2 : ℝ≥0∞) + 3) := by
    simpa [maxPoolingOperator, maxPool, maxEvidence, fuse, s2, s3, g0, f0,
      constScorer, Evidence.hplus_def] using congrArg Evidence.pos hAt
  have hRealRaw : (max (2 : ℝ) 3) = ((2 : ℝ) + 3) := by
    simpa using congrArg ENNReal.toReal hPosRaw
  norm_num at hRealRaw

/-- `fuse` satisfies the pooling-operator axioms. -/
noncomputable def fusePoolingOperator {Goal Fact : Type*} :
    PoolingOperator Goal Fact := by
  refine
    { pool := fuse
      comm := ?_
      assoc := ?_
      neutral_left := ?_
      neutral_right := ?_
      external_bayes := ?_ }
  · intro s₁ s₂
    apply Scorer.ext
    intro g f
    simp [fuse, Evidence.hplus_def, add_comm]
  · intro s₁ s₂ s₃
    apply Scorer.ext
    intro g f
    simp [fuse, Evidence.hplus_def, add_assoc]
  · intro s
    apply Scorer.ext
    intro g f
    simp [fuse, zeroScorer, Evidence.hplus_def, Evidence.zero]
  · intro s
    apply Scorer.ext
    intro g f
    simp [fuse, zeroScorer, Evidence.hplus_def, Evidence.zero]
  · intro s₁ s₂ likelihood
    exact externalBayesianity_hplus_tensor s₁ s₂ likelihood

/-- Characterization inside the weighted family:
if a weighted pool satisfies full pooling-operator axioms, it is exactly `fuse`. -/
theorem weighted_poolingOperator_forces_fuse
    {Goal Fact : Type*}
    (w₁ w₂ : ℝ≥0∞) (g0 : Goal) (f0 : Fact)
    (P : PoolingOperator Goal Fact)
    (hP : P.pool = weightedFuse w₁ w₂) :
    P.pool = fuse := by
  have hLwf : ∀ s : Scorer Goal Fact, weightedFuse w₁ w₂ s zeroScorer = s := by
    intro s
    calc
      weightedFuse w₁ w₂ s zeroScorer = P.pool s zeroScorer := by simp [hP]
      _ = s := P.neutral_right s
  have hRwf : ∀ s : Scorer Goal Fact, weightedFuse w₁ w₂ zeroScorer s = s := by
    intro s
    calc
      weightedFuse w₁ w₂ zeroScorer s = P.pool zeroScorer s := by simp [hP]
      _ = s := P.neutral_left s
  have hEqWF :
      weightedFuse w₁ w₂ = (fuse : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact) :=
    weightedFuse_eq_fuse_of_two_sided_neutrality
      (w₁ := w₁) (w₂ := w₂) (g0 := g0) (f0 := f0) hLwf hRwf
  simpa [hP] using hEqWF

/-- Mask selecting the positive-evidence coordinate under tensor. -/
def maskPos : Evidence := ⟨1, 0⟩

/-- Mask selecting the negative-evidence coordinate under tensor. -/
def maskNeg : Evidence := ⟨0, 1⟩

@[simp] lemma tensor_maskPos (x : Evidence) :
    x * maskPos = ⟨x.pos, 0⟩ := by
  simp [maskPos, Evidence.tensor_def]

@[simp] lemma tensor_maskNeg (x : Evidence) :
    x * maskNeg = ⟨0, x.neg⟩ := by
  simp [maskNeg, Evidence.tensor_def]

/-- Corrected uniqueness theorem at evidence level:
external-Bayesianity with respect to tensor + total additivity forces additive pooling. -/
theorem poolE_eq_hplus_of_externalBayes_totalAdd
    (poolE : Evidence → Evidence → Evidence)
    (hexBayes : ∀ x y ℓ, poolE (x * ℓ) (y * ℓ) = poolE x y * ℓ)
    (htotal : ∀ x y, (poolE x y).total = x.total + y.total) :
    ∀ x y, poolE x y = x + y := by
  intro x y
  have hMaskPos := hexBayes x y maskPos
  have hMaskNeg := hexBayes x y maskNeg
  have hneg_left_posmask : (poolE (x * maskPos) (y * maskPos)).neg = 0 := by
    simpa [maskPos, Evidence.tensor_def] using congrArg Evidence.neg hMaskPos
  have htot_left_posmask :
      (poolE (x * maskPos) (y * maskPos)).total = x.pos + y.pos := by
    calc
      (poolE (x * maskPos) (y * maskPos)).total
          = (x * maskPos).total + (y * maskPos).total := htotal _ _
      _ = x.pos + y.pos := by simp [maskPos, Evidence.tensor_def, Evidence.total]
  have hpos_left_posmask :
      (poolE (x * maskPos) (y * maskPos)).pos = x.pos + y.pos := by
    have hsum :
        (poolE (x * maskPos) (y * maskPos)).pos
          + (poolE (x * maskPos) (y * maskPos)).neg = x.pos + y.pos := by
      simpa [Evidence.total] using htot_left_posmask
    rw [hneg_left_posmask, add_zero] at hsum
    exact hsum
  have hpos_xy :
      (poolE x y).pos = x.pos + y.pos := by
    have hpos_mask :
        (poolE (x * maskPos) (y * maskPos)).pos = (poolE x y).pos := by
      simpa [maskPos, Evidence.tensor_def] using congrArg Evidence.pos hMaskPos
    exact hpos_mask.symm.trans hpos_left_posmask
  have hpos_left_negmask : (poolE (x * maskNeg) (y * maskNeg)).pos = 0 := by
    simpa [maskNeg, Evidence.tensor_def] using congrArg Evidence.pos hMaskNeg
  have htot_left_negmask :
      (poolE (x * maskNeg) (y * maskNeg)).total = x.neg + y.neg := by
    calc
      (poolE (x * maskNeg) (y * maskNeg)).total
          = (x * maskNeg).total + (y * maskNeg).total := htotal _ _
      _ = x.neg + y.neg := by simp [maskNeg, Evidence.tensor_def, Evidence.total]
  have hneg_left_negmask :
      (poolE (x * maskNeg) (y * maskNeg)).neg = x.neg + y.neg := by
    have hsum :
        (poolE (x * maskNeg) (y * maskNeg)).pos
          + (poolE (x * maskNeg) (y * maskNeg)).neg = x.neg + y.neg := by
      simpa [Evidence.total] using htot_left_negmask
    rw [hpos_left_negmask, zero_add] at hsum
    exact hsum
  have hneg_xy :
      (poolE x y).neg = x.neg + y.neg := by
    have hneg_mask :
        (poolE (x * maskNeg) (y * maskNeg)).neg = (poolE x y).neg := by
      simpa [maskNeg, Evidence.tensor_def] using congrArg Evidence.neg hMaskNeg
    exact hneg_mask.symm.trans hneg_left_negmask
  exact Evidence.ext' hpos_xy hneg_xy

/-- Corrected scorer-level uniqueness:
if a pooling operator is pointwise from `poolE`, and `poolE` is total-additive,
then external-Bayesianity forces `pool = fuse`. -/
theorem poolingOperator_pointwise_unique_of_externalBayes_totalAdd
    {Goal Fact : Type*} [Nonempty Goal] [Nonempty Fact]
    (P : PoolingOperator Goal Fact)
    (poolE : Evidence → Evidence → Evidence)
    (hpointwise :
      ∀ s₁ s₂ g f, (P.pool s₁ s₂).score g f = poolE (s₁.score g f) (s₂.score g f))
    (htotal : ∀ x y, (poolE x y).total = x.total + y.total) :
    P.pool = fuse := by
  have hexBayesE : ∀ x y ℓ, poolE (x * ℓ) (y * ℓ) = poolE x y * ℓ := by
    intro x y ℓ
    let sx : Scorer Goal Fact := constScorer x
    let sy : Scorer Goal Fact := constScorer y
    let sl : Scorer Goal Fact := constScorer ℓ
    have hsc : P.pool (update sx sl) (update sy sl) = update (P.pool sx sy) sl :=
      P.external_bayes sx sy sl
    let g0 : Goal := Classical.choice ‹Nonempty Goal›
    let f0 : Fact := Classical.choice ‹Nonempty Fact›
    have hAt := congrArg (fun sc : Scorer Goal Fact => sc.score g0 f0) hsc
    simpa [sx, sy, sl, update, constScorer, hpointwise, g0, f0] using hAt
  have hpoolE : ∀ x y, poolE x y = x + y :=
    poolE_eq_hplus_of_externalBayes_totalAdd poolE hexBayesE htotal
  funext s₁ s₂
  apply Scorer.ext
  intro g f
  calc
    (P.pool s₁ s₂).score g f = poolE (s₁.score g f) (s₂.score g f) := hpointwise s₁ s₂ g f
    _ = s₁.score g f + s₂.score g f := hpoolE _ _
    _ = (fuse s₁ s₂).score g f := rfl

/-- Necessity of a pointwise lift for scorer-level uniqueness arguments:
if a pooling operator admits no evidence-level pointwise kernel, it cannot be `fuse`. -/
theorem not_fuse_of_no_pointwise_lift
    {Goal Fact : Type*}
    (P : PoolingOperator Goal Fact)
    (hNoPointwise :
      ¬ ∃ poolE : Evidence → Evidence → Evidence,
        ∀ s₁ s₂ g f, (P.pool s₁ s₂).score g f = poolE (s₁.score g f) (s₂.score g f)) :
    P.pool ≠ fuse := by
  intro hEq
  apply hNoPointwise
  refine ⟨(fun x y => x + y), ?_⟩
  intro s₁ s₂ g f
  simp [hEq, fuse]

/-- In the weighted-linear family, the two weights are uniquely determined by the
pooling operator itself. -/
theorem weightedFuse_weights_identifiable
    {Goal Fact : Type*}
    (w₁ w₂ w₁' w₂' : ℝ≥0∞) (g0 : Goal) (f0 : Fact) :
    weightedFuse w₁ w₂ = (weightedFuse w₁' w₂' : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact)
      ↔ w₁ = w₁' ∧ w₂ = w₂' := by
  constructor
  · intro hEq
    have hLeftScorer :
        weightedFuse w₁ w₂ (oneScorer : Scorer Goal Fact) (zeroScorer : Scorer Goal Fact) =
          weightedFuse w₁' w₂' (oneScorer : Scorer Goal Fact) (zeroScorer : Scorer Goal Fact) := by
      simpa using
        congrArg
          (fun (F : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact) =>
            F (oneScorer : Scorer Goal Fact) (zeroScorer : Scorer Goal Fact))
          hEq
    have hRightScorer :
        weightedFuse w₁ w₂ (zeroScorer : Scorer Goal Fact) (oneScorer : Scorer Goal Fact) =
          weightedFuse w₁' w₂' (zeroScorer : Scorer Goal Fact) (oneScorer : Scorer Goal Fact) := by
      simpa using
        congrArg
          (fun (F : Scorer Goal Fact → Scorer Goal Fact → Scorer Goal Fact) =>
            F (zeroScorer : Scorer Goal Fact) (oneScorer : Scorer Goal Fact))
          hEq
    have hw₁ :
        w₁ = w₁' := by
      have hpos :=
        congrArg (fun sc : Scorer Goal Fact => (sc.score g0 f0).pos) hLeftScorer
      simpa [weightedFuse, scaleScorer, scaleEvidence, oneScorer, zeroScorer,
        fuse, Evidence.hplus_def, Evidence.one, Evidence.zero] using hpos
    have hw₂ :
        w₂ = w₂' := by
      have hpos :=
        congrArg (fun sc : Scorer Goal Fact => (sc.score g0 f0).pos) hRightScorer
      simpa [weightedFuse, scaleScorer, scaleEvidence, oneScorer, zeroScorer,
        fuse, Evidence.hplus_def, Evidence.one, Evidence.zero] using hpos
    exact ⟨hw₁, hw₂⟩
  · intro h
    rcases h with ⟨hw₁, hw₂⟩
    subst hw₁
    subst hw₂
    rfl

/-- Strength is invariant under pool/update order (commutation corollary). -/
theorem externalBayesianity_strength {Goal Fact : Type*}
    (s₁ s₂ likelihood : Scorer Goal Fact) (g : Goal) (f : Fact) :
    Evidence.toStrength ((fuse (update s₁ likelihood) (update s₂ likelihood)).score g f) =
      Evidence.toStrength ((update (fuse s₁ s₂) likelihood).score g f) := by
  simp [externalBayesianity_hplus_tensor (s₁ := s₁) (s₂ := s₂) (likelihood := likelihood)]

/-- Confidence is invariant under pool/update order (commutation corollary). -/
theorem externalBayesianity_confidence {Goal Fact : Type*}
    (κ : ℝ≥0∞) (s₁ s₂ likelihood : Scorer Goal Fact) (g : Goal) (f : Fact) :
    Evidence.toConfidence κ
      ((fuse (update s₁ likelihood) (update s₂ likelihood)).score g f) =
      Evidence.toConfidence κ
        ((update (fuse s₁ s₂) likelihood).score g f) := by
  simp [externalBayesianity_hplus_tensor (s₁ := s₁) (s₂ := s₂) (likelihood := likelihood)]

/-- Strength is invariant under finite-family pool/update order. -/
theorem externalBayesianity_fuseFamily_strength {Goal Fact ι : Type*} [Fintype ι]
    (s : ι → Scorer Goal Fact) (likelihood : Scorer Goal Fact) (g : Goal) (f : Fact) :
    Evidence.toStrength ((fuseFamily (fun i => update (s i) likelihood)).score g f) =
      Evidence.toStrength ((update (fuseFamily s) likelihood).score g f) := by
  simp [externalBayesianity_fuseFamily_tensor (s := s) (likelihood := likelihood)]

/-- Confidence is invariant under finite-family pool/update order. -/
theorem externalBayesianity_fuseFamily_confidence {Goal Fact ι : Type*} [Fintype ι]
    (κ : ℝ≥0∞) (s : ι → Scorer Goal Fact) (likelihood : Scorer Goal Fact) (g : Goal) (f : Fact) :
    Evidence.toConfidence κ ((fuseFamily (fun i => update (s i) likelihood)).score g f) =
      Evidence.toConfidence κ ((update (fuseFamily s) likelihood).score g f) := by
  simp [externalBayesianity_fuseFamily_tensor (s := s) (likelihood := likelihood)]

end Mettapedia.Logic.PremiseSelection
