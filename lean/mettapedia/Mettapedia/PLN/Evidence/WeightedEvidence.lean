import Mettapedia.PLN.Evidence.EvidentialLedger

/-!
# Weighted binary evidence and fractional fading

PLN's existing `BinaryEvidence` is already the honest weighted count carrier:
its coordinates lie in `ℝ≥0∞`, independent fusion is componentwise addition,
and strength/confidence are derived views.  This file gives that carrier the
explicit operational name `WeightedEvidence` and adds the missing
nonnegative-scalar action used for fractional forgetting.  It does not create
a second evidence representation.

Uniform fading distributes over fusion.  The temporal operation used online
is different: it fades the old packet and then fuses fresh evidence at full
weight.  A theorem below states that distinction exactly, with a concrete
noncommuting fixture.
-/

namespace Mettapedia.PLN.Evidence

open EvidenceQuantale
open EvidentialLedger
open scoped ENNReal

/-- Operational name for the existing real-weighted PLN evidence carrier. -/
abbrev WeightedEvidence := BinaryEvidence

namespace WeightedEvidence

/-! ## Fusion and the exact-count embedding -/

/-- Exact natural counts embed additively into weighted evidence. -/
noncomputable def ofBinEvNat : BinEvNat →+ WeightedEvidence where
  toFun := BinEvNat.toBinaryEvidence
  map_zero' := BinEvNat.toBinaryEvidence_zero
  map_add' := BinEvNat.toBinaryEvidence_add

/-- The exact-count embedding preserves both coordinates. -/
theorem ofBinEvNat_components (evidence : BinEvNat) :
    (ofBinEvNat evidence).pos = evidence.pos ∧
      (ofBinEvNat evidence).neg = evidence.neg := by
  exact ⟨rfl, rfl⟩

/-- The exact-count embedding is injective. -/
theorem ofBinEvNat_injective : Function.Injective ofBinEvNat := by
  intro first second heq
  apply BinEvNat.ext
  · have hpos := congrArg BinaryEvidence.pos heq
    change (first.pos : ℝ≥0∞) = (second.pos : ℝ≥0∞) at hpos
    exact_mod_cast hpos
  · have hneg := congrArg BinaryEvidence.neg heq
    change (first.neg : ℝ≥0∞) = (second.neg : ℝ≥0∞) at hneg
    exact_mod_cast hneg

/-- Fusion is the inherited commutative-monoid addition of weighted counts. -/
theorem fusion_components (first second : WeightedEvidence) :
    ((first + second).pos, (first + second).neg) =
      (first.pos + second.pos, first.neg + second.neg) :=
  rfl

/-! ## Derived chart and effective evidence -/

/-- Strength and confidence remain derived columns over weighted counts. -/
noncomputable def derivedSTV
    (κ : ℝ≥0∞) (evidence : WeightedEvidence) : ℝ × ℝ :=
  BinaryEvidence.toSTV κ evidence

/-- The weighted chart is exactly PLN's canonical strength/confidence view. -/
theorem derivedSTV_eq_canonical
    (κ : ℝ≥0∞) (evidence : WeightedEvidence) :
    derivedSTV κ evidence =
      ((BinaryEvidence.toStrength evidence).toReal,
       (BinaryEvidence.toConfidence κ evidence).toReal) :=
  rfl

/-- Effective evidence is the total real-weighted count. -/
noncomputable def effectiveEvidence (evidence : WeightedEvidence) : ℝ≥0∞ :=
  evidence.total

/-- The existing confidence formula is a function of effective evidence alone. -/
theorem confidence_eq_effectiveEvidence_div
    (κ : ℝ≥0∞) (evidence : WeightedEvidence) :
    BinaryEvidence.toConfidence κ evidence =
      effectiveEvidence evidence / (effectiveEvidence evidence + κ) :=
  rfl

/-! ## Fractional fading as a distributive monoid action -/

/-- Scale both weighted evidence coordinates by a nonnegative retention. -/
noncomputable instance : SMul ℝ≥0∞ WeightedEvidence where
  smul retention evidence :=
    ⟨retention * evidence.pos, retention * evidence.neg⟩

/-- Nonnegative retention acts multiplicatively and distributes over evidence
fusion, so fractional fading is a lawful action on the additive carrier. -/
noncomputable instance : DistribMulAction ℝ≥0∞ WeightedEvidence where
  one_smul evidence := by
    ext <;> simp [HSMul.hSMul, SMul.smul]
  mul_smul first second evidence := by
    ext <;> simp [HSMul.hSMul, SMul.smul, mul_assoc]
  smul_zero retention := by
    ext <;> simp [HSMul.hSMul, SMul.smul]
  smul_add retention first second := by
    ext <;> simp [HSMul.hSMul, SMul.smul, mul_add,
      BinaryEvidence.hplus_def]

/-- Fading scales effective evidence by exactly the same retention. -/
theorem effectiveEvidence_smul
    (retention : ℝ≥0∞) (evidence : WeightedEvidence) :
    effectiveEvidence (retention • evidence) =
      retention * effectiveEvidence evidence := by
  unfold effectiveEvidence BinaryEvidence.total
  change retention * evidence.pos + retention * evidence.neg =
    retention * (evidence.pos + evidence.neg)
  exact (mul_add retention evidence.pos evidence.neg).symm

/-- Fusion adds effective evidence exactly. -/
theorem effectiveEvidence_add (first second : WeightedEvidence) :
    effectiveEvidence (first + second) =
      effectiveEvidence first + effectiveEvidence second := by
  unfold effectiveEvidence BinaryEvidence.total
  simp only [BinaryEvidence.hplus_def]
  ac_rfl

/-- Uniformly fading an already fused batch commutes with fusion. -/
theorem smul_fusion
    (retention : ℝ≥0∞) (first second : WeightedEvidence) :
    retention • (first + second) =
      retention • first + retention • second :=
  smul_add retention first second

/-- Online temporal revision: fade old evidence, then add fresh evidence at
full weight. -/
noncomputable def fadeThenFuse
    (retention : ℝ≥0∞) (old fresh : WeightedEvidence) : WeightedEvidence :=
  retention • old + fresh

/-- Batch fading: fuse first, then fade both packets. -/
noncomputable def fuseThenFade
    (retention : ℝ≥0∞) (old fresh : WeightedEvidence) : WeightedEvidence :=
  retention • (old + fresh)

/-- Precise interaction law: batch fading also fades the fresh packet, whereas
online temporal revision does not. -/
theorem fuseThenFade_eq_fadedOld_add_fadedFresh
    (retention : ℝ≥0∞) (old fresh : WeightedEvidence) :
    fuseThenFade retention old fresh =
      retention • old + retention • fresh := by
  exact smul_fusion retention old fresh

/-- Unit retention makes online and batch order coincide with exact addition. -/
theorem fadeThenFuse_one
    (old fresh : WeightedEvidence) :
    fadeThenFuse 1 old fresh = old + fresh := by
  simp [fadeThenFuse]

/-- Exponential law: iterating a fixed fade is multiplication by the retention
power. -/
theorem fade_iterate
    (retention : ℝ≥0∞) (evidence : WeightedEvidence) (steps : ℕ) :
    (fun current => retention • current)^[steps] evidence =
      retention ^ steps • evidence := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      simpa [mul_comm] using
        (mul_smul retention (retention ^ steps) evidence).symm

/-! ## Positive and negative fixtures -/

/-- Exact counts enter the weighted fusion monoid without changing values. -/
theorem exactCountEmbedding_positiveExample :
    ofBinEvNat (⟨2, 1⟩ : BinEvNat) + ofBinEvNat ⟨1, 2⟩ =
      (⟨3, 3⟩ : WeightedEvidence) := by
  ext <;> norm_num [ofBinEvNat, BinEvNat.toBinaryEvidence,
    BinaryEvidence.hplus_def]

/-- Half retention produces genuinely fractional evidence. -/
theorem halfFade_positiveExample :
    ((1 / 2 : ℝ≥0∞) • ofBinEvNat (⟨1, 1⟩ : BinEvNat)) =
      (⟨1 / 2, 1 / 2⟩ : WeightedEvidence) := by
  ext <;> norm_num [ofBinEvNat, BinEvNat.toBinaryEvidence,
    HSMul.hSMul, SMul.smul]

/-- Negative commutation fixture: fresh evidence must not be retroactively
discarded, so online fade-then-fuse differs from fuse-then-fade. -/
theorem fadeThenFuse_ne_fuseThenFade_negativeExample :
    fadeThenFuse 0 (⟨2, 0⟩ : WeightedEvidence) ⟨1, 0⟩ ≠
      fuseThenFade 0 (⟨2, 0⟩ : WeightedEvidence) ⟨1, 0⟩ := by
  intro heq
  have hpos := congrArg BinaryEvidence.pos heq
  norm_num [fadeThenFuse, fuseThenFade, HSMul.hSMul, SMul.smul,
    BinaryEvidence.hplus_def] at hpos

#print axioms ofBinEvNat_injective
#print axioms fusion_components
#print axioms derivedSTV_eq_canonical
#print axioms effectiveEvidence_smul
#print axioms effectiveEvidence_add
#print axioms smul_fusion
#print axioms fadeThenFuse_one
#print axioms fade_iterate
#print axioms exactCountEmbedding_positiveExample
#print axioms halfFade_positiveExample
#print axioms fadeThenFuse_ne_fuseThenFade_negativeExample

end WeightedEvidence

end Mettapedia.PLN.Evidence
