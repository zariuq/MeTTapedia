import Mathlib.Tactic
import Mettapedia.Logic.PeTTaLibPLNTruthFunctions
import Mettapedia.Logic.PLNClassicTruthFunctions
import Mettapedia.Logic.NuPLNEvidenceBridge
import Mettapedia.Logic.PLNRevision
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNInferenceRules
import Mettapedia.Logic.PLNConjunction

namespace Mettapedia.Logic.WMPLNJustifiedTruthFunctions

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLNInferenceRules

/-!
# WM-PLN Justified Truth Functions

This file records the strongest theorem-backed truth-value formulas and
conservative scalar bounds currently available in the Lean WM-PLN development.

Interpretation:

* "Exact" means backed by explicit world-model / BinaryEvidence / probability
  bridge theorems already in the development.
* "Conservative" means the scalar confidence formula is justified as a safe
  lower bound or safe bounded aggregator, but not yet proved uniquely canonical.
* Heuristic OpenCog/PeTTa extras that lack a theorem path are intentionally
  omitted from this file.

Quick map for readers:

* Exact WM-backed TV rules in this file:
  - `truthRevision`
  - `truthInduction`
  - `truthAbduction`
  - `truthNegation`
* Conservative scalar TV rules in this file:
  - `truthDeductionConservative`
  - `truthModusPonensConservative`
  - `truthSymmetricModusPonensConservative`
* Additional WM-backed TV surfaces not present in current upstream PeTTa main:
  - `truthPredictiveImplicationConservative`
  - `truthConjunctionConditionalConservative`
  - `truthConjunctionIndependentEvidenceStyle`
  - `truthConjunctionHypergeometric`
* Distribution-backed WM view families live in:
  - `Mettapedia.Logic.WMPLNDistributionalTruthFunctions`
* Formal comparison against PeTTa and canonical upstream lives in:
  - `Mettapedia.Logic.PeTTaLibPLNFormalAnalysis`

Design note:

* Conjunction is currently kept regime-explicit rather than collapsed into a
  single overloaded `truthConjunction`. The present file exposes the
  conditional/product, independent/evidence-style, and hypergeometric/modal
  regimes separately because they answer different semantic questions.

## Reading this file if you are not a Lean user

The *story* lives in (i) section headers, (ii) theorem and definition
names, and (iii) their plain-English docstrings (`/-- ... -/`). Proof
bodies — the blocks starting with `by` — are machine verification and
can be skipped on first read.

Lean syntax you will see:

* `TV.s`, `TV.c` are accessor dot-notation; for a truth value `t`,
  `t.s` is its strength and `t.c` its confidence.
* `Set.Icc a b` is the closed interval `[a, b]`; appears as in-range
  hypotheses on inputs.
* `theorem foo : … := by …` is a claim followed by its proof. The
  claim is everything before `:=`; the proof lives after `by` and can
  be skipped.
* `noncomputable def` introduces a real-valued function defined via
  classical reals; semantically identical to a PLN/MeTTa formula, just
  not kernel-executable.
* Anonymous-constructor `⟨a, b⟩` builds a pair / structure value; e.g.
  `⟨0.7, 0.9⟩` for a TV with strength 0.7 and confidence 0.9.

PLN-adjacent auxiliary symbols used throughout:

* `MAX_CONF = 0.9999` — the hard confidence cap (a confidence of 1 is
  disallowed so that more evidence can always raise it).
* `c2w c = c / (1 - c)` — confidence → evidence weight.
* `w2c w = w / (w + 1)` — evidence weight → confidence (inverse of
  `c2w`).
* `capConf c = max 0 (min c MAX_CONF)` — clip into `[0, MAX_CONF]`.

**The running story.** The exact induction/abduction confidence currently
used here is `w2c (min (c2w cBA) (c2w cBC))`: the min is taken in weight
space, then converted back. A theorem in this file
(`truthInduction_conf_eq_min_capped`) proves that this round-trip
equals `min (capConf cBA) (capConf cBC)` — the intuitive "your chained
confidence is the weaker of your two inputs'".

The historical raw-min formula `w2c (min cBA cBC)` is analyzed in
`Mettapedia.Logic.PLNBugAnalysis`; it double-damps by treating a
confidence as if it were already an evidence weight.
-/

abbrev TV := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV
abbrev MettaTV := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.TV
abbrev MAX_CONF := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.MAX_CONF
abbrev capConf := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.capConf

/-- A no-op type coercion. The Lean code has two aliases (`TV` and
`MettaTV`) for the same `(strength, confidence)` pair, and this is the
identity between them — nothing numeric happens. It exists only to keep
bridge-theorem statements readable by avoiding explicit alias-swap
gymnastics. -/
def toMettaTV (t : TV) : MettaTV := t

@[simp] theorem toMettaTV_s (t : TV) : (toMettaTV t).s = t.s := rfl

@[simp] theorem toMettaTV_c (t : TV) : (toMettaTV t).c = t.c := rfl

/-! ## Exact WM-backed rules -/

/-- Exact TV-level revision rule, justified by BinaryEvidence aggregation. -/
noncomputable def truthRevision (t1 t2 : TV) : TV :=
  let w1 := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w t1.c
  let w2 := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w t2.c
  let w := w1 + w2
  let f := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.safeDiv (w1 * t1.s + w2 * t2.s) w
  let c := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c w
  ⟨min 1 f, min 1 c⟩

theorem truthRevision_strength_eq_toStrength
    (κ : ENNReal) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (t1 t2 : TV)
    (hs1 : 0 ≤ t1.s) (hs1' : t1.s ≤ 1)
    (hs2 : 0 ≤ t2.s) (hs2' : t2.s ≤ 1) :
    (truthRevision t1 t2).s =
      (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.BinaryEvidence.toTV κ
        (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t1) +
         Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t2))).s := by
  exact congrArg (·.s)
    (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.truthRevision_eq_toTV_hplus
      (κ := κ) hκ0 hκT (toMettaTV t1) (toMettaTV t2) hs1 hs1' hs2 hs2')

theorem truthRevision_conf_eq_toConfidence
    (κ : ENNReal) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (t1 t2 : TV)
    (hs1 : 0 ≤ t1.s) (hs1' : t1.s ≤ 1)
    (hs2 : 0 ≤ t2.s) (hs2' : t2.s ≤ 1) :
    (truthRevision t1 t2).c =
      (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.BinaryEvidence.toTV κ
        (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t1) +
         Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t2))).c := by
  exact congrArg (·.c)
    (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.truthRevision_eq_toTV_hplus
      (κ := κ) hκ0 hκT (toMettaTV t1) (toMettaTV t2) hs1 hs1' hs2 hs2')

/-- **Revision, read as evidence accumulation.** The revised TV equals
what you get by translating both inputs into BinaryEvidence count form
(counts of positive and negative observations, parameterized by the
evidence-scale `κ`), summing those counts, and translating the sum
back into a TV.

This is the theorem that justifies using PLN revision as the
single-parameter aggregator for independent observations of the same
hypothesis: it is literally "accumulate the counts, then read off the
(strength, confidence) summary." -/
theorem truthRevision_eq_toTV_hplus
    (κ : ENNReal) (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤)
    (t1 t2 : TV)
    (hs1 : 0 ≤ t1.s) (hs1' : t1.s ≤ 1)
    (hs2 : 0 ≤ t2.s) (hs2' : t2.s ≤ 1) :
    toMettaTV (truthRevision t1 t2) =
      Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.BinaryEvidence.toTV κ
        (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t1) +
         Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t2)) := by
  let rhs :=
    Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.BinaryEvidence.toTV κ
      (Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t1) +
       Mettapedia.Logic.NuEvidenceQuantaleBridge.Bridge.TV.toEvidence κ (toMettaTV t2))
  have hs : (truthRevision t1 t2).s = rhs.s :=
    truthRevision_strength_eq_toStrength κ hκ0 hκT t1 t2 hs1 hs1' hs2 hs2'
  have hc : (truthRevision t1 t2).c = rhs.c :=
    truthRevision_conf_eq_toConfidence κ hκ0 hκT t1 t2 hs1 hs1' hs2 hs2'
  cases htv : rhs with
  | mk s c =>
      simp [rhs, htv, toMettaTV] at hs hc ⊢
      cases hs
      cases hc
      simpa [rhs, toMettaTV] using htv.symm

/-- Exact induction rule currently justified in Lean:
strength from the Bayes+dediuction derivation, confidence from the corrected
weight-space minimum (equivalently min of capped confidences). -/
noncomputable def truthInduction (a b c ba bc : TV) : TV :=
  let s := plnInductionStrength ba.s bc.s a.s b.s c.s
  let conf :=
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
      (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w ba.c)
           (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w bc.c))
  ⟨s, conf⟩

theorem truthInduction_strength_eq (a b c ba bc : TV) :
    (truthInduction a b c ba bc).s = plnInductionStrength ba.s bc.s a.s b.s c.s := by
  simp [truthInduction]

/-- **Headline theorem: the weight-space detour collapses.** The
WM-corrected induction confidence is just the smaller of the two input
confidences, after each has been clipped to `[0, MAX_CONF]`. In
symbols: `w2c (min (c2w cBA) (c2w cBC)) = min (capConf cBA) (capConf cBC)`.

Intuition: go into weight space, take the min, come back — the detour
cancels. The weight-space transform is not adding anything fancy; it is
exactly the right wrapper to make the obvious answer come out.

**Numeric example.** For `cBA = 0.5, cBC = 0.7`, both `capConf` calls
are the identity, so this theorem gives `min(0.5, 0.7) = 0.5` — "your
chained confidence equals your weakest input's." The historical raw-min
bug computed `Truth_w2c (min cBA cBC) = w2c(0.5) = 0.5 / 1.5 = 1/3 ≈
0.333` instead by feeding a raw confidence back into `w2c` as if it were
a weight. -/
theorem truthInduction_conf_eq_min_capped (a b c ba bc : TV) :
    (truthInduction a b c ba bc).c = min (capConf ba.c) (capConf bc.c) := by
  simpa [truthInduction, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthInduction] using
    Mettapedia.Logic.NuEvidenceQuantaleBridge.InductionAbductionBridge.inductionAbduction_conf_eq_min_capped
      ba.c bc.c

/-- Consequence of `truthInduction_conf_eq_min_capped`: chained
induction confidence never exceeds the weakest input confidence. You
never get *more* confident by chaining than you were on your
most-uncertain premise. -/
theorem truthInduction_conf_le_inputs
    (a b c ba bc : TV) (hba : 0 ≤ ba.c) (hbc : 0 ≤ bc.c) :
    (truthInduction a b c ba bc).c ≤ min ba.c bc.c := by
  simpa [truthInduction] using
    Mettapedia.Logic.NuEvidenceQuantaleBridge.InductionAbductionBridge.inductionAbduction_conf_le_min
      ba.c bc.c hba hbc

/-- Exact abduction rule currently justified in Lean:
strength from the Bayes+dediuction derivation, confidence from the corrected
weight-space minimum (equivalently min of capped confidences). -/
noncomputable def truthAbduction (a b c ab cb : TV) : TV :=
  let s := plnAbductionStrength ab.s cb.s a.s b.s c.s
  let conf :=
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
      (min (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w ab.c)
           (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w cb.c))
  ⟨s, conf⟩

theorem truthAbduction_strength_eq (a b c ab cb : TV) :
    (truthAbduction a b c ab cb).s = plnAbductionStrength ab.s cb.s a.s b.s c.s := by
  simp [truthAbduction]

/-- Abduction counterpart of the induction headline theorem. The
WM-corrected abduction confidence also reduces to the plain
`min (capConf cAB) (capConf cCB)`: same collapse of the weight-space
round-trip, same intuition ("weaker premise wins"), same correction of
the historical raw-min double-damping formula `Truth_w2c (min cAB cCB)`. -/
theorem truthAbduction_conf_eq_min_capped (a b c ab cb : TV) :
    (truthAbduction a b c ab cb).c = min (capConf ab.c) (capConf cb.c) := by
  simpa [truthAbduction, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthAbduction] using
    Mettapedia.Logic.NuEvidenceQuantaleBridge.InductionAbductionBridge.inductionAbduction_conf_eq_min_capped
      ab.c cb.c

/-- Consequence of `truthAbduction_conf_eq_min_capped`: chained
abduction confidence is capped by the weaker premise confidence. -/
theorem truthAbduction_conf_le_inputs
    (a b c ab cb : TV) (hab : 0 ≤ ab.c) (hcb : 0 ≤ cb.c) :
    (truthAbduction a b c ab cb).c ≤ min ab.c cb.c := by
  simpa [truthAbduction] using
    Mettapedia.Logic.NuEvidenceQuantaleBridge.InductionAbductionBridge.inductionAbduction_conf_le_min
      ab.c cb.c hab hcb

/-- Exact negation rule at the truth-value layer. -/
noncomputable abbrev truthNegation := Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthNegation

@[simp] theorem truthNegation_strength_eq (t : TV) :
    (truthNegation t).s = 1 - t.s := by
  rfl

@[simp] theorem truthNegation_conf_eq (t : TV) :
    (truthNegation t).c = t.c := by
  rfl

/-! ## Conservative scalar rules -/

/-- Deduction with exact strength formula and conservative minimum-confidence rule.

The strength component is backed by the probability/deduction bridge. The
confidence component is a conservative lower bound rather than a uniquely
derived WM confidence law. -/
noncomputable abbrev truthDeductionConservative :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction

theorem truthDeduction_conf_le_inputs
    (p q r pq qr : TV)
    (hp : 0 ≤ p.c) (hq : 0 ≤ q.c) (hr : 0 ≤ r.c) (hpq : 0 ≤ pq.c) (hqr : 0 ≤ qr.c) :
    (truthDeductionConservative p q r pq qr).c ≤ p.c ∧
    (truthDeductionConservative p q r pq qr).c ≤ q.c ∧
    (truthDeductionConservative p q r pq qr).c ≤ r.c ∧
    (truthDeductionConservative p q r pq qr).c ≤ pq.c ∧
    (truthDeductionConservative p q r pq qr).c ≤ qr.c := by
  by_cases h :
      conditionalProbabilityConsistency p.s q.s pq.s ∧
      conditionalProbabilityConsistency q.s r.s qr.s
  · have hc :
        (truthDeductionConservative p q r pq qr).c =
          min p.c (min q.c (min r.c (min pq.c qr.c))) := by
        simp [truthDeductionConservative, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction, h]
    rw [hc]
    exact Mettapedia.Logic.PLNDeduction.min_confidence_is_lower_bound
      p.c q.c r.c pq.c qr.c
  · have hc : (truthDeductionConservative p q r pq qr).c = 0 := by
        simp [truthDeductionConservative, Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthDeduction, h]
    rw [hc]
    exact And.intro hp (And.intro hq (And.intro hr (And.intro hpq hqr)))

/-- Modus ponens with PeTTa's product confidence, kept only as a conservative
scalar bound. -/
noncomputable abbrev truthModusPonensConservative :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthModusPonens

theorem truthModusPonens_conf_nonneg
    (p pq : TV) (hp : 0 ≤ p.c) (hpq : 0 ≤ pq.c) :
    0 ≤ (truthModusPonensConservative p pq).c := by
  change 0 ≤ p.c * pq.c
  exact mul_nonneg hp hpq

theorem truthModusPonens_conf_le_inputs
    (p pq : TV) (hp : p.c ∈ Set.Icc (0 : ℝ) 1) (hpq : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    (truthModusPonensConservative p pq).c ≤ p.c ∧
    (truthModusPonensConservative p pq).c ≤ pq.c := by
  constructor
  · change p.c * pq.c ≤ p.c
    nlinarith [hp.1, hp.2, hpq.1, hpq.2]
  · change p.c * pq.c ≤ pq.c
    nlinarith [hp.1, hp.2, hpq.1, hpq.2]

/-- Symmetric modus ponens with PeTTa's minimum-style confidence, kept as a
conservative scalar bound. -/
noncomputable abbrev truthSymmetricModusPonensConservative :=
  Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens

theorem truthSymmetricModusPonens_conf_nonneg
    (a ab : TV) (ha : 0 ≤ a.c) (hab : 0 ≤ ab.c) :
    0 ≤ (truthSymmetricModusPonensConservative a ab).c := by
  simp [truthSymmetricModusPonensConservative,
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens]
  constructor
  · exact And.intro hab (by norm_num)
  · exact ha

theorem truthSymmetricModusPonens_conf_le_inputs
    (a ab : TV) :
    (truthSymmetricModusPonensConservative a ab).c ≤ a.c ∧
    (truthSymmetricModusPonensConservative a ab).c ≤ ab.c := by
  unfold truthSymmetricModusPonensConservative
  unfold Mettapedia.Logic.PeTTaLibPLNTruthFunctions.truthSymmetricModusPonens
  constructor
  · exact min_le_right _ _
  · exact le_trans (min_le_left _ _) (min_le_left _ _)

/-! ## Additional WM-backed rule surfaces absent from current upstream PeTTa main

These are constructive additions from the WM side of the development.

They are included here because the underlying WM theory is already real and
useful, even though the current upstream PeTTa/OpenCog-style `lib_pln.metta`
line does not ship them as first-class truth functions.
-/

/-- Conservative TV-level predictive implication application.

Chapter 14 provides the semantic predictive-implication connective and its
modus-ponens rule. At the scalar truth-value level we package the same
multiplicative core used by the other conservative product rules. -/
noncomputable def truthPredictiveImplicationConservative (p pq : TV) : TV :=
  ⟨p.s * pq.s, p.c * pq.c⟩

@[simp] theorem truthPredictiveImplication_strength_eq (p pq : TV) :
    (truthPredictiveImplicationConservative p pq).s = p.s * pq.s := rfl

@[simp] theorem truthPredictiveImplication_conf_eq (p pq : TV) :
    (truthPredictiveImplicationConservative p pq).c = p.c * pq.c := rfl

theorem truthPredictiveImplication_conf_nonneg
    (p pq : TV) (hp : 0 ≤ p.c) (hpq : 0 ≤ pq.c) :
    0 ≤ (truthPredictiveImplicationConservative p pq).c := by
  simp [truthPredictiveImplicationConservative, mul_nonneg hp hpq]

theorem truthPredictiveImplication_conf_le_inputs
    (p pq : TV) (hp : p.c ∈ Set.Icc (0 : ℝ) 1) (hpq : pq.c ∈ Set.Icc (0 : ℝ) 1) :
    (truthPredictiveImplicationConservative p pq).c ≤ p.c ∧
    (truthPredictiveImplicationConservative p pq).c ≤ pq.c := by
  constructor
  · change p.c * pq.c ≤ p.c
    nlinarith [hp.1, hp.2, hpq.1, hpq.2]
  · change p.c * pq.c ≤ pq.c
    nlinarith [hp.1, hp.2, hpq.1, hpq.2]

/-- TV-level independent conjunction in the BinaryEvidence / weight-style regime.

This matches the weight-space conjunction formula used elsewhere in the Lean PLN
development. It is kept regime-explicit here so it is not confused with either
the conditional product rule or the finite-population hypergeometric rule. -/
noncomputable def truthConjunctionIndependentEvidenceStyle (a b : TV) : TV :=
  ⟨a.s * b.s,
    Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
      (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w a.c *
       Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w b.c)⟩

@[simp] theorem truthConjunctionIndependent_strength_eq (a b : TV) :
    (truthConjunctionIndependentEvidenceStyle a b).s = a.s * b.s := rfl

@[simp] theorem truthConjunctionIndependent_conf_eq (a b : TV) :
    (truthConjunctionIndependentEvidenceStyle a b).c =
      Mettapedia.Logic.PeTTaLibPLNTruthFunctions.w2c
        (Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w a.c *
         Mettapedia.Logic.PeTTaLibPLNTruthFunctions.c2w b.c) := rfl

theorem truthConjunctionIndependent_strength_le_inputs
    (a b : TV) (ha : a.s ∈ Set.Icc (0 : ℝ) 1) (hb : b.s ∈ Set.Icc (0 : ℝ) 1) :
    (truthConjunctionIndependentEvidenceStyle a b).s ≤ a.s ∧
    (truthConjunctionIndependentEvidenceStyle a b).s ≤ b.s := by
  constructor
  · change a.s * b.s ≤ a.s
    nlinarith [ha.1, ha.2, hb.1, hb.2]
  · change a.s * b.s ≤ b.s
    nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- Finite-population hypergeometric conjunction wrapper.

Strength is the modal overlap fraction in a finite universe of size `n`.
Confidence is the probability mass of that modal overlap. This regime is
explicitly cardinality-based and should not be conflated with the plain TV-only
conjunction regimes above. -/
noncomputable def truthConjunctionHypergeometric (n a b : ℕ) : TV :=
  if n = 0 then
    ⟨0, 0⟩
  else
    let k := Mettapedia.Logic.PLNConjunction.hypergeometricMode n a b
    ⟨(k : ℝ) / n,
      ENNReal.toReal (Mettapedia.Logic.PLNConjunction.hypergeometricPMF n a b k)⟩

theorem truthConjunctionHypergeometric_strength_nonneg (n a b : ℕ) :
    0 ≤ (truthConjunctionHypergeometric n a b).s := by
  by_cases hn : n = 0
  · simp [truthConjunctionHypergeometric, hn]
  · simp [truthConjunctionHypergeometric, hn]
    exact div_nonneg (by positivity) (by positivity)

theorem truthConjunctionHypergeometric_strength_le_min_fraction
    (n a b : ℕ) (hn : 0 < n) (ha : a ≤ n) (hb : b ≤ n) :
    (truthConjunctionHypergeometric n a b).s ≤ (min a b : ℝ) / n := by
  have hmode : Mettapedia.Logic.PLNConjunction.hypergeometricMode n a b ≤ min a b :=
    Mettapedia.Logic.PLNConjunction.hypergeometricMode_in_range n a b ha hb
  have hmodeR :
      (Mettapedia.Logic.PLNConjunction.hypergeometricMode n a b : ℝ) ≤ (min a b : ℝ) := by
    exact_mod_cast hmode
  have hnR : 0 ≤ (n : ℝ) := by positivity
  simp [truthConjunctionHypergeometric, Nat.ne_of_gt hn]
  exact div_le_div_of_nonneg_right hmodeR hnR

theorem truthConjunctionHypergeometric_strength_le_one
    (n a b : ℕ) (hn : 0 < n) (ha : a ≤ n) (hb : b ≤ n) :
    (truthConjunctionHypergeometric n a b).s ≤ 1 := by
  have hmin : min a b ≤ n := le_trans (Nat.min_le_left _ _) ha
  have hfrac :
      (min a b : ℝ) / n ≤ 1 := by
    have hminR : (min a b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmin
    have h : (min a b : ℝ) / n ≤ (n : ℝ) / n := by
      exact div_le_div_of_nonneg_right hminR (show 0 ≤ (n : ℝ) by positivity)
    have hnR_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    simpa [hnR_ne] using h
  exact le_trans
    (truthConjunctionHypergeometric_strength_le_min_fraction n a b hn ha hb)
    hfrac

theorem truthConjunctionHypergeometric_conf_nonneg (n a b : ℕ) :
    0 ≤ (truthConjunctionHypergeometric n a b).c := by
  by_cases hn : n = 0
  · simp [truthConjunctionHypergeometric, hn]
  · simp [truthConjunctionHypergeometric, hn]

/-- Conservative TV-level conditional conjunction.

The strength component is the exact Chapter-6/WM conditional conjunction
formula `P(A ∧ B) = P(A) * P(B | A)`. The confidence component is packaged
conservatively with the same multiplicative scalar law used elsewhere in this
file. -/
noncomputable def truthConjunctionConditionalConservative (a ab : TV) : TV :=
  ⟨a.s * ab.s, a.c * ab.c⟩

@[simp] theorem truthConjunctionConditional_strength_eq (a ab : TV) :
    (truthConjunctionConditionalConservative a ab).s = a.s * ab.s := rfl

@[simp] theorem truthConjunctionConditional_conf_eq (a ab : TV) :
    (truthConjunctionConditionalConservative a ab).c = a.c * ab.c := rfl

theorem truthConjunctionConditional_strength_lifts_to_wm
    (a ab : TV) (ha : 0 ≤ a.s) :
    ENNReal.ofReal (truthConjunctionConditionalConservative a ab).s =
      Mettapedia.Logic.PLNConjunction.conjunctionConditional
        (ENNReal.ofReal a.s) (ENNReal.ofReal ab.s) := by
  simpa [truthConjunctionConditionalConservative,
    Mettapedia.Logic.PLNConjunction.conjunctionConditional] using
    (ENNReal.ofReal_mul (p := a.s) (q := ab.s) ha)

theorem truthConjunctionConditional_strength_le_left
    (a ab : TV) (ha : a.s ∈ Set.Icc (0 : ℝ) 1) (hab : ab.s ∈ Set.Icc (0 : ℝ) 1) :
    (truthConjunctionConditionalConservative a ab).s ≤ a.s := by
  change a.s * ab.s ≤ a.s
  nlinarith [ha.1, ha.2, hab.1, hab.2]

theorem truthConjunctionConditional_conf_nonneg
    (a ab : TV) (ha : 0 ≤ a.c) (hab : 0 ≤ ab.c) :
    0 ≤ (truthConjunctionConditionalConservative a ab).c := by
  simp [truthConjunctionConditionalConservative, mul_nonneg ha hab]

theorem truthConjunctionConditional_conf_le_inputs
    (a ab : TV) (ha : a.c ∈ Set.Icc (0 : ℝ) 1) (hab : ab.c ∈ Set.Icc (0 : ℝ) 1) :
    (truthConjunctionConditionalConservative a ab).c ≤ a.c ∧
    (truthConjunctionConditionalConservative a ab).c ≤ ab.c := by
  constructor
  · change a.c * ab.c ≤ a.c
    nlinarith [ha.1, ha.2, hab.1, hab.2]
  · change a.c * ab.c ≤ ab.c
    nlinarith [ha.1, ha.2, hab.1, hab.2]

/-! ## Constructive WM-facing strength analogues for non-core mirrored rules

The mirrored PeTTa/OpenCog-style rules below are not promoted as fully justified
truth-value rules yet, but the Lean development already contains stronger formal
analogues for their *strength* components.  These are the constructive WM-facing
surfaces that the comparison file can use.

The reasons they stay out of the fully justified TV layer are not uniform:

* `truthInversion` splits into two formally meaningful variants:
  the compiled-rule-catalog strength keeps `s_BA = s_AB`, while the
  Bayes-inversion strength is the quantity used internally by
  induction/abduction derivations.  The mirrored library confidence is still a
  damped heuristic (`0.6 * ...`).
* `truthEquivalenceToImplication` is very close to `sim2inh` away from the
  threshold hack, but the mirrored TV rule still hard-codes the threshold.
* `truthTransitiveSimilarity` already matches the formal similarity-composition
  strength, while confidence remains only conservative.
* `truthEvaluationImplication` reuses a deduction-style strength core, but the
  confidence is still a hand-tuned attenuation heuristic.
-/

/-- **Standalone / catalog inversion strength.** In this reading, the
inverted implication keeps the same strength as the original:
`s_BA = s_AB`. This matches the compiled rule-catalog form and is
under-parameterized for Bayes inversion — it does not depend on
`P(A)` or `P(B)`. -/
noncomputable def truthInversionStrength (ab : TV) : ℝ :=
  ab.s

/-- **Bayes inversion strength.** The full probabilistic reading:
`s_BA = P(A|B) = P(B|A) · P(A) / P(B) = s_AB · s_A / s_B`. This is the
quantity used internally by induction/abduction derivations, and it
disagrees with `truthInversionStrength` in general (see the
counterexample `truthInversion_catalog_ne_bayes_example` in the
analysis file). -/
noncomputable def truthInversionBayesStrength (a b ab : TV) : ℝ :=
  Mettapedia.Logic.PLN.bayesInversion ab.s a.s b.s

/-- Strength analogue for the mirrored equivalence-to-implication rule.
Drops the mirror's 0.99 threshold branch and identifies the underlying
transformation with `sim2inh` (similarity → inheritance), whose strength
formula comes out of the Chapter-6 probability reading. -/
noncomputable def truthEquivalenceToImplicationStrength (a b ab : TV) : ℝ :=
  Mettapedia.Logic.PLNInferenceRules.sim2inh ab.s a.s b.s

/-- Strength analogue for the mirrored transitive-similarity rule.
Delegates to the formal similarity-composition formula from
`PLNInferenceRules`; the corresponding confidence is still only a
conservative minimum-style aggregator in the mirror, so this covers the
strength half only. -/
noncomputable def truthTransitiveSimilarityStrength (a b c ab bc : TV) : ℝ :=
  Mettapedia.Logic.PLNInferenceRules.transitiveSimilarity ab.s bc.s a.s b.s c.s

/-- Strength analogue for the mirrored evaluation-implication rule.
Strips the mirror's `0.9 * 0.9 * …` confidence-attenuation heuristic and
exposes just the deduction-strength formula that is the proper formal
core. Confidence remains a hand-tuned heuristic in the mirror and is not
promoted to a theorem-backed quantity here. -/
noncomputable def truthEvaluationImplicationStrength (a b c ab ac : TV) : ℝ :=
  Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula b.s a.s c.s ab.s ac.s

@[simp] theorem truthInversionStrength_eq (ab : TV) :
    truthInversionStrength ab = ab.s := rfl

@[simp] theorem truthInversionBayesStrength_eq (a b ab : TV) :
    truthInversionBayesStrength a b ab = Mettapedia.Logic.PLN.bayesInversion ab.s a.s b.s := rfl

@[simp] theorem truthEquivalenceToImplicationStrength_eq (a b ab : TV) :
    truthEquivalenceToImplicationStrength a b ab =
      Mettapedia.Logic.PLNInferenceRules.sim2inh ab.s a.s b.s := rfl

@[simp] theorem truthTransitiveSimilarityStrength_eq (a b c ab bc : TV) :
    truthTransitiveSimilarityStrength a b c ab bc =
      Mettapedia.Logic.PLNInferenceRules.transitiveSimilarity ab.s bc.s a.s b.s c.s := rfl

@[simp] theorem truthEvaluationImplicationStrength_eq (a b c ab ac : TV) :
    truthEvaluationImplicationStrength a b c ab ac =
      Mettapedia.Logic.PLNDeduction.simpleDeductionStrengthFormula b.s a.s c.s ab.s ac.s := rfl

end Mettapedia.Logic.WMPLNJustifiedTruthFunctions
