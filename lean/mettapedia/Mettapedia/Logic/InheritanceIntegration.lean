import Mettapedia.Logic.ExtensionalIntensionalDivergence
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.WMPLNJustifiedTruthFunctions

/-!
# Integration bridges: the new inheritance theory ↔ the existing PLN/credal stack

This module wires the standalone divergence/strength/truth-value theory of
`ExtensionalIntensionalDivergence` into the pre-existing inheritance infrastructure,
so the new `⟨strength, confidence⟩` and credal coordinates are load-bearing rather
than parallel.

## (#1) Extensional strength bridge
`pureExtensionalStrength` (the `Set.ncard`-based extensional strength) is proved equal
to the existing Chapter-12 `finiteExtensionalProb` (the `Fintype.card`-based extensional
proxy that the credal inheritance table uses). Consequently the full inheritance
strength refines the existing table strength: it is dominated by it, with the deficit
exactly the intensional content the proxy ignores.
-/

namespace Mettapedia.Logic.ExtensionalIntensionalDivergence

open Mettapedia.Logic.AbstractInheritance
open Mettapedia.Logic.IntensionalInheritance.Interpretation

universe u v w

open Mettapedia.Logic.WMPLNJustifiedTruthFunctions

/-- Repackage an STV as the WM/PeTTa `(strength, confidence)` truth value. This is a
shape bridge only: no numerical content changes. -/
def stvToWMTruthValue (t : Mettapedia.Logic.PLNDeduction.STV) : TV :=
  ⟨t.strength, t.confidence⟩

@[simp] theorem stvToWMTruthValue_s (t : Mettapedia.Logic.PLNDeduction.STV) :
    (stvToWMTruthValue t).s = t.strength := rfl

@[simp] theorem stvToWMTruthValue_c (t : Mettapedia.Logic.PLNDeduction.STV) :
    (stvToWMTruthValue t).c = t.confidence := rfl

section ExtensionalBridge
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj]

/-- The Chapter-12 extent count equals the `Set.ncard` of the interpreted extent. -/
theorem extentCount_eq_ncard (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    extentCount I c = (I.meaning c).extent.ncard := by
  classical
  unfold extentCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_coe_set_eq _

/-- The Chapter-12 joint extent count equals the `Set.ncard` of the extent overlap. -/
theorem jointExtentCount_eq_ncard (I : Interpretation Carrier Obj Attr) (a b : Carrier) :
    jointExtentCount I a b = ((I.meaning a).extent ∩ (I.meaning b).extent).ncard := by
  classical
  unfold jointExtentCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_coe_set_eq _

/-- **Bridge (#1):** the new pure extensional strength agrees exactly with the existing
Chapter-12 extensional inheritance probability. The two frameworks compute the same
extensional overlap, so the new theory genuinely extends — rather than competes with —
the strength the credal inheritance table already uses. -/
theorem pureExtensionalStrength_eq_finiteExtensionalProb
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    pureExtensionalStrength I sub super = finiteExtensionalProb I sub super := by
  unfold pureExtensionalStrength finiteExtensionalProb
  by_cases h : (I.meaning sub).extent.ncard = 0
  · rw [if_pos h, dif_pos (by rw [extentCount_eq_ncard]; exact h)]
  · rw [if_neg h, dif_neg (by rw [extentCount_eq_ncard]; exact h),
        extentCount_eq_ncard I sub, jointExtentCount_eq_ncard I sub super,
        Set.inter_comm (I.meaning super).extent (I.meaning sub).extent]

/-- The new pure extensional strength is exactly the existing
`finiteInheritanceStrength` (which is the extensional proxy by definition). -/
theorem pureExtensionalStrength_eq_finiteInheritanceStrength
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    pureExtensionalStrength I sub super = finiteInheritanceStrength I sub super := by
  rw [pureExtensionalStrength_eq_finiteExtensionalProb, finiteInheritanceStrength_eq]

end ExtensionalBridge

section FullVsTable
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj]

/-- **Integration (#1):** the full inheritance strength is the existing (extensional)
credal-table strength conjoined with the genuine intensional strength — it is the
weakest link of the two. This is exactly how the new intensional content enters the
existing table. -/
theorem fullInheritanceStrength_eq_min_table_intensional
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    fullInheritanceStrength I sub super
      = min (finiteInheritanceStrength I sub super) (pureIntensionalStrength I sub super) := by
  unfold fullInheritanceStrength
  rw [pureExtensionalStrength_eq_finiteInheritanceStrength]

/-- The full inheritance strength refines the existing table strength: it is always at
most the extensional proxy, with equality iff the intensional strength does not bind.
The credal inheritance table strength is thus an *over-estimate* corrected by the
intensional factor. -/
theorem fullInheritanceStrength_le_finiteInheritanceStrength
    (I : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    fullInheritanceStrength I sub super ≤ finiteInheritanceStrength I sub super := by
  rw [fullInheritanceStrength_eq_min_table_intensional]
  exact min_le_left _ _

end FullVsTable

/-! ## (#2) The credal interval IS a Walley lower/upper envelope

The gate family induces a credal set — the set of per-gate strengths. The Walley
lower (resp. upper) envelope of a credal set is, by definition, the greatest lower
(resp. least upper) bound of its values. We prove `lowerInheritanceStrength` and
`upperInheritanceStrength` are exactly that, characterizing the credal interval as a
Walley envelope at the order-theoretic level. (Embedding into the measure-theoretic
`ProjectiveCredal.boundedMeasurableLowerEnvelope` previsions is a deeper, separate
bridge.) -/

section WalleyEnvelope
variable {Gate : Type*} [Fintype Gate] [Nonempty Gate]
variable {Carrier : Type u} {Obj : Type v} {Attr : Type w}

/-- The lower inheritance strength is the Walley **lower envelope** of the gate-induced
credal set: the greatest lower bound of the per-gate strengths. -/
theorem lowerInheritanceStrength_isGLB
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    IsGLB (Set.range (fun g => fullInheritanceStrength (J g) sub super))
      (lowerInheritanceStrength J sub super) := by
  constructor
  · rintro _ ⟨g, rfl⟩
    exact lowerInheritanceStrength_le_gate J sub super g
  · intro b hb
    apply Finset.le_inf'
    intro g _
    exact hb ⟨g, rfl⟩

/-- The upper inheritance strength is the Walley **upper envelope** of the gate-induced
credal set: the least upper bound of the per-gate strengths. -/
theorem upperInheritanceStrength_isLUB
    (J : Gate → Interpretation Carrier Obj Attr) (sub super : Carrier) :
    IsLUB (Set.range (fun g => fullInheritanceStrength (J g) sub super))
      (upperInheritanceStrength J sub super) := by
  constructor
  · rintro _ ⟨g, rfl⟩
    exact gate_le_upperInheritanceStrength J sub super g
  · intro b hb
    apply Finset.sup'_le
    intro g _
    exact hb ⟨g, rfl⟩

end WalleyEnvelope

/-! ## (#3) Concept priors as canonical inheritance-facing truth values

To make the induction/abduction bridges fully concept-native, we package a single
concept's prior strength together with the evidence weight carried by its extent.
This is the direct analogue of `inheritanceTV`, but for unary concept priors
`P(A), P(B), P(C)` rather than binary inheritance links. -/

section PriorTV

open Mettapedia.Logic.PLNWeightTV

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj]

private theorem prior_w2c_lt_one {x : ℝ} (hx : 0 ≤ x) :
    Mettapedia.Logic.PLNWeightTV.w2c x < 1 := by
  unfold Mettapedia.Logic.PLNWeightTV.w2c
  rw [div_lt_one (by linarith)]
  linarith

/-- The finite interpreted extent count never exceeds the ambient object carrier. -/
theorem extentCount_le_card
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    extentCount I c ≤ Fintype.card Obj := by
  classical
  unfold extentCount
  exact Fintype.card_subtype_le (fun x => x ∈ (I.meaning c).extent)

/-- The finite prior probability read from an interpreted extent is nonnegative. -/
theorem finitePriorProb_nonneg
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    0 ≤ finitePriorProb I c := by
  unfold finitePriorProb
  positivity

/-- The finite prior probability is bounded by `1`. -/
theorem finitePriorProb_le_one
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    finitePriorProb I c ≤ 1 := by
  unfold finitePriorProb
  by_cases hcard : Fintype.card Obj = 0
  · simp [hcard]
  · have hpos : 0 < (Fintype.card Obj : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    rw [div_le_one hpos]
    exact_mod_cast extentCount_le_card I c

/-- The prior-evidence weight of a concept: the size of its interpreted extent. -/
noncomputable def conceptPriorWeight
    (I : Interpretation Carrier Obj Attr) (c : Carrier) : ℝ :=
  extentCount I c

theorem conceptPriorWeight_nonneg
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    0 ≤ conceptPriorWeight I c := by
  unfold conceptPriorWeight
  positivity

/-- Weight-primary prior truth value for a single concept. Strength is the prior
probability `P(c)`, while weight is the extent-count evidence behind that prior. -/
noncomputable def conceptPriorWTV
    (I : Interpretation Carrier Obj Attr) (c : Carrier) : WTV where
  strength := finitePriorProb I c
  weight := conceptPriorWeight I c
  strength_nonneg := finitePriorProb_nonneg I c
  strength_le_one := finitePriorProb_le_one I c
  weight_nonneg := conceptPriorWeight_nonneg I c

/-- STV view of a concept prior. This is the canonical concept-native source of the
term probabilities `P(A), P(B), P(C)` used by induction/abduction. -/
noncomputable def conceptPriorTV
    (I : Interpretation Carrier Obj Attr) (c : Carrier) : Mettapedia.Logic.PLNDeduction.STV :=
  (conceptPriorWTV I c).toCTV

@[simp] theorem conceptPriorTV_strength_eq
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    (conceptPriorTV I c).strength = finitePriorProb I c := rfl

@[simp] theorem conceptPriorTV_confidence_eq
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    (conceptPriorTV I c).confidence =
      Mettapedia.Logic.PLNWeightTV.w2c (conceptPriorWeight I c) := rfl

/-- Finite extent evidence never yields confidence `1` for a concept prior. -/
theorem conceptPriorTV_confidence_lt_one
    (I : Interpretation Carrier Obj Attr) (c : Carrier) :
    (conceptPriorTV I c).confidence < 1 := by
  rw [conceptPriorTV_confidence_eq]
  exact prior_w2c_lt_one (conceptPriorWeight_nonneg I c)

end PriorTV

/-! ## (#4) Inheritance TVs and the exact induction/abduction confidence laws

The WM-PLN library already proves exact confidence propagation laws for induction and
abduction. This section shows that the new inheritance truth values plug into those
rules directly: once an inheritance judgment is packaged as an STV, the justified WM
confidence formulas apply unchanged. -/

section InferenceBridge

open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLN
open Mettapedia.Logic.WMPLNJustifiedTruthFunctions

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} [Fintype Obj]

/-- The exact WM induction strength formula applies directly to inheritance truth
values once they are viewed as `(strength, confidence)` pairs. This is the clean
strength-side bridge from the new inheritance TV to the existing justified induction
surface. -/
theorem inheritanceTV_truthInduction_strength_eq
    (a b c : TV)
    (I : Interpretation Carrier Obj Attr) (sub mid super : Carrier) :
    (truthInduction a b c
      (stvToWMTruthValue (inheritanceTV I sub mid))
      (stvToWMTruthValue (inheritanceTV I mid super))).s =
    plnInductionStrength
      (inheritanceTV I sub mid).strength
      (inheritanceTV I mid super).strength
      a.s b.s c.s := by
  simpa using truthInduction_strength_eq a b c
    (stvToWMTruthValue (inheritanceTV I sub mid))
    (stvToWMTruthValue (inheritanceTV I mid super))

/-- The exact WM induction confidence law specializes cleanly to inheritance truth
values: the derived confidence is the minimum of the capped premise confidences. -/
theorem inheritanceTV_truthInduction_conf_eq_min_capped
    (a b c : TV)
    (I : Interpretation Carrier Obj Attr) (sub mid super : Carrier) :
    (truthInduction a b c
      (stvToWMTruthValue (inheritanceTV I sub mid))
      (stvToWMTruthValue (inheritanceTV I mid super))).c =
    min (capConf (inheritanceTV I sub mid).confidence)
        (capConf (inheritanceTV I mid super).confidence) := by
  simpa using truthInduction_conf_eq_min_capped a b c
    (stvToWMTruthValue (inheritanceTV I sub mid))
    (stvToWMTruthValue (inheritanceTV I mid super))

/-- Consequence: induction from inheritance TVs cannot be more confident than the
weaker premise inheritance judgment. -/
theorem inheritanceTV_truthInduction_conf_le_inputs
    (a b c : TV)
    (I : Interpretation Carrier Obj Attr) (sub mid super : Carrier) :
    (truthInduction a b c
      (stvToWMTruthValue (inheritanceTV I sub mid))
      (stvToWMTruthValue (inheritanceTV I mid super))).c ≤
    min (inheritanceTV I sub mid).confidence
        (inheritanceTV I mid super).confidence := by
  simpa using truthInduction_conf_le_inputs a b c
    (stvToWMTruthValue (inheritanceTV I sub mid))
    (stvToWMTruthValue (inheritanceTV I mid super))
    (inheritanceTV I sub mid).confidence_nonneg
    (inheritanceTV I mid super).confidence_nonneg

/-- Concept-native induction bridge: using the canonical prior TVs for the three term
probabilities turns the induction strength theorem into a fully semantic concept-level
statement rather than one parameterized by external prior TVs. -/
theorem inheritanceTV_truthInduction_strength_eq_conceptPrior
    (I : Interpretation Carrier Obj Attr) (sub mid super : Carrier) :
    (truthInduction
      (stvToWMTruthValue (conceptPriorTV I sub))
      (stvToWMTruthValue (conceptPriorTV I mid))
      (stvToWMTruthValue (conceptPriorTV I super))
      (stvToWMTruthValue (inheritanceTV I sub mid))
      (stvToWMTruthValue (inheritanceTV I mid super))).s =
    plnInductionStrength
      (inheritanceTV I sub mid).strength
      (inheritanceTV I mid super).strength
      (finitePriorProb I sub)
      (finitePriorProb I mid)
      (finitePriorProb I super) := by
  simpa using inheritanceTV_truthInduction_strength_eq
    (stvToWMTruthValue (conceptPriorTV I sub))
    (stvToWMTruthValue (conceptPriorTV I mid))
    (stvToWMTruthValue (conceptPriorTV I super))
    I sub mid super

/-- Concept-native induction confidence law: with canonical concept priors, the WM
confidence result still reduces to the weaker inheritance premise confidence. -/
theorem inheritanceTV_truthInduction_conf_eq_min_capped_conceptPrior
    (I : Interpretation Carrier Obj Attr) (sub mid super : Carrier) :
    (truthInduction
      (stvToWMTruthValue (conceptPriorTV I sub))
      (stvToWMTruthValue (conceptPriorTV I mid))
      (stvToWMTruthValue (conceptPriorTV I super))
      (stvToWMTruthValue (inheritanceTV I sub mid))
      (stvToWMTruthValue (inheritanceTV I mid super))).c =
    min (capConf (inheritanceTV I sub mid).confidence)
        (capConf (inheritanceTV I mid super).confidence) := by
  simpa using inheritanceTV_truthInduction_conf_eq_min_capped
    (stvToWMTruthValue (conceptPriorTV I sub))
    (stvToWMTruthValue (conceptPriorTV I mid))
    (stvToWMTruthValue (conceptPriorTV I super))
    I sub mid super

/-- The exact WM abduction strength formula also applies directly to inheritance truth
values. This is the strength-side bridge for the sink-rule / collider regime. -/
theorem inheritanceTV_truthAbduction_strength_eq
    (a b c : TV)
    (I : Interpretation Carrier Obj Attr) (left common right : Carrier) :
    (truthAbduction a b c
      (stvToWMTruthValue (inheritanceTV I left common))
      (stvToWMTruthValue (inheritanceTV I right common))).s =
    plnAbductionStrength
      (inheritanceTV I left common).strength
      (inheritanceTV I right common).strength
      a.s b.s c.s := by
  simpa using truthAbduction_strength_eq a b c
    (stvToWMTruthValue (inheritanceTV I left common))
    (stvToWMTruthValue (inheritanceTV I right common))

/-- The exact WM abduction confidence law specializes cleanly to inheritance truth
values: the derived confidence is the minimum of the capped premise confidences. -/
theorem inheritanceTV_truthAbduction_conf_eq_min_capped
    (a b c : TV)
    (I : Interpretation Carrier Obj Attr) (left common right : Carrier) :
    (truthAbduction a b c
      (stvToWMTruthValue (inheritanceTV I left common))
      (stvToWMTruthValue (inheritanceTV I right common))).c =
    min (capConf (inheritanceTV I left common).confidence)
        (capConf (inheritanceTV I right common).confidence) := by
  simpa using truthAbduction_conf_eq_min_capped a b c
    (stvToWMTruthValue (inheritanceTV I left common))
    (stvToWMTruthValue (inheritanceTV I right common))

/-- Consequence: abduction from inheritance TVs is capped by the weaker premise
inheritance confidence. -/
theorem inheritanceTV_truthAbduction_conf_le_inputs
    (a b c : TV)
    (I : Interpretation Carrier Obj Attr) (left common right : Carrier) :
    (truthAbduction a b c
      (stvToWMTruthValue (inheritanceTV I left common))
      (stvToWMTruthValue (inheritanceTV I right common))).c ≤
    min (inheritanceTV I left common).confidence
        (inheritanceTV I right common).confidence := by
  simpa using truthAbduction_conf_le_inputs a b c
    (stvToWMTruthValue (inheritanceTV I left common))
    (stvToWMTruthValue (inheritanceTV I right common))
    (inheritanceTV I left common).confidence_nonneg
    (inheritanceTV I right common).confidence_nonneg

/-- Concept-native abduction bridge: using canonical concept priors turns the
abduction strength theorem into a fully semantic concept-level statement. -/
theorem inheritanceTV_truthAbduction_strength_eq_conceptPrior
    (I : Interpretation Carrier Obj Attr) (left common right : Carrier) :
    (truthAbduction
      (stvToWMTruthValue (conceptPriorTV I left))
      (stvToWMTruthValue (conceptPriorTV I common))
      (stvToWMTruthValue (conceptPriorTV I right))
      (stvToWMTruthValue (inheritanceTV I left common))
      (stvToWMTruthValue (inheritanceTV I right common))).s =
    plnAbductionStrength
      (inheritanceTV I left common).strength
      (inheritanceTV I right common).strength
      (finitePriorProb I left)
      (finitePriorProb I common)
      (finitePriorProb I right) := by
  simpa using inheritanceTV_truthAbduction_strength_eq
    (stvToWMTruthValue (conceptPriorTV I left))
    (stvToWMTruthValue (conceptPriorTV I common))
    (stvToWMTruthValue (conceptPriorTV I right))
    I left common right

/-- Concept-native abduction confidence law: with canonical concept priors, the WM
confidence result still reduces to the weaker inheritance premise confidence. -/
theorem inheritanceTV_truthAbduction_conf_eq_min_capped_conceptPrior
    (I : Interpretation Carrier Obj Attr) (left common right : Carrier) :
    (truthAbduction
      (stvToWMTruthValue (conceptPriorTV I left))
      (stvToWMTruthValue (conceptPriorTV I common))
      (stvToWMTruthValue (conceptPriorTV I right))
      (stvToWMTruthValue (inheritanceTV I left common))
      (stvToWMTruthValue (inheritanceTV I right common))).c =
    min (capConf (inheritanceTV I left common).confidence)
        (capConf (inheritanceTV I right common).confidence) := by
  simpa using inheritanceTV_truthAbduction_conf_eq_min_capped
    (stvToWMTruthValue (conceptPriorTV I left))
    (stvToWMTruthValue (conceptPriorTV I common))
    (stvToWMTruthValue (conceptPriorTV I right))
    I left common right

end InferenceBridge

end Mettapedia.Logic.ExtensionalIntensionalDivergence
