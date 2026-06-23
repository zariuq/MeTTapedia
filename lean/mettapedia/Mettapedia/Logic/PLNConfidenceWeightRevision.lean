import Mettapedia.Logic.PLNConfidenceWeight
import KnuthSkilling.Counterexamples.RegradeCounterexample
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Piecewise

/-!
# Confidence-Weight Revision Charts

This file records the algebraic revision laws for confidence displays viewed
as charts over latent evidence weight.

The key boundary is:

* any valid confidence chart can transport additive evidence revision through
  decode-add-reencode;
* the PLN chart is distinguished here by the extra law that
  confidence odds `c / (1 - c)` are additive for evidence-weight revision.

The full rigidity theorem in this file has explicit regularity/domain gates on
the nonnegative evidence-weight axis: continuous additive confidence odds,
normalization at one unit, and exclusion of the totalized-division singularity
`c = 1`.
-/

namespace Mettapedia.Logic.PLNConfidenceWeight
namespace EvidenceWeightCoordinate

/-! ## Display-level revision laws -/

/-- Ordinary odds of a displayed confidence value.  This is the odds chart on
the evidence-weight/concentration axis, distinct from support odds `n+ / n-`
on the strength/direction axis. -/
noncomputable def confidenceOdds (c : ℝ) : ℝ := c / (1 - c)

/-- PLN/Mobius transported revision law for displayed confidence values. -/
noncomputable def plnConfidenceRevision (c1 c2 : ℝ) : ℝ :=
  (c1 + c2 - 2 * c1 * c2) / (1 - c1 * c2)

/-- Exponential/hazard transported revision law, also known as noisy-OR or
probabilistic-sum composition. -/
noncomputable def expConfidenceRevision (c1 c2 : ℝ) : ℝ :=
  c1 + c2 - c1 * c2

/-- Tanh/Einstein-style transported revision law. -/
noncomputable def tanhConfidenceRevision (c1 c2 : ℝ) : ℝ :=
  (c1 + c2) / (1 + c1 * c2)

/-! ## Generic transported revision -/

/-- The generic displayed revision law transported through an evidence-weight
coordinate: decode both displays to latent weights, add, then re-encode. -/
noncomputable def transportedConfidenceRevision
    (χ : EvidenceWeightCoordinate) (c1 c2 : ℝ) : ℝ :=
  χ.encode (χ.decode c1 + χ.decode c2)

/-- Transported revision of two encoded nonnegative weights re-encodes their
sum. -/
theorem transportedConfidenceRevision_of_encoded_weights
    (χ : EvidenceWeightCoordinate) {w1 w2 : ℝ} (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) :
    transportedConfidenceRevision χ (χ.encode w1) (χ.encode w2) =
      χ.encode (w1 + w2) := by
  simp [transportedConfidenceRevision, χ.decode_encode_of_nonneg hw1,
    χ.decode_encode_of_nonneg hw2]

/-- Transported revision really adds decoded weights when those decoded
weights are admissible nonnegative evidence weights. -/
theorem decode_transportedConfidenceRevision
    (χ : EvidenceWeightCoordinate) {c1 c2 : ℝ}
    (h1 : 0 ≤ χ.decode c1) (h2 : 0 ≤ χ.decode c2) :
    χ.decode (transportedConfidenceRevision χ c1 c2) =
      χ.decode c1 + χ.decode c2 := by
  unfold transportedConfidenceRevision
  exact χ.decode_encode_of_nonneg (add_nonneg h1 h2)

/-- Transported revision is commutative at the displayed level. -/
theorem transportedConfidenceRevision_comm
    (χ : EvidenceWeightCoordinate) (c1 c2 : ℝ) :
    transportedConfidenceRevision χ c1 c2 =
      transportedConfidenceRevision χ c2 c1 := by
  unfold transportedConfidenceRevision
  rw [add_comm]

/-- Transported revision is associative on displays whose decoded weights are
nonnegative. -/
theorem transportedConfidenceRevision_assoc_of_nonneg
    (χ : EvidenceWeightCoordinate) {c1 c2 c3 : ℝ}
    (h1 : 0 ≤ χ.decode c1) (h2 : 0 ≤ χ.decode c2) (h3 : 0 ≤ χ.decode c3) :
    transportedConfidenceRevision χ
        (transportedConfidenceRevision χ c1 c2) c3 =
      transportedConfidenceRevision χ c1
        (transportedConfidenceRevision χ c2 c3) := by
  unfold transportedConfidenceRevision
  rw [χ.decode_encode_of_nonneg (add_nonneg h1 h2),
    χ.decode_encode_of_nonneg (add_nonneg h2 h3)]
  congr 1
  ring

/-! ## Abstract chart torsor -/

/-- The nonnegative evidence-weight axis. -/
abbrev NonnegativeEvidenceWeight := {w : ℝ // 0 ≤ w}

/-- A fully lossless confidence chart with a fixed display type.

This is stronger than `EvidenceWeightCoordinate`: it is an equivalence, so it
is the honest abstraction for torsor-style statements about all charts with
one display type. -/
abbrev EvidenceWeightChartIso (Display : Type*) :=
  NonnegativeEvidenceWeight ≃ Display

/-- Reparametrize a chart by a display-space automorphism. -/
def reparametrizeChart {Display : Type*}
    (σ : Equiv.Perm Display) (χ : EvidenceWeightChartIso Display) :
    EvidenceWeightChartIso Display where
  toFun w := σ (χ w)
  invFun d := χ.symm (σ.symm d)
  left_inv := by
    intro w
    simp
  right_inv := by
    intro d
    simp

/-- The unique display reparametrization carrying one chart to another. -/
def chartDifference {Display : Type*}
    (χ ψ : EvidenceWeightChartIso Display) : Equiv.Perm Display :=
  χ.symm.trans ψ

/-- Any chart can be carried to any other chart by its chart difference:
the action is transitive. -/
theorem reparametrizeChart_chartDifference {Display : Type*}
    (χ ψ : EvidenceWeightChartIso Display) :
    reparametrizeChart (chartDifference χ ψ) χ = ψ := by
  ext w
  simp [reparametrizeChart, chartDifference]

/-- A display reparametrization is determined by its action on one chart:
the action is free. -/
theorem reparametrizeChart_free {Display : Type*}
    (χ : EvidenceWeightChartIso Display) {σ τ : Equiv.Perm Display}
    (h : reparametrizeChart σ χ = reparametrizeChart τ χ) :
    σ = τ := by
  ext d
  have hfun := congrArg (fun e : EvidenceWeightChartIso Display => e (χ.symm d)) h
  simpa [reparametrizeChart] using hfun

/-- The chart difference is the unique display reparametrization carrying
`χ` to `ψ`.  This is the concrete torsor law: differences between charts are
canonical, but no chart is distinguished without an extra law. -/
theorem chartDifference_unique {Display : Type*}
    (χ ψ : EvidenceWeightChartIso Display) (σ : Equiv.Perm Display) :
    reparametrizeChart σ χ = ψ ↔ σ = chartDifference χ ψ := by
  constructor
  · intro h
    apply reparametrizeChart_free χ
    rw [h, reparametrizeChart_chartDifference χ ψ]
  · intro h
    rw [h]
    exact reparametrizeChart_chartDifference χ ψ

/-- The self-difference of a chart is the identity reparametrization. -/
theorem chartDifference_self {Display : Type*}
    (χ : EvidenceWeightChartIso Display) :
    chartDifference χ χ = Equiv.refl Display := by
  ext d
  simp [chartDifference]

/-! ## Order-enriched chart torsor -/

/-- A fully lossless confidence chart whose display type also preserves the
order on nonnegative evidence weight.

This is the monotone/order-enriched refinement of `EvidenceWeightChartIso`: it
is the right abstraction when a confidence display is meant to preserve
"more evidence means no less confidence", not merely reconstruct latent weight. -/
abbrev OrderedEvidenceWeightChartIso (Display : Type*) [LE Display] :=
  NonnegativeEvidenceWeight ≃o Display

/-- Forget an order-preserving chart down to its equivalence-level chart. -/
abbrev OrderedEvidenceWeightChartIso.toChartIso
    {Display : Type*} [LE Display]
    (χ : OrderedEvidenceWeightChartIso Display) :
    EvidenceWeightChartIso Display :=
  χ.toEquiv

/-- Reparametrize an ordered chart by an order automorphism of the display. -/
def reparametrizeOrderedChart {Display : Type*} [LE Display]
    (σ : Display ≃o Display)
    (χ : OrderedEvidenceWeightChartIso Display) :
    OrderedEvidenceWeightChartIso Display :=
  χ.trans σ

/-- The unique order-preserving display reparametrization carrying one ordered
chart to another. -/
def orderedChartDifference {Display : Type*} [LE Display]
    (χ ψ : OrderedEvidenceWeightChartIso Display) : Display ≃o Display :=
  χ.symm.trans ψ

/-- Ordered charts are transitive under order-preserving display
reparametrizations. -/
theorem reparametrizeOrderedChart_orderedChartDifference
    {Display : Type*} [LE Display]
    (χ ψ : OrderedEvidenceWeightChartIso Display) :
    reparametrizeOrderedChart (orderedChartDifference χ ψ) χ = ψ := by
  ext w
  simp [reparametrizeOrderedChart, orderedChartDifference]

/-- Ordered display reparametrizations are determined by their action on one
ordered chart. -/
theorem reparametrizeOrderedChart_free
    {Display : Type*} [LE Display]
    (χ : OrderedEvidenceWeightChartIso Display)
    {σ τ : Display ≃o Display}
    (h : reparametrizeOrderedChart σ χ = reparametrizeOrderedChart τ χ) :
    σ = τ := by
  ext d
  have hfun :=
    congrArg (fun e : OrderedEvidenceWeightChartIso Display => e (χ.symm d)) h
  simpa [reparametrizeOrderedChart] using hfun

/-- The ordered chart difference is the unique order-preserving display
reparametrization carrying `χ` to `ψ`. -/
theorem orderedChartDifference_unique
    {Display : Type*} [LE Display]
    (χ ψ : OrderedEvidenceWeightChartIso Display) (σ : Display ≃o Display) :
    reparametrizeOrderedChart σ χ = ψ ↔ σ = orderedChartDifference χ ψ := by
  constructor
  · intro h
    apply reparametrizeOrderedChart_free χ
    rw [h, reparametrizeOrderedChart_orderedChartDifference χ ψ]
  · intro h
    rw [h]
    exact reparametrizeOrderedChart_orderedChartDifference χ ψ

/-- The self-difference of an ordered chart is the identity order
reparametrization. -/
theorem orderedChartDifference_self
    {Display : Type*} [LE Display]
    (χ : OrderedEvidenceWeightChartIso Display) :
    orderedChartDifference χ χ = OrderIso.refl Display := by
  ext d
  simp [orderedChartDifference]

/-- Forgetting the ordered chart action recovers the equivalence-level chart
action. -/
theorem reparametrizeOrderedChart_toChartIso
    {Display : Type*} [LE Display]
    (σ : Display ≃o Display)
    (χ : OrderedEvidenceWeightChartIso Display) :
    (reparametrizeOrderedChart σ χ).toChartIso =
      reparametrizeChart σ.toEquiv χ.toChartIso := by
  ext w
  rfl

/-- Forgetting ordered chart differences recovers the equivalence-level chart
difference. -/
theorem orderedChartDifference_toEquiv
    {Display : Type*} [LE Display]
    (χ ψ : OrderedEvidenceWeightChartIso Display) :
    (orderedChartDifference χ ψ).toEquiv =
      chartDifference χ.toChartIso ψ.toChartIso := by
  ext d
  rfl

/-- Negative canary: not every display permutation is order-preserving.

The order-enriched torsor is therefore a genuine refinement of the raw
equivalence torsor. -/
theorem boolSwap_not_monotone :
    ¬ Monotone (Equiv.swap false true : Equiv.Perm Bool) := by
  intro h
  have hle : false ≤ true := by decide
  have hbad : true ≤ false := by simpa using h hle
  exact (by decide : ¬ true ≤ false) hbad

/-! ## Non-Mobius reconstructive coordinates -/

/-- Exponential confidence chart: `c = 1 - exp(-w/k)`.

This is appropriate for hazard/opportunity-style evidence accumulation. -/
noncomputable def expCoordinate (k : ℝ) (_hk : 0 < k) :
    EvidenceWeightCoordinate where
  encode w := 1 - Real.exp (-w / k)
  decode c := -k * Real.log (1 - c)
  decode_encode_of_nonneg := by
    intro w _hw
    have hk_ne : k ≠ 0 := by linarith
    simp [Real.log_exp]
    field_simp [hk_ne]

/-- One-sided tanh confidence chart: `c = tanh(w/k)`.

This can be read as a bounded signed/log-margin style display restricted to
nonnegative evidence weights. -/
noncomputable def tanhCoordinate (k : ℝ) (hk : 0 < k) :
    EvidenceWeightCoordinate where
  encode w := Real.tanh (w / k)
  decode c := k * Real.artanh c
  decode_encode_of_nonneg := by
    intro w _hw
    have hk_ne : k ≠ 0 := ne_of_gt hk
    rw [Real.artanh_tanh]
    field_simp [hk_ne]

/-- Arctan confidence chart: `c = (2/pi) * atan(w/k)`.

This gives a bounded, heavy-tailed display coordinate for evidence weight. -/
noncomputable def arctanCoordinate (k : ℝ) (hk : 0 < k) :
    EvidenceWeightCoordinate where
  encode w := (2 / Real.pi) * Real.arctan (w / k)
  decode c := k * Real.tan ((Real.pi / 2) * c)
  decode_encode_of_nonneg := by
    intro w _hw
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hk_ne : k ≠ 0 := ne_of_gt hk
    have hangle :
        (Real.pi / 2) * ((2 / Real.pi) * Real.arctan (w / k)) =
          Real.arctan (w / k) := by
      field_simp [hpi_ne]
    rw [hangle, Real.tan_arctan]
    field_simp [hk_ne]

theorem expCoordinate_decode_encode
    (k : ℝ) (hk : 0 < k) {w : ℝ} (hw : 0 ≤ w) :
    (expCoordinate k hk).decode ((expCoordinate k hk).encode w) = w :=
  (expCoordinate k hk).decode_encode_of_nonneg hw

theorem tanhCoordinate_decode_encode
    (k : ℝ) (hk : 0 < k) {w : ℝ} (hw : 0 ≤ w) :
    (tanhCoordinate k hk).decode ((tanhCoordinate k hk).encode w) = w :=
  (tanhCoordinate k hk).decode_encode_of_nonneg hw

theorem arctanCoordinate_decode_encode
    (k : ℝ) (hk : 0 < k) {w : ℝ} (hw : 0 ≤ w) :
    (arctanCoordinate k hk).decode ((arctanCoordinate k hk).encode w) = w :=
  (arctanCoordinate k hk).decode_encode_of_nonneg hw

/-! ## PLN ordinary-odds additivity -/

/-- PLN confidence odds are evidence weight measured in units of `k`. -/
theorem confidenceOdds_plnOddsCoordinate_encode_eq_weight_div
    {k n : ℝ} (hk : 0 < k) (hn : 0 ≤ n) :
    confidenceOdds ((plnOddsCoordinate k hk).encode n) = n / k := by
  unfold confidenceOdds plnOddsCoordinate
  have hden_pos : 0 < n + k := by linarith
  have hden_ne : n + k ≠ 0 := ne_of_gt hden_pos
  have hk_ne : k ≠ 0 := ne_of_gt hk
  field_simp [hden_ne, hk_ne]
  ring

/-- The PLN chart is additive in ordinary confidence odds under additive
evidence-weight revision. -/
theorem confidenceOdds_pln_revision_additive
    {k n1 n2 : ℝ} (hk : 0 < k) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) :
    confidenceOdds ((plnOddsCoordinate k hk).encode (n1 + n2)) =
      confidenceOdds ((plnOddsCoordinate k hk).encode n1) +
        confidenceOdds ((plnOddsCoordinate k hk).encode n2) := by
  rw [confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk (add_nonneg h1 h2)]
  rw [confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk h1]
  rw [confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk h2]
  field_simp [ne_of_gt hk]

/-- Walley's width-complement bridge and the canonical PLN odds chart use the
same horizon: with IDM strength `s`, `1 - width = n / (n + s)`. -/
theorem walley_width_complement_eq_plnOddsCoordinate_encode
    {s n : ℝ} (hs : 0 < s) (hn : 0 ≤ n) :
    1 - walleyPredictiveWidth n s =
      (plnOddsCoordinate s hs).encode n := by
  have h := walley_width_add_plnOdds s hs hn
  linarith

/-- The Walley width complement has additive confidence odds with the same
scale `s` as canonical evidence-weight revision. -/
theorem confidenceOdds_walley_width_complement_eq_weight_div
    {s n : ℝ} (hs : 0 < s) (hn : 0 ≤ n) :
    confidenceOdds (1 - walleyPredictiveWidth n s) = n / s := by
  rw [walley_width_complement_eq_plnOddsCoordinate_encode hs hn]
  exact confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hs hn

/-- Algebraic endpoint for the later rigidity theorem: if a reconstructive
chart has confidence odds exactly equal to evidence weight in units of `k`,
then its display value is the PLN/NARS display value.  The nonsingularity
hypothesis excludes the totalized-division artifact at `c = 1`. -/
theorem confidenceOdds_weight_identity_forces_pln_encode
    {χ : EvidenceWeightCoordinate} {k n : ℝ} (hk : 0 < k) (hn : 0 ≤ n)
    (hnot : χ.encode n ≠ 1)
    (hχ : confidenceOdds (χ.encode n) = n / k) :
    χ.encode n = (plnOddsCoordinate k hk).encode n := by
  unfold confidenceOdds at hχ
  dsimp [plnOddsCoordinate]
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have hden_c : 1 - χ.encode n ≠ 0 := by
    intro h
    apply hnot
    linarith
  field_simp [hden_c, hk_ne] at hχ ⊢
  nlinarith

/-- A domain-restricted Cauchy lemma for evidence weights.

If a real-valued function is additive and continuous on the nonnegative
evidence-weight axis, then it is linear there.  The proof extends the
nonnegative additive law to an odd continuous additive map on all of `ℝ`, then
uses mathlib's continuous-additive linearity theorem. -/
theorem nonnegative_additive_continuous_linear
    (f : ℝ → ℝ)
    (hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f (x + y) = f x + f y)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    {n : ℝ} (hn : 0 ≤ n) :
    f n = n * f 1 := by
  classical
  have hzero : f 0 = 0 := by
    have h := hadd 0 0 (by norm_num) (by norm_num)
    simp at h
    linarith
  let fExt : ℝ → ℝ :=
    (Set.Ici (0 : ℝ)).piecewise f (fun x : ℝ => - f (-x))
  have hfExt_eq_nonneg : ∀ {x : ℝ}, 0 ≤ x → fExt x = f x := by
    intro x hx
    simp [fExt, hx]
  have hfExt_eq_neg : ∀ {x : ℝ}, x < 0 → fExt x = - f (-x) := by
    intro x hx
    have hxnot : ¬ 0 ≤ x := by linarith
    simp [fExt, hxnot]
  have hfExt_zero : fExt 0 = 0 := by
    rw [hfExt_eq_nonneg (by norm_num), hzero]
  have hnegCont :
      ContinuousOn (fun x : ℝ => - f (-x)) (Set.Iic (0 : ℝ)) := by
    have hmaps :
        Set.MapsTo (fun x : ℝ => -x) (Set.Iic (0 : ℝ)) (Set.Ici (0 : ℝ)) := by
      intro x hx
      simp at hx ⊢
      linarith
    have hcomp : ContinuousOn (fun x : ℝ => f (-x)) (Set.Iic (0 : ℝ)) := by
      exact hcont.comp' (by fun_prop) hmaps
    exact continuous_neg.comp_continuousOn' hcomp
  have hcontExt : Continuous fExt := by
    have hfront :
        ∀ a ∈ frontier (Set.Ici (0 : ℝ)), f a = - f (-a) := by
      intro a ha
      have ha0 : a = 0 := by
        simpa [frontier_Ici] using ha
      subst a
      simp [hzero]
    have hpiece :=
      continuous_piecewise (s := Set.Ici (0 : ℝ)) (f := f)
        (g := fun x : ℝ => - f (-x)) hfront
        (by simpa [closure_Ici] using hcont)
        (by simpa [Set.compl_Ici, closure_Iio] using hnegCont)
    simpa [fExt] using hpiece
  have hExtAdd : ∀ x y : ℝ, fExt (x + y) = fExt x + fExt y := by
    intro x y
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · rw [hfExt_eq_nonneg (add_nonneg hx hy),
          hfExt_eq_nonneg hx, hfExt_eq_nonneg hy]
        exact hadd x y hx hy
      · have hylt : y < 0 := by linarith
        by_cases hxy : 0 ≤ x + y
        · rw [hfExt_eq_nonneg hxy, hfExt_eq_nonneg hx,
            hfExt_eq_neg hylt]
          have hsum : f x = f (x + y) + f (-y) := by
            have h := hadd (x + y) (-y) hxy (by linarith)
            have harg : x + y + -y = x := by ring
            rwa [harg] at h
          linarith
        · have hxylt : x + y < 0 := by linarith
          rw [hfExt_eq_neg hxylt, hfExt_eq_nonneg hx,
            hfExt_eq_neg hylt]
          have hsum : f (-y) = f (-(x + y)) + f x := by
            have h := hadd (-(x + y)) x (by linarith) hx
            have harg : -(x + y) + x = -y := by ring
            rwa [harg] at h
          linarith
    · have hxlt : x < 0 := by linarith
      by_cases hy : 0 ≤ y
      · by_cases hxy : 0 ≤ x + y
        · rw [hfExt_eq_nonneg hxy, hfExt_eq_neg hxlt,
            hfExt_eq_nonneg hy]
          have hsum : f y = f (-x) + f (x + y) := by
            have h := hadd (-x) (x + y) (by linarith) hxy
            have harg : -x + (x + y) = y := by ring
            rwa [harg] at h
          linarith
        · have hxylt : x + y < 0 := by linarith
          rw [hfExt_eq_neg hxylt, hfExt_eq_neg hxlt,
            hfExt_eq_nonneg hy]
          have hsum : f (-x) = f (-(x + y)) + f y := by
            have h := hadd (-(x + y)) y (by linarith) hy
            have harg : -(x + y) + y = -x := by ring
            rwa [harg] at h
          linarith
      · have hylt : y < 0 := by linarith
        rw [hfExt_eq_neg (by linarith : x + y < 0),
          hfExt_eq_neg hxlt, hfExt_eq_neg hylt]
        have hsum : f (-(x + y)) = f (-x) + f (-y) := by
          have h := hadd (-x) (-y) (by linarith) (by linarith)
          have harg : -x + -y = -(x + y) := by ring
          rwa [harg] at h
        linarith
  let fAdd : ℝ →+ ℝ :=
    { toFun := fExt
      map_zero' := hfExt_zero
      map_add' := hExtAdd }
  have hlin := map_real_smul fAdd hcontExt n (1 : ℝ)
  calc
    f n = fExt n := by rw [hfExt_eq_nonneg hn]
    _ = n * fExt 1 := by
      simpa [fAdd, fExt, smul_eq_mul] using hlin
    _ = n * f 1 := by
      rw [hfExt_eq_nonneg (by norm_num : (0 : ℝ) ≤ 1)]

/-- A domain-restricted monotone Cauchy lemma for evidence weights.

If a real-valued function is additive and monotone on the nonnegative
evidence-weight axis, then it is linear there.  The proof extends the
nonnegative additive law to an odd additive map on all of `ℝ`; monotonicity on
the nonnegative axis makes the extension monotone globally, so the existing
monotone-additive Cauchy theorem applies. -/
theorem nonnegative_additive_monotone_linear
    (f : ℝ → ℝ)
    (hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f (x + y) = f x + f y)
    (hmono : MonotoneOn f (Set.Ici (0 : ℝ)))
    {n : ℝ} (hn : 0 ≤ n) :
    f n = n * f 1 := by
  classical
  have hzero : f 0 = 0 := by
    have h := hadd 0 0 (by norm_num) (by norm_num)
    simp at h
    linarith
  let fExt : ℝ → ℝ :=
    (Set.Ici (0 : ℝ)).piecewise f (fun x : ℝ => - f (-x))
  have hfExt_eq_nonneg : ∀ {x : ℝ}, 0 ≤ x → fExt x = f x := by
    intro x hx
    simp [fExt, hx]
  have hfExt_eq_neg : ∀ {x : ℝ}, x < 0 → fExt x = - f (-x) := by
    intro x hx
    have hxnot : ¬ 0 ≤ x := by linarith
    simp [fExt, hxnot]
  have hfExt_zero : fExt 0 = 0 := by
    rw [hfExt_eq_nonneg (by norm_num), hzero]
  have hExtAdd : ∀ x y : ℝ, fExt (x + y) = fExt x + fExt y := by
    intro x y
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · rw [hfExt_eq_nonneg (add_nonneg hx hy),
          hfExt_eq_nonneg hx, hfExt_eq_nonneg hy]
        exact hadd x y hx hy
      · have hylt : y < 0 := by linarith
        by_cases hxy : 0 ≤ x + y
        · rw [hfExt_eq_nonneg hxy, hfExt_eq_nonneg hx,
            hfExt_eq_neg hylt]
          have hsum : f x = f (x + y) + f (-y) := by
            have h := hadd (x + y) (-y) hxy (by linarith)
            have harg : x + y + -y = x := by ring
            rwa [harg] at h
          linarith
        · have hxylt : x + y < 0 := by linarith
          rw [hfExt_eq_neg hxylt, hfExt_eq_nonneg hx,
            hfExt_eq_neg hylt]
          have hsum : f (-y) = f (-(x + y)) + f x := by
            have h := hadd (-(x + y)) x (by linarith) hx
            have harg : -(x + y) + x = -y := by ring
            rwa [harg] at h
          linarith
    · have hxlt : x < 0 := by linarith
      by_cases hy : 0 ≤ y
      · by_cases hxy : 0 ≤ x + y
        · rw [hfExt_eq_nonneg hxy, hfExt_eq_neg hxlt,
            hfExt_eq_nonneg hy]
          have hsum : f y = f (-x) + f (x + y) := by
            have h := hadd (-x) (x + y) (by linarith) hxy
            have harg : -x + (x + y) = y := by ring
            rwa [harg] at h
          linarith
        · have hxylt : x + y < 0 := by linarith
          rw [hfExt_eq_neg hxylt, hfExt_eq_neg hxlt,
            hfExt_eq_nonneg hy]
          have hsum : f (-x) = f (-(x + y)) + f y := by
            have h := hadd (-(x + y)) y (by linarith) hy
            have harg : -(x + y) + y = -x := by ring
            rwa [harg] at h
          linarith
      · have hylt : y < 0 := by linarith
        rw [hfExt_eq_neg (by linarith : x + y < 0),
          hfExt_eq_neg hxlt, hfExt_eq_neg hylt]
        have hsum : f (-(x + y)) = f (-x) + f (-y) := by
          have h := hadd (-x) (-y) (by linarith) (by linarith)
          have harg : -x + -y = -(x + y) := by ring
          rwa [harg] at h
        linarith
  have hExtNonneg : ∀ {x : ℝ}, 0 ≤ x → 0 ≤ fExt x := by
    intro x hx
    rw [hfExt_eq_nonneg hx]
    have hle : f 0 ≤ f x := hmono (by norm_num) hx hx
    rwa [hzero] at hle
  have hExtMono : Monotone fExt := by
    intro x y hxy
    have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
    have hpos : 0 ≤ fExt (y - x) := hExtNonneg hdiff
    have haddxy := hExtAdd x (y - x)
    have harg : x + (y - x) = y := by ring
    rw [harg] at haddxy
    linarith
  have hlinExt :=
    KnuthSkilling.Counterexamples.monotone_additive_is_linear
      hExtAdd hExtMono n
  calc
    f n = fExt n := by rw [hfExt_eq_nonneg hn]
    _ = fExt 1 * n := hlinExt
    _ = n * f 1 := by
      rw [hfExt_eq_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      ring

/-- Canonical confidence-odds rigidity for the PLN/NARS display family.

If displayed confidence odds are additive and continuous on the nonnegative
latent evidence-weight axis, normalized so one unit has odds `1 / k`, and
avoid the totalized-division singularity `c = 1` there, then the display itself
is the PLN/NARS odds coordinate `n / (n + k)`.

This is intentionally narrower than "all reconstructive confidence charts are
PLN": reconstructive charts remain free until this operational/regularity law
is added. -/
theorem canonical_odds_additive_forces_pln
    {χ : EvidenceWeightCoordinate} {k : ℝ} (hk : 0 < k)
    (hadd : ∀ x y : ℝ,
      0 ≤ x → 0 ≤ y →
      confidenceOdds (χ.encode (x + y)) =
        confidenceOdds (χ.encode x) + confidenceOdds (χ.encode y))
    (hcont : ContinuousOn
      (fun w : ℝ => confidenceOdds (χ.encode w)) (Set.Ici (0 : ℝ)))
    (hnorm : confidenceOdds (χ.encode 1) = 1 / k)
    (hnot : ∀ {n : ℝ}, 0 ≤ n → χ.encode n ≠ 1)
    {n : ℝ} (hn : 0 ≤ n) :
    χ.encode n = (plnOddsCoordinate k hk).encode n := by
  let f : ℝ → ℝ := fun w => confidenceOdds (χ.encode w)
  have hlin := nonnegative_additive_continuous_linear f hadd hcont hn
  have hfid : f n = n / k := by
    calc
      f n = n * f 1 := by
        simpa [f, smul_eq_mul] using hlin
      _ = n * (1 / k) := by
        change n * confidenceOdds (χ.encode 1) = n * (1 / k)
        rw [hnorm]
      _ = n / k := by ring
  exact confidenceOdds_weight_identity_forces_pln_encode hk hn (hnot hn) hfid

/-- Monotone-gate variant of canonical confidence-odds rigidity.

The continuity assumption in `canonical_odds_additive_forces_pln` can be
replaced by monotonicity on the nonnegative evidence-weight axis.  This is the
sharper ordered-Cauchy form: additivity plus order-preservation fixes the
confidence-odds scale up to the normalization constant `k`. -/
theorem canonical_odds_monotone_additive_forces_pln
    {χ : EvidenceWeightCoordinate} {k : ℝ} (hk : 0 < k)
    (hadd : ∀ x y : ℝ,
      0 ≤ x → 0 ≤ y →
      confidenceOdds (χ.encode (x + y)) =
        confidenceOdds (χ.encode x) + confidenceOdds (χ.encode y))
    (hmono : MonotoneOn
      (fun w : ℝ => confidenceOdds (χ.encode w)) (Set.Ici (0 : ℝ)))
    (hnorm : confidenceOdds (χ.encode 1) = 1 / k)
    (hnot : ∀ {n : ℝ}, 0 ≤ n → χ.encode n ≠ 1)
    {n : ℝ} (hn : 0 ≤ n) :
    χ.encode n = (plnOddsCoordinate k hk).encode n := by
  let f : ℝ → ℝ := fun w => confidenceOdds (χ.encode w)
  have hlin := nonnegative_additive_monotone_linear f hadd hmono hn
  have hfid : f n = n / k := by
    calc
      f n = n * f 1 := by
        simpa [f, smul_eq_mul] using hlin
      _ = n * (1 / k) := by
        change n * confidenceOdds (χ.encode 1) = n * (1 / k)
        rw [hnorm]
      _ = n / k := by ring
  exact confidenceOdds_weight_identity_forces_pln_encode hk hn (hnot hn) hfid

/-- Non-vacuity witness for the canonical gates: the PLN/NARS chart actually
satisfies the nonnegative-domain additivity, continuity, normalization, and
nonsingularity assumptions used by `canonical_odds_additive_forces_pln`. -/
theorem plnOddsCoordinate_satisfies_canonical_gates {k : ℝ} (hk : 0 < k) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      confidenceOdds ((plnOddsCoordinate k hk).encode (x + y)) =
        confidenceOdds ((plnOddsCoordinate k hk).encode x) +
          confidenceOdds ((plnOddsCoordinate k hk).encode y)) ∧
    ContinuousOn
      (fun w : ℝ => confidenceOdds ((plnOddsCoordinate k hk).encode w))
      (Set.Ici (0 : ℝ)) ∧
    confidenceOdds ((plnOddsCoordinate k hk).encode 1) = 1 / k ∧
    (∀ {n : ℝ}, 0 ≤ n → (plnOddsCoordinate k hk).encode n ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact confidenceOdds_pln_revision_additive hk hx hy
  · have hcont : ContinuousOn (fun w : ℝ => w / k) (Set.Ici (0 : ℝ)) := by
      fun_prop
    refine hcont.congr ?_
    intro w hw
    exact confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk hw
  · exact confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk (by norm_num)
  · intro n hn h
    dsimp [plnOddsCoordinate] at h
    have hden_pos : 0 < n + k := by linarith
    have hden_ne : n + k ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne] at h
    linarith

/-- Non-vacuity witness for the monotone canonical gates. -/
theorem plnOddsCoordinate_satisfies_monotone_canonical_gates {k : ℝ} (hk : 0 < k) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      confidenceOdds ((plnOddsCoordinate k hk).encode (x + y)) =
        confidenceOdds ((plnOddsCoordinate k hk).encode x) +
          confidenceOdds ((plnOddsCoordinate k hk).encode y)) ∧
    MonotoneOn
      (fun w : ℝ => confidenceOdds ((plnOddsCoordinate k hk).encode w))
      (Set.Ici (0 : ℝ)) ∧
    confidenceOdds ((plnOddsCoordinate k hk).encode 1) = 1 / k ∧
    (∀ {n : ℝ}, 0 ≤ n → (plnOddsCoordinate k hk).encode n ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact confidenceOdds_pln_revision_additive hk hx hy
  · intro x hx y hy hxy
    change confidenceOdds ((plnOddsCoordinate k hk).encode x) ≤
      confidenceOdds ((plnOddsCoordinate k hk).encode y)
    rw [confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk hx,
      confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk hy]
    exact div_le_div_of_nonneg_right hxy (le_of_lt hk)
  · exact confidenceOdds_plnOddsCoordinate_encode_eq_weight_div hk (by norm_num)
  · intro n hn h
    dsimp [plnOddsCoordinate] at h
    have hden_pos : 0 < n + k := by linarith
    have hden_ne : n + k ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne] at h
    linarith

/-! ## PLN/Mobius closed form -/

/-- Unit-scale helper for the PLN confidence chart. -/
noncomputable def unitPLNConfidence (u : ℝ) : ℝ := u / (u + 1)

/-- The unit-scale PLN chart transports addition to the Mobius confidence
revision law. -/
theorem unitPLNConfidence_revision_closedForm
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    unitPLNConfidence (u + v) =
      plnConfidenceRevision (unitPLNConfidence u) (unitPLNConfidence v) := by
  unfold unitPLNConfidence plnConfidenceRevision
  have hdu_pos : 0 < u + 1 := by linarith
  have hdv_pos : 0 < v + 1 := by linarith
  have hduv_pos : 0 < u + v + 1 := by linarith
  have hdu_ne : u + 1 ≠ 0 := ne_of_gt hdu_pos
  have hdv_ne : v + 1 ≠ 0 := ne_of_gt hdv_pos
  have hduv_ne : u + v + 1 ≠ 0 := ne_of_gt hduv_pos
  have hprod_ne : (u + 1) * (v + 1) ≠ 0 := mul_ne_zero hdu_ne hdv_ne
  have hnum :
      u / (u + 1) + v / (v + 1) -
          2 * (u / (u + 1)) * (v / (v + 1)) =
        (u + v) / ((u + 1) * (v + 1)) := by
    field_simp [hdu_ne, hdv_ne]
    ring
  have hden :
      1 - u / (u + 1) * (v / (v + 1)) =
        (u + v + 1) / ((u + 1) * (v + 1)) := by
    field_simp [hdu_ne, hdv_ne]
    ring
  rw [hnum, hden]
  field_simp [hprod_ne, hduv_ne]

/-- Closed-form PLN confidence revision for additive evidence weights. -/
theorem plnConfidence_revision_closedForm
    {k n1 n2 : ℝ} (hk : 0 < k) (h1 : 0 ≤ n1) (h2 : 0 ≤ n2) :
    (plnOddsCoordinate k hk).encode (n1 + n2) =
      plnConfidenceRevision
        ((plnOddsCoordinate k hk).encode n1)
        ((plnOddsCoordinate k hk).encode n2) := by
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have henc1 : (plnOddsCoordinate k hk).encode n1 = unitPLNConfidence (n1 / k) := by
    dsimp [plnOddsCoordinate, unitPLNConfidence]
    field_simp [hk_ne]
  have henc2 : (plnOddsCoordinate k hk).encode n2 = unitPLNConfidence (n2 / k) := by
    dsimp [plnOddsCoordinate, unitPLNConfidence]
    field_simp [hk_ne]
  have henc12 :
      (plnOddsCoordinate k hk).encode (n1 + n2) =
        unitPLNConfidence (n1 / k + n2 / k) := by
    dsimp [plnOddsCoordinate, unitPLNConfidence]
    field_simp [hk_ne]
  rw [henc12, henc1, henc2]
  exact unitPLNConfidence_revision_closedForm
    (div_nonneg h1 (le_of_lt hk)) (div_nonneg h2 (le_of_lt hk))

/-! ## Exponential/noisy-OR transported revision -/

/-- The exponential chart transports additive evidence revision to noisy-OR. -/
theorem expCoordinate_revision_closedForm
    {k n1 n2 : ℝ} (hk : 0 < k) :
    (expCoordinate k hk).encode (n1 + n2) =
      expConfidenceRevision ((expCoordinate k hk).encode n1)
        ((expCoordinate k hk).encode n2) := by
  dsimp [expCoordinate, expConfidenceRevision]
  have hk_ne : k ≠ 0 := by linarith
  have hsplit : -(n1 + n2) / k = -n1 / k + -n2 / k := by
    field_simp [hk_ne]
    ring
  rw [hsplit, Real.exp_add]
  ring

/-! ## Tanh/Einstein transported revision -/

/-- Hyperbolic tangent addition, stated locally in the display-law form used by
the tanh confidence chart. -/
theorem tanh_add_formula (x y : ℝ) :
    Real.tanh (x + y) =
      (Real.tanh x + Real.tanh y) / (1 + Real.tanh x * Real.tanh y) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  rw [Real.tanh_eq_sinh_div_cosh x, Real.tanh_eq_sinh_div_cosh y]
  field_simp [ne_of_gt (Real.cosh_pos x), ne_of_gt (Real.cosh_pos y),
    ne_of_gt (Real.cosh_pos (x + y))]

/-- The tanh chart transports additive evidence revision to the
Einstein-style displayed revision law. -/
theorem tanhCoordinate_revision_closedForm
    {k n1 n2 : ℝ} (hk : 0 < k) :
    (tanhCoordinate k hk).encode (n1 + n2) =
      tanhConfidenceRevision ((tanhCoordinate k hk).encode n1)
        ((tanhCoordinate k hk).encode n2) := by
  dsimp [tanhCoordinate, tanhConfidenceRevision]
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have hsplit : (n1 + n2) / k = n1 / k + n2 / k := by
    field_simp [hk_ne]
  rw [hsplit, tanh_add_formula]

/-! ## Law-difference canaries -/

theorem expRevision_differs_from_plnRevision_at_half :
    expConfidenceRevision (1 / 2) (1 / 2) ≠
      plnConfidenceRevision (1 / 2) (1 / 2) := by
  norm_num [expConfidenceRevision, plnConfidenceRevision]

theorem plnRevision_confidenceOdds_additive_at_half :
    confidenceOdds (plnConfidenceRevision (1 / 2) (1 / 2)) =
      confidenceOdds (1 / 2) + confidenceOdds (1 / 2) := by
  norm_num [confidenceOdds, plnConfidenceRevision]

theorem expRevision_not_confidenceOdds_additive_at_half :
    confidenceOdds (expConfidenceRevision (1 / 2) (1 / 2)) ≠
      confidenceOdds (1 / 2) + confidenceOdds (1 / 2) := by
  norm_num [confidenceOdds, expConfidenceRevision]

theorem tanhRevision_differs_from_plnRevision_at_half :
    tanhConfidenceRevision (1 / 2) (1 / 2) ≠
      plnConfidenceRevision (1 / 2) (1 / 2) := by
  norm_num [tanhConfidenceRevision, plnConfidenceRevision]

end EvidenceWeightCoordinate
end Mettapedia.Logic.PLNConfidenceWeight
