import Mettapedia.ProbabilityTheory.ImpreciseProbability.Basic
import Mettapedia.ProbabilityTheory.FiniteMeasureSupport
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Pointwise
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order
import Mathlib.Tactic

/-!
# Projective Credal Systems

This module isolates the shared finite-to-infinite abstraction behind two
threads:

* Walley natural extension: compatible local assessments induce a conservative
  lower envelope over global completions.
* Infinite MLN/Gibbs semantics: compatible finite-dimensional marginals define
  a projective family of possible global completions.

The file deliberately proves the envelope and compatibility laws that are
available without functional-analysis compactness.  Full inverse-limit
existence is a later theorem: here nonemptiness is an explicit hypothesis or a
concrete global completion.

Terminology matches Walley's lower-prevision presentation: natural extension is
modeled as a lower envelope of compatible precise previsions, the shared base is
finite-additive/functional, and σ-additivity/conglomerability are refinement
axes rather than hidden assumptions.
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

open Set
open Pointwise
open MeasureTheory
open Mettapedia.ProbabilityTheory.FiniteMeasureSupport
open Mettapedia.ProbabilityTheory.ImpreciseProbability

/-! ## Bounded measurable observable carrier -/

/-- A bounded measurable gamble: the honest σ-additive observable carrier.

The base Walley layer keeps `Gamble Ω = Ω → ℝ` as a finite-additive functional
domain.  Measure-theoretic previsions require a smaller domain: measurable
bounded observables.  This structure is the carrier that future weak*/compact
and σ-additive adapters should target. -/
structure BoundedMeasurableGamble (Ω : Type*) [MeasurableSpace Ω] where
  toFun : Ω → ℝ
  measurable_toFun : Measurable toFun
  bounded_abs : ∃ B : ℝ, 0 ≤ B ∧ ∀ ω : Ω, |toFun ω| ≤ B

namespace BoundedMeasurableGamble

variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]

instance : CoeFun (BoundedMeasurableGamble Ω) (fun _ => Ω → ℝ) := ⟨toFun⟩

@[ext] theorem ext {X Y : BoundedMeasurableGamble Ω}
    (h : ∀ ω, X ω = Y ω) : X = Y := by
  cases X
  cases Y
  simp only [mk.injEq]
  funext ω
  exact h ω

/-- Forget a bounded measurable observable to the raw Walley gamble type. -/
def toGamble (X : BoundedMeasurableGamble Ω) : Gamble Ω :=
  fun ω => X ω

@[simp] theorem toGamble_apply (X : BoundedMeasurableGamble Ω) (ω : Ω) :
    X.toGamble ω = X ω :=
  rfl

/-- Constant bounded measurable gambles. -/
def const (c : ℝ) : BoundedMeasurableGamble Ω where
  toFun := fun _ => c
  measurable_toFun := measurable_const
  bounded_abs := by
    refine ⟨|c|, abs_nonneg c, ?_⟩
    intro ω
    simp

instance : Zero (BoundedMeasurableGamble Ω) := ⟨const 0⟩
instance : One (BoundedMeasurableGamble Ω) := ⟨const 1⟩

@[simp] theorem const_apply (c : ℝ) (ω : Ω) :
    const (Ω := Ω) c ω = c :=
  rfl

@[simp] theorem zero_apply (ω : Ω) :
    (0 : BoundedMeasurableGamble Ω) ω = 0 :=
  rfl

@[simp] theorem one_apply (ω : Ω) :
    (1 : BoundedMeasurableGamble Ω) ω = 1 :=
  rfl

instance : Neg (BoundedMeasurableGamble Ω) where
  neg X :=
    { toFun := fun ω => -X ω
      measurable_toFun := X.measurable_toFun.neg
      bounded_abs := by
        rcases X.bounded_abs with ⟨B, hB0, hB⟩
        refine ⟨B, hB0, ?_⟩
        intro ω
        simpa using hB ω }

@[simp] theorem neg_apply (X : BoundedMeasurableGamble Ω) (ω : Ω) :
    (-X) ω = -X ω :=
  rfl

instance : Add (BoundedMeasurableGamble Ω) where
  add X Y :=
    { toFun := fun ω => X ω + Y ω
      measurable_toFun := X.measurable_toFun.add Y.measurable_toFun
      bounded_abs := by
        rcases X.bounded_abs with ⟨BX, hBX0, hBX⟩
        rcases Y.bounded_abs with ⟨BY, hBY0, hBY⟩
        refine ⟨BX + BY, add_nonneg hBX0 hBY0, ?_⟩
        intro ω
        calc
          |X ω + Y ω| ≤ |X ω| + |Y ω| := abs_add_le (X ω) (Y ω)
          _ ≤ BX + BY := add_le_add (hBX ω) (hBY ω) }

@[simp] theorem add_apply (X Y : BoundedMeasurableGamble Ω) (ω : Ω) :
    (X + Y) ω = X ω + Y ω :=
  rfl

instance : Sub (BoundedMeasurableGamble Ω) where
  sub X Y := X + (-Y)

@[simp] theorem sub_apply (X Y : BoundedMeasurableGamble Ω) (ω : Ω) :
    (X - Y) ω = X ω - Y ω :=
  rfl

instance : SMul ℝ (BoundedMeasurableGamble Ω) where
  smul r X :=
    { toFun := fun ω => r * X ω
      measurable_toFun := X.measurable_toFun.const_mul r
      bounded_abs := by
        rcases X.bounded_abs with ⟨B, hB0, hB⟩
        refine ⟨|r| * B, mul_nonneg (abs_nonneg r) hB0, ?_⟩
        intro ω
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hB ω) (abs_nonneg r) }

@[simp] theorem smul_apply (r : ℝ) (X : BoundedMeasurableGamble Ω) (ω : Ω) :
    (r • X) ω = r * X ω :=
  rfl

/-- Every bounded measurable gamble has a raw absolute bound. -/
theorem exists_abs_bound (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ω : Ω, |X ω| ≤ B :=
  X.bounded_abs

/-- Every bounded measurable gamble has a finite upper pointwise bound. -/
theorem exists_upper_bound (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, ∀ ω : Ω, X ω ≤ B := by
  rcases X.bounded_abs with ⟨B, _hB0, hB⟩
  refine ⟨B, ?_⟩
  intro ω
  exact (abs_le.mp (hB ω)).2

/-- Every bounded measurable gamble has a finite lower pointwise bound. -/
theorem exists_lower_bound (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, ∀ ω : Ω, B ≤ X ω := by
  rcases X.bounded_abs with ⟨B, _hB0, hB⟩
  refine ⟨-B, ?_⟩
  intro ω
  exact (abs_le.mp (hB ω)).1

/-- Bounded measurable real observables are Bochner-integrable against any
finite measure. -/
theorem integrable (X : BoundedMeasurableGamble Ω)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable (fun ω => X ω) μ := by
  rcases X.bounded_abs with ⟨B, _hB0, hB⟩
  refine Integrable.mono' (integrable_const B)
    X.measurable_toFun.aestronglyMeasurable ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using hB ω

/-- Pull a bounded measurable gamble back along a measurable map.  This is the
carrier-level form of cylinder restriction/pushforward duality. -/
def pullback (f : Γ → Ω) (hf : Measurable f)
    (X : BoundedMeasurableGamble Ω) : BoundedMeasurableGamble Γ where
  toFun := fun γ => X (f γ)
  measurable_toFun := X.measurable_toFun.comp hf
  bounded_abs := by
    rcases X.bounded_abs with ⟨B, hB0, hB⟩
    exact ⟨B, hB0, fun γ => hB (f γ)⟩

@[simp] theorem pullback_apply (f : Γ → Ω) (hf : Measurable f)
    (X : BoundedMeasurableGamble Ω) (γ : Γ) :
    pullback f hf X γ = X (f γ) :=
  rfl

/-- On a finite measurable state space with measurable singletons, every raw
gamble is automatically a bounded measurable gamble.  This is the precise
finite-window/cylinder bridge into the σ-additive observable carrier. -/
noncomputable def ofFinite
    [Fintype Ω] [MeasurableSingletonClass Ω] (X : Gamble Ω) :
    BoundedMeasurableGamble Ω where
  toFun := X
  measurable_toFun := measurable_of_finite X
  bounded_abs := by
    classical
    by_cases hnonempty : (Finset.univ : Finset Ω).Nonempty
    · obtain ⟨ω₀, _hω₀, hmax⟩ :=
        Finset.exists_max_image
          (s := (Finset.univ : Finset Ω)) (f := fun ω => |X ω|)
          hnonempty
      refine ⟨|X ω₀|, abs_nonneg (X ω₀), ?_⟩
      intro ω
      exact hmax ω (Finset.mem_univ ω)
    · refine ⟨0, le_rfl, ?_⟩
      intro ω
      exact False.elim (hnonempty ⟨ω, Finset.mem_univ ω⟩)

@[simp] theorem ofFinite_apply
    [Fintype Ω] [MeasurableSingletonClass Ω] (X : Gamble Ω) (ω : Ω) :
    ofFinite X ω = X ω :=
  rfl

end BoundedMeasurableGamble

/-! ## σ-additive bounded-observable previsions -/

/-- A precise prevision on bounded measurable observables.

This is the σ-additive refinement target: unlike `PrecisePrevision Ω`, whose
domain is all raw `Gamble Ω`, this structure only evaluates bounded measurable
observables.  Probability measures inhabit this structure by Bochner
integration. -/
structure BoundedMeasurablePrecisePrevision
    (Ω : Type*) [MeasurableSpace Ω] where
  toFun : BoundedMeasurableGamble Ω → ℝ
  lower_bound : ∀ (X : BoundedMeasurableGamble Ω) (c : ℝ),
    (∀ ω, c ≤ X ω) → c ≤ toFun X
  pos_homog : ∀ (r : ℝ) (X : BoundedMeasurableGamble Ω),
    0 ≤ r → toFun (r • X) = r * toFun X
  add : ∀ (X Y : BoundedMeasurableGamble Ω),
    toFun (X + Y) = toFun X + toFun Y

namespace BoundedMeasurablePrecisePrevision

variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]

instance : CoeFun (BoundedMeasurablePrecisePrevision Ω)
    (fun _ => BoundedMeasurableGamble Ω → ℝ) := ⟨toFun⟩

@[ext] theorem ext {P Q : BoundedMeasurablePrecisePrevision Ω}
    (h : ∀ X : BoundedMeasurableGamble Ω, P X = Q X) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq]
  exact funext h

/-- A probability measure induces a precise prevision on bounded measurable
observables by integration. -/
noncomputable def ofProbabilityMeasure
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    BoundedMeasurablePrecisePrevision Ω where
  toFun X := ∫ ω, X ω ∂μ
  lower_bound := by
    intro X c hc
    have hconst : Integrable (fun _ : Ω => c) μ := integrable_const c
    have hX : Integrable (fun ω => X ω) μ := X.integrable μ
    have hmono : (fun _ : Ω => c) ≤ᵐ[μ] fun ω => X ω := by
      filter_upwards with ω
      exact hc ω
    have h := integral_mono_ae hconst hX hmono
    simpa using h
  pos_homog := by
    intro r X _hr
    simpa using
      (integral_smul (μ := μ) r (fun ω => X ω))
  add := by
    intro X Y
    simpa using
      (integral_add (μ := μ) (X.integrable μ) (Y.integrable μ))

@[simp] theorem ofProbabilityMeasure_apply
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : BoundedMeasurableGamble Ω) :
    ofProbabilityMeasure μ X = ∫ ω, X ω ∂μ :=
  rfl

theorem ofProbabilityMeasure_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : BoundedMeasurableGamble Ω) (c : ℝ)
    (hc : ∀ ω, c ≤ X ω) :
    c ≤ ofProbabilityMeasure μ X :=
  (ofProbabilityMeasure μ).lower_bound X c hc

theorem ofProbabilityMeasure_add
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : BoundedMeasurableGamble Ω) :
    ofProbabilityMeasure μ (X + Y) =
      ofProbabilityMeasure μ X + ofProbabilityMeasure μ Y :=
  (ofProbabilityMeasure μ).add X Y

theorem ofProbabilityMeasure_pos_homog
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : ℝ) (X : BoundedMeasurableGamble Ω) (hr : 0 ≤ r) :
    ofProbabilityMeasure μ (r • X) =
      r * ofProbabilityMeasure μ X :=
  (ofProbabilityMeasure μ).pos_homog r X hr

@[simp] theorem map_zero (P : BoundedMeasurablePrecisePrevision Ω) :
    P (0 : BoundedMeasurableGamble Ω) = 0 := by
  have h := P.pos_homog 0 (0 : BoundedMeasurableGamble Ω) (le_refl 0)
  have hzero : (0 : ℝ) • (0 : BoundedMeasurableGamble Ω) =
      (0 : BoundedMeasurableGamble Ω) := by
    ext ω
    simp
  rw [hzero, zero_mul] at h
  exact h

@[simp] theorem map_neg (P : BoundedMeasurablePrecisePrevision Ω)
    (X : BoundedMeasurableGamble Ω) :
    P (-X) = -P X := by
  have hadd := P.add X (-X)
  have hzero : X + -X = (0 : BoundedMeasurableGamble Ω) := by
    ext ω
    simp
  rw [hzero, P.map_zero] at hadd
  linarith

theorem map_sub (P : BoundedMeasurablePrecisePrevision Ω)
    (X Y : BoundedMeasurableGamble Ω) :
    P (X - Y) = P X - P Y := by
  change P (X + -Y) = P X - P Y
  rw [P.add X (-Y), P.map_neg Y]
  ring

/-- Positive homogeneity plus additivity gives full real homogeneity. -/
theorem map_smul (P : BoundedMeasurablePrecisePrevision Ω)
    (r : ℝ) (X : BoundedMeasurableGamble Ω) :
    P (r • X) = r * P X := by
  by_cases hr : 0 ≤ r
  · exact P.pos_homog r X hr
  · have hneg_nonneg : 0 ≤ -r := by linarith
    have hpos := P.pos_homog (-r) X hneg_nonneg
    have hsmul : r • X = -((-r) • X) := by
      ext ω
      change r * X ω = -((-r) * X ω)
      ring
    calc
      P (r • X) = P (-((-r) • X)) := by rw [hsmul]
      _ = -P ((-r) • X) := P.map_neg ((-r) • X)
      _ = -((-r) * P X) := by rw [hpos]
      _ = r * P X := by ring

@[simp] theorem map_const_one (P : BoundedMeasurablePrecisePrevision Ω) :
    P (BoundedMeasurableGamble.const (Ω := Ω) 1) = 1 := by
  have hlo : (1 : ℝ) ≤
      P (BoundedMeasurableGamble.const (Ω := Ω) 1) := by
    exact P.lower_bound (BoundedMeasurableGamble.const (Ω := Ω) 1) 1
      (by intro ω; rfl)
  have hneg_bound : (-1 : ℝ) ≤
      P (-(BoundedMeasurableGamble.const (Ω := Ω) 1)) := by
    exact P.lower_bound
      (-(BoundedMeasurableGamble.const (Ω := Ω) 1)) (-1)
      (by intro ω; rfl)
  have hhi : P (BoundedMeasurableGamble.const (Ω := Ω) 1) ≤ 1 := by
    rw [P.map_neg] at hneg_bound
    linarith
  exact le_antisymm hhi hlo

@[simp] theorem map_const (P : BoundedMeasurablePrecisePrevision Ω)
    (c : ℝ) :
    P (BoundedMeasurableGamble.const (Ω := Ω) c) = c := by
  have hconst : BoundedMeasurableGamble.const (Ω := Ω) c =
      c • BoundedMeasurableGamble.const (Ω := Ω) 1 := by
    ext ω
    change c = c * 1
    ring
  calc
    P (BoundedMeasurableGamble.const (Ω := Ω) c) =
        P (c • BoundedMeasurableGamble.const (Ω := Ω) 1) := by
          rw [hconst]
    _ = c * P (BoundedMeasurableGamble.const (Ω := Ω) 1) :=
        P.map_smul c (BoundedMeasurableGamble.const (Ω := Ω) 1)
    _ = c := by simp

theorem upper_bound (P : BoundedMeasurablePrecisePrevision Ω)
    (X : BoundedMeasurableGamble Ω) (c : ℝ)
    (hc : ∀ ω, X ω ≤ c) :
    P X ≤ c := by
  have hnonneg : 0 ≤
      P (BoundedMeasurableGamble.const (Ω := Ω) c - X) := by
    exact P.lower_bound (BoundedMeasurableGamble.const (Ω := Ω) c - X) 0
      (by
        intro ω
        change (0 : ℝ) ≤ c - X ω
        linarith [hc ω])
  rw [P.map_sub, P.map_const] at hnonneg
  linarith

/-- A bounded precise prevision is norm-bounded by any pointwise absolute
bound on the observable.  This is the basic dual-ball estimate needed by the
future weak*/compact carrier. -/
theorem abs_apply_le_of_abs_le (P : BoundedMeasurablePrecisePrevision Ω)
    (X : BoundedMeasurableGamble Ω) (B : ℝ)
    (hX : ∀ ω, |X ω| ≤ B) :
    |P X| ≤ B := by
  have hlo : -B ≤ P X := by
    exact P.lower_bound X (-B) fun ω => (abs_le.mp (hX ω)).1
  have hhi : P X ≤ B := by
    exact P.upper_bound X B fun ω => (abs_le.mp (hX ω)).2
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Every bounded observable has a finite absolute bound on its precise
prevision value. -/
theorem exists_abs_apply_bound (P : BoundedMeasurablePrecisePrevision Ω)
    (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ |P X| ≤ B := by
  rcases X.exists_abs_bound with ⟨B, hB0, hB⟩
  exact ⟨B, hB0, P.abs_apply_le_of_abs_le X B hB⟩

/-- Convex mixture of two bounded-measurable precise previsions.  This is the
bounded-observable analogue of `PrecisePrevision.mix`. -/
def mix (t : ℝ) (P Q : BoundedMeasurablePrecisePrevision Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    BoundedMeasurablePrecisePrevision Ω where
  toFun X := t * P X + (1 - t) * Q X
  lower_bound := by
    intro X c hc
    have hP : c ≤ P X := P.lower_bound X c hc
    have hQ : c ≤ Q X := Q.lower_bound X c hc
    have h1t : 0 ≤ 1 - t := by linarith
    nlinarith
  pos_homog := by
    intro r X hr
    rw [P.pos_homog r X hr, Q.pos_homog r X hr]
    ring
  add := by
    intro X Y
    rw [P.add X Y, Q.add X Y]
    ring

@[simp] theorem mix_apply (t : ℝ)
    (P Q : BoundedMeasurablePrecisePrevision Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X : BoundedMeasurableGamble Ω) :
    mix t P Q ht0 ht1 X = t * P X + (1 - t) * Q X :=
  rfl

/-- Precise previsions are Lipschitz for any supplied pointwise sup bound on
the difference of two observables. -/
theorem abs_apply_sub_apply_le_of_abs_sub_le
    (P : BoundedMeasurablePrecisePrevision Ω)
    (X Y : BoundedMeasurableGamble Ω) (B : ℝ)
    (hXY : ∀ ω, |X ω - Y ω| ≤ B) :
    |P X - P Y| ≤ B := by
  have h := P.abs_apply_le_of_abs_le (X - Y) B (by
    intro ω
    simpa using hXY ω)
  rwa [P.map_sub] at h

/-- Every pair of bounded observables has a finite absolute bound on the
difference of their precise prevision values. -/
theorem exists_abs_apply_sub_apply_bound
    (P : BoundedMeasurablePrecisePrevision Ω)
    (X Y : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ |P X - P Y| ≤ B := by
  rcases (X - Y).exists_abs_bound with ⟨B, hB0, hB⟩
  exact ⟨B, hB0, P.abs_apply_sub_apply_le_of_abs_sub_le X Y B hB⟩

/-- Evaluation-coordinate map for bounded-measurable precise previsions.

This is the bounded-observable analogue of the finite atomic evaluation
coordinate.  The induced topology is the weak*/pointwise-evaluation topology
used before the eventual compactness theorem. -/
def evaluationCoordinate
    (P : BoundedMeasurablePrecisePrevision Ω) :
    BoundedMeasurableGamble Ω → ℝ :=
  fun X => P X

/-- Bounded-measurable precise previsions are determined by their observable
evaluation coordinates. -/
theorem evaluationCoordinate_injective :
    Function.Injective (evaluationCoordinate :
      BoundedMeasurablePrecisePrevision Ω →
        BoundedMeasurableGamble Ω → ℝ) := by
  intro P Q hPQ
  ext X
  exact congrFun hPQ X

/-- Evaluation topology on bounded-measurable precise previsions, induced by
all bounded-observable evaluations. -/
def evaluationTopology :
    TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
  TopologicalSpace.induced
    (fun P : BoundedMeasurablePrecisePrevision Ω =>
      evaluationCoordinate P)
    inferInstance

theorem evaluationCoordinate_continuous :
    @Continuous (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurableGamble Ω → ℝ)
      evaluationTopology inferInstance evaluationCoordinate :=
  continuous_induced_dom

/-- The evaluation-coordinate map induces the evaluation topology. -/
theorem evaluationCoordinate_isInducing :
    @Topology.IsInducing (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurableGamble Ω → ℝ)
      evaluationTopology inferInstance evaluationCoordinate :=
  Topology.IsInducing.induced _

/-- The evaluation-coordinate map embeds bounded-measurable precise previsions
into the product coordinate space. -/
theorem evaluationCoordinate_isEmbedding :
    @Topology.IsEmbedding (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurableGamble Ω → ℝ)
      evaluationTopology inferInstance evaluationCoordinate :=
  Topology.IsEmbedding.induced evaluationCoordinate_injective

/-- Every bounded-observable evaluation is continuous for the evaluation
topology. -/
theorem eval_continuous (X : BoundedMeasurableGamble Ω) :
    @Continuous (BoundedMeasurablePrecisePrevision Ω) ℝ
      evaluationTopology inferInstance (fun P => P X) := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change @Continuous (BoundedMeasurablePrecisePrevision Ω) ℝ
      evaluationTopology inferInstance
      ((fun f : BoundedMeasurableGamble Ω → ℝ => f X) ∘
        evaluationCoordinate)
  exact (continuous_apply X).comp evaluationCoordinate_continuous

/-- Fixed-coefficient convex mixing is continuous in the bounded-measurable
evaluation topology. -/
theorem mix_continuous (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
      evaluationTopology
    Continuous
      (fun PQ :
          BoundedMeasurablePrecisePrevision Ω ×
            BoundedMeasurablePrecisePrevision Ω =>
        mix t PQ.1 PQ.2 ht0 ht1) := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change @Continuous
    (BoundedMeasurablePrecisePrevision Ω ×
      BoundedMeasurablePrecisePrevision Ω)
    (BoundedMeasurablePrecisePrevision Ω)
    inferInstance
    (TopologicalSpace.induced
      (fun P : BoundedMeasurablePrecisePrevision Ω =>
        evaluationCoordinate P)
      inferInstance)
    (fun PQ => mix t PQ.1 PQ.2 ht0 ht1)
  rw [continuous_induced_rng]
  change Continuous
    (fun PQ :
        BoundedMeasurablePrecisePrevision Ω ×
          BoundedMeasurablePrecisePrevision Ω =>
      evaluationCoordinate (mix t PQ.1 PQ.2 ht0 ht1))
  rw [continuous_pi_iff]
  intro X
  change Continuous
    (fun PQ :
        BoundedMeasurablePrecisePrevision Ω ×
          BoundedMeasurablePrecisePrevision Ω =>
      t * PQ.1 X + (1 - t) * PQ.2 X)
  exact
    (continuous_const.mul ((eval_continuous X).comp continuous_fst)).add
      (continuous_const.mul ((eval_continuous X).comp continuous_snd))

/-- Evaluation equality constraints are closed in the bounded-measurable
evaluation topology. -/
theorem isClosed_eval_eq
    (X : BoundedMeasurableGamble Ω) (c : ℝ) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω) evaluationTopology
      {P | P X = c} := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change IsClosed {P : BoundedMeasurablePrecisePrevision Ω | P X = c}
  exact isClosed_eq (eval_continuous X) continuous_const

/-- Upper halfspace evaluation constraints are closed in the
bounded-measurable evaluation topology. -/
theorem isClosed_eval_le
    (X : BoundedMeasurableGamble Ω) (c : ℝ) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω) evaluationTopology
      {P | P X ≤ c} := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change IsClosed {P : BoundedMeasurablePrecisePrevision Ω | P X ≤ c}
  exact isClosed_le (eval_continuous X) continuous_const

/-- Lower halfspace evaluation constraints are closed in the
bounded-measurable evaluation topology. -/
theorem isClosed_le_eval
    (X : BoundedMeasurableGamble Ω) (c : ℝ) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω) evaluationTopology
      {P | c ≤ P X} := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change IsClosed {P : BoundedMeasurablePrecisePrevision Ω | c ≤ P X}
  exact isClosed_le continuous_const (eval_continuous X)

/-- Normalization is a closed constraint in the bounded-measurable evaluation
topology. -/
theorem isClosed_normalized :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω) evaluationTopology
      {P | P (BoundedMeasurableGamble.const (Ω := Ω) 1) = 1} := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change IsClosed
    {P : BoundedMeasurablePrecisePrevision Ω |
      P (BoundedMeasurableGamble.const (Ω := Ω) 1) = 1}
  exact isClosed_eval_eq (BoundedMeasurableGamble.const (Ω := Ω) 1) 1

/-- Positivity on a fixed observable is a closed constraint in the
bounded-measurable evaluation topology. -/
theorem isClosed_nonnegative_on
    (X : BoundedMeasurableGamble Ω) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω) evaluationTopology
      {P | 0 ≤ P X} := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  change IsClosed {P : BoundedMeasurablePrecisePrevision Ω | 0 ≤ P X}
  exact isClosed_le_eval X 0

/-! ### Product-coordinate carrier laws -/

/-- Coordinate functions satisfying the lower-bound law of precise previsions. -/
def coordinateLowerBoundSet :
    Set (BoundedMeasurableGamble Ω → ℝ) :=
  {φ | ∀ (X : BoundedMeasurableGamble Ω) (c : ℝ),
    (∀ ω, c ≤ X ω) → c ≤ φ X}

/-- Coordinate functions satisfying positive homogeneity. -/
def coordinatePosHomogSet :
    Set (BoundedMeasurableGamble Ω → ℝ) :=
  {φ | ∀ (r : ℝ) (X : BoundedMeasurableGamble Ω),
    0 ≤ r → φ (r • X) = r * φ X}

/-- Coordinate functions satisfying additivity. -/
def coordinateAddSet :
    Set (BoundedMeasurableGamble Ω → ℝ) :=
  {φ | ∀ (X Y : BoundedMeasurableGamble Ω),
    φ (X + Y) = φ X + φ Y}

/-- The product-coordinate law set for bounded-measurable precise previsions.

This is the closed subset of the product coordinate space whose points are
exactly the functions `X ↦ P X` satisfying the precise-prevision laws. -/
def coordinateLawSet :
    Set (BoundedMeasurableGamble Ω → ℝ) :=
  coordinateLowerBoundSet ∩ (coordinatePosHomogSet ∩ coordinateAddSet)

theorem coordinateLowerBoundSet_isClosed :
    IsClosed (coordinateLowerBoundSet (Ω := Ω)) := by
  unfold coordinateLowerBoundSet
  simp only [setOf_forall]
  exact isClosed_iInter fun X =>
    isClosed_iInter fun c =>
      isClosed_iInter fun _hc =>
        isClosed_le continuous_const (continuous_apply X)

theorem coordinatePosHomogSet_isClosed :
    IsClosed (coordinatePosHomogSet (Ω := Ω)) := by
  unfold coordinatePosHomogSet
  simp only [setOf_forall]
  exact isClosed_iInter fun r =>
    isClosed_iInter fun X =>
      isClosed_iInter fun _hr =>
        isClosed_eq (continuous_apply (r • X))
          (continuous_const.mul (continuous_apply X))

theorem coordinateAddSet_isClosed :
    IsClosed (coordinateAddSet (Ω := Ω)) := by
  unfold coordinateAddSet
  simp only [setOf_forall]
  exact isClosed_iInter fun X =>
    isClosed_iInter fun Y =>
      isClosed_eq (continuous_apply (X + Y))
        ((continuous_apply X).add (continuous_apply Y))

/-- The bounded-measurable precise-prevision laws cut out a closed subset of
the product coordinate space. -/
theorem coordinateLawSet_isClosed :
    IsClosed (coordinateLawSet (Ω := Ω)) := by
  unfold coordinateLawSet
  exact (coordinateLowerBoundSet_isClosed (Ω := Ω)).inter
    ((coordinatePosHomogSet_isClosed (Ω := Ω)).inter
      (coordinateAddSet_isClosed (Ω := Ω)))

theorem evaluationCoordinate_mem_coordinateLawSet
    (P : BoundedMeasurablePrecisePrevision Ω) :
    evaluationCoordinate P ∈ coordinateLawSet (Ω := Ω) := by
  exact ⟨P.lower_bound, P.pos_homog, P.add⟩

/-- Reconstruct a bounded-measurable precise prevision from product coordinates
satisfying the precise-prevision laws. -/
def ofCoordinate
    (φ : BoundedMeasurableGamble Ω → ℝ)
    (hφ : φ ∈ coordinateLawSet (Ω := Ω)) :
    BoundedMeasurablePrecisePrevision Ω where
  toFun := φ
  lower_bound := hφ.1
  pos_homog := hφ.2.1
  add := hφ.2.2

@[simp] theorem ofCoordinate_apply
    (φ : BoundedMeasurableGamble Ω → ℝ)
    (hφ : φ ∈ coordinateLawSet (Ω := Ω))
    (X : BoundedMeasurableGamble Ω) :
    ofCoordinate φ hφ X = φ X :=
  rfl

@[simp] theorem evaluationCoordinate_ofCoordinate
    (φ : BoundedMeasurableGamble Ω → ℝ)
    (hφ : φ ∈ coordinateLawSet (Ω := Ω)) :
    evaluationCoordinate (ofCoordinate φ hφ) = φ :=
  rfl

/-- The coordinate image of bounded-measurable precise previsions is exactly
the closed product-coordinate law set. -/
theorem range_evaluationCoordinate_eq_coordinateLawSet :
    Set.range (evaluationCoordinate :
      BoundedMeasurablePrecisePrevision Ω →
        BoundedMeasurableGamble Ω → ℝ) =
      coordinateLawSet (Ω := Ω) := by
  ext φ
  constructor
  · rintro ⟨P, rfl⟩
    exact evaluationCoordinate_mem_coordinateLawSet P
  · intro hφ
    exact ⟨ofCoordinate φ hφ, rfl⟩

/-- The bounded-measurable precise-prevision carrier has closed image in the
product coordinate space.  This is the closed-carrier precursor to the future
compactness theorem. -/
theorem isClosed_range_evaluationCoordinate :
    IsClosed (Set.range (evaluationCoordinate :
      BoundedMeasurablePrecisePrevision Ω →
        BoundedMeasurableGamble Ω → ℝ)) := by
  rw [range_evaluationCoordinate_eq_coordinateLawSet]
  exact coordinateLawSet_isClosed

/-! ### Compact product-coordinate carrier -/

/-- A canonical absolute bound for a bounded measurable observable. -/
noncomputable def observableAbsBound
    (X : BoundedMeasurableGamble Ω) : ℝ :=
  Classical.choose X.exists_abs_bound

theorem observableAbsBound_nonneg (X : BoundedMeasurableGamble Ω) :
    0 ≤ observableAbsBound X :=
  (Classical.choose_spec X.exists_abs_bound).1

theorem abs_le_observableAbsBound (X : BoundedMeasurableGamble Ω) :
    ∀ ω : Ω, |X ω| ≤ observableAbsBound X :=
  (Classical.choose_spec X.exists_abs_bound).2

/-- The product coordinate box cut out by the canonical observable bounds. -/
def coordinateAbsBoundBox :
    Set (BoundedMeasurableGamble Ω → ℝ) :=
  Set.pi Set.univ fun X : BoundedMeasurableGamble Ω =>
    Set.Icc (-(observableAbsBound X)) (observableAbsBound X)

theorem mem_coordinateAbsBoundBox_iff
    {φ : BoundedMeasurableGamble Ω → ℝ} :
    φ ∈ coordinateAbsBoundBox (Ω := Ω) ↔
      ∀ X : BoundedMeasurableGamble Ω, |φ X| ≤ observableAbsBound X := by
  constructor
  · intro hφ X
    exact abs_le.mpr (hφ X (Set.mem_univ X))
  · intro hφ X _hX
    exact abs_le.mp (hφ X)

/-- The canonical coordinate box is compact by Tychonoff: each coordinate is
a compact real interval. -/
theorem coordinateAbsBoundBox_isCompact :
    IsCompact (coordinateAbsBoundBox (Ω := Ω)) := by
  unfold coordinateAbsBoundBox
  exact isCompact_univ_pi fun X =>
    isCompact_Icc

/-- Every law-satisfying coordinate functional lies in the canonical bounded
coordinate box. -/
theorem coordinateLawSet_subset_coordinateAbsBoundBox :
    coordinateLawSet (Ω := Ω) ⊆ coordinateAbsBoundBox (Ω := Ω) := by
  intro φ hφ
  rw [mem_coordinateAbsBoundBox_iff]
  intro X
  simpa using
    (ofCoordinate φ hφ).abs_apply_le_of_abs_le
      X (observableAbsBound X) (abs_le_observableAbsBound X)

/-- The coordinate law set is compact: it is a closed subset of the canonical
compact coordinate box. -/
theorem coordinateLawSet_isCompact :
    IsCompact (coordinateLawSet (Ω := Ω)) :=
  coordinateAbsBoundBox_isCompact.of_isClosed_subset
    coordinateLawSet_isClosed
    coordinateLawSet_subset_coordinateAbsBoundBox

/-- The coordinate image of bounded-measurable precise previsions is compact.

This is the first genuine compact carrier theorem for the bounded-observable
prevision layer: the carrier is compact after embedding into product
coordinates. -/
theorem range_evaluationCoordinate_isCompact :
    IsCompact (Set.range (evaluationCoordinate :
      BoundedMeasurablePrecisePrevision Ω →
        BoundedMeasurableGamble Ω → ℝ)) := by
  rw [range_evaluationCoordinate_eq_coordinateLawSet]
  exact coordinateLawSet_isCompact

/-- Every law-satisfying coordinate functional is realized by a
bounded-measurable precise prevision. -/
theorem coordinateLawSet_subset_range_evaluationCoordinate :
    coordinateLawSet (Ω := Ω) ⊆
      Set.range (evaluationCoordinate :
        BoundedMeasurablePrecisePrevision Ω →
          BoundedMeasurableGamble Ω → ℝ) := by
  rw [range_evaluationCoordinate_eq_coordinateLawSet]

/-- The coordinate-law constraint cuts out the entire prevision carrier when
pulled back along the evaluation-coordinate map. -/
theorem preimage_coordinateLawSet_evaluationCoordinate :
    ((evaluationCoordinate :
      BoundedMeasurablePrecisePrevision Ω →
        BoundedMeasurableGamble Ω → ℝ) ⁻¹'
      coordinateLawSet (Ω := Ω)) =
      (Set.univ : Set (BoundedMeasurablePrecisePrevision Ω)) := by
  ext P
  simp [evaluationCoordinate_mem_coordinateLawSet P]

/-- The bounded-measurable precise-prevision carrier is compact in the
evaluation topology.

This transports compactness from the product-coordinate law set back to the
actual prevision structure.  The proof uses the evaluation topology as an
induced topology, so no discreteness or finite-dimensional shortcut is hidden in
the carrier. -/
theorem evaluationTopology_univCompact :
    @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      evaluationTopology Set.univ := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  have hpreCompact :
      IsCompact (((evaluationCoordinate :
        BoundedMeasurablePrecisePrevision Ω →
          BoundedMeasurableGamble Ω → ℝ) ⁻¹'
        coordinateLawSet (Ω := Ω)) :
        Set (BoundedMeasurablePrecisePrevision Ω)) :=
    (evaluationCoordinate_isInducing (Ω := Ω)).isCompact_preimage'
      (coordinateLawSet_isCompact (Ω := Ω))
      (coordinateLawSet_subset_range_evaluationCoordinate (Ω := Ω))
  simpa [preimage_coordinateLawSet_evaluationCoordinate (Ω := Ω)] using
    hpreCompact

/-- The evaluation topology makes bounded-measurable precise previsions a
compact space. -/
theorem evaluationCompactSpace :
    @CompactSpace (BoundedMeasurablePrecisePrevision Ω)
      evaluationTopology := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    evaluationTopology
  exact ⟨by simpa using evaluationTopology_univCompact (Ω := Ω)⟩

/-- Probability-measure bounded-observable previsions commute with measurable
pushforward: integrating an observable after pushforward is the same as
integrating its pullback before pushforward. -/
theorem ofProbabilityMeasure_map_apply
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Γ) (hf : Measurable f)
    (X : BoundedMeasurableGamble Γ) :
    @ofProbabilityMeasure Γ _
        (Measure.map f μ) (Measure.isProbabilityMeasure_map hf.aemeasurable) X =
      ofProbabilityMeasure μ (BoundedMeasurableGamble.pullback f hf X) := by
  simpa [ofProbabilityMeasure, BoundedMeasurableGamble.pullback] using
    (integral_map (μ := μ) hf.aemeasurable
      X.measurable_toFun.aestronglyMeasurable)

end BoundedMeasurablePrecisePrevision

/-! ## Bounded-measurable credal envelopes -/

/-- A credal set of precise previsions on bounded measurable observables.

This is the sigma-additive refinement of `CredalPrevisionSet`: it keeps the
observable domain measurable and bounded, so probability-measure completions can
inhabit it directly. -/
abbrev BoundedMeasurableCredalSet
    (Ω : Type*) [MeasurableSpace Ω] :=
  Set (BoundedMeasurablePrecisePrevision Ω)

namespace BoundedMeasurableCredalSet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Credal convexity for bounded-measurable precise prevision sets. -/
def IsConvex (C : BoundedMeasurableCredalSet Ω) : Prop :=
  ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P Q : BoundedMeasurablePrecisePrevision Ω),
    P ∈ C → Q ∈ C →
      BoundedMeasurablePrecisePrevision.mix t P Q ht0 ht1 ∈ C

theorem isConvex_singleton (P : BoundedMeasurablePrecisePrevision Ω) :
    IsConvex ({P} : BoundedMeasurableCredalSet Ω) := by
  intro t ht0 ht1 Q R hQ hR
  simp only [Set.mem_singleton_iff] at hQ hR ⊢
  subst Q
  subst R
  ext X
  simp [BoundedMeasurablePrecisePrevision.mix]
  ring

theorem isConvex_univ :
    IsConvex (Set.univ : BoundedMeasurableCredalSet Ω) := by
  intro t ht0 ht1 P Q hP hQ
  exact Set.mem_univ _

theorem IsConvex.inter {C D : BoundedMeasurableCredalSet Ω}
    (hC : IsConvex C) (hD : IsConvex D) :
    IsConvex (C ∩ D) := by
  intro t ht0 ht1 P Q hP hQ
  exact ⟨hC t ht0 ht1 P Q hP.1 hQ.1,
    hD t ht0 ht1 P Q hP.2 hQ.2⟩

end BoundedMeasurableCredalSet

/-- Evaluation-topology closure of a bounded-measurable credal set.

This is the honest compactification operation for sigma-additive credal sets:
it does not assert that a generated credal set is already closed, only that the
closed credal object generated by it lives inside the compact
bounded-observable prevision carrier. -/
noncomputable def boundedMeasurableCredalSetEvaluationClosure
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) :
    BoundedMeasurableCredalSet Ω :=
  @closure (BoundedMeasurablePrecisePrevision Ω)
    (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)) C

theorem boundedMeasurableCredalSet_subset_evaluationClosure
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) :
    C ⊆ boundedMeasurableCredalSetEvaluationClosure C := by
  intro P hP
  change P ∈ @closure (BoundedMeasurablePrecisePrevision Ω)
    (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)) C
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  exact subset_closure hP

theorem boundedMeasurableCredalSetEvaluationClosure_isClosed
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
      (boundedMeasurableCredalSetEvaluationClosure C) := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  exact isClosed_closure

theorem boundedMeasurableCredalSetEvaluationClosure_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) :
    @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
      (boundedMeasurableCredalSetEvaluationClosure C) := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  exact
    (BoundedMeasurablePrecisePrevision.evaluationTopology_univCompact
        (Ω := Ω)).of_isClosed_subset
      (boundedMeasurableCredalSetEvaluationClosure_isClosed C)
      (by intro P _hP; exact Set.mem_univ P)

theorem boundedMeasurableCredalSetEvaluationClosure_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    (boundedMeasurableCredalSetEvaluationClosure C).Nonempty := by
  rcases hC with ⟨P, hP⟩
  exact ⟨P, boundedMeasurableCredalSet_subset_evaluationClosure C hP⟩

/-- Evaluation-topology closure preserves bounded-measurable credal convexity. -/
theorem boundedMeasurableCredalSetEvaluationClosure_isConvex
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (hC : BoundedMeasurableCredalSet.IsConvex C) :
    BoundedMeasurableCredalSet.IsConvex
      (boundedMeasurableCredalSetEvaluationClosure C) := by
  intro t ht0 ht1 P Q hP hQ
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  change BoundedMeasurablePrecisePrevision.mix t P Q ht0 ht1 ∈
    @closure (BoundedMeasurablePrecisePrevision Ω) _ C
  exact
    map_mem_closure₂
      (f := fun P Q =>
        BoundedMeasurablePrecisePrevision.mix t P Q ht0 ht1)
      (s := C) (t := C) (u := C)
      (BoundedMeasurablePrecisePrevision.mix_continuous
        (Ω := Ω) t ht0 ht1)
      hP hQ
      (fun P hP Q hQ => hC t ht0 ht1 P Q hP hQ)

/-- Lower envelope over bounded measurable precise previsions. -/
noncomputable def boundedMeasurableLowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : ℝ :=
  sInf ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C)

/-- Upper envelope over bounded measurable precise previsions. -/
noncomputable def boundedMeasurableUpperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : ℝ :=
  sSup ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C)

/-- Width of the bounded-measurable credal envelope. -/
noncomputable def boundedMeasurableEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : ℝ :=
  boundedMeasurableUpperEnvelope C X -
    boundedMeasurableLowerEnvelope C X

/-- Width-complement display coordinate for bounded-measurable envelopes. -/
noncomputable def boundedMeasurableEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : ℝ :=
  1 - boundedMeasurableEnvelopeWidth C X

/-- Midpoint display coordinate for bounded-measurable envelopes. -/
noncomputable def boundedMeasurableEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : ℝ :=
  (boundedMeasurableLowerEnvelope C X +
    boundedMeasurableUpperEnvelope C X) / 2

/-- A full unit interval forces bounded-measurable midpoint display strength
to one half. -/
theorem boundedMeasurableEnvelopeMidpoint_eq_half_of_lower_eq_zero_upper_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hL : boundedMeasurableLowerEnvelope C X = 0)
    (hU : boundedMeasurableUpperEnvelope C X = 1) :
    boundedMeasurableEnvelopeMidpoint C X = (1 / 2 : ℝ) := by
  unfold boundedMeasurableEnvelopeMidpoint
  rw [hL, hU]
  ring

/-- A full bounded-measurable unit interval has maximal credal width. -/
theorem boundedMeasurableEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hL : boundedMeasurableLowerEnvelope C X = 0)
    (hU : boundedMeasurableUpperEnvelope C X = 1) :
    boundedMeasurableEnvelopeWidth C X = 1 := by
  unfold boundedMeasurableEnvelopeWidth
  rw [hL, hU]
  ring

/-- A full bounded-measurable unit interval forces width-complement confidence
to zero. -/
theorem boundedMeasurableEnvelopeWidthComplement_eq_zero_of_lower_eq_zero_upper_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hL : boundedMeasurableLowerEnvelope C X = 0)
    (hU : boundedMeasurableUpperEnvelope C X = 1) :
    boundedMeasurableEnvelopeWidthComplement C X = 0 := by
  unfold boundedMeasurableEnvelopeWidthComplement
  rw [boundedMeasurableEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one
    C X hL hU]
  ring

/-- If `Plo` and `Phi` attain the lower and upper endpoint of an observable,
then the credal width is their expectation gap. -/
theorem boundedMeasurableEnvelopeWidth_eq_endpointGap
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (Plo Phi : BoundedMeasurablePrecisePrevision Ω)
    (hlo : Plo X = boundedMeasurableLowerEnvelope C X)
    (hhi : Phi X = boundedMeasurableUpperEnvelope C X) :
    boundedMeasurableEnvelopeWidth C X = Phi X - Plo X := by
  unfold boundedMeasurableEnvelopeWidth
  rw [← hlo, ← hhi]

/-- Endpoint-attainer form of the width-complement confidence coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_eq_one_sub_endpointGap
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (Plo Phi : BoundedMeasurablePrecisePrevision Ω)
    (hlo : Plo X = boundedMeasurableLowerEnvelope C X)
    (hhi : Phi X = boundedMeasurableUpperEnvelope C X) :
    boundedMeasurableEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) := by
  unfold boundedMeasurableEnvelopeWidthComplement
  rw [boundedMeasurableEnvelopeWidth_eq_endpointGap C X Plo Phi hlo hhi]

/-- Endpoint-attainer form of the midpoint strength coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_eq_endpointMean
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (Plo Phi : BoundedMeasurablePrecisePrevision Ω)
    (hlo : Plo X = boundedMeasurableLowerEnvelope C X)
    (hhi : Phi X = boundedMeasurableUpperEnvelope C X) :
    boundedMeasurableEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  unfold boundedMeasurableEnvelopeMidpoint
  rw [← hlo, ← hhi]

theorem boundedMeasurableLowerEnvelope_le_of_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hBdd : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C) :
    boundedMeasurableLowerEnvelope C X ≤ P X := by
  exact csInf_le hBdd ⟨P, hP, rfl⟩

theorem le_boundedMeasurableLowerEnvelope_of_forall_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) {a : ℝ}
    (ha : ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C → a ≤ P X) :
    a ≤ boundedMeasurableLowerEnvelope C X := by
  unfold boundedMeasurableLowerEnvelope
  refine le_csInf ?_ ?_
  · rcases hC with ⟨P, hP⟩
    exact ⟨P X, ⟨P, hP, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact ha P hP

theorem boundedMeasurableUpperEnvelope_le_of_forall_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) {a : ℝ}
    (ha : ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C → P X ≤ a) :
    boundedMeasurableUpperEnvelope C X ≤ a := by
  unfold boundedMeasurableUpperEnvelope
  refine csSup_le ?_ ?_
  · rcases hC with ⟨P, hP⟩
    exact ⟨P X, ⟨P, hP, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact ha P hP

theorem le_boundedMeasurableUpperEnvelope_of_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hBdd : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C) :
    P X ≤ boundedMeasurableUpperEnvelope C X := by
  exact le_csSup hBdd ⟨P, hP, rfl⟩

theorem boundedMeasurableCredalRange_bddBelow
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) :
    BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C) := by
  rcases X.exists_lower_bound with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.lower_bound X c hc

theorem boundedMeasurableCredalRange_bddAbove
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) :
    BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C) := by
  rcases X.exists_upper_bound with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.upper_bound X c hc

/-- Compact bounded-measurable credal carriers attain their lower envelope on
each observable.  This is the weak*/evaluation-topology compactness theorem
that turns an infimum into an actual precise completion. -/
theorem boundedMeasurableLowerEnvelope_exists_mem_eq_of_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (hCompact : @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ C ∧ P X = boundedMeasurableLowerEnvelope C X := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  rcases hCompact.exists_sInf_image_eq hC
      ((BoundedMeasurablePrecisePrevision.eval_continuous X).continuousOn) with
    ⟨P, hP, hEq⟩
  exact ⟨P, hP, hEq.symm⟩

/-- Compact bounded-measurable credal carriers attain their upper envelope on
each observable. -/
theorem boundedMeasurableUpperEnvelope_exists_mem_eq_of_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (hCompact : @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ C ∧ P X = boundedMeasurableUpperEnvelope C X := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  rcases hCompact.exists_sSup_image_eq hC
      ((BoundedMeasurablePrecisePrevision.eval_continuous X).continuousOn) with
    ⟨P, hP, hEq⟩
  exact ⟨P, hP, hEq.symm⟩

/-- Passing to the evaluation-topology closure does not change the lower
envelope of any bounded observable.  This is the semantic conservation theorem
for compactifying a generated bounded-measurable credal set: compact closure may
add limit completions, but continuous evaluation sees the same infimum. -/
theorem boundedMeasurableLowerEnvelope_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelope
        (boundedMeasurableCredalSetEvaluationClosure C) X =
      boundedMeasurableLowerEnvelope C X := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  apply le_antisymm
  · refine le_boundedMeasurableLowerEnvelope_of_forall_le C hC X ?_
    intro P hP
    exact boundedMeasurableLowerEnvelope_le_of_mem
      (boundedMeasurableCredalSetEvaluationClosure C) X
      (boundedMeasurableCredalRange_bddBelow
        (boundedMeasurableCredalSetEvaluationClosure C) X)
      (boundedMeasurableCredalSet_subset_evaluationClosure C hP)
  · have hClosed :
        IsClosed
          {P : BoundedMeasurablePrecisePrevision Ω |
            boundedMeasurableLowerEnvelope C X ≤ P X} :=
      BoundedMeasurablePrecisePrevision.isClosed_le_eval X
        (boundedMeasurableLowerEnvelope C X)
    have hRawSubset :
        C ⊆
          {P : BoundedMeasurablePrecisePrevision Ω |
            boundedMeasurableLowerEnvelope C X ≤ P X} := by
      intro P hP
      exact boundedMeasurableLowerEnvelope_le_of_mem C X
        (boundedMeasurableCredalRange_bddBelow C X) hP
    have hClosureSubset :
        boundedMeasurableCredalSetEvaluationClosure C ⊆
          {P : BoundedMeasurablePrecisePrevision Ω |
            boundedMeasurableLowerEnvelope C X ≤ P X} := by
      change closure C ⊆
        {P : BoundedMeasurablePrecisePrevision Ω |
          boundedMeasurableLowerEnvelope C X ≤ P X}
      exact (hClosed.closure_subset_iff).2 hRawSubset
    refine le_boundedMeasurableLowerEnvelope_of_forall_le
      (boundedMeasurableCredalSetEvaluationClosure C)
      (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC) X ?_
    intro P hP
    exact hClosureSubset hP

/-- Evaluation-closure compactification supplies an actual precise completion
that attains the original lower envelope.  The completion may be a limit point
of the original carrier; compactification is what makes attainment available. -/
theorem boundedMeasurableLowerEnvelope_exists_mem_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
        P X = boundedMeasurableLowerEnvelope C X := by
  rcases boundedMeasurableLowerEnvelope_exists_mem_eq_of_isCompact
      (boundedMeasurableCredalSetEvaluationClosure C)
      (boundedMeasurableCredalSetEvaluationClosure_isCompact C)
      (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC) X with
    ⟨P, hP, hEq⟩
  refine ⟨P, hP, ?_⟩
  rwa [boundedMeasurableLowerEnvelope_evaluationClosure_eq C hC X] at hEq

/-- Passing to the evaluation-topology closure does not change the upper
envelope of any bounded observable. -/
theorem boundedMeasurableUpperEnvelope_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelope
        (boundedMeasurableCredalSetEvaluationClosure C) X =
      boundedMeasurableUpperEnvelope C X := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  apply le_antisymm
  · have hClosed :
        IsClosed
          {P : BoundedMeasurablePrecisePrevision Ω |
            P X ≤ boundedMeasurableUpperEnvelope C X} :=
      BoundedMeasurablePrecisePrevision.isClosed_eval_le X
        (boundedMeasurableUpperEnvelope C X)
    have hRawSubset :
        C ⊆
          {P : BoundedMeasurablePrecisePrevision Ω |
            P X ≤ boundedMeasurableUpperEnvelope C X} := by
      intro P hP
      exact le_boundedMeasurableUpperEnvelope_of_mem C X
        (boundedMeasurableCredalRange_bddAbove C X) hP
    have hClosureSubset :
        boundedMeasurableCredalSetEvaluationClosure C ⊆
          {P : BoundedMeasurablePrecisePrevision Ω |
            P X ≤ boundedMeasurableUpperEnvelope C X} := by
      change closure C ⊆
        {P : BoundedMeasurablePrecisePrevision Ω |
          P X ≤ boundedMeasurableUpperEnvelope C X}
      exact (hClosed.closure_subset_iff).2 hRawSubset
    refine boundedMeasurableUpperEnvelope_le_of_forall_le
      (boundedMeasurableCredalSetEvaluationClosure C)
      (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC) X ?_
    intro P hP
    exact hClosureSubset hP
  · refine boundedMeasurableUpperEnvelope_le_of_forall_le C hC X ?_
    intro P hP
    exact le_boundedMeasurableUpperEnvelope_of_mem
      (boundedMeasurableCredalSetEvaluationClosure C) X
      (boundedMeasurableCredalRange_bddAbove
        (boundedMeasurableCredalSetEvaluationClosure C) X)
      (boundedMeasurableCredalSet_subset_evaluationClosure C hP)

/-- Evaluation-closure compactification supplies an actual precise completion
that attains the original upper envelope. -/
theorem boundedMeasurableUpperEnvelope_exists_mem_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
        P X = boundedMeasurableUpperEnvelope C X := by
  rcases boundedMeasurableUpperEnvelope_exists_mem_eq_of_isCompact
      (boundedMeasurableCredalSetEvaluationClosure C)
      (boundedMeasurableCredalSetEvaluationClosure_isCompact C)
      (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC) X with
    ⟨P, hP, hEq⟩
  refine ⟨P, hP, ?_⟩
  rwa [boundedMeasurableUpperEnvelope_evaluationClosure_eq C hC X] at hEq

/-- Compactifying by evaluation closure preserves bounded-observable envelope
widths. -/
theorem boundedMeasurableEnvelopeWidth_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidth
        (boundedMeasurableCredalSetEvaluationClosure C) X =
      boundedMeasurableEnvelopeWidth C X := by
  unfold boundedMeasurableEnvelopeWidth
  rw [boundedMeasurableLowerEnvelope_evaluationClosure_eq C hC X,
    boundedMeasurableUpperEnvelope_evaluationClosure_eq C hC X]

/-- Compactifying by evaluation closure preserves the width-complement
confidence coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidthComplement
        (boundedMeasurableCredalSetEvaluationClosure C) X =
      boundedMeasurableEnvelopeWidthComplement C X := by
  unfold boundedMeasurableEnvelopeWidthComplement
  rw [boundedMeasurableEnvelopeWidth_evaluationClosure_eq C hC X]

/-- Compactifying by evaluation closure preserves the midpoint strength
coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeMidpoint
        (boundedMeasurableCredalSetEvaluationClosure C) X =
      boundedMeasurableEnvelopeMidpoint C X := by
  unfold boundedMeasurableEnvelopeMidpoint
  rw [boundedMeasurableLowerEnvelope_evaluationClosure_eq C hC X,
    boundedMeasurableUpperEnvelope_evaluationClosure_eq C hC X]

/-- A bounded-measurable credal set determines an observable when all
admissible completions assign the same expectation to it. -/
def boundedMeasurableCredalSetDetermines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : Prop :=
  ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
    ∀ Q : BoundedMeasurablePrecisePrevision Ω, Q ∈ C → P X = Q X

/-- A bounded-measurable credal set has strict width on an observable when two
admissible completions strictly disagree on its expectation. -/
def boundedMeasurableCredalSetHasStrictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) : Prop :=
  ∃ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C ∧
    ∃ Q : BoundedMeasurablePrecisePrevision Ω, Q ∈ C ∧ P X < Q X

/-- If a nonempty bounded-measurable credal set determines an observable, then
its evaluation-topology closure determines that observable too.  The proof uses
closedness of the evaluation-equality halfspace: all raw completions lie in the
closed set of completions with the same value, so all closure completions do as
well. -/
theorem boundedMeasurableCredalSetDetermines_evaluationClosure_of_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hDet : boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableCredalSetDetermines
      (boundedMeasurableCredalSetEvaluationClosure C) X := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  rcases hC with ⟨R, hR⟩
  have hClosed :
      IsClosed {P : BoundedMeasurablePrecisePrevision Ω | P X = R X} :=
    BoundedMeasurablePrecisePrevision.isClosed_eval_eq X (R X)
  have hRawSubset :
      C ⊆ {P : BoundedMeasurablePrecisePrevision Ω | P X = R X} := by
    intro P hP
    exact hDet P hP R hR
  have hClosureSubset :
      boundedMeasurableCredalSetEvaluationClosure C ⊆
        {P : BoundedMeasurablePrecisePrevision Ω | P X = R X} := by
    change closure C ⊆
      {P : BoundedMeasurablePrecisePrevision Ω | P X = R X}
    exact (hClosed.closure_subset_iff).2 hRawSubset
  intro P hP Q hQ
  exact (hClosureSubset hP).trans (hClosureSubset hQ).symm

/-- Determination by the evaluation-topology closure reflects back to the raw
bounded-measurable credal set, since every raw completion is a closure
completion. -/
theorem boundedMeasurableCredalSetDetermines_of_evaluationClosure_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hDet : boundedMeasurableCredalSetDetermines
      (boundedMeasurableCredalSetEvaluationClosure C) X) :
    boundedMeasurableCredalSetDetermines C X := by
  intro P hP Q hQ
  exact hDet P (boundedMeasurableCredalSet_subset_evaluationClosure C hP)
    Q (boundedMeasurableCredalSet_subset_evaluationClosure C hQ)

/-- For a nonempty bounded-measurable credal set, determination of an observable
is invariant under passage to the evaluation-topology closure.  This is the
compact-carrier conservativity theorem for the "width zero" side of the PLN
compression. -/
theorem boundedMeasurableCredalSetDetermines_evaluationClosure_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableCredalSetDetermines
        (boundedMeasurableCredalSetEvaluationClosure C) X ↔
      boundedMeasurableCredalSetDetermines C X := by
  constructor
  · exact boundedMeasurableCredalSetDetermines_of_evaluationClosure_determines
      C X
  · exact boundedMeasurableCredalSetDetermines_evaluationClosure_of_determines
      C hC X

/-- Strict-width witnesses survive passage to the evaluation-topology closure,
because every raw completion belongs to its closure. -/
theorem boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    boundedMeasurableCredalSetHasStrictWidth
      (boundedMeasurableCredalSetEvaluationClosure C) X := by
  rcases hWidth with ⟨P, hP, Q, hQ, hlt⟩
  exact ⟨P, boundedMeasurableCredalSet_subset_evaluationClosure C hP,
    Q, boundedMeasurableCredalSet_subset_evaluationClosure C hQ, hlt⟩

/-- Strict width prevents determination: two admissible completions that differ
strictly cannot both be assigned the same expectation. -/
theorem boundedMeasurableCredalSet_not_determines_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    ¬ boundedMeasurableCredalSetDetermines C X := by
  rintro hDet
  rcases hWidth with ⟨P, hP, Q, hQ, hlt⟩
  exact (ne_of_lt hlt) (hDet P hP Q hQ)

/-- Failure of determination exhibits strict width.  Since expectations are
real-valued, two unequal completion values can be oriented into a strict pair. -/
theorem boundedMeasurableCredalSetHasStrictWidth_of_not_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hNotDet : ¬ boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableCredalSetHasStrictWidth C X := by
  classical
  by_contra hNoWidth
  apply hNotDet
  intro P hP Q hQ
  by_cases hlt : P X < Q X
  · exact False.elim (hNoWidth ⟨P, hP, Q, hQ, hlt⟩)
  · by_cases hgt : Q X < P X
    · exact False.elim (hNoWidth ⟨Q, hQ, P, hP, hgt⟩)
    · exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

/-- Strict width is exactly failure of determination. -/
theorem boundedMeasurableCredalSetHasStrictWidth_iff_not_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableCredalSetHasStrictWidth C X ↔
      ¬ boundedMeasurableCredalSetDetermines C X := by
  constructor
  · exact boundedMeasurableCredalSet_not_determines_of_strictWidth C X
  · exact boundedMeasurableCredalSetHasStrictWidth_of_not_determines C X

/-- Strict width in the evaluation-topology closure reflects back to the raw
bounded-measurable credal set.  Compactifying a nonempty carrier therefore does
not manufacture new PLN imprecision; any strict-width observable in the closure
already has raw completions that strictly disagree. -/
theorem boundedMeasurableCredalSetHasStrictWidth_of_evaluationClosure_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth
      (boundedMeasurableCredalSetEvaluationClosure C) X) :
    boundedMeasurableCredalSetHasStrictWidth C X := by
  refine boundedMeasurableCredalSetHasStrictWidth_of_not_determines
    C X ?_
  intro hDet
  exact boundedMeasurableCredalSet_not_determines_of_strictWidth
    (boundedMeasurableCredalSetEvaluationClosure C) X hWidth
    ((boundedMeasurableCredalSetDetermines_evaluationClosure_iff C hC X).2
      hDet)

/-- For nonempty bounded-measurable credal sets, strict width is invariant under
passage to the evaluation-topology closure. -/
theorem boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableCredalSetHasStrictWidth
        (boundedMeasurableCredalSetEvaluationClosure C) X ↔
      boundedMeasurableCredalSetHasStrictWidth C X := by
  constructor
  · exact boundedMeasurableCredalSetHasStrictWidth_of_evaluationClosure_strictWidth
      C hC X
  · exact boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_of_strictWidth
      C X

/-- A lower prevision on bounded measurable observables.

This is Walley's lower-prevision structure restricted to the σ-additive
observable carrier.  It is intentionally separate from `LowerPrevision Ω`,
whose domain is all raw gambles. -/
structure BoundedMeasurableLowerPrevision
    (Ω : Type*) [MeasurableSpace Ω] where
  toFun : BoundedMeasurableGamble Ω → ℝ
  lower_bound : ∀ (X : BoundedMeasurableGamble Ω) (c : ℝ),
    (∀ ω, c ≤ X ω) → c ≤ toFun X
  pos_homog : ∀ (r : ℝ) (X : BoundedMeasurableGamble Ω),
    0 ≤ r → toFun (r • X) = r * toFun X
  superadd : ∀ (X Y : BoundedMeasurableGamble Ω),
    toFun X + toFun Y ≤ toFun (X + Y)

namespace BoundedMeasurableLowerPrevision

variable {Ω : Type*} [MeasurableSpace Ω]

instance : CoeFun (BoundedMeasurableLowerPrevision Ω)
    (fun _ => BoundedMeasurableGamble Ω → ℝ) := ⟨toFun⟩

/-- The conjugate upper functional of a bounded-measurable lower prevision. -/
def conjugate (P : BoundedMeasurableLowerPrevision Ω) :
    BoundedMeasurableGamble Ω → ℝ :=
  fun X => -P (-X)

@[simp] theorem map_zero (P : BoundedMeasurableLowerPrevision Ω) :
    P (0 : BoundedMeasurableGamble Ω) = 0 := by
  have h := P.pos_homog 0 (0 : BoundedMeasurableGamble Ω) (le_refl 0)
  have hzero : (0 : ℝ) • (0 : BoundedMeasurableGamble Ω) =
      (0 : BoundedMeasurableGamble Ω) := by
    ext ω
    simp
  rw [hzero, zero_mul] at h
  exact h

end BoundedMeasurableLowerPrevision

/-- An upper prevision on bounded measurable observables. -/
structure BoundedMeasurableUpperPrevision
    (Ω : Type*) [MeasurableSpace Ω] where
  toFun : BoundedMeasurableGamble Ω → ℝ
  upper_bound : ∀ (X : BoundedMeasurableGamble Ω) (c : ℝ),
    (∀ ω, X ω ≤ c) → toFun X ≤ c
  pos_homog : ∀ (r : ℝ) (X : BoundedMeasurableGamble Ω),
    0 ≤ r → toFun (r • X) = r * toFun X
  subadditive : ∀ (X Y : BoundedMeasurableGamble Ω),
    toFun (X + Y) ≤ toFun X + toFun Y

namespace BoundedMeasurableUpperPrevision

variable {Ω : Type*} [MeasurableSpace Ω]

instance : CoeFun (BoundedMeasurableUpperPrevision Ω)
    (fun _ => BoundedMeasurableGamble Ω → ℝ) := ⟨toFun⟩

/-- The conjugate lower functional of a bounded-measurable upper prevision. -/
def conjugate (P : BoundedMeasurableUpperPrevision Ω) :
    BoundedMeasurableGamble Ω → ℝ :=
  fun X => -P (-X)

end BoundedMeasurableUpperPrevision

/-- Evaluation of a negated bounded observable negates the expectation-image
set of a bounded-measurable credal set. -/
theorem boundedMeasurableCredalExpectationImage_neg
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω) :
    ((fun P : BoundedMeasurablePrecisePrevision Ω => P (-X)) '' C) =
      -((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C) := by
  ext y
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [Set.mem_neg]
    refine ⟨P, hP, ?_⟩
    simp [BoundedMeasurablePrecisePrevision.map_neg]
  · intro hy
    rw [Set.mem_neg] at hy
    rcases hy with ⟨P, hP, hy⟩
    refine ⟨P, hP, ?_⟩
    simp [BoundedMeasurablePrecisePrevision.map_neg, hy]

/-- Bounded lower and upper envelopes are conjugate under observable negation. -/
theorem boundedMeasurableLowerEnvelope_neg_eq_neg_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelope C (-X) =
      -boundedMeasurableUpperEnvelope C X := by
  unfold boundedMeasurableLowerEnvelope boundedMeasurableUpperEnvelope
  rw [boundedMeasurableCredalExpectationImage_neg C X, Real.sInf_neg]

/-- Bounded upper and lower envelopes are conjugate under observable negation. -/
theorem boundedMeasurableUpperEnvelope_neg_eq_neg_lowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelope C (-X) =
      -boundedMeasurableLowerEnvelope C X := by
  unfold boundedMeasurableLowerEnvelope boundedMeasurableUpperEnvelope
  rw [boundedMeasurableCredalExpectationImage_neg C X, Real.sSup_neg]

theorem boundedMeasurableLowerEnvelope_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (c : ℝ)
    (hc : ∀ ω, c ≤ X ω) :
    c ≤ boundedMeasurableLowerEnvelope C X :=
  le_boundedMeasurableLowerEnvelope_of_forall_le C hC X fun P _hP =>
    P.lower_bound X c hc

theorem boundedMeasurableLowerEnvelope_pos_homog
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (r : ℝ) (X : BoundedMeasurableGamble Ω) (hr : 0 ≤ r) :
    boundedMeasurableLowerEnvelope C (r • X) =
      r * boundedMeasurableLowerEnvelope C X := by
  unfold boundedMeasurableLowerEnvelope
  by_cases hr0 : r = 0
  · subst hr0
    simp only [zero_mul]
    have hset :
        ((fun P : BoundedMeasurablePrecisePrevision Ω =>
          P ((0 : ℝ) • X)) '' C) = ({0} : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨P, _hP, rfl⟩
        have hzero : (0 : ℝ) • X =
            (0 : BoundedMeasurableGamble Ω) := by
          ext ω
          simp
        rw [hzero]
        exact P.map_zero
      · intro hy
        rcases hy with rfl
        rcases hC with ⟨P, hP⟩
        refine ⟨P, hP, ?_⟩
        have hzero : (0 : ℝ) • X =
            (0 : BoundedMeasurableGamble Ω) := by
          ext ω
          simp
        rw [hzero]
        exact P.map_zero
    rw [hset, csInf_singleton]
  · have hset :
        ((fun P : BoundedMeasurablePrecisePrevision Ω =>
          P (r • X)) '' C) =
          r • ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C) := by
      ext y
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact ⟨P X, ⟨P, hP, rfl⟩, by
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
      · rintro ⟨x, ⟨P, hP, hx⟩, hy⟩
        exact ⟨P, hP, by
          rw [← hy, ← hx]
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
    rw [hset, Real.sInf_smul_of_nonneg hr, smul_eq_mul]

theorem boundedMeasurableLowerEnvelope_superadditive
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddBelow
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (X Y : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelope C X +
      boundedMeasurableLowerEnvelope C Y ≤
        boundedMeasurableLowerEnvelope C (X + Y) := by
  apply le_boundedMeasurableLowerEnvelope_of_forall_le C hC
  intro P hP
  rw [P.add X Y]
  exact add_le_add
    (boundedMeasurableLowerEnvelope_le_of_mem C X (hBdd X) hP)
    (boundedMeasurableLowerEnvelope_le_of_mem C Y (hBdd Y) hP)

/-- The upper bounded-measurable envelope respects pointwise upper bounds. -/
theorem boundedMeasurableUpperEnvelope_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (c : ℝ)
    (hc : ∀ ω, X ω ≤ c) :
    boundedMeasurableUpperEnvelope C X ≤ c :=
  boundedMeasurableUpperEnvelope_le_of_forall_le C hC X fun P _hP =>
    P.upper_bound X c hc

theorem boundedMeasurableUpperEnvelope_pos_homog
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (r : ℝ) (X : BoundedMeasurableGamble Ω) (hr : 0 ≤ r) :
    boundedMeasurableUpperEnvelope C (r • X) =
      r * boundedMeasurableUpperEnvelope C X := by
  unfold boundedMeasurableUpperEnvelope
  by_cases hr0 : r = 0
  · subst hr0
    simp only [zero_mul]
    have hset :
        ((fun P : BoundedMeasurablePrecisePrevision Ω =>
          P ((0 : ℝ) • X)) '' C) = ({0} : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨P, _hP, rfl⟩
        have hzero : (0 : ℝ) • X =
            (0 : BoundedMeasurableGamble Ω) := by
          ext ω
          simp
        rw [hzero]
        exact P.map_zero
      · intro hy
        rcases hy with rfl
        rcases hC with ⟨P, hP⟩
        refine ⟨P, hP, ?_⟩
        have hzero : (0 : ℝ) • X =
            (0 : BoundedMeasurableGamble Ω) := by
          ext ω
          simp
        rw [hzero]
        exact P.map_zero
    rw [hset, csSup_singleton]
  · have hset :
        ((fun P : BoundedMeasurablePrecisePrevision Ω =>
          P (r • X)) '' C) =
          r • ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C) := by
      ext y
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact ⟨P X, ⟨P, hP, rfl⟩, by
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
      · rintro ⟨x, ⟨P, hP, hx⟩, hy⟩
        exact ⟨P, hP, by
          rw [← hy, ← hx]
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
    rw [hset, Real.sSup_smul_of_nonneg hr, smul_eq_mul]

theorem boundedMeasurableUpperEnvelope_subadditive
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddAbove
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (X Y : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelope C (X + Y) ≤
      boundedMeasurableUpperEnvelope C X +
        boundedMeasurableUpperEnvelope C Y := by
  apply boundedMeasurableUpperEnvelope_le_of_forall_le C hC
  intro P hP
  rw [P.add X Y]
  exact add_le_add
    (le_boundedMeasurableUpperEnvelope_of_mem C X (hBdd X) hP)
    (le_boundedMeasurableUpperEnvelope_of_mem C Y (hBdd Y) hP)

/-- The lower envelope of a nonempty bounded-below set of bounded-measurable
precise completions is a bounded-measurable lower prevision. -/
noncomputable def boundedMeasurableLowerEnvelopePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddBelow
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C)) :
    BoundedMeasurableLowerPrevision Ω where
  toFun := boundedMeasurableLowerEnvelope C
  lower_bound := boundedMeasurableLowerEnvelope_lower_bound C hC
  pos_homog := boundedMeasurableLowerEnvelope_pos_homog C hC
  superadd := boundedMeasurableLowerEnvelope_superadditive C hC hBdd

/-- The upper envelope of a nonempty bounded-above set of bounded-measurable
precise completions is a bounded-measurable upper prevision. -/
noncomputable def boundedMeasurableUpperEnvelopePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddAbove
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C)) :
    BoundedMeasurableUpperPrevision Ω where
  toFun := boundedMeasurableUpperEnvelope C
  upper_bound := boundedMeasurableUpperEnvelope_upper_bound C hC
  pos_homog := boundedMeasurableUpperEnvelope_pos_homog C hC
  subadditive := boundedMeasurableUpperEnvelope_subadditive C hC hBdd

@[simp] theorem boundedMeasurableLowerEnvelopePrevision_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC hBdd)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelopePrevision C hC hBdd X =
      boundedMeasurableLowerEnvelope C X :=
  rfl

@[simp] theorem boundedMeasurableUpperEnvelopePrevision_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC hBdd)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelopePrevision C hC hBdd X =
      boundedMeasurableUpperEnvelope C X :=
  rfl

/-- The conjugate upper functional of the bounded lower-envelope prevision is
exactly the bounded-measurable upper envelope. -/
theorem boundedMeasurableLowerEnvelopePrevision_conjugate_eq_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddBelow
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (X : BoundedMeasurableGamble Ω) :
    (boundedMeasurableLowerEnvelopePrevision C hC hBdd).conjugate X =
      boundedMeasurableUpperEnvelope C X := by
  dsimp [BoundedMeasurableLowerPrevision.conjugate]
  rw [boundedMeasurableLowerEnvelope_neg_eq_neg_upperEnvelope C X]
  ring

/-- The conjugate lower functional of the bounded upper-envelope prevision is
exactly the bounded-measurable lower envelope. -/
theorem boundedMeasurableUpperEnvelopePrevision_conjugate_eq_lowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddAbove
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (X : BoundedMeasurableGamble Ω) :
    (boundedMeasurableUpperEnvelopePrevision C hC hBdd).conjugate X =
      boundedMeasurableLowerEnvelope C X := by
  dsimp [BoundedMeasurableUpperPrevision.conjugate]
  rw [boundedMeasurableUpperEnvelope_neg_eq_neg_lowerEnvelope C X]
  ring

/-- The natural lower envelope of a nonempty bounded-measurable credal set.

Unlike the raw-gamble version, boundedness of the observable carrier supplies
the range-boundedness hypothesis automatically. -/
noncomputable def boundedMeasurableNaturalExtensionPrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    BoundedMeasurableLowerPrevision Ω :=
  boundedMeasurableLowerEnvelopePrevision C hC
    (boundedMeasurableCredalRange_bddBelow C)

/-- The natural upper envelope of a nonempty bounded-measurable credal set. -/
noncomputable def boundedMeasurableNaturalUpperEnvelopePrevision
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    BoundedMeasurableUpperPrevision Ω :=
  boundedMeasurableUpperEnvelopePrevision C hC
    (boundedMeasurableCredalRange_bddAbove C)

@[simp] theorem boundedMeasurableNaturalExtensionPrevision_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableNaturalExtensionPrevision C hC X =
      boundedMeasurableLowerEnvelope C X :=
  rfl

@[simp] theorem boundedMeasurableNaturalUpperEnvelopePrevision_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableNaturalUpperEnvelopePrevision C hC X =
      boundedMeasurableUpperEnvelope C X :=
  rfl

/-- Natural-extension form of the bounded-measurable full-interval midpoint
readout. -/
theorem boundedMeasurableEnvelopeMidpoint_eq_half_of_natural_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hL : boundedMeasurableNaturalExtensionPrevision C hC X = 0)
    (hU : boundedMeasurableNaturalUpperEnvelopePrevision C hC X = 1) :
    boundedMeasurableEnvelopeMidpoint C X = (1 / 2 : ℝ) := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply] at hL
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply] at hU
  exact boundedMeasurableEnvelopeMidpoint_eq_half_of_lower_eq_zero_upper_eq_one
    C X hL hU

/-- Natural-extension form of the bounded-measurable full-interval width
readout. -/
theorem boundedMeasurableEnvelopeWidth_eq_one_of_natural_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hL : boundedMeasurableNaturalExtensionPrevision C hC X = 0)
    (hU : boundedMeasurableNaturalUpperEnvelopePrevision C hC X = 1) :
    boundedMeasurableEnvelopeWidth C X = 1 := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply] at hL
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply] at hU
  exact boundedMeasurableEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one
    C X hL hU

/-- Natural-extension form of the bounded-measurable full-interval
width-complement confidence readout. -/
theorem boundedMeasurableEnvelopeWidthComplement_eq_zero_of_natural_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hL : boundedMeasurableNaturalExtensionPrevision C hC X = 0)
    (hU : boundedMeasurableNaturalUpperEnvelopePrevision C hC X = 1) :
    boundedMeasurableEnvelopeWidthComplement C X = 0 := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply] at hL
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply] at hU
  exact
    boundedMeasurableEnvelopeWidthComplement_eq_zero_of_lower_eq_zero_upper_eq_one
      C X hL hU

/-- The natural-extension lower prevision generated by the compact evaluation
closure agrees with the one generated by the original bounded-measurable credal
set on every bounded observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableNaturalExtensionPrevision
        (boundedMeasurableCredalSetEvaluationClosure C)
        (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC) X =
      boundedMeasurableNaturalExtensionPrevision C hC X := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_evaluationClosure_eq C hC X]

/-- The upper natural envelope generated by the compact evaluation closure
agrees with the one generated by the original bounded-measurable credal set on
every bounded observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (boundedMeasurableCredalSetEvaluationClosure C)
        (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC) X =
      boundedMeasurableNaturalUpperEnvelopePrevision C hC X := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_evaluationClosure_eq C hC X]

/-- The conjugate of the bounded-measurable natural extension is the natural
upper envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_conjugate_eq_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    (boundedMeasurableNaturalExtensionPrevision C hC).conjugate X =
      boundedMeasurableNaturalUpperEnvelopePrevision C hC X := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply]
  exact boundedMeasurableLowerEnvelopePrevision_conjugate_eq_upperEnvelope
    C hC (boundedMeasurableCredalRange_bddBelow C) X

/-- The conjugate of the bounded-measurable natural upper envelope is the
natural lower envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_conjugate_eq_lowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    (boundedMeasurableNaturalUpperEnvelopePrevision C hC).conjugate X =
      boundedMeasurableNaturalExtensionPrevision C hC X := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply]
  exact boundedMeasurableUpperEnvelopePrevision_conjugate_eq_lowerEnvelope
    C hC (boundedMeasurableCredalRange_bddAbove C) X

/-- For nonempty bounded-measurable credal sets, lower envelope is below upper
envelope on every bounded observable. -/
theorem boundedMeasurableLowerEnvelope_le_upperEnvelope_of_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty) :
    boundedMeasurableLowerEnvelope C X ≤
      boundedMeasurableUpperEnvelope C X := by
  rcases hC with ⟨P, hP⟩
  exact
    (boundedMeasurableLowerEnvelope_le_of_mem C X
      (boundedMeasurableCredalRange_bddBelow C X) hP).trans
      (le_boundedMeasurableUpperEnvelope_of_mem C X
        (boundedMeasurableCredalRange_bddAbove C X) hP)

/-- Lower envelopes inherit any pointwise absolute bound on the observable. -/
theorem boundedMeasurableLowerEnvelope_abs_le_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (B : ℝ)
    (hX : ∀ ω, |X ω| ≤ B) :
    |boundedMeasurableLowerEnvelope C X| ≤ B := by
  have hlo : -B ≤ boundedMeasurableLowerEnvelope C X := by
    exact boundedMeasurableLowerEnvelope_lower_bound C hC X (-B)
      fun ω => (abs_le.mp (hX ω)).1
  rcases hC with ⟨P, hP⟩
  have hPX : |P X| ≤ B := P.abs_apply_le_of_abs_le X B hX
  have hhi : boundedMeasurableLowerEnvelope C X ≤ B := by
    exact
      (boundedMeasurableLowerEnvelope_le_of_mem C X
        (boundedMeasurableCredalRange_bddBelow C X) hP).trans
        (abs_le.mp hPX).2
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Upper envelopes inherit any pointwise absolute bound on the observable. -/
theorem boundedMeasurableUpperEnvelope_abs_le_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (B : ℝ)
    (hX : ∀ ω, |X ω| ≤ B) :
    |boundedMeasurableUpperEnvelope C X| ≤ B := by
  have hhi : boundedMeasurableUpperEnvelope C X ≤ B := by
    exact boundedMeasurableUpperEnvelope_upper_bound C hC X B
      fun ω => (abs_le.mp (hX ω)).2
  rcases hC with ⟨P, hP⟩
  have hPX : |P X| ≤ B := P.abs_apply_le_of_abs_le X B hX
  have hlo : -B ≤ boundedMeasurableUpperEnvelope C X := by
    exact
      (abs_le.mp hPX).1.trans
        (le_boundedMeasurableUpperEnvelope_of_mem C X
          (boundedMeasurableCredalRange_bddAbove C X) hP)
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Envelope width is controlled by twice any pointwise absolute bound. -/
theorem boundedMeasurableEnvelopeWidth_le_two_mul_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (B : ℝ)
    (hX : ∀ ω, |X ω| ≤ B) :
    boundedMeasurableEnvelopeWidth C X ≤ 2 * B := by
  have hLower :=
    boundedMeasurableLowerEnvelope_abs_le_of_abs_le C hC X B hX
  have hUpper :=
    boundedMeasurableUpperEnvelope_abs_le_of_abs_le C hC X B hX
  unfold boundedMeasurableEnvelopeWidth
  linarith [(abs_le.mp hLower).1, (abs_le.mp hUpper).2]

/-- Every bounded observable has a finite absolute bound on its lower envelope. -/
theorem boundedMeasurableLowerEnvelope_exists_abs_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ |boundedMeasurableLowerEnvelope C X| ≤ B := by
  rcases X.exists_abs_bound with ⟨B, hB0, hB⟩
  exact ⟨B, hB0, boundedMeasurableLowerEnvelope_abs_le_of_abs_le C hC X B hB⟩

/-- Every bounded observable has a finite absolute bound on its upper envelope. -/
theorem boundedMeasurableUpperEnvelope_exists_abs_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ |boundedMeasurableUpperEnvelope C X| ≤ B := by
  rcases X.exists_abs_bound with ⟨B, hB0, hB⟩
  exact ⟨B, hB0, boundedMeasurableUpperEnvelope_abs_le_of_abs_le C hC X B hB⟩

/-- The bounded-measurable natural extension is norm-bounded by any pointwise
absolute bound on the observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_abs_apply_le_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (B : ℝ)
    (hX : ∀ ω, |X ω| ≤ B) :
    |boundedMeasurableNaturalExtensionPrevision C hC X| ≤ B := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply]
  exact boundedMeasurableLowerEnvelope_abs_le_of_abs_le C hC X B hX

/-- The bounded-measurable natural upper envelope is norm-bounded by any
pointwise absolute bound on the observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_abs_apply_le_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) (B : ℝ)
    (hX : ∀ ω, |X ω| ≤ B) :
    |boundedMeasurableNaturalUpperEnvelopePrevision C hC X| ≤ B := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply]
  exact boundedMeasurableUpperEnvelope_abs_le_of_abs_le C hC X B hX

/-- Every bounded observable has a finite absolute bound under the natural
extension. -/
theorem boundedMeasurableNaturalExtensionPrevision_exists_abs_apply_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧
      |boundedMeasurableNaturalExtensionPrevision C hC X| ≤ B := by
  rcases X.exists_abs_bound with ⟨B, hB0, hB⟩
  exact ⟨B, hB0,
    boundedMeasurableNaturalExtensionPrevision_abs_apply_le_of_abs_le
      C hC X B hB⟩

/-- Every bounded observable has a finite absolute bound under the natural
upper envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_exists_abs_apply_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ B : ℝ, 0 ≤ B ∧
      |boundedMeasurableNaturalUpperEnvelopePrevision C hC X| ≤ B := by
  rcases X.exists_abs_bound with ⟨B, hB0, hB⟩
  exact ⟨B, hB0,
    boundedMeasurableNaturalUpperEnvelopePrevision_abs_apply_le_of_abs_le
      C hC X B hB⟩

theorem boundedMeasurableEnvelopeWidth_nonneg_of_nonempty
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty) :
    0 ≤ boundedMeasurableEnvelopeWidth C X := by
  unfold boundedMeasurableEnvelopeWidth
  exact sub_nonneg.mpr
    (boundedMeasurableLowerEnvelope_le_upperEnvelope_of_nonempty C X hC)

theorem boundedMeasurableLowerEnvelope_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableLowerEnvelope C X ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact boundedMeasurableLowerEnvelope_lower_bound C hC X 0
      fun ω => (hX ω).1
  · rcases hC with ⟨P, hP⟩
    exact
      (boundedMeasurableLowerEnvelope_le_of_mem C X
        (boundedMeasurableCredalRange_bddBelow C X) hP).trans
        (P.upper_bound X 1 fun ω => (hX ω).2)

theorem boundedMeasurableUpperEnvelope_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableUpperEnvelope C X ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rcases hC with ⟨P, hP⟩
    exact
      (P.lower_bound X 0 fun ω => (hX ω).1).trans
        (le_boundedMeasurableUpperEnvelope_of_mem C X
          (boundedMeasurableCredalRange_bddAbove C X) hP)
  · exact boundedMeasurableUpperEnvelope_upper_bound C hC X 1
      fun ω => (hX ω).2

theorem boundedMeasurableEnvelopeWidth_le_one_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidth C X ≤ 1 := by
  have hLower := boundedMeasurableLowerEnvelope_in_unit_of_unit C X hC hX
  have hUpper := boundedMeasurableUpperEnvelope_in_unit_of_unit C X hC hX
  unfold boundedMeasurableEnvelopeWidth
  linarith [hLower.1, hUpper.2]

theorem boundedMeasurableEnvelopeWidth_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidth C X ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨boundedMeasurableEnvelopeWidth_nonneg_of_nonempty C X hC,
    boundedMeasurableEnvelopeWidth_le_one_of_unit C X hC hX⟩

theorem boundedMeasurableEnvelopeWidthComplement_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidthComplement C X ∈ Set.Icc (0 : ℝ) 1 := by
  have hWidth :=
    boundedMeasurableEnvelopeWidth_in_unit_of_unit C X hC hX
  unfold boundedMeasurableEnvelopeWidthComplement
  exact ⟨by linarith [hWidth.2], by linarith [hWidth.1]⟩

theorem boundedMeasurableEnvelopeMidpoint_in_unit_of_unit
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeMidpoint C X ∈ Set.Icc (0 : ℝ) 1 := by
  have hLower := boundedMeasurableLowerEnvelope_in_unit_of_unit C X hC hX
  have hUpper := boundedMeasurableUpperEnvelope_in_unit_of_unit C X hC hX
  unfold boundedMeasurableEnvelopeMidpoint
  constructor <;> nlinarith [hLower.1, hLower.2, hUpper.1, hUpper.2]

/-- The bounded-measurable lower-envelope prevision is below every precise
completion in the generating credal set. -/
theorem boundedMeasurableLowerEnvelopePrevision_le_completion
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddBelow
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelopePrevision C hC hBdd X ≤ P X :=
  boundedMeasurableLowerEnvelope_le_of_mem C X (hBdd X) hP

/-- The bounded-measurable lower-envelope prevision is the greatest bounded
lower prevision dominated by every precise completion in the generating credal
set. -/
theorem boundedMeasurableLowerEnvelopePrevision_greatest_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddBelow
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (L : BoundedMeasurableLowerPrevision Ω)
    (hL : ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
      ∀ X : BoundedMeasurableGamble Ω, L X ≤ P X)
    (X : BoundedMeasurableGamble Ω) :
  L X ≤ boundedMeasurableLowerEnvelopePrevision C hC hBdd X :=
  le_boundedMeasurableLowerEnvelope_of_forall_le C hC X
    fun P hP => hL P hP X

/-- The bounded-measurable upper-envelope prevision is above every precise
completion in the generating credal set. -/
theorem boundedMeasurableUpperEnvelopePrevision_completion_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddAbove
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (X : BoundedMeasurableGamble Ω) :
    P X ≤ boundedMeasurableUpperEnvelopePrevision C hC hBdd X :=
  le_boundedMeasurableUpperEnvelope_of_mem C X (hBdd X) hP

/-- The bounded-measurable upper-envelope prevision is the least bounded upper
prevision dominating every precise completion in the generating credal set. -/
theorem boundedMeasurableUpperEnvelopePrevision_least_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : BoundedMeasurableGamble Ω,
      BddAbove
        ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (U : BoundedMeasurableUpperPrevision Ω)
    (hU : ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
      ∀ X : BoundedMeasurableGamble Ω, P X ≤ U X)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelopePrevision C hC hBdd X ≤ U X :=
  boundedMeasurableUpperEnvelope_le_of_forall_le C hC X
    fun P hP => hU P hP X

/-- The bounded-measurable natural extension is below every precise completion
in the generating credal set. -/
theorem boundedMeasurableNaturalExtensionPrevision_le_completion
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableNaturalExtensionPrevision C hC X ≤ P X :=
  boundedMeasurableLowerEnvelopePrevision_le_completion C hC
    (boundedMeasurableCredalRange_bddBelow C) hP X

/-- The bounded-measurable natural extension is the greatest bounded lower
prevision dominated by every precise completion in the generating credal set. -/
theorem boundedMeasurableNaturalExtensionPrevision_greatest_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (L : BoundedMeasurableLowerPrevision Ω)
    (hL : ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
      ∀ X : BoundedMeasurableGamble Ω, L X ≤ P X)
    (X : BoundedMeasurableGamble Ω) :
    L X ≤ boundedMeasurableNaturalExtensionPrevision C hC X :=
  boundedMeasurableLowerEnvelopePrevision_greatest_lower_bound C hC
    (boundedMeasurableCredalRange_bddBelow C) L hL X

/-- Every precise completion in the generating credal set lies below the
bounded-measurable natural upper envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (X : BoundedMeasurableGamble Ω) :
    P X ≤ boundedMeasurableNaturalUpperEnvelopePrevision C hC X :=
  boundedMeasurableUpperEnvelopePrevision_completion_le C hC
    (boundedMeasurableCredalRange_bddAbove C) hP X

/-- The bounded-measurable natural upper envelope is the least bounded upper
prevision dominating every precise completion in the generating credal set. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_least_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (U : BoundedMeasurableUpperPrevision Ω)
    (hU : ∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
      ∀ X : BoundedMeasurableGamble Ω, P X ≤ U X)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableNaturalUpperEnvelopePrevision C hC X ≤ U X :=
  boundedMeasurableUpperEnvelopePrevision_least_upper_bound C hC
    (boundedMeasurableCredalRange_bddAbove C) U hU X

/-- Precise bounded-measurable completions that dominate a bounded lower
prevision.  This is the bounded-observable analogue of Walley's dominating
linear previsions. -/
def boundedMeasurableDominatingPreciseCompletions
    {Ω : Type*} [MeasurableSpace Ω]
    (L : BoundedMeasurableLowerPrevision Ω) :
    BoundedMeasurableCredalSet Ω :=
  {P | ∀ X : BoundedMeasurableGamble Ω, L X ≤ P X}

/-- Exact lower-envelope representation over bounded-measurable dominating
precise completions. -/
def boundedMeasurableHasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (L : BoundedMeasurableLowerPrevision Ω) : Prop :=
  (boundedMeasurableDominatingPreciseCompletions L).Nonempty ∧
    ∀ X : BoundedMeasurableGamble Ω,
      boundedMeasurableLowerEnvelope
          (boundedMeasurableDominatingPreciseCompletions L) X =
        L X

/-- Dominating bounded-measurable precise completions form a convex credal set. -/
theorem boundedMeasurableDominatingPreciseCompletions_isConvex
    {Ω : Type*} [MeasurableSpace Ω]
    (L : BoundedMeasurableLowerPrevision Ω) :
    BoundedMeasurableCredalSet.IsConvex
      (boundedMeasurableDominatingPreciseCompletions L) := by
  intro t ht0 ht1 P Q hP hQ X
  dsimp [boundedMeasurableDominatingPreciseCompletions,
    BoundedMeasurablePrecisePrevision.mix]
  have h1t : 0 ≤ 1 - t := by linarith
  have hPX : L X ≤ P X := hP X
  have hQX : L X ≤ Q X := hQ X
  nlinarith

/-- Dominating bounded-measurable precise completions are closed in the
evaluation topology.  Each domination obligation is a closed lower halfspace
for one observable, and the completion set is their intersection. -/
theorem boundedMeasurableDominatingPreciseCompletions_isClosed
    {Ω : Type*} [MeasurableSpace Ω]
    (L : BoundedMeasurableLowerPrevision Ω) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
      (boundedMeasurableDominatingPreciseCompletions L) := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  change IsClosed
    {P : BoundedMeasurablePrecisePrevision Ω |
      ∀ X : BoundedMeasurableGamble Ω, L X ≤ P X}
  rw [show
      {P : BoundedMeasurablePrecisePrevision Ω |
        ∀ X : BoundedMeasurableGamble Ω, L X ≤ P X} =
        ⋂ X : BoundedMeasurableGamble Ω,
          {P : BoundedMeasurablePrecisePrevision Ω | L X ≤ P X} by
    ext P
    simp]
  exact isClosed_iInter fun X =>
    BoundedMeasurablePrecisePrevision.isClosed_le_eval X (L X)

/-- Dominating bounded-measurable precise completions form a compact carrier in
the evaluation topology.  The set may be empty for an arbitrary lower
prevision, but compactness is still the right closed-subset-of-compact-carrier
fact consumed by natural-extension and DLR/de Finetti endpoint theorems. -/
theorem boundedMeasurableDominatingPreciseCompletions_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (L : BoundedMeasurableLowerPrevision Ω) :
    @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
      (boundedMeasurableDominatingPreciseCompletions L) := by
  letI : TopologicalSpace (BoundedMeasurablePrecisePrevision Ω) :=
    BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)
  exact
    (BoundedMeasurablePrecisePrevision.evaluationTopology_univCompact
        (Ω := Ω)).of_isClosed_subset
      (boundedMeasurableDominatingPreciseCompletions_isClosed L)
      (by intro P _hP; exact Set.mem_univ P)

/-- Any exact lower-envelope representation by dominating bounded-measurable
precise completions has a touching completion for each observable. -/
theorem boundedMeasurableHasExactDominatingPreciseEnvelope_exists_touching
    {Ω : Type*} [MeasurableSpace Ω]
    {L : BoundedMeasurableLowerPrevision Ω}
    (hExact : boundedMeasurableHasExactDominatingPreciseEnvelope L)
    (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ boundedMeasurableDominatingPreciseCompletions L ∧
        P X = L X := by
  let D : BoundedMeasurableCredalSet Ω :=
    boundedMeasurableDominatingPreciseCompletions L
  have hDCompact :
      @IsCompact (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        D := by
    exact boundedMeasurableDominatingPreciseCompletions_isCompact L
  rcases boundedMeasurableLowerEnvelope_exists_mem_eq_of_isCompact
      D hDCompact hExact.1 X with
    ⟨P, hP, hPX⟩
  refine ⟨P, hP, ?_⟩
  calc
    P X = boundedMeasurableLowerEnvelope D X := hPX
    _ = L X := hExact.2 X

/-- An exact dominating lower-envelope representation also recovers the
conjugate upper envelope over the same dominating completions. -/
theorem boundedMeasurableHasExactDominatingPreciseEnvelope_upperEnvelope_eq_conjugate
    {Ω : Type*} [MeasurableSpace Ω]
    {L : BoundedMeasurableLowerPrevision Ω}
    (hExact : boundedMeasurableHasExactDominatingPreciseEnvelope L)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelope
        (boundedMeasurableDominatingPreciseCompletions L) X =
      L.conjugate X := by
  let D : BoundedMeasurableCredalSet Ω :=
    boundedMeasurableDominatingPreciseCompletions L
  have hneg :
      boundedMeasurableLowerEnvelope D (-X) =
        -boundedMeasurableUpperEnvelope D X :=
    boundedMeasurableLowerEnvelope_neg_eq_neg_upperEnvelope D X
  have hLower : boundedMeasurableLowerEnvelope D (-X) = L (-X) :=
    hExact.2 (-X)
  dsimp [BoundedMeasurableLowerPrevision.conjugate]
  linarith

/-- Any exact dominating representation has an upper touching completion for
each observable, where "upper" is the conjugate of the lower prevision. -/
theorem boundedMeasurableHasExactDominatingPreciseEnvelope_exists_conjugate_touching
    {Ω : Type*} [MeasurableSpace Ω]
    {L : BoundedMeasurableLowerPrevision Ω}
    (hExact : boundedMeasurableHasExactDominatingPreciseEnvelope L)
    (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ boundedMeasurableDominatingPreciseCompletions L ∧
        P X = L.conjugate X := by
  let D : BoundedMeasurableCredalSet Ω :=
    boundedMeasurableDominatingPreciseCompletions L
  have hDCompact :
      @IsCompact (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        D := by
    exact boundedMeasurableDominatingPreciseCompletions_isCompact L
  rcases boundedMeasurableUpperEnvelope_exists_mem_eq_of_isCompact
      D hDCompact hExact.1 X with
    ⟨P, hP, hPX⟩
  refine ⟨P, hP, ?_⟩
  calc
    P X = boundedMeasurableUpperEnvelope D X := hPX
    _ = L.conjugate X :=
      boundedMeasurableHasExactDominatingPreciseEnvelope_upperEnvelope_eq_conjugate
        hExact X

/-- Endpoint-pair readout for an exact dominating bounded-measurable
lower-envelope representation.

The two precise completions may differ: one touches the lower envelope, the
other touches the conjugate upper envelope.  Together they compute the complete
PLN-facing interval coordinates of the dominating-completion carrier. -/
theorem boundedMeasurableHasExactDominatingPreciseEnvelope_exists_endpointPairReadout
    {Ω : Type*} [MeasurableSpace Ω]
    {L : BoundedMeasurableLowerPrevision Ω}
    (hExact : boundedMeasurableHasExactDominatingPreciseEnvelope L)
    (X : BoundedMeasurableGamble Ω) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableDominatingPreciseCompletions L ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableDominatingPreciseCompletions L ∧
        Plo X = L X ∧
        Phi X = L.conjugate X ∧
        boundedMeasurableEnvelopeWidth
            (boundedMeasurableDominatingPreciseCompletions L) X =
          Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement
            (boundedMeasurableDominatingPreciseCompletions L) X =
          1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint
            (boundedMeasurableDominatingPreciseCompletions L) X =
          (Plo X + Phi X) / 2 := by
  let D : BoundedMeasurableCredalSet Ω :=
    boundedMeasurableDominatingPreciseCompletions L
  rcases boundedMeasurableHasExactDominatingPreciseEnvelope_exists_touching
      hExact X with
    ⟨Plo, hPlo, hloL⟩
  rcases boundedMeasurableHasExactDominatingPreciseEnvelope_exists_conjugate_touching
      hExact X with
    ⟨Phi, hPhi, hhiL⟩
  have hloD : Plo X = boundedMeasurableLowerEnvelope D X := by
    calc
      Plo X = L X := hloL
      _ = boundedMeasurableLowerEnvelope D X := by
        simpa [D] using (hExact.2 X).symm
  have hhiD : Phi X = boundedMeasurableUpperEnvelope D X := by
    calc
      Phi X = L.conjugate X := hhiL
      _ = boundedMeasurableUpperEnvelope D X := by
        simpa [D] using
          (boundedMeasurableHasExactDominatingPreciseEnvelope_upperEnvelope_eq_conjugate
            hExact X).symm
  refine ⟨Plo, hPlo, Phi, hPhi, hloL, hhiL, ?_, ?_, ?_⟩
  · exact boundedMeasurableEnvelopeWidth_eq_endpointGap
      D X Plo Phi hloD hhiD
  · exact boundedMeasurableEnvelopeWidthComplement_eq_one_sub_endpointGap
      D X Plo Phi hloD hhiD
  · exact boundedMeasurableEnvelopeMidpoint_eq_endpointMean
      D X Plo Phi hloD hhiD

/-- Strict endpoint-pair readout for an exact dominating bounded-measurable
lower-envelope representation.

If the lower prevision and its conjugate upper prevision are separated on an
observable, the two dominating precise completions touching those endpoints are
strictly separated on that observable. -/
theorem boundedMeasurableHasExactDominatingPreciseEnvelope_exists_strictEndpointPairReadout
    {Ω : Type*} [MeasurableSpace Ω]
    {L : BoundedMeasurableLowerPrevision Ω}
    (hExact : boundedMeasurableHasExactDominatingPreciseEnvelope L)
    (X : BoundedMeasurableGamble Ω)
    (hStrict : L X < L.conjugate X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableDominatingPreciseCompletions L ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableDominatingPreciseCompletions L ∧
        Plo X = L X ∧
        Phi X = L.conjugate X ∧
        Plo X < Phi X ∧
        boundedMeasurableEnvelopeWidth
            (boundedMeasurableDominatingPreciseCompletions L) X =
          Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement
            (boundedMeasurableDominatingPreciseCompletions L) X =
          1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint
            (boundedMeasurableDominatingPreciseCompletions L) X =
          (Plo X + Phi X) / 2 := by
  rcases
      boundedMeasurableHasExactDominatingPreciseEnvelope_exists_endpointPairReadout
        hExact X with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hWidth, hComp, hMid⟩
  have hlt : Plo X < Phi X := by
    rw [hlo, hhi]
    exact hStrict
  exact ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidth, hComp, hMid⟩

/-- Passing the generating credal set to its compact evaluation closure does
not change the dominating precise completions of the generated natural
extension.  Thus compactification is conservative not only for envelope values,
but for the Walley completion object determined by those values. -/
theorem boundedMeasurableDominatingPreciseCompletions_naturalExtension_evaluationClosure_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (boundedMeasurableCredalSetEvaluationClosure C)
          (boundedMeasurableCredalSetEvaluationClosure_nonempty C hC)) =
      boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision C hC) := by
  ext P
  constructor
  · intro hP X
    have h := hP X
    rw [boundedMeasurableNaturalExtensionPrevision_evaluationClosure_eq
      C hC X] at h
    exact h
  · intro hP X
    rw [boundedMeasurableNaturalExtensionPrevision_evaluationClosure_eq
      C hC X]
    exact hP X

/-- A bounded-measurable lower envelope is exactly recovered as the lower
envelope of all bounded-measurable precise completions dominating it.

This is the exact-envelope half of Walley's natural-extension story on the
bounded measurable carrier.  It does not assert that arbitrary assessments have
dominating precise completions; rather, it proves that once a nonempty credal
set generates a lower envelope, passing to all dominating completions loses no
information. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelope
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC)) X =
      boundedMeasurableNaturalExtensionPrevision C hC X := by
  let L : BoundedMeasurableLowerPrevision Ω :=
    boundedMeasurableNaturalExtensionPrevision C hC
  let D : BoundedMeasurableCredalSet Ω :=
    boundedMeasurableDominatingPreciseCompletions L
  have hsubset : C ⊆ D := by
    intro P hP Y
    change L Y ≤ P Y
    dsimp [L]
    exact boundedMeasurableLowerEnvelope_le_of_mem C Y
      (boundedMeasurableCredalRange_bddBelow C Y) hP
  have hle :
      boundedMeasurableLowerEnvelope D X ≤
        boundedMeasurableLowerEnvelope C X := by
    apply le_boundedMeasurableLowerEnvelope_of_forall_le C hC X
    intro P hP
    exact boundedMeasurableLowerEnvelope_le_of_mem D X
      (boundedMeasurableCredalRange_bddBelow D X) (hsubset hP)
  have hD : D.Nonempty := by
    rcases hC with ⟨P, hP⟩
    exact ⟨P, hsubset hP⟩
  have hge :
      boundedMeasurableNaturalExtensionPrevision C hC X ≤
        boundedMeasurableLowerEnvelope D X := by
    apply le_boundedMeasurableLowerEnvelope_of_forall_le D hD X
    intro P hP
    exact hP X
  refine le_antisymm ?_ hge
  simpa [L, D] using hle

/-- The bounded-measurable natural extension generated by a nonempty credal set
has an exact dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision C hC) := by
  constructor
  · rcases hC with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    intro X
    rw [boundedMeasurableNaturalExtensionPrevision_apply]
    exact boundedMeasurableLowerEnvelope_le_of_mem C X
      (boundedMeasurableCredalRange_bddBelow C X) hP
  · intro X
    exact boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_eq
      C hC X

/-- The dominating-completion carrier of a generated bounded-measurable
natural extension is closed in the evaluation topology. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isClosed
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    @IsClosed (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
      (boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision C hC)) :=
  boundedMeasurableDominatingPreciseCompletions_isClosed
    (boundedMeasurableNaturalExtensionPrevision C hC)

/-- The dominating-completion carrier of a generated bounded-measurable
natural extension is compact in the evaluation topology. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isCompact
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
      (boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision C hC)) :=
  boundedMeasurableDominatingPreciseCompletions_isCompact
    (boundedMeasurableNaturalExtensionPrevision C hC)

/-- The dominating-completion carrier of a generated bounded-measurable
natural extension is convex. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isConvex
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty) :
    BoundedMeasurableCredalSet.IsConvex
      (boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision C hC)) :=
  boundedMeasurableDominatingPreciseCompletions_isConvex
    (boundedMeasurableNaturalExtensionPrevision C hC)

/-- The dominating precise completions of a bounded-measurable natural
extension preserve the generated upper natural envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_upperEnvelope_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelope
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC)) X =
      boundedMeasurableNaturalUpperEnvelopePrevision C hC X := by
  have hExact :
      boundedMeasurableHasExactDominatingPreciseEnvelope
        (boundedMeasurableNaturalExtensionPrevision C hC) :=
    boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      C hC
  calc
    boundedMeasurableUpperEnvelope
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC)) X =
      (boundedMeasurableNaturalExtensionPrevision C hC).conjugate X :=
        boundedMeasurableHasExactDominatingPreciseEnvelope_upperEnvelope_eq_conjugate
          hExact X
    _ = boundedMeasurableNaturalUpperEnvelopePrevision C hC X :=
        boundedMeasurableNaturalExtensionPrevision_conjugate_eq_upperEnvelope
          C hC X

/-- A bounded-measurable natural extension is touched, on each query, by an
actual dominating precise completion.

The proof uses the compactness of the full dominating-completion carrier, not
only the compact closure of the original generating credal set.  This is the
Walley-facing endpoint theorem: the lower-envelope value is not merely an
infimum over completions, but is attained by a precise completion that dominates
the generated lower prevision. -/
theorem boundedMeasurableNaturalExtensionPrevision_exists_dominatingPreciseCompletion_touching
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC) ∧
        P X = boundedMeasurableNaturalExtensionPrevision C hC X := by
  have hExact :
      boundedMeasurableHasExactDominatingPreciseEnvelope
        (boundedMeasurableNaturalExtensionPrevision C hC) :=
    boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      C hC
  exact boundedMeasurableHasExactDominatingPreciseEnvelope_exists_touching
    hExact X

/-- A bounded-measurable natural extension has, for each query, a dominating
precise completion that touches the conjugate upper envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_exists_dominatingPreciseCompletion_upper_touching
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ P : BoundedMeasurablePrecisePrevision Ω,
      P ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC) ∧
        P X = boundedMeasurableNaturalUpperEnvelopePrevision C hC X := by
  have hExact :
      boundedMeasurableHasExactDominatingPreciseEnvelope
        (boundedMeasurableNaturalExtensionPrevision C hC) :=
    boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      C hC
  rcases
      boundedMeasurableHasExactDominatingPreciseEnvelope_exists_conjugate_touching
        hExact X with
    ⟨P, hP, hPX⟩
  refine ⟨P, hP, ?_⟩
  rw [hPX]
  exact boundedMeasurableNaturalExtensionPrevision_conjugate_eq_upperEnvelope
    C hC X

/-- Replacing a generated bounded-measurable credal set by all precise
completions dominating its natural extension preserves the full interval width.
-/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_envelopeWidth_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidth
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC)) X =
      boundedMeasurableEnvelopeWidth C X := by
  unfold boundedMeasurableEnvelopeWidth
  rw [boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_eq
      C hC X,
    boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_upperEnvelope_eq
      C hC X,
    boundedMeasurableNaturalUpperEnvelopePrevision_apply]

/-- The width-complement confidence coordinate is also preserved by passing to
all precise completions dominating the generated natural extension. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_widthComplement_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidthComplement
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC)) X =
      boundedMeasurableEnvelopeWidthComplement C X := by
  unfold boundedMeasurableEnvelopeWidthComplement
  rw [boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_envelopeWidth_eq
    C hC X]

/-- The midpoint strength coordinate is preserved by passing to all precise
completions dominating the generated natural extension. -/
theorem boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_midpoint_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeMidpoint
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC)) X =
      boundedMeasurableEnvelopeMidpoint C X := by
  unfold boundedMeasurableEnvelopeMidpoint
  rw [boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_eq
      C hC X,
    boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_upperEnvelope_eq
      C hC X,
    boundedMeasurableNaturalUpperEnvelopePrevision_apply]

/-- Endpoint-pair readout for the natural extension generated by a nonempty
bounded-measurable credal set.

The endpoint completions live in the dominating-completion carrier of the
natural extension, but their values compute the original credal interval and
the resulting PLN-facing width, confidence-complement, and midpoint
coordinates. -/
theorem boundedMeasurableNaturalExtensionPrevision_exists_dominatingEndpointPairReadout
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
            (boundedMeasurableNaturalExtensionPrevision C hC) ∧
        Plo X = boundedMeasurableNaturalExtensionPrevision C hC X ∧
        Phi X = boundedMeasurableNaturalUpperEnvelopePrevision C hC X ∧
        boundedMeasurableEnvelopeWidth C X = Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement C X =
          1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint C X =
          (Plo X + Phi X) / 2 := by
  have hExact :
      boundedMeasurableHasExactDominatingPreciseEnvelope
        (boundedMeasurableNaturalExtensionPrevision C hC) :=
    boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      C hC
  rcases
      boundedMeasurableHasExactDominatingPreciseEnvelope_exists_endpointPairReadout
        hExact X with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhiConj, _hWidthD, _hCompD, _hMidD⟩
  have hhi :
      Phi X = boundedMeasurableNaturalUpperEnvelopePrevision C hC X := by
    calc
      Phi X =
          (boundedMeasurableNaturalExtensionPrevision C hC).conjugate X :=
        hhiConj
      _ = boundedMeasurableNaturalUpperEnvelopePrevision C hC X :=
        boundedMeasurableNaturalExtensionPrevision_conjugate_eq_upperEnvelope
          C hC X
  have hloC : Plo X = boundedMeasurableLowerEnvelope C X := by
    simpa [boundedMeasurableNaturalExtensionPrevision_apply] using hlo
  have hhiC : Phi X = boundedMeasurableUpperEnvelope C X := by
    simpa [boundedMeasurableNaturalUpperEnvelopePrevision_apply] using hhi
  refine ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, ?_, ?_, ?_⟩
  · exact boundedMeasurableEnvelopeWidth_eq_endpointGap C X Plo Phi hloC hhiC
  · exact boundedMeasurableEnvelopeWidthComplement_eq_one_sub_endpointGap
      C X Plo Phi hloC hhiC
  · exact boundedMeasurableEnvelopeMidpoint_eq_endpointMean
      C X Plo Phi hloC hhiC

/-- Strict endpoint-pair readout for a generated bounded-measurable natural
extension.

Strict width in the original credal set produces two dominating precise
completions of the natural extension whose query values are strictly ordered
and compute the original PLN-facing interval coordinates. -/
theorem boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C hC) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
            (boundedMeasurableNaturalExtensionPrevision C hC) ∧
        Plo X = boundedMeasurableNaturalExtensionPrevision C hC X ∧
        Phi X = boundedMeasurableNaturalUpperEnvelopePrevision C hC X ∧
        Plo X < Phi X ∧
        boundedMeasurableEnvelopeWidth C X = Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement C X =
          1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint C X =
          (Plo X + Phi X) / 2 := by
  rcases
      boundedMeasurableNaturalExtensionPrevision_exists_dominatingEndpointPairReadout
        C hC X with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hWidthEq, hComp, hMid⟩
  have hLowerUpper :
      boundedMeasurableLowerEnvelope C X <
        boundedMeasurableUpperEnvelope C X := by
    rcases hWidth with ⟨P, hP, Q, hQ, hPQ⟩
    calc
      boundedMeasurableLowerEnvelope C X ≤ P X :=
        boundedMeasurableLowerEnvelope_le_of_mem C X
          (boundedMeasurableCredalRange_bddBelow C X) hP
      _ < Q X := hPQ
      _ ≤ boundedMeasurableUpperEnvelope C X :=
        le_boundedMeasurableUpperEnvelope_of_mem C X
          (boundedMeasurableCredalRange_bddAbove C X) hQ
  have hloC : Plo X = boundedMeasurableLowerEnvelope C X := by
    simpa [boundedMeasurableNaturalExtensionPrevision_apply] using hlo
  have hhiC : Phi X = boundedMeasurableUpperEnvelope C X := by
    simpa [boundedMeasurableNaturalUpperEnvelopePrevision_apply] using hhi
  have hlt : Plo X < Phi X := by
    rw [hloC, hhiC]
    exact hLowerUpper
  exact ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hComp, hMid⟩

theorem boundedMeasurableLowerEnvelope_eq_of_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (hDet : boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableLowerEnvelope C X = P X := by
  refine le_antisymm ?_ ?_
  · exact boundedMeasurableLowerEnvelope_le_of_mem C X hBddBelow hP
  · exact le_boundedMeasurableLowerEnvelope_of_forall_le C hC X fun Q hQ =>
      le_of_eq (hDet P hP Q hQ)

theorem boundedMeasurableUpperEnvelope_eq_of_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (hDet : boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableUpperEnvelope C X = P X := by
  refine le_antisymm ?_ ?_
  · exact boundedMeasurableUpperEnvelope_le_of_forall_le C hC X fun Q hQ =>
      le_of_eq (hDet Q hQ P hP)
  · exact le_boundedMeasurableUpperEnvelope_of_mem C X hBddAbove hP

theorem boundedMeasurableEnvelopeWidth_eq_zero_of_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (hDet : boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableEnvelopeWidth C X = 0 := by
  rw [boundedMeasurableEnvelopeWidth,
    boundedMeasurableLowerEnvelope_eq_of_determines
      C X hC hBddBelow hP hDet,
    boundedMeasurableUpperEnvelope_eq_of_determines
      C X hC hBddAbove hP hDet]
  ring

theorem boundedMeasurableLowerEnvelope_eq_upperEnvelope_of_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (hDet : boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableLowerEnvelope C X =
      boundedMeasurableUpperEnvelope C X := by
  rw [boundedMeasurableLowerEnvelope_eq_of_determines
      C X hC hBddBelow hP hDet,
    boundedMeasurableUpperEnvelope_eq_of_determines
      C X hC hBddAbove hP hDet]

theorem boundedMeasurableEnvelopeWidthComplement_eq_one_of_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P : BoundedMeasurablePrecisePrevision Ω} (hP : P ∈ C)
    (hDet : boundedMeasurableCredalSetDetermines C X) :
    boundedMeasurableEnvelopeWidthComplement C X = 1 := by
  unfold boundedMeasurableEnvelopeWidthComplement
  rw [boundedMeasurableEnvelopeWidth_eq_zero_of_determines
    C X hC hBddBelow hBddAbove hP hDet]
  ring

theorem boundedMeasurableLower_upperEnvelope_nontrivial_of_disagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    {P Q : BoundedMeasurablePrecisePrevision Ω}
    (hP : P ∈ C) (hQ : Q ∈ C) (hPQ : P X < Q X) :
    boundedMeasurableLowerEnvelope C X <
      boundedMeasurableUpperEnvelope C X := by
  calc
    boundedMeasurableLowerEnvelope C X ≤ P X :=
      boundedMeasurableLowerEnvelope_le_of_mem C X hBddBelow hP
    _ < Q X := hPQ
    _ ≤ boundedMeasurableUpperEnvelope C X :=
      le_boundedMeasurableUpperEnvelope_of_mem C X hBddAbove hQ

theorem boundedMeasurableLower_upperEnvelope_nontrivial_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    boundedMeasurableLowerEnvelope C X <
      boundedMeasurableUpperEnvelope C X := by
  rcases hWidth with ⟨P, hP, Q, hQ, hPQ⟩
  exact boundedMeasurableLower_upperEnvelope_nontrivial_of_disagreement
    C X hBddBelow hBddAbove hP hQ hPQ

/-- Compact strict width is witnessed by actual lower- and upper-endpoint
precise completions.  This packages compact endpoint attainment with the
strict-width/nontrivial-envelope theorem. -/
theorem boundedMeasurableEnvelope_exists_endpointPair_of_isCompact_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (hCompact : @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω, Plo ∈ C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω, Phi ∈ C ∧
        Plo X = boundedMeasurableLowerEnvelope C X ∧
          Phi X = boundedMeasurableUpperEnvelope C X ∧ Plo X < Phi X := by
  rcases boundedMeasurableLowerEnvelope_exists_mem_eq_of_isCompact
      C hCompact hC X with
    ⟨Plo, hPlo, hlo⟩
  rcases boundedMeasurableUpperEnvelope_exists_mem_eq_of_isCompact
      C hCompact hC X with
    ⟨Phi, hPhi, hhi⟩
  have hlt :=
    boundedMeasurableLower_upperEnvelope_nontrivial_of_strictWidth
      C X (boundedMeasurableCredalRange_bddBelow C X)
      (boundedMeasurableCredalRange_bddAbove C X) hWidth
  refine ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, ?_⟩
  rw [hlo, hhi]
  exact hlt

/-- Compact strict width has endpoint witnesses whose values directly compute
the PLN-facing width, width-complement, and midpoint coordinates. -/
theorem boundedMeasurableEnvelope_exists_endpointPairReadout_of_isCompact_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (hCompact : @IsCompact (BoundedMeasurablePrecisePrevision Ω)
      (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω, Plo ∈ C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω, Phi ∈ C ∧
        Plo X = boundedMeasurableLowerEnvelope C X ∧
        Phi X = boundedMeasurableUpperEnvelope C X ∧
        Plo X < Phi X ∧
        boundedMeasurableEnvelopeWidth C X = Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  rcases boundedMeasurableEnvelope_exists_endpointPair_of_isCompact_strictWidth
      C hCompact hC X hWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt⟩
  exact ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt,
    boundedMeasurableEnvelopeWidth_eq_endpointGap C X Plo Phi hlo hhi,
    boundedMeasurableEnvelopeWidthComplement_eq_one_sub_endpointGap
      C X Plo Phi hlo hhi,
    boundedMeasurableEnvelopeMidpoint_eq_endpointMean C X Plo Phi hlo hhi⟩

/-- If a raw bounded-measurable carrier has strict width, its compact
evaluation closure contains actual lower- and upper-endpoint completions for
the original interval. -/
theorem boundedMeasurableEnvelope_exists_endpointPair_evaluationClosure_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
        Plo X = boundedMeasurableLowerEnvelope C X ∧
          Phi X = boundedMeasurableUpperEnvelope C X ∧ Plo X < Phi X := by
  rcases boundedMeasurableLowerEnvelope_exists_mem_evaluationClosure_eq
      C hC X with
    ⟨Plo, hPlo, hlo⟩
  rcases boundedMeasurableUpperEnvelope_exists_mem_evaluationClosure_eq
      C hC X with
    ⟨Phi, hPhi, hhi⟩
  have hlt :=
    boundedMeasurableLower_upperEnvelope_nontrivial_of_strictWidth
      C X (boundedMeasurableCredalRange_bddBelow C X)
      (boundedMeasurableCredalRange_bddAbove C X) hWidth
  refine ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, ?_⟩
  rw [hlo, hhi]
  exact hlt

/-- Evaluation-closure form of the endpoint readout theorem: strict width in a
raw carrier gives compact limit completions that compute the original interval
width, width-complement, and midpoint. -/
theorem boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
        Plo X = boundedMeasurableLowerEnvelope C X ∧
        Phi X = boundedMeasurableUpperEnvelope C X ∧
        Plo X < Phi X ∧
        boundedMeasurableEnvelopeWidth C X = Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  rcases boundedMeasurableEnvelope_exists_endpointPair_evaluationClosure_of_strictWidth
      C hC X hWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt⟩
  exact ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt,
    boundedMeasurableEnvelopeWidth_eq_endpointGap C X Plo Phi hlo hhi,
    boundedMeasurableEnvelopeWidthComplement_eq_one_sub_endpointGap
      C X Plo Phi hlo hhi,
    boundedMeasurableEnvelopeMidpoint_eq_endpointMean C X Plo Phi hlo hhi⟩

/-- Disagreement between two raw bounded-measurable precise previsions is the
minimal reusable source of compact endpoint readout.  The endpoint completions
may live in the evaluation closure of the raw carrier, but their values compute
the original lower/upper interval and its PLN-facing coordinates. -/
theorem boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_disagreement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (X : BoundedMeasurableGamble Ω)
    {P Q : BoundedMeasurablePrecisePrevision Ω}
    (hP : P ∈ C) (hQ : Q ∈ C) (hPQ : P X < Q X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableCredalSetEvaluationClosure C ∧
        Plo X = boundedMeasurableLowerEnvelope C X ∧
        Phi X = boundedMeasurableUpperEnvelope C X ∧
        Plo X < Phi X ∧
        boundedMeasurableEnvelopeWidth C X = Phi X - Plo X ∧
        boundedMeasurableEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) ∧
        boundedMeasurableEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  exact
    boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_strictWidth
      C ⟨P, hP⟩ X ⟨P, hP, Q, hQ, hPQ⟩

theorem boundedMeasurableEnvelopeWidth_pos_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    0 < boundedMeasurableEnvelopeWidth C X := by
  have hlt :=
    boundedMeasurableLower_upperEnvelope_nontrivial_of_strictWidth
      C X hBddBelow hBddAbove hWidth
  unfold boundedMeasurableEnvelopeWidth
  linarith

theorem boundedMeasurableEnvelopeWidthComplement_lt_one_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω)
    (X : BoundedMeasurableGamble Ω)
    (hBddBelow : BddBelow
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove
      ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) '' C))
    (hWidth : boundedMeasurableCredalSetHasStrictWidth C X) :
    boundedMeasurableEnvelopeWidthComplement C X < 1 := by
  have hpos :=
    boundedMeasurableEnvelopeWidth_pos_of_strictWidth
      C X hBddBelow hBddAbove hWidth
  unfold boundedMeasurableEnvelopeWidthComplement
  linarith

/-- For nonempty bounded-measurable credal sets, the width-complement display
coordinate is maximal exactly when the observable is determined by all
admissible completions. -/
theorem boundedMeasurableEnvelopeWidthComplement_eq_one_iff_determines
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidthComplement C X = 1 ↔
      boundedMeasurableCredalSetDetermines C X := by
  constructor
  · intro hEq
    by_contra hNot
    have hWidth : boundedMeasurableCredalSetHasStrictWidth C X :=
      (boundedMeasurableCredalSetHasStrictWidth_iff_not_determines C X).2 hNot
    have hLt :=
      boundedMeasurableEnvelopeWidthComplement_lt_one_of_strictWidth
        C X (boundedMeasurableCredalRange_bddBelow C X)
        (boundedMeasurableCredalRange_bddAbove C X) hWidth
    exact (ne_of_lt hLt) hEq
  · intro hDet
    rcases hC with ⟨P, hP⟩
    exact boundedMeasurableEnvelopeWidthComplement_eq_one_of_determines
      C X ⟨P, hP⟩ (boundedMeasurableCredalRange_bddBelow C X)
      (boundedMeasurableCredalRange_bddAbove C X) hP hDet

/-- For nonempty bounded-measurable credal sets, the width-complement display
coordinate falls below one exactly when admissible completions strictly disagree
on the observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_lt_one_iff_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : BoundedMeasurableCredalSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidthComplement C X < 1 ↔
      boundedMeasurableCredalSetHasStrictWidth C X := by
  constructor
  · intro hLt
    refine
      (boundedMeasurableCredalSetHasStrictWidth_iff_not_determines C X).2 ?_
    intro hDet
    have hEq :=
      (boundedMeasurableEnvelopeWidthComplement_eq_one_iff_determines
        C hC X).2 hDet
    rw [hEq] at hLt
    exact (not_lt_of_ge le_rfl) hLt
  · intro hWidth
    exact boundedMeasurableEnvelopeWidthComplement_lt_one_of_strictWidth
      C X (boundedMeasurableCredalRange_bddBelow C X)
      (boundedMeasurableCredalRange_bddAbove C X) hWidth

/-! ## Precise prevision completions -/

/-- A precise prevision is a linear expectation-like functional on gambles.

It is the point-valued completion object whose lower envelope gives Walley's
lower prevision.  This is intentionally finite-additive/functional rather than
measure-theoretic; σ-additivity is a later refinement, not built into the
shared base. -/
structure PrecisePrevision (Ω : Type*) where
  toFun : Gamble Ω → ℝ
  lower_bound : ∀ (X : Gamble Ω) (c : ℝ), (∀ ω, c ≤ X ω) → c ≤ toFun X
  pos_homog : ∀ (r : ℝ) (X : Gamble Ω), 0 ≤ r → toFun (r • X) = r * toFun X
  add : ∀ (X Y : Gamble Ω), toFun (X + Y) = toFun X + toFun Y

namespace PrecisePrevision

variable {Ω : Type*}

instance : CoeFun (PrecisePrevision Ω) (fun _ => Gamble Ω → ℝ) := ⟨toFun⟩

/-- Every precise prevision is, in particular, a coherent lower prevision. -/
def toLowerPrevision (P : PrecisePrevision Ω) : LowerPrevision Ω where
  toFun := P
  lower_bound := P.lower_bound
  pos_homog := P.pos_homog
  superadd := by
    intro X Y
    rw [P.add X Y]

@[simp] theorem toLowerPrevision_apply (P : PrecisePrevision Ω) (X : Gamble Ω) :
    P.toLowerPrevision X = P X :=
  rfl

@[simp] theorem map_zero (P : PrecisePrevision Ω) : P 0 = 0 := by
  have h := P.pos_homog 0 0 (le_refl 0)
  simpa only [zero_smul, zero_mul] using h

@[simp] theorem map_neg (P : PrecisePrevision Ω) (X : Gamble Ω) :
    P (-X) = -P X := by
  have hadd := P.add X (-X)
  have hsum : P X + P (-X) = 0 := by
    calc
      P X + P (-X) = P (X + -X) := hadd.symm
      _ = 0 := by
        simp
  linarith

theorem map_sub (P : PrecisePrevision Ω) (X Y : Gamble Ω) :
    P (X - Y) = P X - P Y := by
  change P (X + -Y) = P X - P Y
  rw [P.add X (-Y), P.map_neg Y]
  ring

/-- Finite sums of gambles evaluate pointwise.  We keep this local because
`Gamble` has its own pointwise additive structure. -/
theorem sum_gamble_apply {α : Type*} (s : Finset α)
    (f : α → Gamble Ω) (ω : Ω) :
    (∑ a ∈ s, f a) ω = ∑ a ∈ s, f a ω := by
  classical
  refine Finset.induction_on s ?base ?step
  · change (0 : ℝ) = 0
    rfl
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change f a ω + (∑ x ∈ s, f x) ω = f a ω + ∑ x ∈ s, f x ω
    rw [ih]

theorem sum_gamble_apply_univ {α : Type*} [Fintype α]
    (f : α → Gamble Ω) (ω : Ω) :
    (∑ a, f a) ω = ∑ a, f a ω := by
  simpa using sum_gamble_apply (Ω := Ω) (Finset.univ : Finset α) f ω

/-- Positive homogeneity plus additivity gives full real homogeneity. -/
theorem map_smul (P : PrecisePrevision Ω) (r : ℝ) (X : Gamble Ω) :
    P (r • X) = r * P X := by
  by_cases hr : 0 ≤ r
  · exact P.pos_homog r X hr
  · have hneg_nonneg : 0 ≤ -r := by linarith
    have hpos := P.pos_homog (-r) X hneg_nonneg
    have hsmul : r • X = -((-r) • X) := by
      funext ω
      change r * X ω = -((-r) * X ω)
      ring
    calc
      P (r • X) = P (-((-r) • X)) := by rw [hsmul]
      _ = -P ((-r) • X) := P.map_neg ((-r) • X)
      _ = -((-r) * P X) := by rw [hpos]
      _ = r * P X := by ring

theorem map_sum {α : Type*} (P : PrecisePrevision Ω)
    (s : Finset α) (f : α → Gamble Ω) :
    P (∑ a ∈ s, f a) = ∑ a ∈ s, P (f a) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [P.map_zero]
  · intro a s ha ih
    simp [Finset.sum_insert ha, P.add, ih]

theorem map_sum_univ {α : Type*} [Fintype α] (P : PrecisePrevision Ω)
    (f : α → Gamble Ω) :
    P (∑ a, f a) = ∑ a, P (f a) := by
  simpa using P.map_sum (Finset.univ : Finset α) f

@[simp] theorem map_const_one (P : PrecisePrevision Ω) :
    P (Gamble.const (1 : ℝ)) = 1 := by
  have hlo : (1 : ℝ) ≤ P (Gamble.const (1 : ℝ)) := by
    exact P.lower_bound (Gamble.const (1 : ℝ)) 1 (by intro ω; rfl)
  have hneg_bound : (-1 : ℝ) ≤ P (-(Gamble.const (1 : ℝ) : Gamble Ω)) := by
    exact P.lower_bound (-(Gamble.const (1 : ℝ) : Gamble Ω)) (-1) (by intro ω; rfl)
  have hhi : P (Gamble.const (1 : ℝ)) ≤ 1 := by
    have hneg : (-1 : ℝ) ≤ -P (Gamble.const (1 : ℝ)) := by
      simpa using hneg_bound
    linarith
  exact le_antisymm hhi hlo

@[simp] theorem map_const (P : PrecisePrevision Ω) (c : ℝ) :
    P (Gamble.const c) = c := by
  have hconst : (Gamble.const c : Gamble Ω) =
      c • (Gamble.const (1 : ℝ) : Gamble Ω) := by
    funext ω
    change c = c * 1
    ring
  calc
    P (Gamble.const c) =
        P (c • (Gamble.const (1 : ℝ) : Gamble Ω)) := by rw [hconst]
    _ = c * P (Gamble.const (1 : ℝ)) := P.map_smul c (Gamble.const (1 : ℝ))
    _ = c := by simp

theorem upper_bound (P : PrecisePrevision Ω)
    (X : Gamble Ω) (c : ℝ) (hc : ∀ ω, X ω ≤ c) :
    P X ≤ c := by
  have hnonneg : 0 ≤ P (Gamble.const c - X) := by
    exact P.lower_bound (Gamble.const c - X) 0 (by
      intro ω
      change (0 : ℝ) ≤ c - X ω
      linarith [hc ω])
  rw [P.map_sub, P.map_const] at hnonneg
  linarith

/-- Precise previsions are monotone with respect to pointwise gamble order. -/
theorem mono (P : PrecisePrevision Ω)
    {X Y : Gamble Ω} (hXY : ∀ ω, X ω ≤ Y ω) :
    P X ≤ P Y := by
  have hnonneg : 0 ≤ P (Y - X) := by
    exact P.lower_bound (Y - X) 0 (by
      intro ω
      change (0 : ℝ) ≤ Y ω - X ω
      linarith [hXY ω])
  rw [P.map_sub] at hnonneg
  linarith

/-- Precise previsions are additive as lower previsions. -/
theorem toLowerPrevision_precise (P : PrecisePrevision Ω) :
    P.toLowerPrevision.isPrecise := by
  rw [LowerPrevision.precise_iff_additive]
  exact P.add

/-- Extensionality for precise previsions: proof fields are irrelevant once
the pointwise expectation functional is fixed. -/
@[ext] theorem ext {P Q : PrecisePrevision Ω} (h : ∀ X, P X = Q X) : P = Q := by
  cases P
  cases Q
  congr
  funext X
  exact h X

/-- Convex mixture of two precise previsions.  The coefficients are restricted
to `[0,1]`, which is the affine/credal operation that preserves normalization. -/
def mix (t : ℝ) (P Q : PrecisePrevision Ω) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PrecisePrevision Ω where
  toFun X := t * P X + (1 - t) * Q X
  lower_bound := by
    intro X c hc
    have hP : c ≤ P X := P.lower_bound X c hc
    have hQ : c ≤ Q X := Q.lower_bound X c hc
    have h1t : 0 ≤ 1 - t := by linarith
    nlinarith
  pos_homog := by
    intro r X hr
    rw [P.pos_homog r X hr, Q.pos_homog r X hr]
    ring
  add := by
    intro X Y
    rw [P.add X Y, Q.add X Y]
    ring

/-- Point-evaluation precise prevision.  This is the concrete Dirac completion:
all uncertainty has collapsed to the global state `ω`. -/
def dirac (ω : Ω) : PrecisePrevision Ω where
  toFun X := X ω
  lower_bound := by
    intro X c hc
    exact hc ω
  pos_homog := by
    intro r X hr
    rfl
  add := by
    intro X Y
    rfl

@[simp] theorem dirac_apply (ω : Ω) (X : Gamble Ω) :
    dirac ω X = X ω :=
  rfl

theorem dirac_precise (ω : Ω) :
    (dirac ω).toLowerPrevision.isPrecise :=
  toLowerPrevision_precise (dirac ω)

/-- Finite probability weights: an explicit finite carrier for precise
previsions.  This is the finite-dimensional face of the weak*/compact carrier:
nonnegative weights on a finite state space, normalized to total mass `1`. -/
structure FiniteWeights (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteWeights

variable {Ω : Type*} [Fintype Ω]

/-- Extensionality for finite weights. -/
@[ext] theorem ext {w v : FiniteWeights Ω}
    (h : ∀ ω, w.weight ω = v.weight ω) : w = v := by
  cases w
  cases v
  congr
  funext ω
  exact h ω

/-- A finite probability vector is exactly a point of Mathlib's standard
simplex.  This is the finite-dimensional compact carrier used before the
infinite weak*/Banach--Alaoglu refinement. -/
noncomputable def toStdSimplex (w : FiniteWeights Ω) : stdSimplex ℝ Ω :=
  ⟨w.weight, w.nonneg, w.total⟩

@[simp] theorem toStdSimplex_apply (w : FiniteWeights Ω) (ω : Ω) :
    w.toStdSimplex.1 ω = w.weight ω :=
  rfl

/-- A point of the standard simplex gives finite probability weights. -/
noncomputable def ofStdSimplex (w : stdSimplex ℝ Ω) : FiniteWeights Ω where
  weight := w.1
  nonneg := w.2.1
  total := w.2.2

@[simp] theorem ofStdSimplex_weight (w : stdSimplex ℝ Ω) (ω : Ω) :
    (ofStdSimplex w).weight ω = w.1 ω :=
  rfl

@[simp] theorem ofStdSimplex_toStdSimplex (w : FiniteWeights Ω) :
    ofStdSimplex w.toStdSimplex = w := by
  cases w
  rfl

@[simp] theorem toStdSimplex_ofStdSimplex (w : stdSimplex ℝ Ω) :
    (ofStdSimplex w).toStdSimplex = w := by
  cases w
  rfl

/-- The finite-weight carrier is equivalent to the standard simplex.  This is
the algebraic part of the finite compact crown; the topological homeomorphism
for precise previsions is a later layer, not assumed here. -/
noncomputable def equivStdSimplex : FiniteWeights Ω ≃ stdSimplex ℝ Ω where
  toFun := toStdSimplex
  invFun := ofStdSimplex
  left_inv := ofStdSimplex_toStdSimplex
  right_inv := toStdSimplex_ofStdSimplex

/-- The actual finite compactness input: finite weights live on Mathlib's
compact standard simplex. -/
theorem stdSimplexCarrierCompact :
    IsCompact (stdSimplex ℝ Ω) :=
  isCompact_stdSimplex ℝ Ω

section AtomicRepresentation

variable [DecidableEq Ω]

/-- The singleton indicator gamble for a finite state. -/
def atomGamble (ω : Ω) : Gamble Ω :=
  fun η => if η = ω then 1 else 0

omit [Fintype Ω] in
theorem atomGamble_self (ω : Ω) :
    atomGamble (Ω := Ω) ω ω = 1 := by
  simp [atomGamble]

attribute [simp] atomGamble_self

omit [Fintype Ω] in
theorem atomGamble_nonneg (ω η : Ω) :
    0 ≤ atomGamble (Ω := Ω) ω η := by
  by_cases h : η = ω
  · simp [atomGamble, h]
  · simp [atomGamble, h]

/-- The atomic indicators partition the constant-one gamble. -/
theorem sum_atomGamble :
    (∑ ω : Ω, atomGamble (Ω := Ω) ω) = Gamble.const (1 : ℝ) := by
  funext η
  rw [PrecisePrevision.sum_gamble_apply_univ]
  rw [Finset.sum_eq_single η]
  · simp [atomGamble]
  · intro ω _hω hne
    have hηω : η ≠ ω := by exact Ne.symm hne
    simp [atomGamble, hηω]
  · intro hη
    exact (hη (Finset.mem_univ η)).elim

/-- Every gamble is the finite linear combination of its atomic values. -/
theorem sum_smul_atomGamble (X : Gamble Ω) :
    (∑ ω : Ω, X ω • atomGamble (Ω := Ω) ω) = X := by
  funext η
  rw [PrecisePrevision.sum_gamble_apply_univ]
  rw [Finset.sum_eq_single η]
  · change X η * (if η = η then (1 : ℝ) else 0) = X η
    simp
  · intro ω _hω hne
    have hηω : η ≠ ω := by exact Ne.symm hne
    change X ω * (if η = ω then (1 : ℝ) else 0) = 0
    simp [hηω]
  · intro hη
    exact (hη (Finset.mem_univ η)).elim

/-- Atomic weights extracted from a finite precise prevision. -/
noncomputable def ofPrecisePrevision (P : PrecisePrevision Ω) : FiniteWeights Ω where
  weight ω := P (atomGamble ω)
  nonneg := by
    intro ω
    exact P.lower_bound (atomGamble ω) 0 (atomGamble_nonneg ω)
  total := by
    calc
      ∑ ω : Ω, P (atomGamble ω) = P (∑ ω : Ω, atomGamble ω) := by
        exact (P.map_sum_univ fun ω : Ω => atomGamble ω).symm
      _ = P (Gamble.const (1 : ℝ)) := by rw [sum_atomGamble]
      _ = 1 := P.map_const_one

@[simp] theorem ofPrecisePrevision_weight
    (P : PrecisePrevision Ω) (ω : Ω) :
    (ofPrecisePrevision P).weight ω = P (atomGamble ω) :=
  rfl

end AtomicRepresentation

/-- A finite probability vector induces the usual expectation functional. -/
noncomputable def toPrecisePrevision (w : FiniteWeights Ω) :
    PrecisePrevision Ω where
  toFun X := ∑ ω, w.weight ω * X ω
  lower_bound := by
    intro X c hc
    calc
      c = ∑ ω : Ω, w.weight ω * c := by
        rw [← Finset.sum_mul, w.total, one_mul]
      _ ≤ ∑ ω : Ω, w.weight ω * X ω := by
        exact Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hc ω) (w.nonneg ω)
  pos_homog := by
    intro r X hr
    calc
      ∑ ω : Ω, w.weight ω * (r • X) ω =
          ∑ ω : Ω, r * (w.weight ω * X ω) := by
        apply Finset.sum_congr rfl
        intro ω _hω
        change w.weight ω * (r * X ω) = r * (w.weight ω * X ω)
        ring
      _ = r * ∑ ω : Ω, w.weight ω * X ω := by
        rw [Finset.mul_sum]
  add := by
    intro X Y
    calc
      ∑ ω : Ω, w.weight ω * (X + Y) ω =
          ∑ ω : Ω, (w.weight ω * X ω + w.weight ω * Y ω) := by
        apply Finset.sum_congr rfl
        intro ω _hω
        show w.weight ω * (X ω + Y ω) = w.weight ω * X ω + w.weight ω * Y ω
        ring
      _ = (∑ ω : Ω, w.weight ω * X ω) +
          ∑ ω : Ω, w.weight ω * Y ω := by
        rw [Finset.sum_add_distrib]

@[simp] theorem toPrecisePrevision_apply
    (w : FiniteWeights Ω) (X : Gamble Ω) :
    w.toPrecisePrevision X = ∑ ω, w.weight ω * X ω :=
  rfl

theorem toPrecisePrevision_precise (w : FiniteWeights Ω) :
    w.toPrecisePrevision.toLowerPrevision.isPrecise :=
  PrecisePrevision.toLowerPrevision_precise w.toPrecisePrevision

/-- Push finite probability weights forward along a map into an arbitrary
state space, obtaining a finite-support precise prevision on the target.  This
is the finite-support analogue of the measure-to-expectation adapter used by
the projective/DLR bridges. -/
noncomputable def pushForwardPrevision {Γ : Type*}
    (w : FiniteWeights Ω) (f : Ω → Γ) : PrecisePrevision Γ where
  toFun X := w.toPrecisePrevision (fun ω => X (f ω))
  lower_bound := by
    intro X c hc
    exact w.toPrecisePrevision.lower_bound (fun ω => X (f ω)) c
      (fun ω => hc (f ω))
  pos_homog := by
    intro r X hr
    exact w.toPrecisePrevision.pos_homog r (fun ω => X (f ω)) hr
  add := by
    intro X Y
    exact w.toPrecisePrevision.add (fun ω => X (f ω)) (fun ω => Y (f ω))

@[simp] theorem pushForwardPrevision_apply {Γ : Type*}
    (w : FiniteWeights Ω) (f : Ω → Γ) (X : Gamble Γ) :
    w.pushForwardPrevision f X = ∑ ω, w.weight ω * X (f ω) :=
  rfl

theorem pushForwardPrevision_precise {Γ : Type*}
    (w : FiniteWeights Ω) (f : Ω → Γ) :
    (w.pushForwardPrevision f).toLowerPrevision.isPrecise :=
  PrecisePrevision.toLowerPrevision_precise (w.pushForwardPrevision f)

section AtomicRepresentation

variable [DecidableEq Ω]

/-- On a finite state space, a precise prevision is exactly the finite
expectation induced by its atomic weights. -/
theorem toPrecisePrevision_ofPrecisePrevision
    (P : PrecisePrevision Ω) :
    (ofPrecisePrevision P).toPrecisePrevision = P := by
  ext X
  calc
    (ofPrecisePrevision P).toPrecisePrevision X =
        ∑ ω : Ω, P (atomGamble ω) * X ω := rfl
    _ = ∑ ω : Ω, X ω * P (atomGamble ω) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ = ∑ ω : Ω, P (X ω • atomGamble ω) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      rw [P.map_smul]
    _ = P (∑ ω : Ω, X ω • atomGamble ω) := by
      exact (P.map_sum_univ fun ω : Ω => X ω • atomGamble ω).symm
    _ = P X := by rw [sum_smul_atomGamble X]

/-- Extracting atomic weights from the finite expectation induced by weights
recovers the original weights. -/
theorem ofPrecisePrevision_toPrecisePrevision
    (w : FiniteWeights Ω) :
    ofPrecisePrevision w.toPrecisePrevision = w := by
  ext ω
  calc
    (ofPrecisePrevision w.toPrecisePrevision).weight ω =
        w.toPrecisePrevision (atomGamble ω) := rfl
    _ = ∑ η : Ω, w.weight η * atomGamble ω η := rfl
    _ = w.weight ω := by
      rw [Finset.sum_eq_single ω]
      · simp [atomGamble]
      · intro η _hη hne
        simp [atomGamble, hne]
      · intro hω
        exact (hω (Finset.mem_univ ω)).elim

/-- Finite precise previsions are algebraically equivalent to finite
probability weights.  The topological compactness upgrade factors through this
equivalence and the standard simplex compactness theorem. -/
noncomputable def equivPrecisePrevision :
    FiniteWeights Ω ≃ PrecisePrevision Ω where
  toFun := toPrecisePrevision
  invFun := ofPrecisePrevision
  left_inv := ofPrecisePrevision_toPrecisePrevision
  right_inv := toPrecisePrevision_ofPrecisePrevision

/-- The finite evaluation coordinate map: evaluate a precise prevision on
singleton indicators, obtaining a point of the standard simplex. -/
noncomputable def finiteEvaluationCoordinate
    (P : PrecisePrevision Ω) : stdSimplex ℝ Ω :=
  (ofPrecisePrevision P).toStdSimplex

/-- Finite evaluation topology on precise previsions, induced by the atomic
coordinate map into the standard simplex.  This is the finite-dimensional
version of the weak*/evaluation topology; it is kept explicit rather than
installed as a global instance. -/
noncomputable def finiteEvaluationTopology :
    TopologicalSpace (PrecisePrevision Ω) :=
  TopologicalSpace.induced
    (fun P : PrecisePrevision Ω => finiteEvaluationCoordinate P)
    inferInstance

theorem finiteEvaluationCoordinate_continuous :
    @Continuous (PrecisePrevision Ω) (stdSimplex ℝ Ω)
      finiteEvaluationTopology inferInstance finiteEvaluationCoordinate :=
  continuous_induced_dom

theorem eval_eq_sum_finiteEvaluationCoordinate
    (P : PrecisePrevision Ω) (X : Gamble Ω) :
    P X = ∑ ω, (finiteEvaluationCoordinate P).1 ω * X ω := by
  change P X = (ofPrecisePrevision P).toPrecisePrevision X
  exact (congrArg (fun Q : PrecisePrevision Ω => Q X)
    (toPrecisePrevision_ofPrecisePrevision P)).symm

/-- Evaluation of any finite gamble is continuous in the finite evaluation
topology on precise previsions. -/
theorem eval_continuous (X : Gamble Ω) :
    @Continuous (PrecisePrevision Ω) ℝ
      finiteEvaluationTopology inferInstance (fun P => P X) := by
  letI : TopologicalSpace (PrecisePrevision Ω) := finiteEvaluationTopology
  have hsum :
      Continuous
        (fun P : PrecisePrevision Ω =>
          ∑ ω, (finiteEvaluationCoordinate P).1 ω * X ω) := by
    refine continuous_finset_sum Finset.univ ?_
    intro ω _hω
    have hcoord :
        Continuous
          (fun P : PrecisePrevision Ω => (finiteEvaluationCoordinate P).1 ω) :=
      (((continuous_apply ω).comp continuous_subtype_val).comp
        finiteEvaluationCoordinate_continuous)
    exact hcoord.mul continuous_const
  have hEq :
      (fun P : PrecisePrevision Ω => P X) =
        (fun P : PrecisePrevision Ω =>
          ∑ ω, (finiteEvaluationCoordinate P).1 ω * X ω) := by
    funext P
    exact eval_eq_sum_finiteEvaluationCoordinate P X
  rw [hEq]
  exact hsum

/-- The inverse finite-simplex parametrization of precise previsions. -/
noncomputable def precisePrevisionOfStdSimplex
    (w : stdSimplex ℝ Ω) : PrecisePrevision Ω :=
  (ofStdSimplex w).toPrecisePrevision

@[simp] theorem finiteEvaluationCoordinate_precisePrevisionOfStdSimplex
    (w : stdSimplex ℝ Ω) :
    finiteEvaluationCoordinate (precisePrevisionOfStdSimplex w) = w := by
  have h :
      ofPrecisePrevision (Ω := Ω) (ofStdSimplex w).toPrecisePrevision =
        ofStdSimplex w :=
    ofPrecisePrevision_toPrecisePrevision (Ω := Ω) (ofStdSimplex w)
  rw [finiteEvaluationCoordinate, precisePrevisionOfStdSimplex, h]
  simp

@[simp] theorem precisePrevisionOfStdSimplex_finiteEvaluationCoordinate
    (P : PrecisePrevision Ω) :
    precisePrevisionOfStdSimplex (finiteEvaluationCoordinate P) = P := by
  simpa [finiteEvaluationCoordinate, precisePrevisionOfStdSimplex] using
    toPrecisePrevision_ofPrecisePrevision (Ω := Ω) P

theorem precisePrevisionOfStdSimplex_continuous :
    @Continuous (stdSimplex ℝ Ω) (PrecisePrevision Ω)
      inferInstance finiteEvaluationTopology precisePrevisionOfStdSimplex := by
  rw [finiteEvaluationTopology, continuous_induced_rng]
  have h : (fun P : PrecisePrevision Ω => finiteEvaluationCoordinate P) ∘
      precisePrevisionOfStdSimplex = fun w : stdSimplex ℝ Ω => w := by
    funext w
    simp [Function.comp_def, finiteEvaluationCoordinate_precisePrevisionOfStdSimplex]
  rw [h]
  exact continuous_id

/-- The whole finite precise-prevision carrier is compact in the finite
evaluation topology, by transport from the compact standard simplex. -/
theorem finiteEvaluationTopology_univCompact :
    @IsCompact (PrecisePrevision Ω) finiteEvaluationTopology Set.univ := by
  letI : TopologicalSpace (PrecisePrevision Ω) := finiteEvaluationTopology
  have hcont :
      @Continuous (stdSimplex ℝ Ω) (PrecisePrevision Ω)
        inferInstance finiteEvaluationTopology precisePrevisionOfStdSimplex :=
    precisePrevisionOfStdSimplex_continuous (Ω := Ω)
  have hcompact :
      IsCompact
        (precisePrevisionOfStdSimplex '' (Set.univ : Set (stdSimplex ℝ Ω))) :=
    isCompact_univ.image hcont
  have himage :
      precisePrevisionOfStdSimplex '' (Set.univ : Set (stdSimplex ℝ Ω)) =
        (Set.univ : Set (PrecisePrevision Ω)) := by
    ext P
    constructor
    · intro _hP
      simp
    · intro _hP
      exact ⟨finiteEvaluationCoordinate P, by simp,
        precisePrevisionOfStdSimplex_finiteEvaluationCoordinate P⟩
  simpa [himage] using hcompact

/-- Every finite-evaluation closed subset of the finite precise-prevision
carrier is compact. -/
theorem finiteEvaluationTopology_isCompact_of_isClosed
    (C : Set (PrecisePrevision Ω))
    (hClosed : @IsClosed (PrecisePrevision Ω) finiteEvaluationTopology C) :
    @IsCompact (PrecisePrevision Ω) finiteEvaluationTopology C := by
  letI : TopologicalSpace (PrecisePrevision Ω) := finiteEvaluationTopology
  exact finiteEvaluationTopology_univCompact.of_isClosed_subset hClosed
    (by intro P _hP; exact Set.mem_univ P)

theorem finiteEvaluationCompactSpace :
    @CompactSpace (PrecisePrevision Ω) finiteEvaluationTopology := by
  letI : TopologicalSpace (PrecisePrevision Ω) := finiteEvaluationTopology
  exact ⟨by simpa using finiteEvaluationTopology_univCompact (Ω := Ω)⟩

end AtomicRepresentation

/-- Real-valued finite weights extracted from a finite `PMF`. -/
noncomputable def ofPMF (p : PMF Ω) : FiniteWeights Ω where
  weight ω := (p ω).toReal
  nonneg := by
    intro ω
    exact ENNReal.toReal_nonneg
  total := by
    have hsumENN : (∑ ω : Ω, p ω) = (1 : ENNReal) := by
      calc
        ∑ ω : Ω, p ω = ∑' ω : Ω, p ω := by
          exact (tsum_eq_sum fun ω hω =>
            (hω (Finset.mem_univ ω)).elim).symm
        _ = 1 := PMF.tsum_coe p
    have hfinite : ∀ ω ∈ (Finset.univ : Finset Ω), p ω ≠ ⊤ := by
      intro ω _hω
      exact PMF.apply_ne_top p ω
    rw [← ENNReal.toReal_sum hfinite, hsumENN]
    norm_num

/-- A finite `PMF` induces a precise prevision by finite expectation. -/
noncomputable def ofPMFPrevision (p : PMF Ω) : PrecisePrevision Ω :=
  (ofPMF p).toPrecisePrevision

@[simp] theorem ofPMFPrevision_apply
    (p : PMF Ω) (X : Gamble Ω) :
    ofPMFPrevision p X = ∑ ω, (p ω).toReal * X ω :=
  rfl

theorem ofPMFPrevision_precise (p : PMF Ω) :
    (ofPMFPrevision p).toLowerPrevision.isPrecise :=
  toPrecisePrevision_precise (ofPMF p)

/-- Finite PMF previsions commute with pushforward.  This is the finite
expectation law used by the DLR/de Finetti projective adapters: pushing a law
forward along `f` and evaluating `X` is the same as evaluating `X ∘ f` before
the pushforward. -/
theorem ofPMFPrevision_map_apply
    {Γ : Type*} [Fintype Γ] (p : PMF Ω) (f : Ω → Γ) (X : Gamble Γ) :
    ofPMFPrevision (PMF.map f p) X =
      ofPMFPrevision p (fun ω => X (f ω)) := by
  classical
  rw [ofPMFPrevision_apply, ofPMFPrevision_apply]
  have hmap : ∀ γ : Γ,
      ((PMF.map f p) γ).toReal =
        ∑ ω : Ω, (if γ = f ω then (p ω).toReal else 0) := by
    intro γ
    rw [PMF.map_apply]
    rw [tsum_eq_sum (s := Finset.univ)]
    · rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro ω _hω
        by_cases h : γ = f ω <;> simp [h]
      · intro ω _hω
        by_cases h : γ = f ω <;> simp [h, PMF.apply_ne_top p ω]
    · intro ω hω
      exact (hω (Finset.mem_univ ω)).elim
  calc
    ∑ γ : Γ, ((PMF.map f p) γ).toReal * X γ
        = ∑ γ : Γ,
            (∑ ω : Ω, (if γ = f ω then (p ω).toReal else 0)) * X γ := by
            apply Finset.sum_congr rfl
            intro γ _hγ
            rw [hmap γ]
    _ = ∑ γ : Γ, ∑ ω : Ω,
          (if γ = f ω then (p ω).toReal * X γ else 0) := by
            apply Finset.sum_congr rfl
            intro γ _hγ
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro ω _hω
            by_cases h : γ = f ω <;> simp [h]
    _ = ∑ ω : Ω, ∑ γ : Γ,
          (if γ = f ω then (p ω).toReal * X γ else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ ω : Ω, (p ω).toReal * X (f ω) := by
            apply Finset.sum_congr rfl
            intro ω _hω
            rw [Finset.sum_eq_single (f ω)]
            · simp
            · intro γ _hγ hγ
              simp [hγ]
            · intro hnot
              exact (hnot (Finset.mem_univ (f ω))).elim

/-- Real-valued finite weights extracted from a probability measure on a finite
measurable state space.  This is the finite/cylinder measure-to-prevision
adapter used by the MLN/DLR specialization before the infinite weak* lift. -/
noncomputable def ofFiniteProbabilityMeasure
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : FiniteWeights Ω where
  weight ω := (μ ({ω} : Set Ω)).toReal
  nonneg := by
    intro ω
    exact ENNReal.toReal_nonneg
  total := by
    have hsumENN : ∑ ω : Ω, μ ({ω} : Set Ω) = 1 := by
      calc
        ∑ ω : Ω, μ ({ω} : Set Ω) = μ Set.univ := by
          exact (finiteMeasure_univ_eq_sum_singletons μ).symm
        _ = 1 := measure_univ
    have hfinite : ∀ ω : Ω, μ ({ω} : Set Ω) ≠ ⊤ := by
      intro ω
      have hle : μ ({ω} : Set Ω) ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      have huniv : μ Set.univ = 1 := measure_univ
      exact ne_of_lt (lt_of_le_of_lt (hle.trans_eq huniv) (by simp))
    have hsumToReal := congrArg ENNReal.toReal hsumENN
    rw [ENNReal.toReal_sum] at hsumToReal
    · simpa using hsumToReal
    · intro ω _hω
      exact hfinite ω

/-- A finite probability measure induces a precise prevision by finite
expectation over singleton masses. -/
noncomputable def ofFiniteProbabilityMeasurePrevision
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : PrecisePrevision Ω :=
  (ofFiniteProbabilityMeasure μ).toPrecisePrevision

@[simp] theorem ofFiniteProbabilityMeasurePrevision_apply
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Gamble Ω) :
    ofFiniteProbabilityMeasurePrevision μ X =
      ∑ ω, (μ ({ω} : Set Ω)).toReal * X ω :=
  rfl

theorem ofFiniteProbabilityMeasurePrevision_precise
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (ofFiniteProbabilityMeasurePrevision μ).toLowerPrevision.isPrecise :=
  toPrecisePrevision_precise (ofFiniteProbabilityMeasure μ)

/-- On a finite measurable state space, the probability-measure prevision is
the same finite expectation as the PMF obtained from singleton masses. -/
theorem ofFiniteProbabilityMeasurePrevision_eq_ofPMF_toPMF
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ofFiniteProbabilityMeasurePrevision μ = ofPMFPrevision μ.toPMF := by
  ext X
  rw [ofFiniteProbabilityMeasurePrevision_apply, ofPMFPrevision_apply]
  apply Finset.sum_congr rfl
  intro ω _hω
  rw [MeasureTheory.Measure.toPMF_apply]

/-- Finite probability-measure previsions commute with measurable pushforward.
This is the measure-level version of `ofPMFPrevision_map_apply`, used by
finite/cylinder DLR and de Finetti adapters. -/
theorem ofFiniteProbabilityMeasurePrevision_map_apply
    {Ω Γ : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Γ) (hf : Measurable f) (X : Gamble Γ) :
    @ofFiniteProbabilityMeasurePrevision Γ _ _ _
        (Measure.map f μ) (Measure.isProbabilityMeasure_map hf.aemeasurable) X =
      ofFiniteProbabilityMeasurePrevision μ (fun ω => X (f ω)) := by
  classical
  letI : IsProbabilityMeasure (Measure.map f μ) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [ofFiniteProbabilityMeasurePrevision_eq_ofPMF_toPMF
      (Measure.map f μ)]
  rw [ofFiniteProbabilityMeasurePrevision_eq_ofPMF_toPMF μ]
  have hmeasure :
      Measure.map f μ = (PMF.map f μ.toPMF).toMeasure := by
    calc
      Measure.map f μ = Measure.map f μ.toPMF.toMeasure := by
        rw [MeasureTheory.Measure.toPMF_toMeasure]
      _ = (PMF.map f μ.toPMF).toMeasure := by
        simpa using PMF.toMeasure_map f μ.toPMF hf
  have hpmf :
      (Measure.map f μ).toPMF = PMF.map f μ.toPMF :=
    (PMF.toPMF_eq_iff_toMeasure_eq
      (μ := Measure.map f μ) (p := PMF.map f μ.toPMF)).2 hmeasure
  rw [hpmf]
  exact ofPMFPrevision_map_apply μ.toPMF f X

/-- On a finite measurable state space, the σ-additive bounded-observable
prevision induced by a probability measure agrees with the singleton-mass
finite precise prevision. -/
theorem boundedMeasurablePrevision_ofFinite_eq_finiteProbabilityMeasurePrevision
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Gamble Ω) :
    BoundedMeasurablePrecisePrevision.ofProbabilityMeasure μ
        (BoundedMeasurableGamble.ofFinite X) =
      ofFiniteProbabilityMeasurePrevision μ X := by
  rw [BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_apply,
    ofFiniteProbabilityMeasurePrevision_apply]
  rw [integral_fintype]
  · simp [Measure.real, smul_eq_mul]
  · exact (BoundedMeasurableGamble.ofFinite X).integrable μ

/-- A finite probability-measure prevision evaluates an indicator gamble as the
measure of the indicated set.  This is the reusable finite/cylinder
measure-to-prevision bridge for DLR, de Finetti, and Bayesian-network adapters. -/
theorem ofFiniteProbabilityMeasurePrevision_indicator
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω)
    [DecidablePred (fun ω => ω ∈ S)] :
    ofFiniteProbabilityMeasurePrevision μ
        (fun ω => if ω ∈ S then (1 : ℝ) else 0) =
      (μ S).toReal := by
  classical
  rw [ofFiniteProbabilityMeasurePrevision_apply]
  have hsingleton_ne_top : ∀ ω : Ω, μ ({ω} : Set Ω) ≠ ⊤ := by
    intro ω
    have hle : μ ({ω} : Set Ω) ≤ μ Set.univ :=
      measure_mono (Set.subset_univ _)
    have huniv : μ Set.univ = 1 := measure_univ
    exact ne_of_lt (lt_of_le_of_lt (hle.trans_eq huniv) (by simp))
  have hsumENN :
      ∑ ω : Ω, (if ω ∈ S then μ ({ω} : Set Ω) else 0) = μ S := by
    calc
      ∑ ω : Ω, (if ω ∈ S then μ ({ω} : Set Ω) else 0)
          = ∑ ω : Ω, S.indicator (fun η : Ω => μ ({η} : Set Ω)) ω := by
            apply Finset.sum_congr rfl
            intro ω _hω
            by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]
      _ = (μ.toPMF.toMeasure S) := by
            rw [PMF.toMeasure_apply_fintype]
            apply Finset.sum_congr rfl
            intro ω _hω
            by_cases hω : ω ∈ S <;>
              simp [Set.indicator, hω, MeasureTheory.Measure.toPMF_apply]
      _ = μ S := by
            rw [MeasureTheory.Measure.toPMF_toMeasure]
  have hsumToReal :
      (∑ ω : Ω, (if ω ∈ S then μ ({ω} : Set Ω) else 0)).toReal =
        (μ S).toReal :=
    congrArg ENNReal.toReal hsumENN
  rw [ENNReal.toReal_sum] at hsumToReal
  · have hsumReal :
        ∑ ω : Ω, (if ω ∈ S then (μ ({ω} : Set Ω)).toReal else 0) =
          (μ S).toReal := by
      calc
        ∑ ω : Ω, (if ω ∈ S then (μ ({ω} : Set Ω)).toReal else 0)
            = ∑ ω : Ω, (if ω ∈ S then μ ({ω} : Set Ω) else 0).toReal := by
              apply Finset.sum_congr rfl
              intro ω _hω
              by_cases hmem : ω ∈ S <;> simp [hmem]
        _ = (μ S).toReal := hsumToReal
    calc
      ∑ ω : Ω, (μ ({ω} : Set Ω)).toReal *
          (if ω ∈ S then (1 : ℝ) else 0)
          = ∑ ω : Ω,
              (if ω ∈ S then (μ ({ω} : Set Ω)).toReal else 0) := by
            apply Finset.sum_congr rfl
            intro ω _hω
            by_cases hω : ω ∈ S <;> simp [hω]
      _ = (μ S).toReal := hsumReal
  · intro ω _hω
    by_cases hmem : ω ∈ S
    · simp [hmem, hsingleton_ne_top ω]
    · simp [hmem]

end FiniteWeights

/-- A finite precise prevision is supported on a set when all singleton
indicators outside that set have zero prevision. -/
def supportedOn {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Set Ω) (P : PrecisePrevision Ω) : Prop :=
  ∀ ω, ω ∉ A → P (FiniteWeights.atomGamble ω) = 0

theorem supportedOn_dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {A : Set Ω} {ω : Ω} (hω : ω ∈ A) :
    supportedOn A (dirac ω) := by
  intro η hη
  by_cases h : ω = η
  · subst η
    exact (hη hω).elim
  · simp [FiniteWeights.atomGamble, h]

/-- Finite support restrictions are closed in the finite evaluation topology:
they are finite intersections of atomic zero-evaluation constraints. -/
theorem supportedOn_isClosed {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Set Ω) :
    @IsClosed (PrecisePrevision Ω)
      (FiniteWeights.finiteEvaluationTopology (Ω := Ω))
      {P : PrecisePrevision Ω | supportedOn A P} := by
  letI : TopologicalSpace (PrecisePrevision Ω) :=
    FiniteWeights.finiteEvaluationTopology (Ω := Ω)
  change IsClosed
    {P : PrecisePrevision Ω |
      ∀ ω, ω ∉ A → P (FiniteWeights.atomGamble ω) = 0}
  have hEq :
      {P : PrecisePrevision Ω |
        ∀ ω, ω ∉ A → P (FiniteWeights.atomGamble ω) = 0} =
        ⋂ ω,
          {P : PrecisePrevision Ω |
            ω ∉ A → P (FiniteWeights.atomGamble ω) = 0} := by
    ext P
    simp
  rw [hEq]
  refine isClosed_iInter ?_
  intro ω
  by_cases hω : ω ∈ A
  · have hSet :
        {P : PrecisePrevision Ω |
          ω ∉ A → P (FiniteWeights.atomGamble ω) = 0} =
          Set.univ := by
        ext P
        simp [hω]
    rw [hSet]
    exact isClosed_univ
  · have hSet :
        {P : PrecisePrevision Ω |
          ω ∉ A → P (FiniteWeights.atomGamble ω) = 0} =
          {P : PrecisePrevision Ω |
            P (FiniteWeights.atomGamble ω) = 0} := by
        ext P
        simp [hω]
    rw [hSet]
    exact isClosed_eq
      (FiniteWeights.eval_continuous (FiniteWeights.atomGamble ω))
      continuous_const

/-- Restrict a raw precise prevision to bounded measurable observables.

This is the finite-additive-to-bounded-observable inclusion: it does not add
σ-additivity, but it lets the bounded-measurable envelope layer reuse any
Walley precise completion whose domain is all gambles. -/
def restrictBoundedMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : PrecisePrevision Ω) :
    BoundedMeasurablePrecisePrevision Ω where
  toFun X := P X.toGamble
  lower_bound := by
    intro X c hc
    exact P.lower_bound X.toGamble c hc
  pos_homog := by
    intro r X hr
    have h : (r • X).toGamble = r • X.toGamble := by
      funext ω; show r * X.toFun ω = r * X.toFun ω; rfl
    rw [h]
    exact P.pos_homog r X.toGamble hr
  add := by
    intro X Y
    have h : (X + Y).toGamble = X.toGamble + Y.toGamble := by
      funext ω; show X.toFun ω + Y.toFun ω = X.toFun ω + Y.toFun ω; rfl
    rw [h]
    exact P.add X.toGamble Y.toGamble

@[simp] theorem restrictBoundedMeasurable_apply
    {Ω : Type*} [MeasurableSpace Ω] (P : PrecisePrevision Ω)
    (X : BoundedMeasurableGamble Ω) :
    P.restrictBoundedMeasurable X = P X.toGamble :=
  rfl

@[simp] theorem restrictBoundedMeasurable_ofFinite_apply
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (P : PrecisePrevision Ω) (X : Gamble Ω) :
    P.restrictBoundedMeasurable (BoundedMeasurableGamble.ofFinite X) =
      P X :=
  rfl

end PrecisePrevision

namespace BoundedMeasurablePrecisePrevision

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On a finite measurable state space, every bounded-measurable precise
prevision extends canonically to a raw precise prevision on all gambles, because
all raw gambles are bounded and measurable.

This is the positive finite counterpart to the countable obstruction below:
finite DLR/de Finetti windows may safely use raw Walley previsions, while
infinite carriers must stay on bounded/measurable observables unless an
additional extension assumption is explicit. -/
noncomputable def toRawFinitePrecisePrevision
    [Fintype Ω] [MeasurableSingletonClass Ω]
    (P : BoundedMeasurablePrecisePrevision Ω) :
    PrecisePrevision Ω where
  toFun X := P (BoundedMeasurableGamble.ofFinite X)
  lower_bound := by
    intro X c hc
    exact P.lower_bound (BoundedMeasurableGamble.ofFinite X) c hc
  pos_homog := by
    intro r X hr
    have h :
        BoundedMeasurableGamble.ofFinite (r • X) =
          r • BoundedMeasurableGamble.ofFinite X := by
      ext ω
      rfl
    rw [h]
    exact P.pos_homog r (BoundedMeasurableGamble.ofFinite X) hr
  add := by
    intro X Y
    have h :
        BoundedMeasurableGamble.ofFinite (X + Y) =
          BoundedMeasurableGamble.ofFinite X +
            BoundedMeasurableGamble.ofFinite Y := by
      ext ω
      rfl
    rw [h]
    exact P.add (BoundedMeasurableGamble.ofFinite X)
      (BoundedMeasurableGamble.ofFinite Y)

@[simp] theorem toRawFinitePrecisePrevision_apply
    [Fintype Ω] [MeasurableSingletonClass Ω]
    (P : BoundedMeasurablePrecisePrevision Ω) (X : Gamble Ω) :
    P.toRawFinitePrecisePrevision X =
      P (BoundedMeasurableGamble.ofFinite X) :=
  rfl

/-- On finite measurable carriers, the canonical raw extension commutes with
affine credal mixtures. -/
@[simp] theorem toRawFinitePrecisePrevision_mix
    [Fintype Ω] [MeasurableSingletonClass Ω]
    (t : ℝ) (P Q : BoundedMeasurablePrecisePrevision Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (mix t P Q ht0 ht1).toRawFinitePrecisePrevision =
      PrecisePrevision.mix t P.toRawFinitePrecisePrevision
        Q.toRawFinitePrecisePrevision ht0 ht1 := by
  ext X
  rfl

/-- The canonical finite raw extension restricts back to the original
bounded-measurable precise prevision. -/
@[simp] theorem restrictBoundedMeasurable_toRawFinitePrecisePrevision
    [Fintype Ω] [MeasurableSingletonClass Ω]
    (P : BoundedMeasurablePrecisePrevision Ω) :
    P.toRawFinitePrecisePrevision.restrictBoundedMeasurable = P := by
  ext X
  change P (BoundedMeasurableGamble.ofFinite X.toGamble) = P X
  congr 1

/-- Finite measurable carriers support a raw precise prevision extension for
every bounded-measurable precise prevision. -/
theorem exists_rawFinitePrecisePrevision_extending
    [Fintype Ω] [MeasurableSingletonClass Ω]
    (P : BoundedMeasurablePrecisePrevision Ω) :
    ∃ Q : PrecisePrevision Ω, Q.restrictBoundedMeasurable = P :=
  ⟨P.toRawFinitePrecisePrevision,
    restrictBoundedMeasurable_toRawFinitePrecisePrevision P⟩

end BoundedMeasurablePrecisePrevision

/-! ### A raw-extension obstruction

The raw Walley carrier `Gamble Ω = Ω → ℝ` is intentionally larger than the
bounded-measurable carrier.  The following countable canary shows why a
σ-additive bounded-observable prevision cannot be blindly promoted to a
finite-valued precise prevision on all raw gambles: even the geometric law on
`ℕ` would force the unbounded gamble `n ↦ 2^(n+1)` to have expectation at least
every finite number.
-/

/-- Singleton indicator on `ℕ`, available without a finite state space. -/
def natAtomGamble (n : ℕ) : Gamble ℕ :=
  PrecisePrevision.FiniteWeights.atomGamble n

@[simp] theorem natAtomGamble_apply (n m : ℕ) :
    natAtomGamble n m = if m = n then (1 : ℝ) else 0 :=
  rfl

/-- The geometric singleton mass used by the raw-extension obstruction. -/
noncomputable def natGeometricSingletonWeight (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 1))⁻¹

/-- The unbounded gamble whose geometric expectation would have to be infinite. -/
noncomputable def natGeometricExplodingGamble : Gamble ℕ :=
  fun n => (2 : ℝ) ^ (n + 1)

/-- Finite partial sums of the exploding gamble over the first `N` atoms. -/
noncomputable def natGeometricPartialGamble (N : ℕ) : Gamble ℕ :=
  ∑ n ∈ Finset.range N,
    natGeometricExplodingGamble n • natAtomGamble n

theorem natGeometricExplodingGamble_pos (n : ℕ) :
    0 < natGeometricExplodingGamble n := by
  unfold natGeometricExplodingGamble
  positivity

theorem natGeometricPartialGamble_apply_of_mem
    {N m : ℕ} (hm : m ∈ Finset.range N) :
    natGeometricPartialGamble N m = natGeometricExplodingGamble m := by
  classical
  unfold natGeometricPartialGamble
  rw [PrecisePrevision.sum_gamble_apply]
  rw [Finset.sum_eq_single m]
  · change natGeometricExplodingGamble m *
        PrecisePrevision.FiniteWeights.atomGamble m m =
      natGeometricExplodingGamble m
    simp [PrecisePrevision.FiniteWeights.atomGamble]
  · intro n hn hnm
    have hmn : m ≠ n := by exact Ne.symm hnm
    change natGeometricExplodingGamble n *
        PrecisePrevision.FiniteWeights.atomGamble n m = 0
    simp [PrecisePrevision.FiniteWeights.atomGamble, hmn]
  · intro hnot
    exact (hnot hm).elim

theorem natGeometricPartialGamble_apply_of_not_mem
    {N m : ℕ} (hm : m ∉ Finset.range N) :
    natGeometricPartialGamble N m = 0 := by
  classical
  unfold natGeometricPartialGamble
  rw [PrecisePrevision.sum_gamble_apply]
  rw [Finset.sum_eq_zero]
  intro n hn
  have hmn : m ≠ n := by
    intro h
    exact hm (by simpa [h] using hn)
  change natGeometricExplodingGamble n *
      PrecisePrevision.FiniteWeights.atomGamble n m = 0
  simp [PrecisePrevision.FiniteWeights.atomGamble, hmn]

theorem natGeometricPartialGamble_le_exploding
    (N : ℕ) :
    ∀ m : ℕ, natGeometricPartialGamble N m ≤
      natGeometricExplodingGamble m := by
  intro m
  by_cases hm : m ∈ Finset.range N
  · rw [natGeometricPartialGamble_apply_of_mem hm]
  · rw [natGeometricPartialGamble_apply_of_not_mem hm]
    exact le_of_lt (natGeometricExplodingGamble_pos m)

theorem precisePrevision_natGeometricPartialGamble
    (P : PrecisePrevision ℕ)
    (hAtom : ∀ n : ℕ, P (natAtomGamble n) =
      natGeometricSingletonWeight n)
    (N : ℕ) :
    P (natGeometricPartialGamble N) = (N : ℝ) := by
  classical
  unfold natGeometricPartialGamble
  rw [P.map_sum]
  calc
    ∑ n ∈ Finset.range N,
        P (natGeometricExplodingGamble n • natAtomGamble n) =
      ∑ n ∈ Finset.range N,
        ((2 : ℝ) ^ (n + 1)) * natGeometricSingletonWeight n := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [P.map_smul, hAtom n]
        rfl
    _ = ∑ n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _hn
        unfold natGeometricSingletonWeight
        field_simp [pow_ne_zero (n := n + 1) (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (N : ℝ) := by
        simp

/-- No finite-valued raw precise prevision on all gambles over `ℕ` can extend
the ordinary geometric singleton probabilities.  This is the formal reason the
infinite σ-additive DLR/de Finetti carriers must live on bounded/measurable
observables unless an additional finite-additive extension assumption is made. -/
theorem no_rawPrecisePrevision_extends_natGeometricSingletonWeights :
    ¬ ∃ P : PrecisePrevision ℕ,
      ∀ n : ℕ, P (natAtomGamble n) =
        natGeometricSingletonWeight n := by
  rintro ⟨P, hAtom⟩
  let X : Gamble ℕ := natGeometricExplodingGamble
  have hLower : ∀ N : ℕ, (N : ℝ) ≤ P X := by
    intro N
    have hpartial :=
      precisePrevision_natGeometricPartialGamble P hAtom N
    have hmono :
        P (natGeometricPartialGamble N) ≤ P X :=
      P.mono (natGeometricPartialGamble_le_exploding N)
    rwa [hpartial] at hmono
  obtain ⟨N, hN⟩ := exists_nat_gt (P X)
  exact not_le_of_gt hN (hLower N)

/-! ## Lower envelopes of precise completions -/

/-- A credal set of precise prevision completions. -/
abbrev CredalPrevisionSet (Ω : Type*) := Set (PrecisePrevision Ω)

namespace CredalPrevisionSet

variable {Ω : Type*}

/-- Credal convexity for precise prevision sets.  This uses affine mixtures of
previsions rather than a global vector-space structure on normalized
previsions. -/
def IsConvex (C : CredalPrevisionSet Ω) : Prop :=
  ∀ ⦃P⦄, P ∈ C → ∀ ⦃Q⦄, Q ∈ C → ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
    PrecisePrevision.mix t P Q ht0 ht1 ∈ C

theorem isConvex_singleton (P : PrecisePrevision Ω) :
    IsConvex ({P} : CredalPrevisionSet Ω) := by
  intro Q hQ R hR t ht0 ht1
  have hQP : Q = P := by simpa using hQ
  have hRP : R = P := by simpa using hR
  subst Q
  subst R
  rw [Set.mem_singleton_iff]
  ext X
  dsimp [PrecisePrevision.mix]
  ring

theorem isConvex_univ :
    IsConvex (Set.univ : CredalPrevisionSet Ω) := by
  intro P hP Q hQ t ht0 ht1
  simp

theorem IsConvex.inter {C D : CredalPrevisionSet Ω}
    (hC : IsConvex C) (hD : IsConvex D) :
    IsConvex (C ∩ D) := by
  intro P hP Q hQ t ht0 ht1
  exact ⟨hC hP.1 hQ.1 t ht0 ht1, hD hP.2 hQ.2 t ht0 ht1⟩

/-- Restrict every raw precise completion in a credal set to bounded
measurable observables. -/
def restrictBoundedMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (C : CredalPrevisionSet Ω) :
    BoundedMeasurableCredalSet Ω :=
  {Q | ∃ P : PrecisePrevision Ω, P ∈ C ∧ P.restrictBoundedMeasurable = Q}

theorem restrictBoundedMeasurable_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {C : CredalPrevisionSet Ω}
    (hC : C.Nonempty) :
    (C.restrictBoundedMeasurable).Nonempty := by
  rcases hC with ⟨P, hP⟩
  exact ⟨P.restrictBoundedMeasurable, P, hP, rfl⟩

end CredalPrevisionSet

/-- The lower envelope of a credal set: Walley's conservative forced value. -/
noncomputable def lowerEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  sInf ((fun P : PrecisePrevision Ω => P X) '' C)

/-- The upper envelope, dual to the lower envelope. -/
noncomputable def upperEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  sSup ((fun P : PrecisePrevision Ω => P X) '' C)

/-- Restricting a raw credal set to bounded measurable observables preserves
the expectation-image of every bounded observable. -/
theorem boundedMeasurableCredalExpectationImage_restrictBoundedMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    ((fun P : BoundedMeasurablePrecisePrevision Ω => P X) ''
        C.restrictBoundedMeasurable) =
      ((fun P : PrecisePrevision Ω => P X.toGamble) '' C) := by
  ext y
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rcases hQ with ⟨P, hP, rfl⟩
    exact ⟨P, hP, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.restrictBoundedMeasurable, ⟨P, hP, rfl⟩, rfl⟩

/-- Raw Walley lower envelopes agree with bounded-measurable lower envelopes
after restricting the credal set to bounded observables. -/
theorem boundedMeasurableLowerEnvelope_restrictBoundedMeasurable_eq_lowerEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableLowerEnvelope C.restrictBoundedMeasurable X =
      lowerEnvelope C X.toGamble := by
  unfold boundedMeasurableLowerEnvelope lowerEnvelope
  rw [boundedMeasurableCredalExpectationImage_restrictBoundedMeasurable C X]

/-- Raw Walley upper envelopes agree with bounded-measurable upper envelopes
after restricting the credal set to bounded observables. -/
theorem boundedMeasurableUpperEnvelope_restrictBoundedMeasurable_eq_upperEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableUpperEnvelope C.restrictBoundedMeasurable X =
      upperEnvelope C X.toGamble := by
  unfold boundedMeasurableUpperEnvelope upperEnvelope
  rw [boundedMeasurableCredalExpectationImage_restrictBoundedMeasurable C X]

/-- Evaluation of a negated gamble negates the expectation-image set of a
credal set. -/
theorem credalExpectationImage_neg {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    ((fun P : PrecisePrevision Ω => P (-X)) '' C) =
      -((fun P : PrecisePrevision Ω => P X) '' C) := by
  ext y
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [Set.mem_neg]
    refine ⟨P, hP, ?_⟩
    simp [PrecisePrevision.map_neg]
  · intro hy
    rw [Set.mem_neg] at hy
    rcases hy with ⟨P, hP, hy⟩
    refine ⟨P, hP, ?_⟩
    simp [PrecisePrevision.map_neg, hy]

/-- Lower and upper envelopes are conjugate under gamble negation. -/
theorem lowerEnvelope_neg_eq_neg_upperEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    lowerEnvelope C (-X) = -upperEnvelope C X := by
  unfold lowerEnvelope upperEnvelope
  rw [credalExpectationImage_neg C X, Real.sInf_neg]

/-- Upper and lower envelopes are conjugate under gamble negation. -/
theorem upperEnvelope_neg_eq_neg_lowerEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    upperEnvelope C (-X) = -lowerEnvelope C X := by
  unfold lowerEnvelope upperEnvelope
  rw [credalExpectationImage_neg C X, Real.sSup_neg]

/-- Width of the lower/upper credal envelope on one gamble.  This is the
generic imprecision coordinate that PLN confidence-like displays compress. -/
noncomputable def credalEnvelopeWidth {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  upperEnvelope C X - lowerEnvelope C X

/-- Width complement of the credal envelope.  Under a width-complement
semantics this is the confidence-like display coordinate. -/
noncomputable def credalEnvelopeWidthComplement {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  1 - credalEnvelopeWidth C X

/-- Midpoint of the lower/upper credal envelope on one gamble.  This is the
generic point-estimate coordinate that PLN strength-like displays compress. -/
noncomputable def credalEnvelopeMidpoint {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  (lowerEnvelope C X + upperEnvelope C X) / 2

/-- If `Plo` and `Phi` attain the lower and upper endpoint of a gamble, then
the raw credal width is their expectation gap. -/
theorem credalEnvelopeWidth_eq_endpointGap
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (Plo Phi : PrecisePrevision Ω)
    (hlo : Plo X = lowerEnvelope C X)
    (hhi : Phi X = upperEnvelope C X) :
    credalEnvelopeWidth C X = Phi X - Plo X := by
  unfold credalEnvelopeWidth
  rw [← hlo, ← hhi]

/-- Endpoint-attainer form of the raw width-complement confidence coordinate. -/
theorem credalEnvelopeWidthComplement_eq_one_sub_endpointGap
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (Plo Phi : PrecisePrevision Ω)
    (hlo : Plo X = lowerEnvelope C X)
    (hhi : Phi X = upperEnvelope C X) :
    credalEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) := by
  unfold credalEnvelopeWidthComplement
  rw [credalEnvelopeWidth_eq_endpointGap C X Plo Phi hlo hhi]

/-- Endpoint-attainer form of the raw midpoint strength coordinate. -/
theorem credalEnvelopeMidpoint_eq_endpointMean
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (Plo Phi : PrecisePrevision Ω)
    (hlo : Plo X = lowerEnvelope C X)
    (hhi : Phi X = upperEnvelope C X) :
    credalEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  unfold credalEnvelopeMidpoint
  rw [← hlo, ← hhi]

/-- A full unit interval forces midpoint display strength to one half. -/
theorem credalEnvelopeMidpoint_eq_half_of_lower_eq_zero_upper_eq_one
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hL : lowerEnvelope C X = 0) (hU : upperEnvelope C X = 1) :
    credalEnvelopeMidpoint C X = (1 / 2 : ℝ) := by
  unfold credalEnvelopeMidpoint
  rw [hL, hU]
  ring

/-- A full unit interval has maximal credal width. -/
theorem credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hL : lowerEnvelope C X = 0) (hU : upperEnvelope C X = 1) :
    credalEnvelopeWidth C X = 1 := by
  unfold credalEnvelopeWidth
  rw [hL, hU]
  ring

/-- A full unit interval forces width-complement confidence to zero. -/
theorem credalEnvelopeWidthComplement_eq_zero_of_lower_eq_zero_upper_eq_one
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hL : lowerEnvelope C X = 0) (hU : upperEnvelope C X = 1) :
    credalEnvelopeWidthComplement C X = 0 := by
  unfold credalEnvelopeWidthComplement
  rw [credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one C X hL hU]
  ring

/-- Envelope width is preserved by the raw-to-bounded-measurable restriction. -/
theorem boundedMeasurableEnvelopeWidth_restrictBoundedMeasurable_eq_credalEnvelopeWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidth C.restrictBoundedMeasurable X =
      credalEnvelopeWidth C X.toGamble := by
  unfold boundedMeasurableEnvelopeWidth credalEnvelopeWidth
  rw [boundedMeasurableLowerEnvelope_restrictBoundedMeasurable_eq_lowerEnvelope,
    boundedMeasurableUpperEnvelope_restrictBoundedMeasurable_eq_upperEnvelope]

/-- Width-complement is preserved by the raw-to-bounded-measurable
restriction. -/
theorem boundedMeasurableEnvelopeWidthComplement_restrictBoundedMeasurable_eq_credalEnvelopeWidthComplement
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeWidthComplement C.restrictBoundedMeasurable X =
      credalEnvelopeWidthComplement C X.toGamble := by
  unfold boundedMeasurableEnvelopeWidthComplement credalEnvelopeWidthComplement
  rw [boundedMeasurableEnvelopeWidth_restrictBoundedMeasurable_eq_credalEnvelopeWidth]

/-- Envelope midpoint is preserved by the raw-to-bounded-measurable
restriction. -/
theorem boundedMeasurableEnvelopeMidpoint_restrictBoundedMeasurable_eq_credalEnvelopeMidpoint
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableEnvelopeMidpoint C.restrictBoundedMeasurable X =
      credalEnvelopeMidpoint C X.toGamble := by
  unfold boundedMeasurableEnvelopeMidpoint credalEnvelopeMidpoint
  rw [boundedMeasurableLowerEnvelope_restrictBoundedMeasurable_eq_lowerEnvelope,
    boundedMeasurableUpperEnvelope_restrictBoundedMeasurable_eq_upperEnvelope]

theorem lowerEnvelope_le_of_mem {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hBdd : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C) :
    lowerEnvelope C X ≤ P X := by
  exact csInf_le hBdd ⟨P, hP, rfl⟩

theorem le_lowerEnvelope_of_forall_le {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : Gamble Ω) {a : ℝ}
    (ha : ∀ P : PrecisePrevision Ω, P ∈ C → a ≤ P X) :
    a ≤ lowerEnvelope C X := by
  unfold lowerEnvelope
  refine le_csInf ?_ ?_
  · rcases hC with ⟨P, hP⟩
    exact ⟨P X, ⟨P, hP, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact ha P hP

theorem upperEnvelope_le_of_forall_le {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : Gamble Ω) {a : ℝ}
    (ha : ∀ P : PrecisePrevision Ω, P ∈ C → P X ≤ a) :
    upperEnvelope C X ≤ a := by
  unfold upperEnvelope
  refine csSup_le ?_ ?_
  · rcases hC with ⟨P, hP⟩
    exact ⟨P X, ⟨P, hP, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact ha P hP

theorem le_upperEnvelope_of_mem {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hBdd : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C) :
    P X ≤ upperEnvelope C X := by
  exact le_csSup hBdd ⟨P, hP, rfl⟩

/-- Compact raw credal carriers attain their lower envelope whenever the
observable evaluation is continuous on the carrier. -/
theorem lowerEnvelope_exists_mem_eq_of_isCompact {Ω : Type*}
    [TopologicalSpace (PrecisePrevision Ω)]
    (C : CredalPrevisionSet Ω)
    (hCompact : IsCompact C) (hC : C.Nonempty)
    (X : Gamble Ω)
    (hCont : ContinuousOn (fun P : PrecisePrevision Ω => P X) C) :
    ∃ P : PrecisePrevision Ω, P ∈ C ∧ P X = lowerEnvelope C X := by
  rcases hCompact.exists_sInf_image_eq hC hCont with ⟨P, hP, hEq⟩
  exact ⟨P, hP, hEq.symm⟩

/-- Compact raw credal carriers attain their upper envelope whenever the
observable evaluation is continuous on the carrier. -/
theorem upperEnvelope_exists_mem_eq_of_isCompact {Ω : Type*}
    [TopologicalSpace (PrecisePrevision Ω)]
    (C : CredalPrevisionSet Ω)
    (hCompact : IsCompact C) (hC : C.Nonempty)
    (X : Gamble Ω)
    (hCont : ContinuousOn (fun P : PrecisePrevision Ω => P X) C) :
    ∃ P : PrecisePrevision Ω, P ∈ C ∧ P X = upperEnvelope C X := by
  rcases hCompact.exists_sSup_image_eq hC hCont with ⟨P, hP, hEq⟩
  exact ⟨P, hP, hEq.symm⟩

theorem upperEnvelope_upper_bound {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : Gamble Ω) (c : ℝ) (hc : ∀ ω, X ω ≤ c) :
    upperEnvelope C X ≤ c :=
  upperEnvelope_le_of_forall_le C hC X fun P _hP =>
    P.upper_bound X c hc

theorem upperEnvelope_pos_homog {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (r : ℝ) (X : Gamble Ω) (hr : 0 ≤ r) :
    upperEnvelope C (r • X) = r * upperEnvelope C X := by
  unfold upperEnvelope
  by_cases hr0 : r = 0
  · subst hr0
    simp only [zero_smul, zero_mul]
    have hset :
        ((fun P : PrecisePrevision Ω => P (0 : Gamble Ω)) '' C) =
          ({0} : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨P, _hP, rfl⟩
        exact P.map_zero
      · intro hy
        rcases hy with rfl
        rcases hC with ⟨P, hP⟩
        exact ⟨P, hP, P.map_zero⟩
    rw [hset, csSup_singleton]
  · have hset :
        ((fun P : PrecisePrevision Ω => P (r • X)) '' C) =
          r • ((fun P : PrecisePrevision Ω => P X) '' C) := by
      ext y
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact ⟨P X, ⟨P, hP, rfl⟩, by
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
      · rintro ⟨x, ⟨P, hP, hx⟩, hy⟩
        exact ⟨P, hP, by
          rw [← hy, ← hx]
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
    rw [hset, Real.sSup_smul_of_nonneg hr, smul_eq_mul]

theorem lowerEnvelope_le_upperEnvelope_of_nonempty {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C)) :
    lowerEnvelope C X ≤ upperEnvelope C X := by
  rcases hC with ⟨P, hP⟩
  exact (lowerEnvelope_le_of_mem C X hBddBelow hP).trans
    (le_upperEnvelope_of_mem C X hBddAbove hP)

theorem credalEnvelopeWidth_nonneg_of_nonempty {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C)) :
    0 ≤ credalEnvelopeWidth C X := by
  unfold credalEnvelopeWidth
  exact sub_nonneg.mpr
    (lowerEnvelope_le_upperEnvelope_of_nonempty C X hC hBddBelow hBddAbove)

theorem lowerEnvelope_in_unit_of_unit {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    lowerEnvelope C X ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_lowerEnvelope_of_forall_le C hC X fun P _hP =>
      P.lower_bound X 0 fun ω => (hX ω).1
  · rcases hC with ⟨P, hP⟩
    exact (lowerEnvelope_le_of_mem C X hBddBelow hP).trans
      (P.upper_bound X 1 fun ω => (hX ω).2)

theorem upperEnvelope_in_unit_of_unit {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    upperEnvelope C X ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rcases hC with ⟨P, hP⟩
    exact (P.lower_bound X 0 fun ω => (hX ω).1).trans
      (le_upperEnvelope_of_mem C X hBddAbove hP)
  · exact upperEnvelope_le_of_forall_le C hC X fun P _hP =>
      P.upper_bound X 1 fun ω => (hX ω).2

theorem credalEnvelopeWidth_le_one_of_unit {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    credalEnvelopeWidth C X ≤ 1 := by
  have hLower := lowerEnvelope_in_unit_of_unit C X hC hBddBelow hX
  have hUpper := upperEnvelope_in_unit_of_unit C X hC hBddAbove hX
  unfold credalEnvelopeWidth
  linarith [hLower.1, hUpper.2]

theorem credalEnvelopeWidth_in_unit_of_unit {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    credalEnvelopeWidth C X ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨credalEnvelopeWidth_nonneg_of_nonempty C X hC hBddBelow hBddAbove,
    credalEnvelopeWidth_le_one_of_unit C X hC hBddBelow hBddAbove hX⟩

theorem credalEnvelopeWidthComplement_in_unit_of_unit {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    credalEnvelopeWidthComplement C X ∈ Set.Icc (0 : ℝ) 1 := by
  have hWidth :=
    credalEnvelopeWidth_in_unit_of_unit C X hC hBddBelow hBddAbove hX
  unfold credalEnvelopeWidthComplement
  exact ⟨by linarith [hWidth.2], by linarith [hWidth.1]⟩

theorem credalEnvelopeMidpoint_in_unit_of_unit {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    credalEnvelopeMidpoint C X ∈ Set.Icc (0 : ℝ) 1 := by
  have hLower := lowerEnvelope_in_unit_of_unit C X hC hBddBelow hX
  have hUpper := upperEnvelope_in_unit_of_unit C X hC hBddAbove hX
  unfold credalEnvelopeMidpoint
  constructor <;> nlinarith [hLower.1, hLower.2, hUpper.1, hUpper.2]

/-- A credal set determines a gamble when every admissible precise completion
assigns the same expectation to it. -/
def credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : Prop :=
  ∀ P : PrecisePrevision Ω, P ∈ C →
    ∀ Q : PrecisePrevision Ω, Q ∈ C → P X = Q X

/-- A credal set has strict width on a gamble when two admissible precise
completions strictly disagree on it. -/
def credalSetHasStrictWidth {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : Prop :=
  ∃ P : PrecisePrevision Ω, P ∈ C ∧
    ∃ Q : PrecisePrevision Ω, Q ∈ C ∧ P X < Q X

/-- Compact raw strict width is witnessed by actual lower- and upper-endpoint
precise completions when observable evaluation is continuous on the carrier. -/
theorem credalEnvelope_exists_endpointPair_of_isCompact_strictWidth
    {Ω : Type*} [TopologicalSpace (PrecisePrevision Ω)]
    (C : CredalPrevisionSet Ω)
    (hCompact : IsCompact C) (hC : C.Nonempty)
    (X : Gamble Ω)
    (hCont : ContinuousOn (fun P : PrecisePrevision Ω => P X) C)
    (hWidth : credalSetHasStrictWidth C X) :
    ∃ Plo : PrecisePrevision Ω, Plo ∈ C ∧
      ∃ Phi : PrecisePrevision Ω, Phi ∈ C ∧
        Plo X = lowerEnvelope C X ∧
          Phi X = upperEnvelope C X ∧ Plo X < Phi X := by
  rcases lowerEnvelope_exists_mem_eq_of_isCompact
      C hCompact hC X hCont with
    ⟨Plo, hPlo, hlo⟩
  rcases upperEnvelope_exists_mem_eq_of_isCompact
      C hCompact hC X hCont with
    ⟨Phi, hPhi, hhi⟩
  have hImageCompact :
      IsCompact ((fun P : PrecisePrevision Ω => P X) '' C) :=
    hCompact.image_of_continuousOn hCont
  rcases hWidth with ⟨P, hP, Q, hQ, hPQ⟩
  have hlt : lowerEnvelope C X < upperEnvelope C X :=
    (lowerEnvelope_le_of_mem C X hImageCompact.bddBelow hP).trans_lt
      (hPQ.trans_le
        (le_upperEnvelope_of_mem C X hImageCompact.bddAbove hQ))
  refine ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, ?_⟩
  rw [hlo, hhi]
  exact hlt

/-- Compact raw strict width has endpoint witnesses whose values compute the
PLN-facing width, width-complement, and midpoint coordinates. -/
theorem credalEnvelope_exists_endpointPairReadout_of_isCompact_strictWidth
    {Ω : Type*} [TopologicalSpace (PrecisePrevision Ω)]
    (C : CredalPrevisionSet Ω)
    (hCompact : IsCompact C) (hC : C.Nonempty)
    (X : Gamble Ω)
    (hCont : ContinuousOn (fun P : PrecisePrevision Ω => P X) C)
    (hWidth : credalSetHasStrictWidth C X) :
    ∃ Plo : PrecisePrevision Ω, Plo ∈ C ∧
      ∃ Phi : PrecisePrevision Ω, Phi ∈ C ∧
        Plo X = lowerEnvelope C X ∧
        Phi X = upperEnvelope C X ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth C X = Phi X - Plo X ∧
        credalEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  rcases credalEnvelope_exists_endpointPair_of_isCompact_strictWidth
      C hCompact hC X hCont hWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt⟩
  exact ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt,
    credalEnvelopeWidth_eq_endpointGap C X Plo Phi hlo hhi,
    credalEnvelopeWidthComplement_eq_one_sub_endpointGap C X Plo Phi hlo hhi,
    credalEnvelopeMidpoint_eq_endpointMean C X Plo Phi hlo hhi⟩

/-- Finite-evaluation compact raw strict width has actual endpoint witnesses
whose values compute the PLN-facing width, width-complement, and midpoint. -/
theorem credalEnvelope_exists_endpointPairReadout_of_finiteEvaluationCompact_strictWidth
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (C : CredalPrevisionSet Ω)
    (hCompact : @IsCompact (PrecisePrevision Ω)
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : Gamble Ω)
    (hWidth : credalSetHasStrictWidth C X) :
    ∃ Plo : PrecisePrevision Ω, Plo ∈ C ∧
      ∃ Phi : PrecisePrevision Ω, Phi ∈ C ∧
        Plo X = lowerEnvelope C X ∧
        Phi X = upperEnvelope C X ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth C X = Phi X - Plo X ∧
        credalEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  letI : TopologicalSpace (PrecisePrevision Ω) :=
    PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Ω)
  exact credalEnvelope_exists_endpointPairReadout_of_isCompact_strictWidth
    C hCompact hC X
    ((PrecisePrevision.FiniteWeights.eval_continuous X).continuousOn)
    hWidth

/-- Finite-evaluation closed raw strict width has attained endpoints whose
values compute the PLN-facing width, width-complement, and midpoint. -/
theorem credalEnvelope_exists_endpointPairReadout_of_finiteEvaluationClosed_strictWidth
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (C : CredalPrevisionSet Ω)
    (hClosed : @IsClosed (PrecisePrevision Ω)
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : Gamble Ω)
    (hWidth : credalSetHasStrictWidth C X) :
    ∃ Plo : PrecisePrevision Ω, Plo ∈ C ∧
      ∃ Phi : PrecisePrevision Ω, Phi ∈ C ∧
        Plo X = lowerEnvelope C X ∧
        Phi X = upperEnvelope C X ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth C X = Phi X - Plo X ∧
        credalEnvelopeWidthComplement C X = 1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint C X = (Plo X + Phi X) / 2 := by
  exact credalEnvelope_exists_endpointPairReadout_of_finiteEvaluationCompact_strictWidth
    C
    (PrecisePrevision.FiniteWeights.finiteEvaluationTopology_isCompact_of_isClosed
      C hClosed)
    hC X hWidth

theorem credalSetDetermines_of_subsingleton {Ω : Type*}
    {C : CredalPrevisionSet Ω} {X : Gamble Ω}
    (h : ∀ P : PrecisePrevision Ω, P ∈ C →
      ∀ Q : PrecisePrevision Ω, Q ∈ C → P = Q) :
    credalSetDetermines C X := by
  intro P hP Q hQ
  rw [h P hP Q hQ]

theorem credalSetDetermines_singleton {Ω : Type*}
    (P : PrecisePrevision Ω) (X : Gamble Ω) :
    credalSetDetermines ({P} : CredalPrevisionSet Ω) X := by
  intro Q hQ R hR
  have hQP : Q = P := by simpa using hQ
  have hRP : R = P := by simpa using hR
  rw [hQP, hRP]

theorem lowerEnvelope_eq_of_credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C)
    (hDet : credalSetDetermines C X) :
    lowerEnvelope C X = P X := by
  refine le_antisymm ?_ ?_
  · exact lowerEnvelope_le_of_mem C X hBddBelow hP
  · exact le_lowerEnvelope_of_forall_le C hC X fun Q hQ =>
      le_of_eq (hDet P hP Q hQ)

theorem upperEnvelope_eq_of_credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C)
    (hDet : credalSetDetermines C X) :
    upperEnvelope C X = P X := by
  refine le_antisymm ?_ ?_
  · exact upperEnvelope_le_of_forall_le C hC X fun Q hQ =>
      le_of_eq (hDet Q hQ P hP)
  · exact le_upperEnvelope_of_mem C X hBddAbove hP

theorem lower_eq_upperEnvelope_of_credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C)
    (hDet : credalSetDetermines C X) :
    lowerEnvelope C X = upperEnvelope C X := by
  rw [lowerEnvelope_eq_of_credalSetDetermines C X hC hBddBelow hP hDet,
    upperEnvelope_eq_of_credalSetDetermines C X hC hBddAbove hP hDet]

theorem credalEnvelopeWidth_eq_zero_of_credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C)
    (hDet : credalSetDetermines C X) :
    credalEnvelopeWidth C X = 0 := by
  have hEq :=
    lower_eq_upperEnvelope_of_credalSetDetermines C X hC hBddBelow
      hBddAbove hP hDet
  unfold credalEnvelopeWidth
  rw [hEq]
  ring

/-- If the credal set determines a gamble, the width-complement display
coordinate is maximal.  This is the abstract PLN-confidence reading of a
singleton interval. -/
theorem credalEnvelopeWidthComplement_eq_one_of_credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C)
    (hDet : credalSetDetermines C X) :
    credalEnvelopeWidthComplement C X = 1 := by
  unfold credalEnvelopeWidthComplement
  rw [credalEnvelopeWidth_eq_zero_of_credalSetDetermines
    C X hC hBddBelow hBddAbove hP hDet]
  ring

theorem credalEnvelopeMidpoint_eq_of_credalSetDetermines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hC : C.Nonempty)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C)
    (hDet : credalSetDetermines C X) :
    credalEnvelopeMidpoint C X = P X := by
  have hLower :=
    lowerEnvelope_eq_of_credalSetDetermines C X hC hBddBelow hP hDet
  have hUpper :=
    upperEnvelope_eq_of_credalSetDetermines C X hC hBddAbove hP hDet
  unfold credalEnvelopeMidpoint
  rw [hLower, hUpper]
  ring

theorem not_credalSetDetermines_of_strictWidth {Ω : Type*}
    {C : CredalPrevisionSet Ω} {X : Gamble Ω}
    (hWidth : credalSetHasStrictWidth C X) :
    ¬ credalSetDetermines C X := by
  intro hDet
  rcases hWidth with ⟨P, hP, Q, hQ, hPQ⟩
  have hEq := hDet P hP Q hQ
  exact (ne_of_lt hPQ) hEq

/-- Failure of determination exhibits strict width for ordinary precise-prevision
credal sets.  Since expectations are real-valued, two unequal completion values
can be oriented into a strict pair. -/
theorem credalSetHasStrictWidth_of_not_determines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hNotDet : ¬ credalSetDetermines C X) :
    credalSetHasStrictWidth C X := by
  classical
  by_contra hNoWidth
  apply hNotDet
  intro P hP Q hQ
  by_cases hlt : P X < Q X
  · exact False.elim (hNoWidth ⟨P, hP, Q, hQ, hlt⟩)
  · by_cases hgt : Q X < P X
    · exact False.elim (hNoWidth ⟨Q, hQ, P, hP, hgt⟩)
    · exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

/-- A precise-prevision credal set has strict width on a gamble exactly when it
does not determine that gamble. -/
theorem credalSetHasStrictWidth_iff_not_determines {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    credalSetHasStrictWidth C X ↔ ¬ credalSetDetermines C X := by
  constructor
  · exact not_credalSetDetermines_of_strictWidth
  · exact credalSetHasStrictWidth_of_not_determines C X

/-- Restricting raw precise completions to bounded measurable observables
preserves the determination predicate on every bounded observable. -/
theorem boundedMeasurableCredalSetDetermines_restrictBoundedMeasurable_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableCredalSetDetermines C.restrictBoundedMeasurable X ↔
      credalSetDetermines C X.toGamble := by
  constructor
  · intro hDet P hP Q hQ
    have hEq := hDet P.restrictBoundedMeasurable
      ⟨P, hP, rfl⟩ Q.restrictBoundedMeasurable ⟨Q, hQ, rfl⟩
    simpa using hEq
  · intro hDet P hP Q hQ
    rcases hP with ⟨P₀, hP₀, rfl⟩
    rcases hQ with ⟨Q₀, hQ₀, rfl⟩
    exact hDet P₀ hP₀ Q₀ hQ₀

/-- Restricting raw precise completions to bounded measurable observables
preserves strict credal width on every bounded observable. -/
theorem boundedMeasurableCredalSetHasStrictWidth_restrictBoundedMeasurable_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (X : BoundedMeasurableGamble Ω) :
    boundedMeasurableCredalSetHasStrictWidth C.restrictBoundedMeasurable X ↔
      credalSetHasStrictWidth C X.toGamble := by
  constructor
  · intro hWidth
    rcases hWidth with ⟨P, hP, Q, hQ, hlt⟩
    rcases hP with ⟨P₀, hP₀, rfl⟩
    rcases hQ with ⟨Q₀, hQ₀, rfl⟩
    exact ⟨P₀, hP₀, Q₀, hQ₀, hlt⟩
  · intro hWidth
    rcases hWidth with ⟨P, hP, Q, hQ, hlt⟩
    exact ⟨P.restrictBoundedMeasurable, ⟨P, hP, rfl⟩,
      Q.restrictBoundedMeasurable, ⟨Q, hQ, rfl⟩, hlt⟩

/-- Raw strict credal width on a bounded measurable observable has compact
bounded-measurable endpoint witnesses after restriction.  The endpoint values
compute the raw Walley interval, width-complement, and midpoint coordinates.

This is the shared bridge from raw finite-additive previsions to the compact
bounded-measurable carrier; DLR, de Finetti, and MLN specializations should use
this theorem rather than duplicating the restriction argument. -/
theorem boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_restrictBoundedMeasurable_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : credalSetHasStrictWidth C X.toGamble) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableCredalSetEvaluationClosure C.restrictBoundedMeasurable ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableCredalSetEvaluationClosure C.restrictBoundedMeasurable ∧
        Plo X = lowerEnvelope C X.toGamble ∧
        Phi X = upperEnvelope C X.toGamble ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth C X.toGamble = Phi X - Plo X ∧
        credalEnvelopeWidthComplement C X.toGamble = 1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint C X.toGamble = (Plo X + Phi X) / 2 := by
  have hCrestrict : C.restrictBoundedMeasurable.Nonempty :=
    CredalPrevisionSet.restrictBoundedMeasurable_nonempty hC
  have hWidthRestrict :
      boundedMeasurableCredalSetHasStrictWidth
        C.restrictBoundedMeasurable X :=
    (boundedMeasurableCredalSetHasStrictWidth_restrictBoundedMeasurable_iff
      C X).2 hWidth
  rcases boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_strictWidth
      C.restrictBoundedMeasurable hCrestrict X hWidthRestrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq,
      hWidthComplementEq, hMidpointEq⟩
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hlt, ?_, ?_, ?_⟩
  · rw [← boundedMeasurableLowerEnvelope_restrictBoundedMeasurable_eq_lowerEnvelope
      C X]
    exact hlo
  · rw [← boundedMeasurableUpperEnvelope_restrictBoundedMeasurable_eq_upperEnvelope
      C X]
    exact hhi
  · rw [← boundedMeasurableEnvelopeWidth_restrictBoundedMeasurable_eq_credalEnvelopeWidth
      C X]
    exact hWidthEq
  · rw [← boundedMeasurableEnvelopeWidthComplement_restrictBoundedMeasurable_eq_credalEnvelopeWidthComplement
      C X]
    exact hWidthComplementEq
  · rw [← boundedMeasurableEnvelopeMidpoint_restrictBoundedMeasurable_eq_credalEnvelopeMidpoint
      C X]
    exact hMidpointEq

/-- Raw strict credal width on a bounded measurable observable has Walley
dominating endpoint completions for the bounded-measurable natural extension
generated by restriction.  The endpoint values compute the raw finite-additive
lower/upper interval and its PLN-facing width, width-complement, and midpoint.

Use this as the shared target for concrete DLR, de Finetti, and MLN adapters
that start with raw precise previsions but read out bounded cylinder queries. -/
theorem boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_restrictBoundedMeasurable_of_strictWidth
    {Ω : Type*} [MeasurableSpace Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : BoundedMeasurableGamble Ω)
    (hWidth : credalSetHasStrictWidth C X.toGamble) :
    ∃ Plo : BoundedMeasurablePrecisePrevision Ω,
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            C.restrictBoundedMeasurable
            (CredalPrevisionSet.restrictBoundedMeasurable_nonempty hC)) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision Ω,
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
            (boundedMeasurableNaturalExtensionPrevision
              C.restrictBoundedMeasurable
              (CredalPrevisionSet.restrictBoundedMeasurable_nonempty hC)) ∧
        Plo X = lowerEnvelope C X.toGamble ∧
        Phi X = upperEnvelope C X.toGamble ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth C X.toGamble = Phi X - Plo X ∧
        credalEnvelopeWidthComplement C X.toGamble = 1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint C X.toGamble = (Plo X + Phi X) / 2 := by
  let hCrestrict : C.restrictBoundedMeasurable.Nonempty :=
    CredalPrevisionSet.restrictBoundedMeasurable_nonempty hC
  have hWidthRestrict :
      boundedMeasurableCredalSetHasStrictWidth
        C.restrictBoundedMeasurable X :=
    (boundedMeasurableCredalSetHasStrictWidth_restrictBoundedMeasurable_iff
      C X).2 hWidth
  rcases
      boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        C.restrictBoundedMeasurable hCrestrict X hWidthRestrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq,
      hWidthComplementEq, hMidpointEq⟩
  refine ⟨Plo, ?_, Phi, ?_, ?_, ?_, hlt, ?_, ?_, ?_⟩
  · simpa [hCrestrict] using hPlo
  · simpa [hCrestrict] using hPhi
  · rw [boundedMeasurableNaturalExtensionPrevision_apply] at hlo
    rw [← boundedMeasurableLowerEnvelope_restrictBoundedMeasurable_eq_lowerEnvelope
      C X]
    exact hlo
  · rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply] at hhi
    rw [← boundedMeasurableUpperEnvelope_restrictBoundedMeasurable_eq_upperEnvelope
      C X]
    exact hhi
  · rw [← boundedMeasurableEnvelopeWidth_restrictBoundedMeasurable_eq_credalEnvelopeWidth
      C X]
    exact hWidthEq
  · rw [← boundedMeasurableEnvelopeWidthComplement_restrictBoundedMeasurable_eq_credalEnvelopeWidthComplement
      C X]
    exact hWidthComplementEq
  · rw [← boundedMeasurableEnvelopeMidpoint_restrictBoundedMeasurable_eq_credalEnvelopeMidpoint
      C X]
    exact hMidpointEq

/-- If two precise completions in a credal set disagree on a gamble, the
lower/upper envelope is genuinely imprecise on that gamble.  This is the shared
Walley skeleton behind the MLN "phase transition creates imprecision" canary. -/
theorem lower_upperEnvelope_nontrivial_of_disagreement {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P Q : PrecisePrevision Ω} (hP : P ∈ C) (hQ : Q ∈ C)
    (hPQ : P X < Q X) :
    lowerEnvelope C X < upperEnvelope C X := by
  calc
    lowerEnvelope C X ≤ P X :=
      lowerEnvelope_le_of_mem C X hBddBelow hP
    _ < Q X := hPQ
    _ ≤ upperEnvelope C X :=
      le_upperEnvelope_of_mem C X hBddAbove hQ

theorem lower_upperEnvelope_nontrivial_of_strictWidth {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hWidth : credalSetHasStrictWidth C X) :
    lowerEnvelope C X < upperEnvelope C X := by
  rcases hWidth with ⟨P, hP, Q, hQ, hPQ⟩
  exact lower_upperEnvelope_nontrivial_of_disagreement
    C X hBddBelow hBddAbove hP hQ hPQ

theorem credalEnvelopeWidth_pos_of_strictWidth {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hWidth : credalSetHasStrictWidth C X) :
    0 < credalEnvelopeWidth C X := by
  have hlt :=
    lower_upperEnvelope_nontrivial_of_strictWidth C X hBddBelow hBddAbove
      hWidth
  unfold credalEnvelopeWidth
  linarith

/-- Strict credal width forces the width-complement display coordinate below
one.  This is the abstract PLN-confidence reading of genuine imprecision. -/
theorem credalEnvelopeWidthComplement_lt_one_of_strictWidth {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω)
    (hBddBelow : BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (hWidth : credalSetHasStrictWidth C X) :
    credalEnvelopeWidthComplement C X < 1 := by
  have hpos := credalEnvelopeWidth_pos_of_strictWidth
    C X hBddBelow hBddAbove hWidth
  unfold credalEnvelopeWidthComplement
  linarith

theorem lowerEnvelope_lower_bound {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : Gamble Ω) (c : ℝ) (hc : ∀ ω, c ≤ X ω) :
    c ≤ lowerEnvelope C X :=
  le_lowerEnvelope_of_forall_le C hC X fun P _hP =>
    P.lower_bound X c hc

theorem lowerEnvelope_pos_homog {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (r : ℝ) (X : Gamble Ω) (hr : 0 ≤ r) :
    lowerEnvelope C (r • X) = r * lowerEnvelope C X := by
  unfold lowerEnvelope
  by_cases hr0 : r = 0
  · subst hr0
    simp only [zero_smul, zero_mul]
    have hset :
        ((fun P : PrecisePrevision Ω => P (0 : Gamble Ω)) '' C) =
          ({0} : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact P.map_zero
      · intro hy
        rcases hy with rfl
        rcases hC with ⟨P, hP⟩
        exact ⟨P, hP, P.map_zero⟩
    rw [hset, csInf_singleton]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hset :
        ((fun P : PrecisePrevision Ω => P (r • X)) '' C) =
          r • ((fun P : PrecisePrevision Ω => P X) '' C) := by
      ext y
      constructor
      · rintro ⟨P, hP, rfl⟩
        exact ⟨P X, ⟨P, hP, rfl⟩, by
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
      · rintro ⟨x, ⟨P, hP, hx⟩, hy⟩
        exact ⟨P, hP, by
          rw [← hy, ← hx]
          simp [smul_eq_mul, P.pos_homog r X hr]⟩
    rw [hset, Real.sInf_smul_of_nonneg hr, smul_eq_mul]

theorem lowerEnvelope_superadditive {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (X Y : Gamble Ω) :
    lowerEnvelope C X + lowerEnvelope C Y ≤ lowerEnvelope C (X + Y) := by
  apply le_lowerEnvelope_of_forall_le C hC
  intro P hP
  rw [P.add X Y]
  exact add_le_add
    (lowerEnvelope_le_of_mem C X (hBdd X) hP)
    (lowerEnvelope_le_of_mem C Y (hBdd Y) hP)

theorem upperEnvelope_subadditive {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (X Y : Gamble Ω) :
    upperEnvelope C (X + Y) ≤ upperEnvelope C X + upperEnvelope C Y := by
  apply upperEnvelope_le_of_forall_le C hC
  intro P hP
  rw [P.add X Y]
  exact add_le_add
    (le_upperEnvelope_of_mem C X (hBdd X) hP)
    (le_upperEnvelope_of_mem C Y (hBdd Y) hP)

/-- The lower envelope of a nonempty bounded-below set of precise completions
is a coherent lower prevision. -/
noncomputable def lowerEnvelopePrevision {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)) :
    LowerPrevision Ω where
  toFun := lowerEnvelope C
  lower_bound := lowerEnvelope_lower_bound C hC
  pos_homog := lowerEnvelope_pos_homog C hC
  superadd := lowerEnvelope_superadditive C hC hBdd

@[simp] theorem lowerEnvelopePrevision_apply {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC hBdd) (X : Gamble Ω) :
    lowerEnvelopePrevision C hC hBdd X = lowerEnvelope C X :=
  rfl

/-- The upper envelope of a nonempty bounded-above set of precise completions
is a coherent upper prevision. -/
noncomputable def upperEnvelopePrevision {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddAbove ((fun P : PrecisePrevision Ω => P X) '' C)) :
    UpperPrevision Ω where
  toFun := upperEnvelope C
  upper_bound := upperEnvelope_upper_bound C hC
  pos_homog := upperEnvelope_pos_homog C hC
  subadditive := upperEnvelope_subadditive C hC hBdd

@[simp] theorem upperEnvelopePrevision_apply {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC hBdd) (X : Gamble Ω) :
    upperEnvelopePrevision C hC hBdd X = upperEnvelope C X :=
  rfl

/-- The conjugate upper prevision of the lower-envelope prevision is exactly
the credal upper envelope. -/
theorem lowerEnvelopePrevision_conjugate_eq_upperEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (X : Gamble Ω) :
    (lowerEnvelopePrevision C hC hBdd).conjugate X = upperEnvelope C X := by
  dsimp [LowerPrevision.conjugate]
  rw [lowerEnvelope_neg_eq_neg_upperEnvelope C X]
  ring

/-- The conjugate lower prevision of the upper-envelope prevision is exactly
the credal lower envelope. -/
theorem upperEnvelopePrevision_conjugate_eq_lowerEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (X : Gamble Ω) :
    (upperEnvelopePrevision C hC hBdd).conjugate X = lowerEnvelope C X := by
  dsimp [UpperPrevision.conjugate]
  rw [upperEnvelope_neg_eq_neg_lowerEnvelope C X]
  ring

/-- The lower-envelope prevision is below every precise completion in the
credal set. -/
theorem lowerEnvelopePrevision_le_completion {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C) (X : Gamble Ω) :
    lowerEnvelopePrevision C hC hBdd X ≤ P X :=
  lowerEnvelope_le_of_mem C X (hBdd X) hP

/-- The lower-envelope prevision is the greatest lower prevision that is
pointwise dominated by every precise completion in the credal set. -/
theorem lowerEnvelopePrevision_greatest_lower_bound {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (L : LowerPrevision Ω)
    (hL : ∀ P : PrecisePrevision Ω, P ∈ C →
      ∀ X : Gamble Ω, L X ≤ P X)
    (X : Gamble Ω) :
    L X ≤ lowerEnvelopePrevision C hC hBdd X :=
  le_lowerEnvelope_of_forall_le C hC X fun P hP => hL P hP X

/-- Every precise completion in the credal set is below the upper-envelope
prevision. -/
theorem completion_le_upperEnvelopePrevision {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    {P : PrecisePrevision Ω} (hP : P ∈ C) (X : Gamble Ω) :
    P X ≤ upperEnvelopePrevision C hC hBdd X :=
  le_upperEnvelope_of_mem C X (hBdd X) hP

/-- The upper-envelope prevision is the least upper prevision that pointwise
dominates every precise completion in the credal set. -/
theorem upperEnvelopePrevision_least_upper_bound {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
    (U : UpperPrevision Ω)
    (hU : ∀ P : PrecisePrevision Ω, P ∈ C →
      ∀ X : Gamble Ω, P X ≤ U X)
    (X : Gamble Ω) :
    upperEnvelopePrevision C hC hBdd X ≤ U X :=
  upperEnvelope_le_of_forall_le C hC X fun P hP => hU P hP X

theorem finite_gamble_uniformLowerBound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Gamble Ω) :
    ∃ c : ℝ, ∀ ω, c ≤ X ω := by
  classical
  let values : Finset ℝ := Finset.univ.image X
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  have hvalues : values.Nonempty := by
    refine ⟨X ω₀, ?_⟩
    exact Finset.mem_image.mpr ⟨ω₀, Finset.mem_univ ω₀, rfl⟩
  refine ⟨values.min' hvalues, ?_⟩
  intro ω
  exact Finset.min'_le values (X ω)
    (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩)

theorem finite_gamble_uniformUpperBound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Gamble Ω) :
    ∃ c : ℝ, ∀ ω, X ω ≤ c := by
  classical
  let values : Finset ℝ := Finset.univ.image X
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  have hvalues : values.Nonempty := by
    refine ⟨X ω₀, ?_⟩
    exact Finset.mem_image.mpr ⟨ω₀, Finset.mem_univ ω₀, rfl⟩
  refine ⟨values.max' hvalues, ?_⟩
  intro ω
  exact Finset.le_max' values (X ω)
    (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩)

/-- Finite gambles make every credal expectation range bounded below, because
each precise completion is monotone and every finite gamble has a minimum. -/
theorem finite_credalRange_bddBelow
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    BddBelow ((fun P : PrecisePrevision Ω => P X) '' C) := by
  rcases finite_gamble_uniformLowerBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.lower_bound X c hc

/-- Finite gambles make every credal expectation range bounded above, because
each precise completion is monotone and every finite gamble has a maximum. -/
theorem finite_credalRange_bddAbove
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    BddAbove ((fun P : PrecisePrevision Ω => P X) '' C) := by
  rcases finite_gamble_uniformUpperBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.upper_bound X c hc

/-- Finite natural extension: over a finite nonempty state space, boundedness
of all credal expectation ranges is automatic. -/
noncomputable def finiteLowerEnvelopePrevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) :
    LowerPrevision Ω :=
  lowerEnvelopePrevision C hC (finite_credalRange_bddBelow C)

/-- Finite upper envelope: over a finite nonempty state space, boundedness of
all credal expectation ranges is automatic. -/
noncomputable def finiteUpperEnvelopePrevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) :
    UpperPrevision Ω :=
  upperEnvelopePrevision C hC (finite_credalRange_bddAbove C)

@[simp] theorem finiteLowerEnvelopePrevision_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) (X : Gamble Ω) :
    finiteLowerEnvelopePrevision C hC X = lowerEnvelope C X :=
  rfl

@[simp] theorem finiteUpperEnvelopePrevision_apply
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) (X : Gamble Ω) :
    finiteUpperEnvelopePrevision C hC X = upperEnvelope C X :=
  rfl

/-- The finite lower-envelope prevision is below every precise completion in
the credal set. -/
theorem finiteLowerEnvelopePrevision_le_completion
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    {P : PrecisePrevision Ω} (hP : P ∈ C) (X : Gamble Ω) :
    finiteLowerEnvelopePrevision C hC X ≤ P X :=
  lowerEnvelopePrevision_le_completion C hC
    (finite_credalRange_bddBelow C) hP X

/-- On a finite state space, the lower envelope is automatically the greatest
lower prevision dominated by all precise completions in the credal set. -/
theorem finiteLowerEnvelopePrevision_greatest_lower_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (L : LowerPrevision Ω)
    (hL : ∀ P : PrecisePrevision Ω, P ∈ C →
      ∀ X : Gamble Ω, L X ≤ P X)
    (X : Gamble Ω) :
    L X ≤ finiteLowerEnvelopePrevision C hC X :=
  lowerEnvelopePrevision_greatest_lower_bound C hC
    (finite_credalRange_bddBelow C) L hL X

/-- Every precise completion in a finite credal set is below the finite
upper-envelope prevision. -/
theorem finiteCompletion_le_upperEnvelopePrevision
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    {P : PrecisePrevision Ω} (hP : P ∈ C) (X : Gamble Ω) :
    P X ≤ finiteUpperEnvelopePrevision C hC X :=
  completion_le_upperEnvelopePrevision C hC
    (finite_credalRange_bddAbove C) hP X

/-- On a finite state space, the upper envelope is automatically the least
upper prevision dominating all precise completions in the credal set. -/
theorem finiteUpperEnvelopePrevision_least_upper_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (U : UpperPrevision Ω)
    (hU : ∀ P : PrecisePrevision Ω, P ∈ C →
      ∀ X : Gamble Ω, P X ≤ U X)
    (X : Gamble Ω) :
    finiteUpperEnvelopePrevision C hC X ≤ U X :=
  upperEnvelopePrevision_least_upper_bound C hC
    (finite_credalRange_bddAbove C) U hU X

/-- Any lower-envelope prevision avoids uniform sure loss.  This is the
infinite-domain-safe no-arbitrage statement: if a gamble is bounded below by a
positive margin, then its lower envelope is strictly positive.  Full
pointwise-strict avoiding sure loss is only automatic in finite/noncompact
settings with a uniform lower-bound theorem. -/
theorem lowerEnvelopePrevision_avoidsUniformSureLoss
    {Ω : Type*}
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)) :
    (lowerEnvelopePrevision C hC hBdd).avoidsUniformSureLoss :=
  LowerPrevision.avoidsUniformSureLoss_of_lower_bound
    (lowerEnvelopePrevision C hC hBdd)

/-- On a finite nonempty state space, a nonempty lower envelope of precise
previsions avoids Walley's strict sure loss.  The finite hypothesis supplies a
uniform positive lower bound for every pointwise-strictly-positive gamble. -/
theorem lowerEnvelopePrevision_avoidsSureLoss_of_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)) :
    (lowerEnvelopePrevision C hC hBdd).avoidsSureLoss :=
  LowerPrevision.avoidsSureLoss_of_finite
    (lowerEnvelopePrevision C hC hBdd)

theorem finiteLowerEnvelopePrevision_avoidsSureLoss
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) :
    (finiteLowerEnvelopePrevision C hC).avoidsSureLoss :=
  lowerEnvelopePrevision_avoidsSureLoss_of_finite C hC
    (finite_credalRange_bddBelow C)

/-- Finite nonempty lower envelopes are coherent in the Walley sense used by
the base imprecise-probability layer. -/
theorem lowerEnvelopePrevision_isCoherent_of_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)) :
    (lowerEnvelopePrevision C hC hBdd).isCoherent :=
  LowerPrevision.isCoherent_of_finite
    (lowerEnvelopePrevision C hC hBdd)

theorem finiteLowerEnvelopePrevision_isCoherent
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) :
    (finiteLowerEnvelopePrevision C hC).isCoherent :=
  lowerEnvelopePrevision_isCoherent_of_finite C hC
    (finite_credalRange_bddBelow C)

/-! ### Dominating precise completions

Walley's envelope theorem says that a coherent lower prevision is the lower
envelope of its dominating precise previsions.  The theorem below uses the
algebraic Hahn-Banach theorem already imported by the imprecise-probability base:
for each gamble, there is a dominating precise prevision touching the lower
prevision at that gamble.
-/

/-- The precise completions that dominate a lower prevision pointwise.  This is
the canonical credal-set target in Walley's envelope theorem. -/
def dominatingPreciseCompletions {Ω : Type*}
    (L : LowerPrevision Ω) : CredalPrevisionSet Ω :=
  {P | ∀ X : Gamble Ω, L X ≤ P X}

@[simp] theorem mem_dominatingPreciseCompletions {Ω : Type*}
    (L : LowerPrevision Ω) (P : PrecisePrevision Ω) :
    P ∈ dominatingPreciseCompletions L ↔
      ∀ X : Gamble Ω, L X ≤ P X :=
  Iff.rfl

/-- Dominating precise completions form a convex credal set.  This is the
finite-additive Walley representation side: mixtures of completions that
dominate a lower prevision still dominate it pointwise. -/
theorem dominatingPreciseCompletions_isConvex {Ω : Type*}
    (L : LowerPrevision Ω) :
    CredalPrevisionSet.IsConvex (dominatingPreciseCompletions L) := by
  intro P hP Q hQ t ht0 ht1 X
  dsimp [PrecisePrevision.mix]
  have hP' : L X ≤ P X := hP X
  have hQ' : L X ≤ Q X := hQ X
  have h1t : 0 ≤ 1 - t := by linarith
  nlinarith

/-- The dominating completion values on any gamble are bounded below by the
lower prevision's value on that gamble. -/
theorem dominatingPreciseCompletions_bddBelow {Ω : Type*}
    (L : LowerPrevision Ω) (X : Gamble Ω) :
    BddBelow
      ((fun P : PrecisePrevision Ω => P X) ''
        dominatingPreciseCompletions L) := by
  refine ⟨L X, ?_⟩
  rintro y ⟨P, hP, rfl⟩
  exact hP X

/-- If the dominating precise-completion set is inhabited, its lower envelope is
pointwise above the original lower prevision. -/
theorem lowerPrevision_le_lowerEnvelope_dominatingPreciseCompletions
    {Ω : Type*} (L : LowerPrevision Ω)
    (hD : (dominatingPreciseCompletions L).Nonempty)
    (X : Gamble Ω) :
    L X ≤ lowerEnvelope (dominatingPreciseCompletions L) X :=
  le_lowerEnvelope_of_forall_le (dominatingPreciseCompletions L) hD X
    fun _P hP => hP X

/-- The packaged lower envelope over dominating precise completions also lies
above the original lower prevision. -/
theorem lowerPrevision_le_lowerEnvelopePrevision_dominatingPreciseCompletions
    {Ω : Type*} (L : LowerPrevision Ω)
    (hD : (dominatingPreciseCompletions L).Nonempty)
    (X : Gamble Ω) :
    L X ≤
      lowerEnvelopePrevision (dominatingPreciseCompletions L) hD
        (dominatingPreciseCompletions_bddBelow L) X :=
  lowerPrevision_le_lowerEnvelope_dominatingPreciseCompletions L hD X

/-- Hahn-Banach touching completion: every lower prevision has, for each gamble
`X`, a precise prevision that dominates it pointwise and agrees with it on `X`.

This is the algebraic separation/completion theorem behind the lower-envelope
representation.  It is finite-additive/functional; σ-additive measure
representations remain a separate refinement. -/
theorem exists_dominatingPreciseCompletion_touching
    {Ω : Type*} (L : LowerPrevision Ω) (X : Gamble Ω) :
    ∃ P : PrecisePrevision Ω,
      P ∈ dominatingPreciseCompletions L ∧ P X = L X := by
  classical
  have hKernel :
      ∀ c : ℝ, c • X = 0 → c • (L X : ℝ) = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · have hXzero : X = 0 := by
        funext ω
        have hω := congr_fun hc ω
        change c * X ω = 0 at hω
        exact (mul_eq_zero.mp hω).resolve_left hc0
      rw [hXzero, L.map_zero]
      simp
  let f : Gamble Ω →ₗ.[ℝ] ℝ :=
    LinearPMap.mkSpanSingleton' X (L X) hKernel
  have hSublinearHom :
      ∀ c : ℝ, 0 < c → ∀ Y : Gamble Ω,
        L.conjugate (c • Y) = c * L.conjugate Y := by
    intro c hc Y
    exact L.conjugate_pos_homog_of_nonneg (le_of_lt hc) Y
  have hSublinearAdd :
      ∀ Y Z : Gamble Ω,
        L.conjugate (Y + Z) ≤ L.conjugate Y + L.conjugate Z :=
    L.conjugate_subadditive
  have hf_le :
      ∀ z : f.domain, f z ≤ L.conjugate z := by
    intro z
    rcases z with ⟨Z, hZ⟩
    rcases Submodule.mem_span_singleton.mp hZ with ⟨c, rfl⟩
    change f ⟨c • X, _⟩ ≤ L.conjugate (c • X)
    rw [LinearPMap.mkSpanSingleton'_apply]
    change c * L X ≤ L.conjugate (c • X)
    by_cases hc : 0 ≤ c
    · rw [L.conjugate_pos_homog_of_nonneg hc X]
      exact mul_le_mul_of_nonneg_left (L.le_conjugate X) hc
    · have hcle : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
      rw [L.conjugate_smul_of_nonpos hcle X]
  rcases exists_extension_of_le_sublinear f L.conjugate
      hSublinearHom hSublinearAdd hf_le with
    ⟨g, hg_extends, hg_le_conjugate⟩
  have hDominates : ∀ Y : Gamble Ω, L Y ≤ g Y := by
    intro Y
    have h := hg_le_conjugate (-Y)
    have hg_neg : g (-Y) = -g Y := by
      simp
    rw [hg_neg, L.conjugate_neg Y] at h
    linarith
  let P : PrecisePrevision Ω :=
    { toFun := g
      lower_bound := by
        intro Y c hc
        exact (L.lower_bound Y c hc).trans (hDominates Y)
      pos_homog := by
        intro r Y _hr
        simp
      add := by
        intro Y Z
        exact g.map_add Y Z }
  have hXmem : X ∈ f.domain := by
    simp [f]
  have hgX := hg_extends ⟨X, hXmem⟩
  have hfX : f ⟨X, hXmem⟩ = L X := by
    exact LinearPMap.mkSpanSingleton'_apply_self X (L.toFun X) hKernel hXmem
  refine ⟨P, ?_, ?_⟩
  · intro Y
    exact hDominates Y
  · change g X = L X
    exact hgX.trans hfX

/-- A lower prevision has an exact dominating precise-envelope representation
when its dominating precise completions are nonempty and its value is exactly
their lower envelope on every gamble. -/
def hasExactDominatingPreciseEnvelope {Ω : Type*}
    (L : LowerPrevision Ω) : Prop :=
  (dominatingPreciseCompletions L).Nonempty ∧
    ∀ X : Gamble Ω,
      lowerEnvelope (dominatingPreciseCompletions L) X = L X

theorem hasExactDominatingPreciseEnvelope.nonempty {Ω : Type*}
    {L : LowerPrevision Ω}
    (h : hasExactDominatingPreciseEnvelope L) :
    (dominatingPreciseCompletions L).Nonempty :=
  h.1

theorem hasExactDominatingPreciseEnvelope.lowerEnvelope_eq {Ω : Type*}
    {L : LowerPrevision Ω}
    (h : hasExactDominatingPreciseEnvelope L) (X : Gamble Ω) :
    lowerEnvelope (dominatingPreciseCompletions L) X = L X :=
  h.2 X

/-- An exact dominating raw lower-envelope representation also recovers the
conjugate upper envelope over the same dominating completions. -/
theorem hasExactDominatingPreciseEnvelope.upperEnvelope_eq_conjugate
    {Ω : Type*} {L : LowerPrevision Ω}
    (h : hasExactDominatingPreciseEnvelope L) (X : Gamble Ω) :
    upperEnvelope (dominatingPreciseCompletions L) X = L.conjugate X := by
  let D : CredalPrevisionSet Ω := dominatingPreciseCompletions L
  have hneg : lowerEnvelope D (-X) = -upperEnvelope D X :=
    lowerEnvelope_neg_eq_neg_upperEnvelope D X
  have hLower : lowerEnvelope D (-X) = L (-X) :=
    h.lowerEnvelope_eq (-X)
  dsimp [LowerPrevision.conjugate]
  linarith

/-- Any exact dominating raw lower-envelope representation has a lower
touching completion for each gamble. -/
theorem hasExactDominatingPreciseEnvelope.exists_touching
    {Ω : Type*} {L : LowerPrevision Ω}
    (_h : hasExactDominatingPreciseEnvelope L) (X : Gamble Ω) :
    ∃ P : PrecisePrevision Ω,
      P ∈ dominatingPreciseCompletions L ∧ P X = L X :=
  exists_dominatingPreciseCompletion_touching L X

/-- Any exact dominating raw lower-envelope representation has an upper
touching completion for each gamble, where upper means the conjugate of the
lower prevision. -/
theorem hasExactDominatingPreciseEnvelope.exists_conjugate_touching
    {Ω : Type*} {L : LowerPrevision Ω}
    (_h : hasExactDominatingPreciseEnvelope L) (X : Gamble Ω) :
    ∃ P : PrecisePrevision Ω,
      P ∈ dominatingPreciseCompletions L ∧ P X = L.conjugate X := by
  rcases exists_dominatingPreciseCompletion_touching L (-X) with
    ⟨P, hP, hPX⟩
  refine ⟨P, hP, ?_⟩
  have hmap : P (-X) = -P X := P.map_neg X
  dsimp [LowerPrevision.conjugate]
  linarith

/-- Endpoint-pair readout for an exact dominating raw lower-envelope
representation.  The two precise completions may differ: one touches the lower
endpoint, the other touches the conjugate upper endpoint. -/
theorem hasExactDominatingPreciseEnvelope.exists_endpointPairReadout
    {Ω : Type*} {L : LowerPrevision Ω}
    (h : hasExactDominatingPreciseEnvelope L) (X : Gamble Ω) :
    ∃ Plo : PrecisePrevision Ω,
      Plo ∈ dominatingPreciseCompletions L ∧
      ∃ Phi : PrecisePrevision Ω,
        Phi ∈ dominatingPreciseCompletions L ∧
        Plo X = L X ∧
        Phi X = L.conjugate X ∧
        credalEnvelopeWidth (dominatingPreciseCompletions L) X =
          Phi X - Plo X ∧
        credalEnvelopeWidthComplement (dominatingPreciseCompletions L) X =
          1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint (dominatingPreciseCompletions L) X =
          (Plo X + Phi X) / 2 := by
  let D : CredalPrevisionSet Ω := dominatingPreciseCompletions L
  rcases h.exists_touching X with ⟨Plo, hPlo, hloL⟩
  rcases h.exists_conjugate_touching X with ⟨Phi, hPhi, hhiL⟩
  have hloD : Plo X = lowerEnvelope D X := by
    calc
      Plo X = L X := hloL
      _ = lowerEnvelope D X := by
        simpa [D] using (h.lowerEnvelope_eq X).symm
  have hhiD : Phi X = upperEnvelope D X := by
    calc
      Phi X = L.conjugate X := hhiL
      _ = upperEnvelope D X := by
        simpa [D] using (h.upperEnvelope_eq_conjugate X).symm
  refine ⟨Plo, hPlo, Phi, hPhi, hloL, hhiL, ?_, ?_, ?_⟩
  · exact credalEnvelopeWidth_eq_endpointGap D X Plo Phi hloD hhiD
  · exact credalEnvelopeWidthComplement_eq_one_sub_endpointGap
      D X Plo Phi hloD hhiD
  · exact credalEnvelopeMidpoint_eq_endpointMean D X Plo Phi hloD hhiD

/-- Strict endpoint-pair readout for an exact dominating raw lower-envelope
representation. -/
theorem hasExactDominatingPreciseEnvelope.exists_strictEndpointPairReadout
    {Ω : Type*} {L : LowerPrevision Ω}
    (h : hasExactDominatingPreciseEnvelope L) (X : Gamble Ω)
    (hStrict : L X < L.conjugate X) :
    ∃ Plo : PrecisePrevision Ω,
      Plo ∈ dominatingPreciseCompletions L ∧
      ∃ Phi : PrecisePrevision Ω,
        Phi ∈ dominatingPreciseCompletions L ∧
        Plo X = L X ∧
        Phi X = L.conjugate X ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth (dominatingPreciseCompletions L) X =
          Phi X - Plo X ∧
        credalEnvelopeWidthComplement (dominatingPreciseCompletions L) X =
          1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint (dominatingPreciseCompletions L) X =
          (Plo X + Phi X) / 2 := by
  rcases h.exists_endpointPairReadout X with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hWidth, hComp, hMid⟩
  have hlt : Plo X < Phi X := by
    rw [hlo, hhi]
    exact hStrict
  exact ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidth, hComp, hMid⟩

/-- Walley's lower-envelope representation theorem for the bundled algebraic
lower-prevision structure: every lower prevision is exactly the lower envelope
of all precise previsions that dominate it. -/
theorem lowerPrevision_hasExactDominatingPreciseEnvelope
    {Ω : Type*} (L : LowerPrevision Ω) :
    hasExactDominatingPreciseEnvelope L := by
  classical
  let D : CredalPrevisionSet Ω := dominatingPreciseCompletions L
  obtain ⟨P₀, hP₀, _hP₀⟩ :=
    exists_dominatingPreciseCompletion_touching L (0 : Gamble Ω)
  have hD : D.Nonempty := ⟨P₀, hP₀⟩
  refine ⟨hD, ?_⟩
  intro X
  obtain ⟨P, hP, hPX⟩ :=
    exists_dominatingPreciseCompletion_touching L X
  apply le_antisymm
  · calc
      lowerEnvelope D X ≤ P X :=
        lowerEnvelope_le_of_mem D X
          (dominatingPreciseCompletions_bddBelow L X) hP
      _ = L X := hPX
  · exact lowerPrevision_le_lowerEnvelope_dominatingPreciseCompletions L hD X

/-- The dominating precise-completion credal set of any bundled lower prevision
is inhabited. -/
theorem dominatingPreciseCompletions_nonempty
    {Ω : Type*} (L : LowerPrevision Ω) :
    (dominatingPreciseCompletions L).Nonempty :=
  (lowerPrevision_hasExactDominatingPreciseEnvelope L).nonempty

/-- Direct form of Walley's exact lower-envelope representation: a lower
prevision is the lower envelope of all precise previsions that dominate it. -/
theorem lowerEnvelope_dominatingPreciseCompletions_eq
    {Ω : Type*} (L : LowerPrevision Ω) (X : Gamble Ω) :
    lowerEnvelope (dominatingPreciseCompletions L) X = L X :=
  (lowerPrevision_hasExactDominatingPreciseEnvelope L).lowerEnvelope_eq X

/-- Packaged direct form of Walley's representation theorem: rebuilding a lower
prevision as the lower envelope of its dominating precise completions gives the
same lower prevision extensionally. -/
theorem lowerEnvelopePrevision_dominatingPreciseCompletions_eq
    {Ω : Type*} (L : LowerPrevision Ω) :
    lowerEnvelopePrevision (dominatingPreciseCompletions L)
        (dominatingPreciseCompletions_nonempty L)
        (dominatingPreciseCompletions_bddBelow L) = L := by
  ext X
  exact lowerEnvelope_dominatingPreciseCompletions_eq L X

/-- Every lower envelope is represented exactly by the lower envelope of all
precise completions that dominate it.  This is the lower-envelope specialization
of the general Hahn-Banach representation above. -/
theorem lowerEnvelopePrevision_hasExactDominatingPreciseEnvelope
    {Ω : Type*} (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)) :
    hasExactDominatingPreciseEnvelope
      (lowerEnvelopePrevision C hC hBdd) := by
  let L : LowerPrevision Ω := lowerEnvelopePrevision C hC hBdd
  let D : CredalPrevisionSet Ω := dominatingPreciseCompletions L
  have hD : D.Nonempty := by
    let P : PrecisePrevision Ω := Classical.choose hC
    have hP : P ∈ C := Classical.choose_spec hC
    refine ⟨P, ?_⟩
    intro X
    exact lowerEnvelopePrevision_le_completion C hC hBdd hP X
  refine ⟨hD, ?_⟩
  intro X
  have hle : lowerEnvelope D X ≤ lowerEnvelope C X := by
    unfold lowerEnvelope
    refine le_csInf ?_ ?_
    · rcases hC with ⟨P, hP⟩
      exact ⟨P X, ⟨P, hP, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨P, hP, rfl⟩
      have hPD : P ∈ D := by
        intro Y
        exact lowerEnvelopePrevision_le_completion C hC hBdd hP Y
      exact lowerEnvelope_le_of_mem D X
        (dominatingPreciseCompletions_bddBelow L X) hPD
  have hge : L X ≤ lowerEnvelope D X :=
    lowerPrevision_le_lowerEnvelope_dominatingPreciseCompletions L hD X
  change lowerEnvelope D X = lowerEnvelope C X
  exact le_antisymm hle hge

/-- Query-wise Walley completion for lower envelopes: for each gamble there is
a precise prevision dominating the packaged lower envelope and touching its
lower-envelope value at that gamble. -/
theorem lowerEnvelopePrevision_exists_dominatingPreciseCompletion_touching
    {Ω : Type*} (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (hBdd : ∀ X : Gamble Ω,
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
    (X : Gamble Ω) :
    ∃ P : PrecisePrevision Ω,
      P ∈ dominatingPreciseCompletions (lowerEnvelopePrevision C hC hBdd) ∧
        P X = lowerEnvelope C X := by
  simpa [lowerEnvelopePrevision] using
    exists_dominatingPreciseCompletion_touching
      (lowerEnvelopePrevision C hC hBdd) X

/-- Finite lower envelopes have an exact representation by all precise
completions that dominate them. -/
theorem finiteLowerEnvelopePrevision_hasExactDominatingPreciseEnvelope
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty) :
    hasExactDominatingPreciseEnvelope
      (finiteLowerEnvelopePrevision C hC) :=
  lowerEnvelopePrevision_hasExactDominatingPreciseEnvelope C hC
    (finite_credalRange_bddBelow C)

/-- Query-wise Walley completion for finite lower envelopes. -/
theorem finiteLowerEnvelopePrevision_exists_dominatingPreciseCompletion_touching
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (C : CredalPrevisionSet Ω) (hC : C.Nonempty)
    (X : Gamble Ω) :
    ∃ P : PrecisePrevision Ω,
      P ∈ dominatingPreciseCompletions (finiteLowerEnvelopePrevision C hC) ∧
        P X = lowerEnvelope C X := by
  simpa [finiteLowerEnvelopePrevision] using
    exists_dominatingPreciseCompletion_touching
      (finiteLowerEnvelopePrevision C hC) X

/-- On a finite state space, an exact dominating precise-envelope
representation implies Walley coherence.  The envelope hypothesis is not needed
for bundled finite lower previsions; it is retained here as the Walley-facing
bridge statement used by the projective profile. -/
theorem isCoherent_of_hasExactDominatingPreciseEnvelope_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (L : LowerPrevision Ω)
    (_hExact : hasExactDominatingPreciseEnvelope L) :
    L.isCoherent :=
  LowerPrevision.isCoherent_of_finite L

/-- Singleton credal sets collapse to their precise completion. -/
theorem lowerEnvelope_singleton {Ω : Type*}
    (P : PrecisePrevision Ω) (X : Gamble Ω) :
    lowerEnvelope ({P} : CredalPrevisionSet Ω) X = P X := by
  unfold lowerEnvelope
  have hset :
      ((fun Q : PrecisePrevision Ω => Q X) '' ({P} : Set (PrecisePrevision Ω))) =
        ({P X} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      have hQP : Q = P := by simpa using hQ
      simp [hQP]
    · intro hy
      have hy' : y = P X := by simpa using hy
      subst y
      exact ⟨P, rfl, rfl⟩
  rw [hset, csInf_singleton]

theorem upperEnvelope_singleton {Ω : Type*}
    (P : PrecisePrevision Ω) (X : Gamble Ω) :
    upperEnvelope ({P} : CredalPrevisionSet Ω) X = P X := by
  unfold upperEnvelope
  have hset :
      ((fun Q : PrecisePrevision Ω => Q X) '' ({P} : Set (PrecisePrevision Ω))) =
        ({P X} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      have hQP : Q = P := by simpa using hQ
      simp [hQP]
    · intro hy
      have hy' : y = P X := by simpa using hy
      subst y
      exact ⟨P, rfl, rfl⟩
  rw [hset, csSup_singleton]

/-! ## Concrete finite disagreement canary -/

/-- The two Dirac completions on `Bool`: a minimal credal set with two extreme
precise completions. -/
def boolDiracCredalSet : CredalPrevisionSet Bool :=
  {PrecisePrevision.dirac false, PrecisePrevision.dirac true}

/-- Indicator gamble for the `true` state. -/
def boolTrueGamble : Gamble Bool :=
  fun b => if b then 1 else 0

theorem boolDiracCredalSet_bddBelow :
    BddBelow ((fun P : PrecisePrevision Bool => P boolTrueGamble) ''
      boolDiracCredalSet) := by
  refine ⟨0, ?_⟩
  rintro y ⟨P, hP, rfl⟩
  simp [boolDiracCredalSet] at hP
  rcases hP with hP | hP
  · rw [hP]
    simp [boolTrueGamble]
  · rw [hP]
    simp [boolTrueGamble]

theorem boolDiracCredalSet_bddAbove :
    BddAbove ((fun P : PrecisePrevision Bool => P boolTrueGamble) ''
      boolDiracCredalSet) := by
  refine ⟨1, ?_⟩
  rintro y ⟨P, hP, rfl⟩
  simp [boolDiracCredalSet] at hP
  rcases hP with hP | hP
  · rw [hP]
    simp [boolTrueGamble]
  · rw [hP]
    simp [boolTrueGamble]

/-- The smallest concrete nontrivial-envelope witness: two Dirac completions
disagree on the `true` indicator, so the lower/upper envelope is strict. -/
theorem boolDiracCredalEnvelope_nontrivial :
    lowerEnvelope boolDiracCredalSet boolTrueGamble <
      upperEnvelope boolDiracCredalSet boolTrueGamble := by
  apply lower_upperEnvelope_nontrivial_of_disagreement
    (C := boolDiracCredalSet) (X := boolTrueGamble)
    boolDiracCredalSet_bddBelow boolDiracCredalSet_bddAbove
    (P := PrecisePrevision.dirac false) (Q := PrecisePrevision.dirac true)
  · simp [boolDiracCredalSet]
  · simp [boolDiracCredalSet]
  · simp [boolTrueGamble]

/-! ## Concrete two-spin magnet canary -/

/-- Two binary spins. -/
abbrev TwoSpin := Bool × Bool

def twoSpinAllDown : TwoSpin := (false, false)

def twoSpinAllUp : TwoSpin := (true, true)

/-- The two low-temperature magnet completions in the toy two-spin model:
all-down and all-up. -/
def twoSpinMagnetCredalSet : CredalPrevisionSet TwoSpin :=
  {PrecisePrevision.dirac twoSpinAllDown,
    PrecisePrevision.dirac twoSpinAllUp}

/-- A magnetization-style query: is the first spin up? -/
def twoSpinFirstUpGamble : Gamble TwoSpin :=
  fun σ => if σ.1 then 1 else 0

theorem twoSpinMagnetCredalSet_bddBelow :
    BddBelow ((fun P : PrecisePrevision TwoSpin => P twoSpinFirstUpGamble) ''
      twoSpinMagnetCredalSet) := by
  refine ⟨0, ?_⟩
  rintro y ⟨P, hP, rfl⟩
  simp [twoSpinMagnetCredalSet] at hP
  rcases hP with hP | hP
  · rw [hP]
    simp [twoSpinFirstUpGamble, twoSpinAllDown]
  · rw [hP]
    simp [twoSpinFirstUpGamble, twoSpinAllUp]

theorem twoSpinMagnetCredalSet_bddAbove :
    BddAbove ((fun P : PrecisePrevision TwoSpin => P twoSpinFirstUpGamble) ''
      twoSpinMagnetCredalSet) := by
  refine ⟨1, ?_⟩
  rintro y ⟨P, hP, rfl⟩
  simp [twoSpinMagnetCredalSet] at hP
  rcases hP with hP | hP
  · rw [hP]
    simp [twoSpinFirstUpGamble, twoSpinAllDown]
  · rw [hP]
    simp [twoSpinFirstUpGamble, twoSpinAllUp]

/-- Concrete magnet canary: two global completions with the same local
alignment story but opposite phase/magnetization split the lower and upper
envelopes.  This is not yet the full DLR/Ising phase-transition theorem; it is
the finite two-completion witness that the projective-credal envelope detects
spontaneous imprecision. -/
theorem twoSpinMagnetEnvelope_nontrivial :
    lowerEnvelope twoSpinMagnetCredalSet twoSpinFirstUpGamble <
      upperEnvelope twoSpinMagnetCredalSet twoSpinFirstUpGamble := by
  apply lower_upperEnvelope_nontrivial_of_disagreement
    (C := twoSpinMagnetCredalSet) (X := twoSpinFirstUpGamble)
    twoSpinMagnetCredalSet_bddBelow twoSpinMagnetCredalSet_bddAbove
    (P := PrecisePrevision.dirac twoSpinAllDown)
    (Q := PrecisePrevision.dirac twoSpinAllUp)
  · simp [twoSpinMagnetCredalSet]
  · simp [twoSpinMagnetCredalSet]
  · simp [twoSpinFirstUpGamble, twoSpinAllDown, twoSpinAllUp]

/-- Zero-temperature alignment constraint for the two-spin toy magnet. -/
def twoSpinAligned (σ : TwoSpin) : Prop :=
  σ.1 = σ.2

/-- Structural Gibbs-style magnet credal set: completions are supported only on
aligned spin states.  This is stronger than the two-explicit-completion canary
above, but still finite; the infinite DLR phase-transition theorem is separate. -/
def twoSpinZeroTemperatureAlignedCredalSet : CredalPrevisionSet TwoSpin :=
  {P | PrecisePrevision.supportedOn {σ | twoSpinAligned σ} P}

/-- The structural finite two-spin aligned credal set is closed in the finite
evaluation topology, because alignment support is an atomic zero-mass
constraint outside the aligned states. -/
theorem twoSpinZeroTemperatureAlignedCredalSet_isClosed :
    @IsClosed (PrecisePrevision TwoSpin)
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := TwoSpin))
      twoSpinZeroTemperatureAlignedCredalSet := by
  simpa [twoSpinZeroTemperatureAlignedCredalSet] using
    PrecisePrevision.supportedOn_isClosed
      (A := {σ : TwoSpin | twoSpinAligned σ})

theorem twoSpinZeroTemperatureAlignedCredalSet_bddBelow :
    BddBelow ((fun P : PrecisePrevision TwoSpin => P twoSpinFirstUpGamble) ''
      twoSpinZeroTemperatureAlignedCredalSet) := by
  refine ⟨0, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.lower_bound twoSpinFirstUpGamble 0 (by
    intro σ
    by_cases h : σ.1 <;> simp [twoSpinFirstUpGamble, h])

theorem twoSpinZeroTemperatureAlignedCredalSet_bddAbove :
    BddAbove ((fun P : PrecisePrevision TwoSpin => P twoSpinFirstUpGamble) ''
      twoSpinZeroTemperatureAlignedCredalSet) := by
  refine ⟨1, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.upper_bound twoSpinFirstUpGamble 1 (by
    intro σ
    by_cases h : σ.1 <;> simp [twoSpinFirstUpGamble, h])

/-- Finite Gibbs-style magnet canary: the zero-temperature alignment constraint
admits both all-down and all-up phases, and those phases split the lower and
upper envelope of a magnetization query. -/
theorem twoSpinZeroTemperatureMagnetEnvelope_nontrivial :
    lowerEnvelope twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble <
      upperEnvelope twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble := by
  apply lower_upperEnvelope_nontrivial_of_disagreement
    (C := twoSpinZeroTemperatureAlignedCredalSet) (X := twoSpinFirstUpGamble)
    twoSpinZeroTemperatureAlignedCredalSet_bddBelow
    twoSpinZeroTemperatureAlignedCredalSet_bddAbove
    (P := PrecisePrevision.dirac twoSpinAllDown)
    (Q := PrecisePrevision.dirac twoSpinAllUp)
  · exact PrecisePrevision.supportedOn_dirac (by
      simp [twoSpinAligned, twoSpinAllDown])
  · exact PrecisePrevision.supportedOn_dirac (by
      simp [twoSpinAligned, twoSpinAllUp])
  · simp [twoSpinFirstUpGamble, twoSpinAllDown, twoSpinAllUp]

/-- The zero-temperature aligned two-spin credal set has strict width on the
first-spin-up magnetization query. -/
theorem twoSpinZeroTemperatureAlignedCredalSet_hasStrictWidth :
    credalSetHasStrictWidth twoSpinZeroTemperatureAlignedCredalSet
      twoSpinFirstUpGamble := by
  refine ⟨PrecisePrevision.dirac twoSpinAllDown, ?_,
    PrecisePrevision.dirac twoSpinAllUp, ?_, ?_⟩
  · exact PrecisePrevision.supportedOn_dirac (by
      simp [twoSpinAligned, twoSpinAllDown])
  · exact PrecisePrevision.supportedOn_dirac (by
      simp [twoSpinAligned, twoSpinAllUp])
  · simp [twoSpinFirstUpGamble, twoSpinAllDown, twoSpinAllUp]

/-! ## Projective cylinder systems -/

/-- A projective cylinder system: finite/local windows have local state spaces,
and every local window has a projection from the global state.

The `restrict` and `project_restrict` fields are the local-to-local
compatibility square. -/
structure ProjectiveCylinderSystem.{u, v} (Window : Type u) (Global : Type v) [LE Window] where
  Local : Window → Type v
  project : ∀ i : Window, Global → Local i
  restrict : ∀ {i j : Window}, i ≤ j → Local j → Local i
  project_restrict :
    ∀ {i j : Window} (hij : i ≤ j) (ω : Global),
      restrict hij (project j ω) = project i ω

namespace ProjectiveCylinderSystem

variable {Window Global : Type*} [LE Window]

/-- Pull a local gamble back to a global cylinder gamble. -/
def cylinderGamble (S : ProjectiveCylinderSystem Window Global)
    (i : Window) (X : Gamble (S.Local i)) : Gamble Global :=
  fun ω => X (S.project i ω)

/-- Marginalize a global precise prevision to a local window by evaluating
cylinder gambles. -/
def marginalPrevision (S : ProjectiveCylinderSystem Window Global)
    (i : Window) (P : PrecisePrevision Global) :
    PrecisePrevision (S.Local i) where
  toFun X := P (S.cylinderGamble i X)
  lower_bound := by
    intro X c hc
    exact P.lower_bound (S.cylinderGamble i X) c fun ω => hc (S.project i ω)
  pos_homog := by
    intro r X hr
    exact P.pos_homog r (S.cylinderGamble i X) hr
  add := by
    intro X Y
    exact P.add (S.cylinderGamble i X) (S.cylinderGamble i Y)

@[simp] theorem marginalPrevision_apply
    (S : ProjectiveCylinderSystem Window Global)
    (i : Window) (P : PrecisePrevision Global) (X : Gamble (S.Local i)) :
    S.marginalPrevision i P X = P (S.cylinderGamble i X) :=
  rfl

theorem cylinderGamble_restrict
    (S : ProjectiveCylinderSystem Window Global)
    {i j : Window} (hij : i ≤ j) (X : Gamble (S.Local i)) :
    S.cylinderGamble j (fun xj => X (S.restrict hij xj)) =
      S.cylinderGamble i X := by
  funext ω
  simp [cylinderGamble, S.project_restrict hij ω]

theorem marginalPrevision_mix
    (S : ProjectiveCylinderSystem Window Global)
    (i : Window) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P Q : PrecisePrevision Global) :
    S.marginalPrevision i (PrecisePrevision.mix t P Q ht0 ht1) =
      PrecisePrevision.mix t (S.marginalPrevision i P)
        (S.marginalPrevision i Q) ht0 ht1 := by
  ext X
  rfl

/-! ### Cylinder-only previsions

The following structure is the restricted-domain completion object needed for
measure-theoretic projective systems: it evaluates only finite/local cylinder
gambles and records compatibility under restriction.  A full
`PrecisePrevision Global` induces such an object, but σ-additive measures can
also target this layer directly without pretending to evaluate arbitrary
nonmeasurable global gambles. -/

/-- A projectively compatible family of precise local previsions.  This is a
precise prevision on the cylinder domain of a projective system, not on all
global gambles. -/
structure CylinderPrevision
    (S : ProjectiveCylinderSystem Window Global) where
  toFun : ∀ i : Window, Gamble (S.Local i) → ℝ
  lower_bound :
    ∀ (i : Window) (X : Gamble (S.Local i)) (c : ℝ),
      (∀ x, c ≤ X x) → c ≤ toFun i X
  pos_homog :
    ∀ (i : Window) (r : ℝ) (X : Gamble (S.Local i)),
      0 ≤ r → toFun i (r • X) = r * toFun i X
  add :
    ∀ (i : Window) (X Y : Gamble (S.Local i)),
      toFun i (X + Y) = toFun i X + toFun i Y
  restrict_compat :
    ∀ {i j : Window} (hij : i ≤ j) (X : Gamble (S.Local i)),
      toFun j (fun xj => X (S.restrict hij xj)) = toFun i X

namespace CylinderPrevision

variable {S : ProjectiveCylinderSystem Window Global}

/-- The local precise prevision at a single window. -/
def localPrevision (K : S.CylinderPrevision) (i : Window) :
    PrecisePrevision (S.Local i) where
  toFun := K.toFun i
  lower_bound := K.lower_bound i
  pos_homog := K.pos_homog i
  add := K.add i

@[simp] theorem localPrevision_apply
    (K : S.CylinderPrevision) (i : Window)
    (X : Gamble (S.Local i)) :
    K.localPrevision i X = K.toFun i X :=
  rfl

theorem localPrevision_restrict
    (K : S.CylinderPrevision) {i j : Window}
    (hij : i ≤ j) (X : Gamble (S.Local i)) :
    K.localPrevision j (fun xj => X (S.restrict hij xj)) =
      K.localPrevision i X :=
  K.restrict_compat hij X

/-- Convex mixture of two compatible cylinder-domain precise previsions. -/
def mix (t : ℝ) (K L : S.CylinderPrevision)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : S.CylinderPrevision where
  toFun i X := t * K.toFun i X + (1 - t) * L.toFun i X
  lower_bound := by
    intro i X c hc
    have hK : c ≤ K.toFun i X := K.lower_bound i X c hc
    have hL : c ≤ L.toFun i X := L.lower_bound i X c hc
    have h1t : 0 ≤ 1 - t := by linarith
    nlinarith
  pos_homog := by
    intro i r X hr
    rw [K.pos_homog i r X hr, L.pos_homog i r X hr]
    ring
  add := by
    intro i X Y
    rw [K.add i X Y, L.add i X Y]
    ring
  restrict_compat := by
    intro i j hij X
    rw [K.restrict_compat hij X, L.restrict_compat hij X]

@[simp] theorem mix_apply
    (t : ℝ) (K L : S.CylinderPrevision)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Window) (X : Gamble (S.Local i)) :
    (mix t K L ht0 ht1).toFun i X =
      t * K.toFun i X + (1 - t) * L.toFun i X :=
  rfl

@[simp] theorem localPrevision_mix
    (t : ℝ) (K L : S.CylinderPrevision)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Window) :
    (mix t K L ht0 ht1).localPrevision i =
      PrecisePrevision.mix t (K.localPrevision i)
        (L.localPrevision i) ht0 ht1 := by
  ext X
  rfl

end CylinderPrevision

/-- A full global precise prevision restricts to a compatible cylinder
prevision by evaluating pulled-back cylinder gambles. -/
def cylinderPrevisionOfPrecisePrevision
    (S : ProjectiveCylinderSystem Window Global)
    (P : PrecisePrevision Global) : S.CylinderPrevision where
  toFun i X := P (S.cylinderGamble i X)
  lower_bound := by
    intro i X c hc
    exact P.lower_bound (S.cylinderGamble i X) c
      (fun ω => hc (S.project i ω))
  pos_homog := by
    intro i r X hr
    exact P.pos_homog r (S.cylinderGamble i X) hr
  add := by
    intro i X Y
    exact P.add (S.cylinderGamble i X) (S.cylinderGamble i Y)
  restrict_compat := by
    intro i j hij X
    change P (S.cylinderGamble j (fun xj => X (S.restrict hij xj))) =
      P (S.cylinderGamble i X)
    rw [S.cylinderGamble_restrict hij X]

@[simp] theorem cylinderPrevisionOfPrecisePrevision_localPrevision
    (S : ProjectiveCylinderSystem Window Global)
    (P : PrecisePrevision Global) (i : Window) :
    (S.cylinderPrevisionOfPrecisePrevision P).localPrevision i =
      S.marginalPrevision i P := by
  ext X
  rfl

end ProjectiveCylinderSystem

/-! ## Projective-limit credal sets and natural extension -/

/-- Local credal data over a projective cylinder system. -/
structure ProjectiveLocalCredalSpec.{u, v} (Window : Type u) (Global : Type v) [LE Window] where
  cylinders : ProjectiveCylinderSystem.{u, v} Window Global
  localCredal : ∀ i : Window, CredalPrevisionSet (cylinders.Local i)

namespace ProjectiveLocalCredalSpec

variable {Window Global : Type*} [LE Window]

/-- The projective-limit credal set: all global precise previsions whose local
marginals lie in the stipulated local credal sets. -/
def projectiveLimitCredalSet
    (S : ProjectiveLocalCredalSpec Window Global) :
    CredalPrevisionSet Global :=
  {P | ∀ i, S.cylinders.marginalPrevision i P ∈ S.localCredal i}

/-- Completion-side consistency: at least one global precise prevision matches
all local credal assessments.  This is the projective-limit analogue of the
"there is a coherent completion" gate; stronger Walley regularity and
conglomerability conditions are separate refinements. -/
def hasCompatibleCompletion
    (S : ProjectiveLocalCredalSpec Window Global) : Prop :=
  S.projectiveLimitCredalSet.Nonempty

theorem mem_projectiveLimitCredalSet_iff
    (S : ProjectiveLocalCredalSpec Window Global)
    (P : PrecisePrevision Global) :
    P ∈ S.projectiveLimitCredalSet ↔
      ∀ i, S.cylinders.marginalPrevision i P ∈ S.localCredal i :=
  Iff.rfl

theorem projectiveLimitCredalSet_nonempty_of_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    {P : PrecisePrevision Global}
    (hP : ∀ i, S.cylinders.marginalPrevision i P ∈ S.localCredal i) :
    S.hasCompatibleCompletion :=
  ⟨P, hP⟩

/-- The global projective-limit credal set is closed whenever every local
constraint set is closed in the chosen topology on global precise previsions. -/
theorem projectiveLimitCredalSet_isClosed
    [TopologicalSpace (PrecisePrevision Global)]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hClosed : ∀ i, IsClosed {P : PrecisePrevision Global |
      S.cylinders.marginalPrevision i P ∈ S.localCredal i}) :
    IsClosed S.projectiveLimitCredalSet := by
  have hEq :
      S.projectiveLimitCredalSet =
        ⋂ i, {P : PrecisePrevision Global |
          S.cylinders.marginalPrevision i P ∈ S.localCredal i} := by
    ext P
    constructor
    · intro hP
      exact Set.mem_iInter.2 hP
    · intro hP i
      exact Set.mem_iInter.1 hP i
  rw [hEq]
  exact isClosed_iInter hClosed

/-- Marginalizing a global Dirac prevision gives the Dirac prevision at the
projected local state. -/
theorem marginalPrevision_dirac
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (ω : Global) :
    S.cylinders.marginalPrevision i (PrecisePrevision.dirac ω) =
      PrecisePrevision.dirac (S.cylinders.project i ω) := by
  ext X
  rfl

/-- Concrete inhabitation witness for projective credal consistency: a global
state whose every local Dirac marginal is locally admissible induces a
compatible global precise prevision. -/
theorem hasCompatibleCompletion_of_local_dirac
    (S : ProjectiveLocalCredalSpec Window Global)
    (ω : Global)
    (hω : ∀ i,
      PrecisePrevision.dirac (S.cylinders.project i ω) ∈ S.localCredal i) :
    S.hasCompatibleCompletion := by
  refine S.projectiveLimitCredalSet_nonempty_of_completion
    (P := PrecisePrevision.dirac ω) ?_
  intro i
  rw [S.marginalPrevision_dirac i ω]
  exact hω i

/-! ### Cylinder-domain compatible completions

The next definitions give the same projective-limit idea on the restricted
cylinder domain.  This is the bridge layer for σ-additive/projective measure
families: they can supply finite-window previsions directly, without first
extending to a functional on all global gambles. -/

/-- Cylinder-domain compatible completions: projectively compatible local
previsions whose window marginals belong to the local credal sets. -/
def projectiveCylinderCredalSet
    (S : ProjectiveLocalCredalSpec Window Global) :
    Set S.cylinders.CylinderPrevision :=
  {K | ∀ i, K.localPrevision i ∈ S.localCredal i}

/-- Existence of a compatible cylinder-domain completion.  This is weaker than
`hasCompatibleCompletion`, since it does not require a precise prevision on all
global gambles. -/
def hasCompatibleCylinderCompletion
    (S : ProjectiveLocalCredalSpec Window Global) : Prop :=
  S.projectiveCylinderCredalSet.Nonempty

theorem projectiveCylinderCredalSet_nonempty_of_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    {K : S.cylinders.CylinderPrevision}
    (hK : ∀ i, K.localPrevision i ∈ S.localCredal i) :
    S.hasCompatibleCylinderCompletion :=
  ⟨K, hK⟩

/-- Compatible cylinder-domain completions are closed under affine mixture when
each local credal set is convex. -/
theorem projectiveCylinderCredalSet_mix_mem_of_local_convex
    (S : ProjectiveLocalCredalSpec Window Global)
    (hLocal : ∀ i, CredalPrevisionSet.IsConvex (S.localCredal i))
    {K L : S.cylinders.CylinderPrevision}
    (hK : K ∈ S.projectiveCylinderCredalSet)
    (hL : L ∈ S.projectiveCylinderCredalSet)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ProjectiveCylinderSystem.CylinderPrevision.mix t K L ht0 ht1 ∈
      S.projectiveCylinderCredalSet := by
  intro i
  rw [ProjectiveCylinderSystem.CylinderPrevision.localPrevision_mix]
  exact hLocal i (hK i) (hL i) t ht0 ht1

/-- Every full compatible global precise completion induces a compatible
cylinder-domain completion. -/
theorem hasCompatibleCylinderCompletion_of_hasCompatibleCompletion
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobal : S.hasCompatibleCompletion) :
    S.hasCompatibleCylinderCompletion := by
  rcases hGlobal with ⟨P, hP⟩
  refine S.projectiveCylinderCredalSet_nonempty_of_completion
    (K := S.cylinders.cylinderPrevisionOfPrecisePrevision P) ?_
  intro i
  rw [ProjectiveCylinderSystem.cylinderPrevisionOfPrecisePrevision_localPrevision]
  exact hP i

/-- Cylinder-domain lower envelope for a local gamble at a window. -/
noncomputable def cylinderNaturalExtension
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  sInf ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
    S.projectiveCylinderCredalSet)

/-- Cylinder-domain upper envelope for a local gamble at a window. -/
noncomputable def cylinderUpperEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  sSup ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
    S.projectiveCylinderCredalSet)

/-- Cylinder-domain credal interval width for a local gamble at a window. -/
noncomputable def cylinderEnvelopeWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  S.cylinderUpperEnvelope i X - S.cylinderNaturalExtension i X

/-- Cylinder-domain width-complement coordinate for a local gamble. -/
noncomputable def cylinderEnvelopeWidthComplement
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  1 - S.cylinderEnvelopeWidth i X

/-- Cylinder-domain interval midpoint coordinate for a local gamble. -/
noncomputable def cylinderEnvelopeMidpoint
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  (S.cylinderNaturalExtension i X + S.cylinderUpperEnvelope i X) / 2

/-- A local credal set is exact at window `i` for cylinder completions when
every local precise completion lifts to a compatible cylinder-domain
completion with the same local prevision. -/
def localCylinderCredalExactAt
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window) : Prop :=
  ∀ R : PrecisePrevision (S.cylinders.Local i), R ∈ S.localCredal i →
    ∃ K : S.cylinders.CylinderPrevision,
      K ∈ S.projectiveCylinderCredalSet ∧ K.localPrevision i = R

/-- The ordinary local credal set obtained by taking the window-`i` image of
all compatible cylinder-domain completions.  This lets the cylinder-domain
natural extension reuse the standard Walley lower-envelope API. -/
def cylinderLocalCredalSet
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window) :
    CredalPrevisionSet (S.cylinders.Local i) :=
  {R | ∃ K : S.cylinders.CylinderPrevision,
    K ∈ S.projectiveCylinderCredalSet ∧ R = K.localPrevision i}

theorem cylinderLocalCredalSet_nonempty
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window) :
    (S.cylinderLocalCredalSet i).Nonempty := by
  rcases hS with ⟨K, hK⟩
  exact ⟨K.localPrevision i, K, hK, rfl⟩

/-- The cylinder-image local credal set is always contained in the stipulated
local credal set: compatible cylinder completions have admissible local
marginals by definition. -/
theorem cylinderLocalCredalSet_subset_localCredal
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window) :
    S.cylinderLocalCredalSet i ⊆ S.localCredal i := by
  intro R hR
  rcases hR with ⟨K, hK, hR⟩
  rw [hR]
  exact hK i

/-- Exact cylinder lifting gives the converse inclusion: every stipulated local
precise prevision appears as the window marginal of a compatible cylinder
completion. -/
theorem localCredal_subset_cylinderLocalCredalSet_of_exact
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window)
    (hExact : S.localCylinderCredalExactAt i) :
    S.localCredal i ⊆ S.cylinderLocalCredalSet i := by
  intro R hR
  rcases hExact R hR with ⟨K, hK, hKi⟩
  exact ⟨K, hK, hKi.symm⟩

/-- Under exact cylinder lifting, the local image of compatible cylinder
completions is exactly the stipulated local credal set. -/
theorem cylinderLocalCredalSet_eq_localCredal_of_exact
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window)
    (hExact : S.localCylinderCredalExactAt i) :
    S.cylinderLocalCredalSet i = S.localCredal i := by
  ext R
  constructor
  · intro hR
    exact S.cylinderLocalCredalSet_subset_localCredal i hR
  · intro hR
    exact S.localCredal_subset_cylinderLocalCredalSet_of_exact i hExact hR

/-- Exact cylinder lifting preserves the "determined gamble" predicate:
the image credal set and the stipulated local credal set pin precisely the
same local gambles. -/
theorem cylinderLocalCredalSet_determines_iff_localCredal_of_exact
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window)
    (hExact : S.localCylinderCredalExactAt i)
    (X : Gamble (S.cylinders.Local i)) :
    credalSetDetermines (S.cylinderLocalCredalSet i) X ↔
      credalSetDetermines (S.localCredal i) X := by
  rw [S.cylinderLocalCredalSet_eq_localCredal_of_exact i hExact]

/-- Exact cylinder lifting preserves strict credal width: genuine disagreement
among stipulated local completions is exactly genuine disagreement among the
compatible cylinder completions' local images. -/
theorem cylinderLocalCredalSet_strictWidth_iff_localCredal_of_exact
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window)
    (hExact : S.localCylinderCredalExactAt i)
    (X : Gamble (S.cylinders.Local i)) :
    credalSetHasStrictWidth (S.cylinderLocalCredalSet i) X ↔
      credalSetHasStrictWidth (S.localCredal i) X := by
  rw [S.cylinderLocalCredalSet_eq_localCredal_of_exact i hExact]

/-- The cylinder-domain natural extension is exactly the lower envelope of the
local image credal set of compatible cylinder completions. -/
theorem cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.cylinderNaturalExtension i X =
      lowerEnvelope (S.cylinderLocalCredalSet i) X := by
  unfold cylinderNaturalExtension lowerEnvelope cylinderLocalCredalSet
  congr 1
  ext y
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K.localPrevision i, ⟨K, hK, rfl⟩, rfl⟩
  · rintro ⟨R, ⟨K, hK, hR⟩, rfl⟩
    exact ⟨K, hK, by rw [hR]; rfl⟩

/-- The cylinder-domain upper envelope is exactly the upper envelope of the
local image credal set of compatible cylinder completions. -/
theorem cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.cylinderUpperEnvelope i X =
      upperEnvelope (S.cylinderLocalCredalSet i) X := by
  unfold cylinderUpperEnvelope upperEnvelope cylinderLocalCredalSet
  congr 1
  ext y
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact ⟨K.localPrevision i, ⟨K, hK, rfl⟩, rfl⟩
  · rintro ⟨R, ⟨K, hK, hR⟩, rfl⟩
    exact ⟨K, hK, by rw [hR]; rfl⟩

/-- The cylinder-domain width is the ordinary credal-envelope width of the
local image of compatible cylinder completions. -/
theorem cylinderEnvelopeWidth_eq_credalEnvelopeWidth_cylinderLocalCredalSet
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.cylinderEnvelopeWidth i X =
      credalEnvelopeWidth (S.cylinderLocalCredalSet i) X := by
  unfold cylinderEnvelopeWidth credalEnvelopeWidth
  rw [S.cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet i X,
    S.cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet i X]

/-- The cylinder-domain width-complement is the ordinary width-complement of
the local image of compatible cylinder completions. -/
theorem cylinderEnvelopeWidthComplement_eq_credalEnvelopeWidthComplement_cylinderLocalCredalSet
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.cylinderEnvelopeWidthComplement i X =
      credalEnvelopeWidthComplement (S.cylinderLocalCredalSet i) X := by
  unfold cylinderEnvelopeWidthComplement credalEnvelopeWidthComplement
  rw [S.cylinderEnvelopeWidth_eq_credalEnvelopeWidth_cylinderLocalCredalSet i X]

/-- The cylinder-domain midpoint is the ordinary credal-envelope midpoint of
the local image of compatible cylinder completions. -/
theorem cylinderEnvelopeMidpoint_eq_credalEnvelopeMidpoint_cylinderLocalCredalSet
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.cylinderEnvelopeMidpoint i X =
      credalEnvelopeMidpoint (S.cylinderLocalCredalSet i) X := by
  unfold cylinderEnvelopeMidpoint credalEnvelopeMidpoint
  rw [S.cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet i X,
    S.cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet i X]

/-- If the compatible cylinder completions determine a local gamble, then the
cylinder-domain interval width on that gamble collapses to zero. -/
theorem cylinderEnvelopeWidth_eq_zero_of_cylinderLocalCredalSet_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hDet : credalSetDetermines (S.cylinderLocalCredalSet i) X) :
    S.cylinderEnvelopeWidth i X = 0 := by
  rw [S.cylinderEnvelopeWidth_eq_credalEnvelopeWidth_cylinderLocalCredalSet i X]
  rcases S.cylinderLocalCredalSet_nonempty hS i with ⟨R, hR⟩
  exact credalEnvelopeWidth_eq_zero_of_credalSetDetermines
    (S.cylinderLocalCredalSet i) X (S.cylinderLocalCredalSet_nonempty hS i)
    hBddBelow hBddAbove hR hDet

/-- If compatible cylinder completions strictly disagree on a local gamble,
then the cylinder-domain lower and upper envelopes are genuinely split. -/
theorem cylinderLowerUpperEnvelope_nontrivial_of_cylinderLocalCredalSet_strictWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hWidth : credalSetHasStrictWidth (S.cylinderLocalCredalSet i) X) :
    S.cylinderNaturalExtension i X < S.cylinderUpperEnvelope i X := by
  rw [S.cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet i X,
    S.cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet i X]
  exact lower_upperEnvelope_nontrivial_of_strictWidth
    (S.cylinderLocalCredalSet i) X hBddBelow hBddAbove hWidth

/-- Strict cylinder-local credal width gives positive cylinder-domain interval
width. -/
theorem cylinderEnvelopeWidth_pos_of_cylinderLocalCredalSet_strictWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hWidth : credalSetHasStrictWidth (S.cylinderLocalCredalSet i) X) :
    0 < S.cylinderEnvelopeWidth i X := by
  have hlt :=
    S.cylinderLowerUpperEnvelope_nontrivial_of_cylinderLocalCredalSet_strictWidth
      i X hBddBelow hBddAbove hWidth
  unfold cylinderEnvelopeWidth
  linarith

/-- Cylinder-local determination gives maximal width-complement. -/
theorem cylinderEnvelopeWidthComplement_eq_one_of_cylinderLocalCredalSet_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hDet : credalSetDetermines (S.cylinderLocalCredalSet i) X) :
    S.cylinderEnvelopeWidthComplement i X = 1 := by
  unfold cylinderEnvelopeWidthComplement
  rw [S.cylinderEnvelopeWidth_eq_zero_of_cylinderLocalCredalSet_determines
    hS i X hBddBelow hBddAbove hDet]
  ring

/-- Strict cylinder-local width forces the width-complement below one. -/
theorem cylinderEnvelopeWidthComplement_lt_one_of_cylinderLocalCredalSet_strictWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hWidth : credalSetHasStrictWidth (S.cylinderLocalCredalSet i) X) :
    S.cylinderEnvelopeWidthComplement i X < 1 := by
  have hpos :=
    S.cylinderEnvelopeWidth_pos_of_cylinderLocalCredalSet_strictWidth
      i X hBddBelow hBddAbove hWidth
  unfold cylinderEnvelopeWidthComplement
  linarith

/-- Under exact cylinder lifting, local credal determination collapses the
cylinder-domain interval width. -/
theorem cylinderEnvelopeWidth_eq_zero_of_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hExact : S.localCylinderCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.cylinderEnvelopeWidth i X = 0 := by
  have hBddBelow :
      BddBelow
        ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i) := by
    rwa [S.cylinderLocalCredalSet_eq_localCredal_of_exact i hExact]
  have hBddAbove :
      BddAbove
        ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i) := by
    rwa [S.cylinderLocalCredalSet_eq_localCredal_of_exact i hExact]
  have hDetCylinder :
      credalSetDetermines (S.cylinderLocalCredalSet i) X :=
    (S.cylinderLocalCredalSet_determines_iff_localCredal_of_exact
      i hExact X).mpr hDet
  exact S.cylinderEnvelopeWidth_eq_zero_of_cylinderLocalCredalSet_determines
    hS i X hBddBelow hBddAbove hDetCylinder

/-- Under exact cylinder lifting, strict local credal width gives genuinely
split cylinder-domain lower and upper envelopes. -/
theorem cylinderLowerUpperEnvelope_nontrivial_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hExact : S.localCylinderCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.cylinderNaturalExtension i X < S.cylinderUpperEnvelope i X := by
  have hBddBelow :
      BddBelow
        ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i) := by
    rwa [S.cylinderLocalCredalSet_eq_localCredal_of_exact i hExact]
  have hBddAbove :
      BddAbove
        ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i) := by
    rwa [S.cylinderLocalCredalSet_eq_localCredal_of_exact i hExact]
  have hWidthCylinder :
      credalSetHasStrictWidth (S.cylinderLocalCredalSet i) X :=
    (S.cylinderLocalCredalSet_strictWidth_iff_localCredal_of_exact
      i hExact X).mpr hWidth
  exact
    S.cylinderLowerUpperEnvelope_nontrivial_of_cylinderLocalCredalSet_strictWidth
      i X hBddBelow hBddAbove hWidthCylinder

/-- Under exact cylinder lifting, strict local credal width gives positive
cylinder-domain interval width. -/
theorem cylinderEnvelopeWidth_pos_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hExact : S.localCylinderCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    0 < S.cylinderEnvelopeWidth i X := by
  have hlt :=
    S.cylinderLowerUpperEnvelope_nontrivial_of_localCredal_strictWidth_of_exact
      i X hLocalBddBelow hLocalBddAbove hExact hWidth
  unfold cylinderEnvelopeWidth
  linarith

/-- Under exact cylinder lifting, local credal determination gives maximal
cylinder-domain width-complement. -/
theorem cylinderEnvelopeWidthComplement_eq_one_of_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hExact : S.localCylinderCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.cylinderEnvelopeWidthComplement i X = 1 := by
  unfold cylinderEnvelopeWidthComplement
  rw [S.cylinderEnvelopeWidth_eq_zero_of_localCredal_determines_of_exact
    hS i X hLocalBddBelow hLocalBddAbove hExact hDet]
  ring

/-- Under exact cylinder lifting, strict local credal width forces the
cylinder-domain width-complement below one. -/
theorem cylinderEnvelopeWidthComplement_lt_one_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hExact : S.localCylinderCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.cylinderEnvelopeWidthComplement i X < 1 := by
  have hpos :=
    S.cylinderEnvelopeWidth_pos_of_localCredal_strictWidth_of_exact
      i X hLocalBddBelow hLocalBddAbove hExact hWidth
  unfold cylinderEnvelopeWidthComplement
  linarith

/-- Finite-window exact-cylinder collapse: finite local spaces discharge the
boundedness side conditions automatically. -/
theorem finiteCylinderEnvelopeWidth_eq_zero_of_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCylinderCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.cylinderEnvelopeWidth i X = 0 :=
  S.cylinderEnvelopeWidth_eq_zero_of_localCredal_determines_of_exact
    hS i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X) hExact hDet

/-- Finite-window exact-cylinder strict-width split. -/
theorem finiteCylinderLowerUpperEnvelope_nontrivial_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCylinderCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.cylinderNaturalExtension i X < S.cylinderUpperEnvelope i X :=
  S.cylinderLowerUpperEnvelope_nontrivial_of_localCredal_strictWidth_of_exact
    i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X) hExact hWidth

/-- Finite-window exact-cylinder positive-width theorem. -/
theorem finiteCylinderEnvelopeWidth_pos_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCylinderCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    0 < S.cylinderEnvelopeWidth i X :=
  S.cylinderEnvelopeWidth_pos_of_localCredal_strictWidth_of_exact
    i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X) hExact hWidth

/-- Finite-window exact-cylinder maximal width-complement theorem. -/
theorem finiteCylinderEnvelopeWidthComplement_eq_one_of_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCylinderCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.cylinderEnvelopeWidthComplement i X = 1 :=
  S.cylinderEnvelopeWidthComplement_eq_one_of_localCredal_determines_of_exact
    hS i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X) hExact hDet

/-- Finite-window exact-cylinder strict-width complement theorem. -/
theorem finiteCylinderEnvelopeWidthComplement_lt_one_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCylinderCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.cylinderEnvelopeWidthComplement i X < 1 :=
  S.cylinderEnvelopeWidthComplement_lt_one_of_localCredal_strictWidth_of_exact
    i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X) hExact hWidth

/-- Packaged cylinder-domain natural extension at one window as a genuine
lower prevision on that local state space. -/
noncomputable def cylinderNaturalExtensionPrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i)) :
    LowerPrevision (S.cylinders.Local i) :=
  lowerEnvelopePrevision (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i) hBdd

@[simp] theorem cylinderNaturalExtensionPrevision_apply
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (X : Gamble (S.cylinders.Local i)) :
    S.cylinderNaturalExtensionPrevision hS i hBdd X =
      S.cylinderNaturalExtension i X := by
  rw [cylinderNaturalExtensionPrevision]
  exact (S.cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet i X).symm

/-- Packaged cylinder-domain upper envelope at one window as a genuine upper
prevision on that local state space. -/
noncomputable def cylinderUpperEnvelopePrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddAbove ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i)) :
    UpperPrevision (S.cylinders.Local i) :=
  upperEnvelopePrevision (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i) hBdd

@[simp] theorem cylinderUpperEnvelopePrevision_apply
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddAbove ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (X : Gamble (S.cylinders.Local i)) :
    S.cylinderUpperEnvelopePrevision hS i hBdd X =
      S.cylinderUpperEnvelope i X := by
  rw [cylinderUpperEnvelopePrevision]
  exact (S.cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet i X).symm

/-- The packaged cylinder natural extension is below every compatible
cylinder-domain completion at the chosen window. -/
theorem cylinderNaturalExtensionPrevision_le_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    {K : S.cylinders.CylinderPrevision}
    (hK : K ∈ S.projectiveCylinderCredalSet)
    (X : Gamble (S.cylinders.Local i)) :
    S.cylinderNaturalExtensionPrevision hS i hBdd X ≤ K.toFun i X := by
  rw [cylinderNaturalExtensionPrevision]
  exact lowerEnvelopePrevision_le_completion (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i) hBdd
    (P := K.localPrevision i) ⟨K, hK, rfl⟩ X

/-- The packaged cylinder natural extension is the greatest lower prevision
dominated by every compatible cylinder-domain completion at the chosen window. -/
theorem cylinderNaturalExtensionPrevision_greatest_lower_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (L : LowerPrevision (S.cylinders.Local i))
    (hL : ∀ K : S.cylinders.CylinderPrevision,
      K ∈ S.projectiveCylinderCredalSet →
        ∀ X : Gamble (S.cylinders.Local i), L X ≤ K.toFun i X)
    (X : Gamble (S.cylinders.Local i)) :
    L X ≤ S.cylinderNaturalExtensionPrevision hS i hBdd X := by
  rw [cylinderNaturalExtensionPrevision]
  exact lowerEnvelopePrevision_greatest_lower_bound
    (S.cylinderLocalCredalSet i) (S.cylinderLocalCredalSet_nonempty hS i)
    hBdd L (by
      intro R hR Y
      rcases hR with ⟨K, hK, rfl⟩
      exact hL K hK Y) X

/-- Every compatible cylinder-domain completion is below the packaged cylinder
upper envelope at the chosen window. -/
theorem cylinderCompletion_le_upperEnvelopePrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddAbove ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    {K : S.cylinders.CylinderPrevision}
    (hK : K ∈ S.projectiveCylinderCredalSet)
    (X : Gamble (S.cylinders.Local i)) :
    K.toFun i X ≤ S.cylinderUpperEnvelopePrevision hS i hBdd X := by
  rw [cylinderUpperEnvelopePrevision]
  exact completion_le_upperEnvelopePrevision (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i) hBdd
    (P := K.localPrevision i) ⟨K, hK, rfl⟩ X

/-- The packaged cylinder upper envelope is the least upper prevision dominating
every compatible cylinder-domain completion at the chosen window. -/
theorem cylinderUpperEnvelopePrevision_least_upper_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddAbove ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (U : UpperPrevision (S.cylinders.Local i))
    (hU : ∀ K : S.cylinders.CylinderPrevision,
      K ∈ S.projectiveCylinderCredalSet →
        ∀ X : Gamble (S.cylinders.Local i), K.toFun i X ≤ U X)
    (X : Gamble (S.cylinders.Local i)) :
    S.cylinderUpperEnvelopePrevision hS i hBdd X ≤ U X := by
  rw [cylinderUpperEnvelopePrevision]
  exact upperEnvelopePrevision_least_upper_bound
    (S.cylinderLocalCredalSet i) (S.cylinderLocalCredalSet_nonempty hS i)
    hBdd U (by
      intro R hR Y
      rcases hR with ⟨K, hK, rfl⟩
      exact hU K hK Y) X

/-- The conjugate upper prevision of the packaged cylinder natural extension is
the cylinder-domain upper envelope. -/
theorem cylinderNaturalExtensionPrevision_conjugate_eq_upperEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (X : Gamble (S.cylinders.Local i)) :
    (S.cylinderNaturalExtensionPrevision hS i hBdd).conjugate X =
      S.cylinderUpperEnvelope i X := by
  rw [cylinderNaturalExtensionPrevision,
    S.cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet i X]
  exact lowerEnvelopePrevision_conjugate_eq_upperEnvelope
    (S.cylinderLocalCredalSet i) (S.cylinderLocalCredalSet_nonempty hS i)
    hBdd X

/-- The conjugate lower prevision of the packaged cylinder upper envelope is the
cylinder-domain natural extension. -/
theorem cylinderUpperEnvelopePrevision_conjugate_eq_naturalExtension
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddAbove ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (X : Gamble (S.cylinders.Local i)) :
    (S.cylinderUpperEnvelopePrevision hS i hBdd).conjugate X =
      S.cylinderNaturalExtension i X := by
  rw [cylinderUpperEnvelopePrevision,
    S.cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet i X]
  exact upperEnvelopePrevision_conjugate_eq_lowerEnvelope
    (S.cylinderLocalCredalSet i) (S.cylinderLocalCredalSet_nonempty hS i)
    hBdd X

/-- A compatible cylinder-domain completion makes the packaged cylinder natural
extension avoid uniform sure loss at each window. -/
theorem cylinderNaturalExtensionPrevision_avoidsUniformSureLoss
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i)) :
    (S.cylinderNaturalExtensionPrevision hS i hBdd).avoidsUniformSureLoss :=
  lowerEnvelopePrevision_avoidsUniformSureLoss
    (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i) hBdd

/-- The packaged cylinder natural extension has Walley's exact representation as
the lower envelope of the precise previsions dominating it. -/
theorem cylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i)) :
    hasExactDominatingPreciseEnvelope
      (S.cylinderNaturalExtensionPrevision hS i hBdd) :=
  lowerPrevision_hasExactDominatingPreciseEnvelope
    (S.cylinderNaturalExtensionPrevision hS i hBdd)

/-- Re-envelope the packaged cylinder natural extension by its dominating
precise previsions and recover the same lower prevision. -/
theorem cylinderNaturalExtensionPrevision_dominatingEnvelope_eq
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i)) :
    lowerEnvelopePrevision
        (dominatingPreciseCompletions
          (S.cylinderNaturalExtensionPrevision hS i hBdd))
        (dominatingPreciseCompletions_nonempty
          (S.cylinderNaturalExtensionPrevision hS i hBdd))
        (dominatingPreciseCompletions_bddBelow
          (S.cylinderNaturalExtensionPrevision hS i hBdd)) =
      S.cylinderNaturalExtensionPrevision hS i hBdd :=
  lowerEnvelopePrevision_dominatingPreciseCompletions_eq
    (S.cylinderNaturalExtensionPrevision hS i hBdd)

/-- Query-wise Walley completion for a packaged cylinder-domain natural
extension.  The touching prevision dominates the natural extension; it is not
claimed to be one of the original compatible cylinder completions. -/
theorem cylinderNaturalExtensionPrevision_exists_dominatingPreciseCompletion_touching
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBdd : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (X : Gamble (S.cylinders.Local i)) :
    ∃ P : PrecisePrevision (S.cylinders.Local i),
      P ∈ dominatingPreciseCompletions
        (S.cylinderNaturalExtensionPrevision hS i hBdd) ∧
      P X = S.cylinderNaturalExtension i X := by
  simpa using
    exists_dominatingPreciseCompletion_touching
      (S.cylinderNaturalExtensionPrevision hS i hBdd) X

/-- Strict cylinder-local width is realized by Walley dominating precise
completions of the packaged cylinder natural extension.

This is the endpoint-readout theorem for the cylinder-domain layer, which does
not require a global prevision on all raw infinite-world gambles.  Once the
local cylinder envelope is bounded below and above, strict width on a local
gamble gives lower- and upper-touching dominating precise completions, and
their endpoint gap computes the PLN-facing width, width-complement, and
midpoint coordinates. -/
theorem cylinderNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion) (i : Window)
    (hBddBelow : ∀ X : Gamble (S.cylinders.Local i),
      BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (hBddAbove : ∀ X : Gamble (S.cylinders.Local i),
      BddAbove ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.cylinderLocalCredalSet i))
    (X : Gamble (S.cylinders.Local i))
    (hWidth : credalSetHasStrictWidth (S.cylinderLocalCredalSet i) X) :
    ∃ Plo : PrecisePrevision (S.cylinders.Local i),
      Plo ∈ dominatingPreciseCompletions
          (S.cylinderNaturalExtensionPrevision hS i hBddBelow) ∧
      ∃ Phi : PrecisePrevision (S.cylinders.Local i),
        Phi ∈ dominatingPreciseCompletions
          (S.cylinderNaturalExtensionPrevision hS i hBddBelow) ∧
        Plo X = S.cylinderNaturalExtension i X ∧
        Phi X = S.cylinderUpperEnvelope i X ∧
        Plo X < Phi X ∧
        S.cylinderEnvelopeWidth i X = Phi X - Plo X ∧
        S.cylinderEnvelopeWidthComplement i X =
          1 - (Phi X - Plo X) ∧
        S.cylinderEnvelopeMidpoint i X = (Plo X + Phi X) / 2 := by
  let L : LowerPrevision (S.cylinders.Local i) :=
    S.cylinderNaturalExtensionPrevision hS i hBddBelow
  have hExact : hasExactDominatingPreciseEnvelope L := by
    dsimp [L]
    exact S.cylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      hS i hBddBelow
  have hLower :
      L X = S.cylinderNaturalExtension i X := by
    simp [L]
  have hUpper :
      L.conjugate X = S.cylinderUpperEnvelope i X := by
    dsimp [L]
    exact S.cylinderNaturalExtensionPrevision_conjugate_eq_upperEnvelope
      hS i hBddBelow X
  have hLowerUpper :
      S.cylinderNaturalExtension i X < S.cylinderUpperEnvelope i X :=
    S.cylinderLowerUpperEnvelope_nontrivial_of_cylinderLocalCredalSet_strictWidth
      i X (hBddBelow X) (hBddAbove X) hWidth
  have hStrict : L X < L.conjugate X := by
    calc
      L X = S.cylinderNaturalExtension i X := hLower
      _ < S.cylinderUpperEnvelope i X := hLowerUpper
      _ = L.conjugate X := hUpper.symm
  rcases hExact.exists_strictEndpointPairReadout X hStrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, _hWidthD, _hCompD, _hMidD⟩
  have hloCylinder :
      Plo X = S.cylinderNaturalExtension i X :=
    hlo.trans hLower
  have hhiCylinder :
      Phi X = S.cylinderUpperEnvelope i X :=
    hhi.trans hUpper
  have hloLocal :
      Plo X = lowerEnvelope (S.cylinderLocalCredalSet i) X := by
    calc
      Plo X = S.cylinderNaturalExtension i X := hloCylinder
      _ = lowerEnvelope (S.cylinderLocalCredalSet i) X :=
        S.cylinderNaturalExtension_eq_lowerEnvelope_cylinderLocalCredalSet i X
  have hhiLocal :
      Phi X = upperEnvelope (S.cylinderLocalCredalSet i) X := by
    calc
      Phi X = S.cylinderUpperEnvelope i X := hhiCylinder
      _ = upperEnvelope (S.cylinderLocalCredalSet i) X :=
        S.cylinderUpperEnvelope_eq_upperEnvelope_cylinderLocalCredalSet i X
  refine ⟨Plo, hPlo, Phi, hPhi, hloCylinder, hhiCylinder, hlt, ?_, ?_, ?_⟩
  · calc
      S.cylinderEnvelopeWidth i X =
          credalEnvelopeWidth (S.cylinderLocalCredalSet i) X :=
        S.cylinderEnvelopeWidth_eq_credalEnvelopeWidth_cylinderLocalCredalSet
          i X
      _ = Phi X - Plo X :=
        credalEnvelopeWidth_eq_endpointGap
          (S.cylinderLocalCredalSet i) X Plo Phi hloLocal hhiLocal
  · calc
      S.cylinderEnvelopeWidthComplement i X =
          credalEnvelopeWidthComplement (S.cylinderLocalCredalSet i) X :=
        S.cylinderEnvelopeWidthComplement_eq_credalEnvelopeWidthComplement_cylinderLocalCredalSet
          i X
      _ = 1 - (Phi X - Plo X) :=
        credalEnvelopeWidthComplement_eq_one_sub_endpointGap
          (S.cylinderLocalCredalSet i) X Plo Phi hloLocal hhiLocal
  · calc
      S.cylinderEnvelopeMidpoint i X =
          credalEnvelopeMidpoint (S.cylinderLocalCredalSet i) X :=
        S.cylinderEnvelopeMidpoint_eq_credalEnvelopeMidpoint_cylinderLocalCredalSet
          i X
      _ = (Plo X + Phi X) / 2 :=
        credalEnvelopeMidpoint_eq_endpointMean
          (S.cylinderLocalCredalSet i) X Plo Phi hloLocal hhiLocal

/-- Finite-window cylinder natural extension: boundedness is automatic on a
finite nonempty local state space. -/
noncomputable def finiteCylinderNaturalExtensionPrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)] :
    LowerPrevision (S.cylinders.Local i) :=
  S.cylinderNaturalExtensionPrevision hS i
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i))

/-- Finite-window cylinder upper envelope: boundedness is automatic on a finite
nonempty local state space. -/
noncomputable def finiteCylinderUpperEnvelopePrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)] :
    UpperPrevision (S.cylinders.Local i) :=
  S.cylinderUpperEnvelopePrevision hS i
    (finite_credalRange_bddAbove (S.cylinderLocalCredalSet i))

@[simp] theorem finiteCylinderNaturalExtensionPrevision_apply
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i)) :
    S.finiteCylinderNaturalExtensionPrevision hS i X =
      S.cylinderNaturalExtension i X :=
  S.cylinderNaturalExtensionPrevision_apply hS i
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i)) X

@[simp] theorem finiteCylinderUpperEnvelopePrevision_apply
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i)) :
    S.finiteCylinderUpperEnvelopePrevision hS i X =
      S.cylinderUpperEnvelope i X :=
  S.cylinderUpperEnvelopePrevision_apply hS i
    (finite_credalRange_bddAbove (S.cylinderLocalCredalSet i)) X

/-- On finite local windows, the cylinder natural extension avoids Walley's
strict sure loss. -/
theorem finiteCylinderNaturalExtensionPrevision_avoidsSureLoss
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)] :
    (S.finiteCylinderNaturalExtensionPrevision hS i).avoidsSureLoss :=
  lowerEnvelopePrevision_avoidsSureLoss_of_finite
    (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i)
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i))

/-- On finite local windows, the cylinder natural extension is coherent in
Walley's finite lower-envelope sense. -/
theorem finiteCylinderNaturalExtensionPrevision_isCoherent
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)] :
    (S.finiteCylinderNaturalExtensionPrevision hS i).isCoherent :=
  lowerEnvelopePrevision_isCoherent_of_finite
    (S.cylinderLocalCredalSet i)
    (S.cylinderLocalCredalSet_nonempty hS i)
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i))

/-- Finite local-window natural extensions inherit the exact dominating
precise-envelope representation. -/
theorem finiteCylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)] :
    hasExactDominatingPreciseEnvelope
      (S.finiteCylinderNaturalExtensionPrevision hS i) :=
  S.cylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope hS i
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i))

/-- Re-envelope the finite local-window natural extension by its dominating
precise previsions and recover the same lower prevision. -/
theorem finiteCylinderNaturalExtensionPrevision_dominatingEnvelope_eq
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)] :
    lowerEnvelopePrevision
        (dominatingPreciseCompletions
          (S.finiteCylinderNaturalExtensionPrevision hS i))
        (dominatingPreciseCompletions_nonempty
          (S.finiteCylinderNaturalExtensionPrevision hS i))
        (dominatingPreciseCompletions_bddBelow
          (S.finiteCylinderNaturalExtensionPrevision hS i)) =
      S.finiteCylinderNaturalExtensionPrevision hS i :=
  lowerEnvelopePrevision_dominatingPreciseCompletions_eq
    (S.finiteCylinderNaturalExtensionPrevision hS i)

/-- Query-wise Walley completion for finite local-window natural extensions. -/
theorem finiteCylinderNaturalExtensionPrevision_exists_dominatingPreciseCompletion_touching
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i)) :
    ∃ P : PrecisePrevision (S.cylinders.Local i),
      P ∈ dominatingPreciseCompletions
        (S.finiteCylinderNaturalExtensionPrevision hS i) ∧
      P X = S.cylinderNaturalExtension i X := by
  simpa using
    exists_dominatingPreciseCompletion_touching
      (S.finiteCylinderNaturalExtensionPrevision hS i) X

/-- On finite local windows, the finite cylinder natural extension is below every
compatible cylinder-domain completion. -/
theorem finiteCylinderNaturalExtensionPrevision_le_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    {K : S.cylinders.CylinderPrevision}
    (hK : K ∈ S.projectiveCylinderCredalSet)
    (X : Gamble (S.cylinders.Local i)) :
    S.finiteCylinderNaturalExtensionPrevision hS i X ≤ K.toFun i X :=
  S.cylinderNaturalExtensionPrevision_le_completion hS i
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i)) hK X

/-- On finite local windows, the finite cylinder natural extension is the
greatest lower prevision dominated by every compatible cylinder-domain
completion. -/
theorem finiteCylinderNaturalExtensionPrevision_greatest_lower_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (L : LowerPrevision (S.cylinders.Local i))
    (hL : ∀ K : S.cylinders.CylinderPrevision,
      K ∈ S.projectiveCylinderCredalSet →
        ∀ X : Gamble (S.cylinders.Local i), L X ≤ K.toFun i X)
    (X : Gamble (S.cylinders.Local i)) :
    L X ≤ S.finiteCylinderNaturalExtensionPrevision hS i X :=
  S.cylinderNaturalExtensionPrevision_greatest_lower_bound hS i
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i)) L hL X

/-- On finite local windows, every compatible cylinder-domain completion is below
the finite cylinder upper-envelope prevision. -/
theorem finiteCylinderCompletion_le_upperEnvelopePrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    {K : S.cylinders.CylinderPrevision}
    (hK : K ∈ S.projectiveCylinderCredalSet)
    (X : Gamble (S.cylinders.Local i)) :
    K.toFun i X ≤ S.finiteCylinderUpperEnvelopePrevision hS i X :=
  S.cylinderCompletion_le_upperEnvelopePrevision hS i
    (finite_credalRange_bddAbove (S.cylinderLocalCredalSet i)) hK X

/-- On finite local windows, the finite cylinder upper-envelope prevision is the
least upper prevision dominating every compatible cylinder-domain completion. -/
theorem finiteCylinderUpperEnvelopePrevision_least_upper_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (U : UpperPrevision (S.cylinders.Local i))
    (hU : ∀ K : S.cylinders.CylinderPrevision,
      K ∈ S.projectiveCylinderCredalSet →
        ∀ X : Gamble (S.cylinders.Local i), K.toFun i X ≤ U X)
    (X : Gamble (S.cylinders.Local i)) :
    S.finiteCylinderUpperEnvelopePrevision hS i X ≤ U X :=
  S.cylinderUpperEnvelopePrevision_least_upper_bound hS i
    (finite_credalRange_bddAbove (S.cylinderLocalCredalSet i)) U hU X

/-- Finite cylinder natural-extension conjugacy: the conjugate upper prevision is
the finite cylinder upper envelope. -/
theorem finiteCylinderNaturalExtensionPrevision_conjugate_eq_upperEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i)) :
    (S.finiteCylinderNaturalExtensionPrevision hS i).conjugate X =
      S.cylinderUpperEnvelope i X :=
  S.cylinderNaturalExtensionPrevision_conjugate_eq_upperEnvelope hS i
    (finite_credalRange_bddBelow (S.cylinderLocalCredalSet i)) X

/-- Finite cylinder upper-envelope conjugacy: the conjugate lower prevision is
the finite cylinder natural extension. -/
theorem finiteCylinderUpperEnvelopePrevision_conjugate_eq_naturalExtension
    (S : ProjectiveLocalCredalSpec Window Global)
    (hS : S.hasCompatibleCylinderCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i)) :
    (S.finiteCylinderUpperEnvelopePrevision hS i).conjugate X =
      S.cylinderNaturalExtension i X :=
  S.cylinderUpperEnvelopePrevision_conjugate_eq_naturalExtension hS i
    (finite_credalRange_bddAbove (S.cylinderLocalCredalSet i)) X

/-- Exact-cylinder lower-envelope theorem, restricted to the cylinder domain:
when local completions lift exactly to compatible cylinder previsions, the
cylinder-domain lower envelope agrees with the local lower envelope. -/
theorem cylinderNaturalExtension_eq_localLowerEnvelope_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBdd : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBdd : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i) :
    S.cylinderNaturalExtension i X = lowerEnvelope (S.localCredal i) X := by
  refine le_antisymm ?_ ?_
  · apply le_lowerEnvelope_of_forall_le (S.localCredal i) hLocalNonempty
    intro R hR
    rcases hExact R hR with ⟨K, hK, hKi⟩
    have hle :
        S.cylinderNaturalExtension i X ≤ K.toFun i X := by
      exact csInf_le hCylinderBdd ⟨K, hK, rfl⟩
    have hKX : K.toFun i X = R X := by
      change K.localPrevision i X = R X
      rw [hKi]
    exact hle.trans_eq hKX
  · unfold cylinderNaturalExtension
    refine le_csInf ?nonempty ?lower
    · rcases hCylinderNonempty with ⟨K, hK⟩
      exact ⟨K.toFun i X, ⟨K, hK, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨K, hK, rfl⟩
      exact lowerEnvelope_le_of_mem (S.localCredal i) X hLocalBdd
        (hK i)

/-- Exact-cylinder upper-envelope theorem, restricted to the cylinder domain:
when local completions lift exactly to compatible cylinder previsions, the
cylinder-domain upper envelope agrees with the local upper envelope. -/
theorem cylinderUpperEnvelope_eq_localUpperEnvelope_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBdd : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBdd : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i) :
    S.cylinderUpperEnvelope i X = upperEnvelope (S.localCredal i) X := by
  refine le_antisymm ?_ ?_
  · unfold cylinderUpperEnvelope
    refine csSup_le ?nonempty ?upper
    · rcases hCylinderNonempty with ⟨K, hK⟩
      exact ⟨K.toFun i X, ⟨K, hK, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨K, hK, rfl⟩
      exact le_upperEnvelope_of_mem (S.localCredal i) X hLocalBdd
        (hK i)
  · apply upperEnvelope_le_of_forall_le (S.localCredal i) hLocalNonempty
    intro R hR
    rcases hExact R hR with ⟨K, hK, hKi⟩
    have hle :
        K.toFun i X ≤ S.cylinderUpperEnvelope i X := by
      exact le_csSup hCylinderBdd ⟨K, hK, rfl⟩
    have hKX : K.toFun i X = R X := by
      change K.localPrevision i X = R X
      rw [hKi]
    rw [← hKX]
    exact hle

theorem projectiveLimitCredalSet_isConvex
    (S : ProjectiveLocalCredalSpec Window Global)
    (hLocal : ∀ i, CredalPrevisionSet.IsConvex (S.localCredal i)) :
    CredalPrevisionSet.IsConvex S.projectiveLimitCredalSet := by
  intro P hP Q hQ t ht0 ht1 i
  rw [S.cylinders.marginalPrevision_mix i t ht0 ht1 P Q]
  exact hLocal i (hP i) (hQ i) t ht0 ht1

/-- Global natural extension as the lower envelope of all compatible global
precise completions. -/
noncomputable def globalNaturalExtension
    (S : ProjectiveLocalCredalSpec Window Global) :
    Gamble Global → ℝ :=
  lowerEnvelope S.projectiveLimitCredalSet

/-- Width of the compatible-completion envelope on a global gamble. -/
noncomputable def globalEnvelopeWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global) : ℝ :=
  credalEnvelopeWidth S.projectiveLimitCredalSet X

/-- Width complement of the compatible-completion envelope on a global gamble. -/
noncomputable def globalEnvelopeWidthComplement
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global) : ℝ :=
  credalEnvelopeWidthComplement S.projectiveLimitCredalSet X

/-- Midpoint of the compatible-completion envelope on a global gamble. -/
noncomputable def globalEnvelopeMidpoint
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global) : ℝ :=
  credalEnvelopeMidpoint S.projectiveLimitCredalSet X

/-- If a projective credal query spans the full unit interval, its midpoint
strength display is forced to one half. -/
theorem globalEnvelopeMidpoint_eq_half_of_unit_interval
    (S : ProjectiveLocalCredalSpec Window Global) (X : Gamble Global)
    (hL : S.globalNaturalExtension X = 0)
    (hU : upperEnvelope S.projectiveLimitCredalSet X = 1) :
    S.globalEnvelopeMidpoint X = (1 / 2 : ℝ) := by
  unfold globalNaturalExtension at hL
  unfold globalEnvelopeMidpoint
  exact credalEnvelopeMidpoint_eq_half_of_lower_eq_zero_upper_eq_one
    S.projectiveLimitCredalSet X hL hU

/-- If a projective credal query spans the full unit interval, its width is
maximal. -/
theorem globalEnvelopeWidth_eq_one_of_unit_interval
    (S : ProjectiveLocalCredalSpec Window Global) (X : Gamble Global)
    (hL : S.globalNaturalExtension X = 0)
    (hU : upperEnvelope S.projectiveLimitCredalSet X = 1) :
    S.globalEnvelopeWidth X = 1 := by
  unfold globalNaturalExtension at hL
  unfold globalEnvelopeWidth
  exact credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one
    S.projectiveLimitCredalSet X hL hU

/-- If a projective credal query spans the full unit interval, its
width-complement confidence display is forced to zero. -/
theorem globalEnvelopeWidthComplement_eq_zero_of_unit_interval
    (S : ProjectiveLocalCredalSpec Window Global) (X : Gamble Global)
    (hL : S.globalNaturalExtension X = 0)
    (hU : upperEnvelope S.projectiveLimitCredalSet X = 1) :
    S.globalEnvelopeWidthComplement X = 0 := by
  unfold globalNaturalExtension at hL
  unfold globalEnvelopeWidthComplement
  exact credalEnvelopeWidthComplement_eq_zero_of_lower_eq_zero_upper_eq_one
    S.projectiveLimitCredalSet X hL hU

/-- The compatible global completions determine a gamble when every completion
assigns the same value to it. -/
def determinesGlobalGamble
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global) : Prop :=
  credalSetDetermines S.projectiveLimitCredalSet X

/-- The compatible global completions leave genuine interval-width on a gamble
when two completions strictly disagree on it. -/
def hasStrictGlobalWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global) : Prop :=
  credalSetHasStrictWidth S.projectiveLimitCredalSet X

/-- Global natural extension packaged as a lower prevision once nonemptiness
and bounded-below envelopes have been supplied. -/
noncomputable def globalNaturalExtensionPrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet)) :
    LowerPrevision Global :=
  lowerEnvelopePrevision S.projectiveLimitCredalSet hNonempty hBdd

/-- Global upper envelope packaged as an upper prevision once nonemptiness and
bounded-above envelopes have been supplied. -/
noncomputable def globalUpperEnvelopePrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddAbove ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet)) :
    UpperPrevision Global :=
  upperEnvelopePrevision S.projectiveLimitCredalSet hNonempty hBdd

/-- Finite projective natural extension: when the global state space is finite,
boundedness of the compatible-completion envelope is automatic. -/
noncomputable def finiteGlobalNaturalExtensionPrevision
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    LowerPrevision Global :=
  finiteLowerEnvelopePrevision S.projectiveLimitCredalSet hNonempty

/-- Finite projective upper envelope: when the global state space is finite,
boundedness of the compatible-completion envelope is automatic. -/
noncomputable def finiteGlobalUpperEnvelopePrevision
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    UpperPrevision Global :=
  finiteUpperEnvelopePrevision S.projectiveLimitCredalSet hNonempty

@[simp] theorem finiteGlobalNaturalExtensionPrevision_apply
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) (X : Gamble Global) :
    S.finiteGlobalNaturalExtensionPrevision hNonempty X =
      S.globalNaturalExtension X :=
  rfl

@[simp] theorem finiteGlobalUpperEnvelopePrevision_apply
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) (X : Gamble Global) :
    S.finiteGlobalUpperEnvelopePrevision hNonempty X =
      upperEnvelope S.projectiveLimitCredalSet X :=
  rfl

/-- The packaged global natural extension is below every compatible global
completion. -/
theorem globalNaturalExtensionPrevision_le_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (X : Gamble Global) :
    S.globalNaturalExtensionPrevision hNonempty hBdd X ≤ P X :=
  lowerEnvelopePrevision_le_completion S.projectiveLimitCredalSet
    hNonempty hBdd hP X

/-- The packaged global natural extension is the greatest lower prevision
pointwise dominated by every compatible global completion. -/
theorem globalNaturalExtensionPrevision_greatest_lower_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (L : LowerPrevision Global)
    (hL : ∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
      ∀ X : Gamble Global, L X ≤ P X)
    (X : Gamble Global) :
    L X ≤ S.globalNaturalExtensionPrevision hNonempty hBdd X :=
  lowerEnvelopePrevision_greatest_lower_bound S.projectiveLimitCredalSet
    hNonempty hBdd L hL X

/-- The packaged global natural extension has Walley's exact representation as
the lower envelope of the precise previsions dominating it. -/
theorem globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet)) :
    hasExactDominatingPreciseEnvelope
      (S.globalNaturalExtensionPrevision hNonempty hBdd) :=
  lowerPrevision_hasExactDominatingPreciseEnvelope
    (S.globalNaturalExtensionPrevision hNonempty hBdd)

/-- Re-envelope the packaged global natural extension by its dominating precise
previsions and recover the same lower prevision. -/
theorem globalNaturalExtensionPrevision_dominatingEnvelope_eq
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet)) :
    lowerEnvelopePrevision
        (dominatingPreciseCompletions
          (S.globalNaturalExtensionPrevision hNonempty hBdd))
        (dominatingPreciseCompletions_nonempty
          (S.globalNaturalExtensionPrevision hNonempty hBdd))
        (dominatingPreciseCompletions_bddBelow
          (S.globalNaturalExtensionPrevision hNonempty hBdd)) =
      S.globalNaturalExtensionPrevision hNonempty hBdd :=
  lowerEnvelopePrevision_dominatingPreciseCompletions_eq
    (S.globalNaturalExtensionPrevision hNonempty hBdd)

/-- Query-wise Walley completion for a packaged global natural extension.  The
touching prevision dominates the natural extension; it is not claimed to be one
of the original compatible global completions. -/
theorem globalNaturalExtensionPrevision_exists_dominatingPreciseCompletion_touching
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (X : Gamble Global) :
    ∃ P : PrecisePrevision Global,
      P ∈ dominatingPreciseCompletions
        (S.globalNaturalExtensionPrevision hNonempty hBdd) ∧
      P X = S.globalNaturalExtension X := by
  simpa [globalNaturalExtensionPrevision, globalNaturalExtension] using
    exists_dominatingPreciseCompletion_touching
      (S.globalNaturalExtensionPrevision hNonempty hBdd) X

/-- Every compatible global completion is below the packaged global upper
envelope. -/
theorem globalCompletion_le_upperEnvelopePrevision
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddAbove ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (X : Gamble Global) :
    P X ≤ S.globalUpperEnvelopePrevision hNonempty hBdd X :=
  completion_le_upperEnvelopePrevision S.projectiveLimitCredalSet
    hNonempty hBdd hP X

/-- The packaged global upper envelope is the least upper prevision
dominating every compatible global completion. -/
theorem globalUpperEnvelopePrevision_least_upper_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddAbove ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (U : UpperPrevision Global)
    (hU : ∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
      ∀ X : Gamble Global, P X ≤ U X)
    (X : Gamble Global) :
    S.globalUpperEnvelopePrevision hNonempty hBdd X ≤ U X :=
  upperEnvelopePrevision_least_upper_bound S.projectiveLimitCredalSet
    hNonempty hBdd U hU X

/-- The conjugate upper prevision of the packaged global natural extension is
the projective global upper envelope. -/
theorem globalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (X : Gamble Global) :
    (S.globalNaturalExtensionPrevision hNonempty hBdd).conjugate X =
      upperEnvelope S.projectiveLimitCredalSet X :=
  lowerEnvelopePrevision_conjugate_eq_upperEnvelope
    S.projectiveLimitCredalSet hNonempty hBdd X

/-- The conjugate lower prevision of the packaged global upper envelope is the
projective global natural extension. -/
theorem globalUpperEnvelopePrevision_conjugate_eq_naturalExtension
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddAbove ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (X : Gamble Global) :
    (S.globalUpperEnvelopePrevision hNonempty hBdd).conjugate X =
      S.globalNaturalExtension X :=
  upperEnvelopePrevision_conjugate_eq_lowerEnvelope
    S.projectiveLimitCredalSet hNonempty hBdd X

/-- On a finite global state space, boundedness is automatic, so the finite
global natural extension is below every compatible completion. -/
theorem finiteGlobalNaturalExtensionPrevision_le_completion
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (X : Gamble Global) :
    S.finiteGlobalNaturalExtensionPrevision hNonempty X ≤ P X :=
  finiteLowerEnvelopePrevision_le_completion S.projectiveLimitCredalSet
    hNonempty hP X

/-- On a finite global state space, the finite global natural extension is the
greatest lower prevision dominated by all compatible completions. -/
theorem finiteGlobalNaturalExtensionPrevision_greatest_lower_bound
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (L : LowerPrevision Global)
    (hL : ∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
      ∀ X : Gamble Global, L X ≤ P X)
    (X : Gamble Global) :
    L X ≤ S.finiteGlobalNaturalExtensionPrevision hNonempty X :=
  finiteLowerEnvelopePrevision_greatest_lower_bound
    S.projectiveLimitCredalSet hNonempty L hL X

/-- Finite global natural extensions inherit the exact dominating
precise-envelope representation. -/
theorem finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    hasExactDominatingPreciseEnvelope
      (S.finiteGlobalNaturalExtensionPrevision hNonempty) :=
  finiteLowerEnvelopePrevision_hasExactDominatingPreciseEnvelope
    S.projectiveLimitCredalSet hNonempty

/-- Re-envelope the finite global natural extension by its dominating precise
previsions and recover the same lower prevision. -/
theorem finiteGlobalNaturalExtensionPrevision_dominatingEnvelope_eq
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    lowerEnvelopePrevision
        (dominatingPreciseCompletions
          (S.finiteGlobalNaturalExtensionPrevision hNonempty))
        (dominatingPreciseCompletions_nonempty
          (S.finiteGlobalNaturalExtensionPrevision hNonempty))
        (dominatingPreciseCompletions_bddBelow
          (S.finiteGlobalNaturalExtensionPrevision hNonempty)) =
      S.finiteGlobalNaturalExtensionPrevision hNonempty :=
  lowerEnvelopePrevision_dominatingPreciseCompletions_eq
    (S.finiteGlobalNaturalExtensionPrevision hNonempty)

/-- Query-wise Walley completion for finite global natural extensions. -/
theorem finiteGlobalNaturalExtensionPrevision_exists_dominatingPreciseCompletion_touching
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global) :
    ∃ P : PrecisePrevision Global,
      P ∈ dominatingPreciseCompletions
        (S.finiteGlobalNaturalExtensionPrevision hNonempty) ∧
      P X = S.globalNaturalExtension X := by
  simpa using
    exists_dominatingPreciseCompletion_touching
      (S.finiteGlobalNaturalExtensionPrevision hNonempty) X

/-- On a finite global state space, every compatible completion is below the
finite global upper envelope. -/
theorem finiteGlobalCompletion_le_upperEnvelopePrevision
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (X : Gamble Global) :
    P X ≤ S.finiteGlobalUpperEnvelopePrevision hNonempty X :=
  finiteCompletion_le_upperEnvelopePrevision S.projectiveLimitCredalSet
    hNonempty hP X

/-- On a finite global state space, the finite global upper envelope is the
least upper prevision dominating all compatible completions. -/
theorem finiteGlobalUpperEnvelopePrevision_least_upper_bound
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (U : UpperPrevision Global)
    (hU : ∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
      ∀ X : Gamble Global, P X ≤ U X)
    (X : Gamble Global) :
    S.finiteGlobalUpperEnvelopePrevision hNonempty X ≤ U X :=
  finiteUpperEnvelopePrevision_least_upper_bound
    S.projectiveLimitCredalSet hNonempty U hU X

/-- Finite global natural-extension conjugacy: boundedness is automatic. -/
theorem finiteGlobalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global) :
    (S.finiteGlobalNaturalExtensionPrevision hNonempty).conjugate X =
      upperEnvelope S.projectiveLimitCredalSet X :=
  lowerEnvelopePrevision_conjugate_eq_upperEnvelope
    S.projectiveLimitCredalSet hNonempty
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet) X

/-- Strict finite projective width is realized by Walley dominating precise
completions of the finite global natural extension.

This is the reusable endpoint-readout theorem for finite projective credal
systems: when compatible completions have strict width on a global gamble, the
finite natural extension has lower- and upper-touching dominating precise
completions, and those endpoints compute the PLN-facing width,
width-complement, and midpoint coordinates. -/
theorem finiteGlobalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hWidth : S.hasStrictGlobalWidth X) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ dominatingPreciseCompletions
          (S.finiteGlobalNaturalExtensionPrevision hNonempty) ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ dominatingPreciseCompletions
          (S.finiteGlobalNaturalExtensionPrevision hNonempty) ∧
        Plo X = S.globalNaturalExtension X ∧
        Phi X = upperEnvelope S.projectiveLimitCredalSet X ∧
        Plo X < Phi X ∧
        S.globalEnvelopeWidth X = Phi X - Plo X ∧
        S.globalEnvelopeWidthComplement X = 1 - (Phi X - Plo X) ∧
        S.globalEnvelopeMidpoint X = (Plo X + Phi X) / 2 := by
  let L : LowerPrevision Global := S.finiteGlobalNaturalExtensionPrevision hNonempty
  have hExact : hasExactDominatingPreciseEnvelope L := by
    dsimp [L]
    exact S.finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      hNonempty
  have hLower :
      L X = S.globalNaturalExtension X := by
    simp [L]
  have hUpper :
      L.conjugate X = upperEnvelope S.projectiveLimitCredalSet X := by
    dsimp [L]
    exact S.finiteGlobalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
      hNonempty X
  have hLowerUpper :
      S.globalNaturalExtension X <
        upperEnvelope S.projectiveLimitCredalSet X :=
    lower_upperEnvelope_nontrivial_of_strictWidth S.projectiveLimitCredalSet X
      (finite_credalRange_bddBelow S.projectiveLimitCredalSet X)
      (finite_credalRange_bddAbove S.projectiveLimitCredalSet X)
      hWidth
  have hStrict : L X < L.conjugate X := by
    calc
      L X = S.globalNaturalExtension X := hLower
      _ < upperEnvelope S.projectiveLimitCredalSet X := hLowerUpper
      _ = L.conjugate X := hUpper.symm
  rcases hExact.exists_strictEndpointPairReadout X hStrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, _hWidthD, _hCompD, _hMidD⟩
  have hloGlobal :
      Plo X = S.globalNaturalExtension X :=
    hlo.trans hLower
  have hhiGlobal :
      Phi X = upperEnvelope S.projectiveLimitCredalSet X :=
    hhi.trans hUpper
  have hloProjective :
      Plo X = lowerEnvelope S.projectiveLimitCredalSet X := by
    simpa [ProjectiveLocalCredalSpec.globalNaturalExtension] using hloGlobal
  refine ⟨Plo, ?_, Phi, ?_, hloGlobal, hhiGlobal, hlt, ?_, ?_, ?_⟩
  · simpa [L] using hPlo
  · simpa [L] using hPhi
  · exact
      credalEnvelopeWidth_eq_endpointGap
        S.projectiveLimitCredalSet X Plo Phi hloProjective hhiGlobal
  · exact
      credalEnvelopeWidthComplement_eq_one_sub_endpointGap
        S.projectiveLimitCredalSet X Plo Phi hloProjective hhiGlobal
  · exact
      credalEnvelopeMidpoint_eq_endpointMean
        S.projectiveLimitCredalSet X Plo Phi hloProjective hhiGlobal

/-- Finite global upper-envelope conjugacy: boundedness is automatic. -/
theorem finiteGlobalUpperEnvelopePrevision_conjugate_eq_naturalExtension
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global) :
    (S.finiteGlobalUpperEnvelopePrevision hNonempty).conjugate X =
      S.globalNaturalExtension X :=
  upperEnvelopePrevision_conjugate_eq_lowerEnvelope
    S.projectiveLimitCredalSet hNonempty
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet) X

/-- Local lower envelope at one window. -/
noncomputable def localNaturalExtension
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) : Gamble (S.cylinders.Local i) → ℝ :=
  lowerEnvelope (S.localCredal i)

/-- Local upper envelope at one window. -/
noncomputable def localUpperEnvelope
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) : Gamble (S.cylinders.Local i) → ℝ :=
  upperEnvelope (S.localCredal i)

/-- Local credal-envelope width at one window. -/
noncomputable def localEnvelopeWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  credalEnvelopeWidth (S.localCredal i) X

/-- Local credal-envelope width complement at one window. -/
noncomputable def localEnvelopeWidthComplement
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  credalEnvelopeWidthComplement (S.localCredal i) X

/-- Local credal-envelope midpoint at one window. -/
noncomputable def localEnvelopeMidpoint
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) : ℝ :=
  credalEnvelopeMidpoint (S.localCredal i) X

/-- Exact-cylinder interval-width theorem at the restricted cylinder-domain
completion layer. -/
theorem cylinderEnvelopeWidth_eq_localEnvelopeWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBddBelow : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hCylinderBddAbove : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i) :
    S.cylinderEnvelopeWidth i X = S.localEnvelopeWidth i X := by
  change S.cylinderUpperEnvelope i X - S.cylinderNaturalExtension i X =
    S.localUpperEnvelope i X - S.localNaturalExtension i X
  rw [
    S.cylinderUpperEnvelope_eq_localUpperEnvelope_of_exact
      hCylinderNonempty i X hLocalNonempty hLocalBddAbove
      hCylinderBddAbove hExact,
    S.cylinderNaturalExtension_eq_localLowerEnvelope_of_exact
      hCylinderNonempty i X hLocalNonempty hLocalBddBelow
      hCylinderBddBelow hExact]
  simp [localUpperEnvelope, localNaturalExtension]

/-- Exact-cylinder width-complement theorem at the restricted cylinder-domain
completion layer. -/
theorem cylinderEnvelopeWidthComplement_eq_localEnvelopeWidthComplement_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBddBelow : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hCylinderBddAbove : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i) :
    S.cylinderEnvelopeWidthComplement i X =
      S.localEnvelopeWidthComplement i X := by
  change 1 - S.cylinderEnvelopeWidth i X =
    1 - S.localEnvelopeWidth i X
  rw [
    S.cylinderEnvelopeWidth_eq_localEnvelopeWidth_of_exact
      hCylinderNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
      hCylinderBddBelow hCylinderBddAbove hExact]

/-- Exact-cylinder midpoint theorem at the restricted cylinder-domain
completion layer. -/
theorem cylinderEnvelopeMidpoint_eq_localEnvelopeMidpoint_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBddBelow : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hCylinderBddAbove : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i) :
    S.cylinderEnvelopeMidpoint i X = S.localEnvelopeMidpoint i X := by
  change
    (S.cylinderNaturalExtension i X + S.cylinderUpperEnvelope i X) / 2 =
      (S.localNaturalExtension i X + S.localUpperEnvelope i X) / 2
  rw [
    S.cylinderNaturalExtension_eq_localLowerEnvelope_of_exact
      hCylinderNonempty i X hLocalNonempty hLocalBddBelow
      hCylinderBddBelow hExact,
    S.cylinderUpperEnvelope_eq_localUpperEnvelope_of_exact
      hCylinderNonempty i X hLocalNonempty hLocalBddAbove
      hCylinderBddAbove hExact]
  simp [localNaturalExtension, localUpperEnvelope]

/-- Exact local full-unit interval forces the restricted cylinder midpoint
display to one half. -/
theorem cylinderEnvelopeMidpoint_eq_half_of_localCredal_unitInterval_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBddBelow : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hCylinderBddAbove : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.cylinderEnvelopeMidpoint i X = (1 / 2 : ℝ) := by
  rw [S.cylinderEnvelopeMidpoint_eq_localEnvelopeMidpoint_of_exact
    hCylinderNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hCylinderBddBelow hCylinderBddAbove hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeMidpoint credalEnvelopeMidpoint
  unfold ProjectiveLocalCredalSpec.localNaturalExtension at hL
  unfold ProjectiveLocalCredalSpec.localUpperEnvelope at hU
  rw [hL, hU]
  ring

/-- Exact local full-unit interval forces the restricted cylinder width to be
maximal. -/
theorem cylinderEnvelopeWidth_eq_one_of_localCredal_unitInterval_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBddBelow : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hCylinderBddAbove : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.cylinderEnvelopeWidth i X = 1 := by
  rw [S.cylinderEnvelopeWidth_eq_localEnvelopeWidth_of_exact
    hCylinderNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hCylinderBddBelow hCylinderBddAbove hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeWidth credalEnvelopeWidth
  unfold ProjectiveLocalCredalSpec.localNaturalExtension at hL
  unfold ProjectiveLocalCredalSpec.localUpperEnvelope at hU
  rw [hL, hU]
  ring

/-- Exact local full-unit interval forces the restricted cylinder
width-complement display to zero. -/
theorem cylinderEnvelopeWidthComplement_eq_zero_of_localCredal_unitInterval_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hCylinderNonempty : S.hasCompatibleCylinderCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
        S.localCredal i))
    (hCylinderBddBelow : BddBelow
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hCylinderBddAbove : BddAbove
      ((fun K : S.cylinders.CylinderPrevision => K.toFun i X) ''
        S.projectiveCylinderCredalSet))
    (hExact : S.localCylinderCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.cylinderEnvelopeWidthComplement i X = 0 := by
  rw [S.cylinderEnvelopeWidthComplement_eq_localEnvelopeWidthComplement_of_exact
    hCylinderNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hCylinderBddBelow hCylinderBddAbove hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeWidthComplement
    credalEnvelopeWidthComplement
  rw [credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one]
  · ring
  · exact hL
  · exact hU

theorem compatible_completion_has_local_marginal
    (S : ProjectiveLocalCredalSpec Window Global)
    {P : PrecisePrevision Global}
    (hP : P ∈ S.projectiveLimitCredalSet) (i : Window) :
    S.cylinders.marginalPrevision i P ∈ S.localCredal i :=
  hP i

theorem localNaturalExtension_le_global_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    {P : PrecisePrevision Global}
    (hP : P ∈ S.projectiveLimitCredalSet)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hBdd : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i)) :
    S.localNaturalExtension i X ≤
      P (S.cylinders.cylinderGamble i X) := by
  exact lowerEnvelope_le_of_mem (S.localCredal i) X hBdd
    (compatible_completion_has_local_marginal S hP i)

theorem globalNaturalExtension_le_completion
    (S : ProjectiveLocalCredalSpec Window Global)
    {P : PrecisePrevision Global}
    (hP : P ∈ S.projectiveLimitCredalSet)
    (X : Gamble Global)
    (hBdd : BddBelow
      ((fun Q : PrecisePrevision Global => Q X) '' S.projectiveLimitCredalSet)) :
    S.globalNaturalExtension X ≤ P X :=
  lowerEnvelope_le_of_mem S.projectiveLimitCredalSet X hBdd hP

theorem globalNaturalExtension_lower_bound
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global) (c : ℝ) (hc : ∀ ω, c ≤ X ω) :
    c ≤ S.globalNaturalExtension X :=
  lowerEnvelope_lower_bound S.projectiveLimitCredalSet hNonempty X c hc

theorem globalNaturalExtension_superadditive
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (X Y : Gamble Global) :
    S.globalNaturalExtension X + S.globalNaturalExtension Y ≤
      S.globalNaturalExtension (X + Y) :=
  lowerEnvelope_superadditive S.projectiveLimitCredalSet hNonempty hBdd X Y

theorem globalEnvelopeWidth_nonneg_of_nonempty
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet)) :
    0 ≤ S.globalEnvelopeWidth X :=
  credalEnvelopeWidth_nonneg_of_nonempty S.projectiveLimitCredalSet X
    hNonempty hBddBelow hBddAbove

theorem globalEnvelopeWidth_in_unit_of_unit
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    S.globalEnvelopeWidth X ∈ Set.Icc (0 : ℝ) 1 :=
  credalEnvelopeWidth_in_unit_of_unit S.projectiveLimitCredalSet X
    hNonempty hBddBelow hBddAbove hX

theorem globalEnvelopeWidthComplement_in_unit_of_unit
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    S.globalEnvelopeWidthComplement X ∈ Set.Icc (0 : ℝ) 1 :=
  credalEnvelopeWidthComplement_in_unit_of_unit S.projectiveLimitCredalSet X
    hNonempty hBddBelow hBddAbove hX

theorem globalEnvelopeMidpoint_in_unit_of_unit
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    S.globalEnvelopeMidpoint X ∈ Set.Icc (0 : ℝ) 1 :=
  credalEnvelopeMidpoint_in_unit_of_unit S.projectiveLimitCredalSet X
    hNonempty hBddBelow hBddAbove hX

theorem finiteGlobalEnvelopeWidth_in_unit_of_unit
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    S.globalEnvelopeWidth X ∈ Set.Icc (0 : ℝ) 1 :=
  S.globalEnvelopeWidth_in_unit_of_unit hNonempty X
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet X)
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet X) hX

theorem finiteGlobalEnvelopeWidthComplement_in_unit_of_unit
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    S.globalEnvelopeWidthComplement X ∈ Set.Icc (0 : ℝ) 1 :=
  S.globalEnvelopeWidthComplement_in_unit_of_unit hNonempty X
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet X)
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet X) hX

theorem finiteGlobalEnvelopeMidpoint_in_unit_of_unit
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) :
    S.globalEnvelopeMidpoint X ∈ Set.Icc (0 : ℝ) 1 :=
  S.globalEnvelopeMidpoint_in_unit_of_unit hNonempty X
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet X)
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet X) hX

theorem globalNaturalExtension_eq_of_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (hDet : S.determinesGlobalGamble X) :
    S.globalNaturalExtension X = P X :=
  lowerEnvelope_eq_of_credalSetDetermines S.projectiveLimitCredalSet X
    hNonempty hBddBelow hP hDet

theorem globalEnvelopeWidth_eq_zero_of_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (hDet : S.determinesGlobalGamble X) :
    S.globalEnvelopeWidth X = 0 :=
  credalEnvelopeWidth_eq_zero_of_credalSetDetermines
    S.projectiveLimitCredalSet X hNonempty hBddBelow hBddAbove hP hDet

theorem globalEnvelopeMidpoint_eq_of_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (hDet : S.determinesGlobalGamble X) :
    S.globalEnvelopeMidpoint X = P X :=
  credalEnvelopeMidpoint_eq_of_credalSetDetermines
    S.projectiveLimitCredalSet X hNonempty hBddBelow hBddAbove hP hDet

theorem globalLowerUpperEnvelope_eq_of_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    {P : PrecisePrevision Global} (hP : P ∈ S.projectiveLimitCredalSet)
    (hDet : S.determinesGlobalGamble X) :
    S.globalNaturalExtension X =
      upperEnvelope S.projectiveLimitCredalSet X :=
  lower_eq_upperEnvelope_of_credalSetDetermines S.projectiveLimitCredalSet X
    hNonempty hBddBelow hBddAbove hP hDet

theorem not_determinesGlobalGamble_of_strictWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    {X : Gamble Global} (hWidth : S.hasStrictGlobalWidth X) :
    ¬ S.determinesGlobalGamble X :=
  not_credalSetDetermines_of_strictWidth hWidth

/-- Failure of global determination is exactly genuine strict width in the
compatible-completion credal set. -/
theorem hasStrictGlobalWidth_of_not_determinesGlobalGamble
    (S : ProjectiveLocalCredalSpec Window Global)
    {X : Gamble Global} (hNotDet : ¬ S.determinesGlobalGamble X) :
    S.hasStrictGlobalWidth X :=
  credalSetHasStrictWidth_of_not_determines S.projectiveLimitCredalSet X
    hNotDet

/-- A projective credal specification leaves interval width on a global gamble
exactly when its compatible completions do not determine that gamble. -/
theorem hasStrictGlobalWidth_iff_not_determinesGlobalGamble
    (S : ProjectiveLocalCredalSpec Window Global) (X : Gamble Global) :
    S.hasStrictGlobalWidth X ↔ ¬ S.determinesGlobalGamble X :=
  credalSetHasStrictWidth_iff_not_determines S.projectiveLimitCredalSet X

theorem globalLowerUpperEnvelope_nontrivial_of_strictWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hWidth : S.hasStrictGlobalWidth X) :
    S.globalNaturalExtension X <
      upperEnvelope S.projectiveLimitCredalSet X :=
  lower_upperEnvelope_nontrivial_of_strictWidth S.projectiveLimitCredalSet X
    hBddBelow hBddAbove hWidth

theorem globalEnvelopeWidth_pos_of_strictWidth
    (S : ProjectiveLocalCredalSpec Window Global)
    (X : Gamble Global)
    (hBddBelow : BddBelow
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hBddAbove : BddAbove
      ((fun P : PrecisePrevision Global => P X) '' S.projectiveLimitCredalSet))
    (hWidth : S.hasStrictGlobalWidth X) :
    0 < S.globalEnvelopeWidth X :=
  credalEnvelopeWidth_pos_of_strictWidth S.projectiveLimitCredalSet X
    hBddBelow hBddAbove hWidth

/-- Strict projective width is realized by Walley dominating precise
completions of the packaged global natural extension.

This is the non-finite parent of the finite endpoint theorem: once the
compatible-completion envelope is bounded below and above, strict width on a
global gamble produces lower- and upper-touching dominating precise
completions.  The endpoint gap computes the PLN-facing width,
width-complement, and midpoint coordinates. -/
theorem globalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBddBelow : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (hBddAbove : ∀ X : Gamble Global,
      BddAbove ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet))
    (X : Gamble Global)
    (hWidth : S.hasStrictGlobalWidth X) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ dominatingPreciseCompletions
          (S.globalNaturalExtensionPrevision hNonempty hBddBelow) ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ dominatingPreciseCompletions
          (S.globalNaturalExtensionPrevision hNonempty hBddBelow) ∧
        Plo X = S.globalNaturalExtension X ∧
        Phi X = upperEnvelope S.projectiveLimitCredalSet X ∧
        Plo X < Phi X ∧
        S.globalEnvelopeWidth X = Phi X - Plo X ∧
        S.globalEnvelopeWidthComplement X = 1 - (Phi X - Plo X) ∧
        S.globalEnvelopeMidpoint X = (Plo X + Phi X) / 2 := by
  let L : LowerPrevision Global :=
    S.globalNaturalExtensionPrevision hNonempty hBddBelow
  have hExact : hasExactDominatingPreciseEnvelope L := by
    dsimp [L]
    exact S.globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      hNonempty hBddBelow
  have hLower :
      L X = S.globalNaturalExtension X := by
    simp [L, globalNaturalExtensionPrevision, globalNaturalExtension]
  have hUpper :
      L.conjugate X = upperEnvelope S.projectiveLimitCredalSet X := by
    dsimp [L]
    exact S.globalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
      hNonempty hBddBelow X
  have hLowerUpper :
      S.globalNaturalExtension X <
        upperEnvelope S.projectiveLimitCredalSet X :=
    S.globalLowerUpperEnvelope_nontrivial_of_strictWidth X
      (hBddBelow X) (hBddAbove X) hWidth
  have hStrict : L X < L.conjugate X := by
    calc
      L X = S.globalNaturalExtension X := hLower
      _ < upperEnvelope S.projectiveLimitCredalSet X := hLowerUpper
      _ = L.conjugate X := hUpper.symm
  rcases hExact.exists_strictEndpointPairReadout X hStrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, _hWidthD, _hCompD, _hMidD⟩
  have hloGlobal :
      Plo X = S.globalNaturalExtension X :=
    hlo.trans hLower
  have hhiGlobal :
      Phi X = upperEnvelope S.projectiveLimitCredalSet X :=
    hhi.trans hUpper
  have hloProjective :
      Plo X = lowerEnvelope S.projectiveLimitCredalSet X := by
    simpa [ProjectiveLocalCredalSpec.globalNaturalExtension] using hloGlobal
  refine ⟨Plo, hPlo, Phi, hPhi, hloGlobal, hhiGlobal, hlt, ?_, ?_, ?_⟩
  · exact
      credalEnvelopeWidth_eq_endpointGap
        S.projectiveLimitCredalSet X Plo Phi hloProjective hhiGlobal
  · exact
      credalEnvelopeWidthComplement_eq_one_sub_endpointGap
        S.projectiveLimitCredalSet X Plo Phi hloProjective hhiGlobal
  · exact
      credalEnvelopeMidpoint_eq_endpointMean
        S.projectiveLimitCredalSet X Plo Phi hloProjective hhiGlobal

/-- The packaged natural extension satisfies the weak no-sure-loss condition
that nonnegative gambles receive nonnegative lower prevision.  Strict avoiding
sure loss is a stronger regularity assumption and is not bundled into this
projective lower-envelope skeleton. -/
theorem globalNaturalExtensionPrevision_avoidsWeakSureLoss
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet)) :
    (S.globalNaturalExtensionPrevision hNonempty hBdd).avoidsWeakSureLoss :=
  LowerPrevision.avoidsWeakSureLoss_of_lower_bound
    (S.globalNaturalExtensionPrevision hNonempty hBdd)

/-- The packaged projective natural extension avoids uniform sure loss on any
global state space.  This is the infinite-domain no-arbitrage guarantee that
does not require compactness or finiteness: a positive uniform margin is enough
for a strictly positive lower envelope. -/
theorem globalNaturalExtensionPrevision_avoidsUniformSureLoss
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.projectiveLimitCredalSet)) :
    (S.globalNaturalExtensionPrevision hNonempty hBdd).avoidsUniformSureLoss :=
  lowerEnvelopePrevision_avoidsUniformSureLoss
    S.projectiveLimitCredalSet hNonempty hBdd

theorem finiteGlobalNaturalExtensionPrevision_avoidsSureLoss
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    (S.finiteGlobalNaturalExtensionPrevision hNonempty).avoidsSureLoss :=
  finiteLowerEnvelopePrevision_avoidsSureLoss
    S.projectiveLimitCredalSet hNonempty

theorem finiteGlobalNaturalExtensionPrevision_isCoherent
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    (S.finiteGlobalNaturalExtensionPrevision hNonempty).isCoherent :=
  finiteLowerEnvelopePrevision_isCoherent
    S.projectiveLimitCredalSet hNonempty

/-- Weak no-sure-loss restricted to cylinder gambles. -/
def cylinderGamblesAvoidWeakSureLoss
    (S : ProjectiveLocalCredalSpec Window Global) : Prop :=
  ∀ (i : Window) (X : Gamble (S.cylinders.Local i)),
    (∀ ω, 0 ≤ S.cylinders.cylinderGamble i X ω) →
      0 ≤ S.globalNaturalExtension (S.cylinders.cylinderGamble i X)

/-- Uniform strict no-sure-loss restricted to cylinder gambles.  The explicit
uniform margin is the infinite-domain guard: pointwise positivity alone need
not have a positive infimum. -/
def cylinderGamblesAvoidUniformSureLoss
    (S : ProjectiveLocalCredalSpec Window Global) : Prop :=
  ∀ (i : Window) (X : Gamble (S.cylinders.Local i)),
    (∃ ε : ℝ, 0 < ε ∧ ∀ ω, ε ≤ S.cylinders.cylinderGamble i X ω) →
      0 < S.globalNaturalExtension (S.cylinders.cylinderGamble i X)

theorem globalNaturalExtension_cylinder_avoidsWeakSureLoss
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    S.cylinderGamblesAvoidWeakSureLoss := by
  intro i X hX
  exact S.globalNaturalExtension_lower_bound hNonempty
    (S.cylinders.cylinderGamble i X) 0 hX

theorem globalNaturalExtension_cylinder_avoidsUniformSureLoss
    (S : ProjectiveLocalCredalSpec Window Global)
    (hNonempty : S.hasCompatibleCompletion) :
    S.cylinderGamblesAvoidUniformSureLoss := by
  intro i X hX
  rcases hX with ⟨ε, hεpos, hε⟩
  exact lt_of_lt_of_le hεpos
    (S.globalNaturalExtension_lower_bound hNonempty
      (S.cylinders.cylinderGamble i X) ε hε)

theorem localNaturalExtension_le_globalNaturalExtension_on_cylinder
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBdd : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i)) :
    S.localNaturalExtension i X ≤
      S.globalNaturalExtension (S.cylinders.cylinderGamble i X) := by
  apply le_lowerEnvelope_of_forall_le S.projectiveLimitCredalSet hGlobalNonempty
  intro P hP
  exact S.localNaturalExtension_le_global_completion hP i X hLocalBdd

/-- Every compatible global completion lies below the local upper envelope on a
cylinder gamble. -/
theorem global_completion_le_localUpperEnvelope_on_cylinder
    (S : ProjectiveLocalCredalSpec Window Global)
    {P : PrecisePrevision Global}
    (hP : P ∈ S.projectiveLimitCredalSet)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBdd : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i)) :
    P (S.cylinders.cylinderGamble i X) ≤
      S.localUpperEnvelope i X := by
  exact le_upperEnvelope_of_mem (S.localCredal i) X hLocalBdd
    (compatible_completion_has_local_marginal S hP i)

/-- The global upper envelope on a cylinder gamble is no larger than the local
upper envelope.  Without exactness, the global completions can be a proper
subset of the local credal set, so this is generally only an inequality. -/
theorem globalUpperEnvelope_le_localUpperEnvelope_on_cylinder
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBdd : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i)) :
    upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) ≤
      S.localUpperEnvelope i X := by
  apply upperEnvelope_le_of_forall_le S.projectiveLimitCredalSet
    hGlobalNonempty
  intro P hP
  exact S.global_completion_le_localUpperEnvelope_on_cylinder hP i X hLocalBdd

/-- A local credal set is exact at window `i` when every local precise
completion lifts to a compatible global completion with the same marginal. -/
def localCredalExactAt
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window) : Prop :=
  ∀ R : PrecisePrevision (S.cylinders.Local i), R ∈ S.localCredal i →
    ∃ P : PrecisePrevision Global,
      P ∈ S.projectiveLimitCredalSet ∧ S.cylinders.marginalPrevision i P = R

/-- Local credal determination always lifts to global determination of the
corresponding cylinder gamble: compatible global completions have admissible
local marginals. -/
theorem determinesGlobalGamble_cylinder_of_localCredal_determines
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.determinesGlobalGamble (S.cylinders.cylinderGamble i X) := by
  intro P hP Q hQ
  exact hDet (S.cylinders.marginalPrevision i P) (hP i)
    (S.cylinders.marginalPrevision i Q) (hQ i)

/-- Exact local lifting reflects global cylinder determination back to the
stipulated local credal set. -/
theorem localCredal_determines_of_determinesGlobalGamble_cylinder_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (hExact : S.localCredalExactAt i)
    (X : Gamble (S.cylinders.Local i))
    (hDet : S.determinesGlobalGamble (S.cylinders.cylinderGamble i X)) :
    credalSetDetermines (S.localCredal i) X := by
  intro R hR Q hQ
  rcases hExact R hR with ⟨P, hP, hPi⟩
  rcases hExact Q hQ with ⟨P', hP', hP'i⟩
  have hGlobal := hDet P hP P' hP'
  have hPX : P (S.cylinders.cylinderGamble i X) = R X :=
    congrArg (fun T : PrecisePrevision (S.cylinders.Local i) => T X) hPi
  have hP'X : P' (S.cylinders.cylinderGamble i X) = Q X :=
    congrArg (fun T : PrecisePrevision (S.cylinders.Local i) => T X) hP'i
  rw [← hPX, ← hP'X]
  exact hGlobal

/-- Under exact local lifting, global determination of a cylinder gamble is
equivalent to local credal determination of the local gamble. -/
theorem determinesGlobalGamble_cylinder_iff_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (hExact : S.localCredalExactAt i)
    (X : Gamble (S.cylinders.Local i)) :
    S.determinesGlobalGamble (S.cylinders.cylinderGamble i X) ↔
      credalSetDetermines (S.localCredal i) X := by
  constructor
  · exact S.localCredal_determines_of_determinesGlobalGamble_cylinder_of_exact
      i hExact X
  · exact S.determinesGlobalGamble_cylinder_of_localCredal_determines i X

/-- Under exact local lifting, strict global interval width on a cylinder
gamble is equivalent to strict local credal width. -/
theorem hasStrictGlobalWidth_cylinder_iff_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (hExact : S.localCredalExactAt i)
    (X : Gamble (S.cylinders.Local i)) :
    S.hasStrictGlobalWidth (S.cylinders.cylinderGamble i X) ↔
      credalSetHasStrictWidth (S.localCredal i) X := by
  rw [S.hasStrictGlobalWidth_iff_not_determinesGlobalGamble,
    S.determinesGlobalGamble_cylinder_iff_localCredal_determines_of_exact
      i hExact X]
  exact (credalSetHasStrictWidth_iff_not_determines (S.localCredal i) X).symm

/-- Natural-extension theorem for cylinder gambles: when the local credal set
is exactly the image of compatible global completions at a window, the global
lower envelope on the pulled-back cylinder gamble agrees with the local lower
envelope. -/
theorem globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBdd : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBdd : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i) :
    S.globalNaturalExtension (S.cylinders.cylinderGamble i X) =
      S.localNaturalExtension i X := by
  refine le_antisymm ?_ ?_
  · apply le_lowerEnvelope_of_forall_le (S.localCredal i) hLocalNonempty
    intro R hR
    rcases hExact R hR with ⟨P, hP, hMarg⟩
    have hle :
        S.globalNaturalExtension (S.cylinders.cylinderGamble i X) ≤
          P (S.cylinders.cylinderGamble i X) :=
      S.globalNaturalExtension_le_completion hP
        (S.cylinders.cylinderGamble i X) hGlobalBdd
    have hPX : P (S.cylinders.cylinderGamble i X) = R X := by
      exact congrArg (fun T : PrecisePrevision (S.cylinders.Local i) => T X) hMarg
    exact hle.trans_eq hPX
  · exact S.localNaturalExtension_le_globalNaturalExtension_on_cylinder
      hGlobalNonempty i X hLocalBdd

/-- Finite cylinder exactness: for finite nonempty local and global state
spaces, the boundedness hypotheses in the exact-cylinder natural-extension
theorem are automatic. -/
theorem globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact_finite
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i) :
    S.globalNaturalExtension (S.cylinders.cylinderGamble i X) =
      S.localNaturalExtension i X :=
  S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
    hGlobalNonempty i X hLocalNonempty
    (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact

/-- Exact-cylinder upper-envelope theorem: when the local credal set is exactly
the image of compatible global completions at a window, the global upper
envelope on the pulled-back cylinder gamble agrees with the local upper
envelope. -/
theorem globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBdd : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBdd : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i) :
    upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) =
      S.localUpperEnvelope i X := by
  refine le_antisymm ?_ ?_
  · exact S.globalUpperEnvelope_le_localUpperEnvelope_on_cylinder
      hGlobalNonempty i X hLocalBdd
  · apply upperEnvelope_le_of_forall_le (S.localCredal i) hLocalNonempty
    intro R hR
    rcases hExact R hR with ⟨P, hP, hMarg⟩
    have hle :
        R X ≤
          upperEnvelope S.projectiveLimitCredalSet
            (S.cylinders.cylinderGamble i X) := by
      have hPX :
          P (S.cylinders.cylinderGamble i X) = R X := by
        exact congrArg (fun T : PrecisePrevision (S.cylinders.Local i) => T X) hMarg
      rw [← hPX]
      exact le_upperEnvelope_of_mem S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) hGlobalBdd hP
    exact hle

/-- Finite cylinder upper exactness: for finite nonempty local and global
state spaces, the boundedness hypotheses in the exact-cylinder upper-envelope
theorem are automatic. -/
theorem globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact_finite
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i) :
    upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) =
      S.localUpperEnvelope i X :=
  S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
    hGlobalNonempty i X hLocalNonempty
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact

/-- Exact-cylinder interval-width theorem: when local completions lift exactly,
the global compatible-completion interval width on the cylinder gamble is the
local credal interval width. -/
theorem globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i) :
    S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
      S.localEnvelopeWidth i X := by
  change
    upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) -
      S.globalNaturalExtension (S.cylinders.cylinderGamble i X) =
    S.localUpperEnvelope i X - S.localNaturalExtension i X
  rw [
    S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddAbove
      hGlobalBddAbove hExact,
    S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow
      hGlobalBddBelow hExact]

/-- Exact-cylinder width-complement theorem: the PLN-style confidence display
coordinate derived from interval width is local/global exact under the same
local lifting condition. -/
theorem globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
      S.localEnvelopeWidthComplement i X := by
  change 1 - S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
    1 - S.localEnvelopeWidth i X
  rw [
    S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
      hGlobalBddBelow hGlobalBddAbove hExact]

/-- Exact-cylinder midpoint theorem: the PLN-style point-estimate coordinate
derived from the credal interval is local/global exact under exact local
lifting. -/
theorem globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i) :
    S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
      S.localEnvelopeMidpoint i X := by
  change
    (S.globalNaturalExtension (S.cylinders.cylinderGamble i X) +
        upperEnvelope S.projectiveLimitCredalSet
          (S.cylinders.cylinderGamble i X)) / 2 =
      (S.localNaturalExtension i X + S.localUpperEnvelope i X) / 2
  rw [
    S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow
      hGlobalBddBelow hExact,
    S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddAbove
      hGlobalBddAbove hExact]

/-- Exact local lifting transports an attained local lower/upper endpoint pair
to actual compatible global completions on the corresponding cylinder gamble.

The theorem deliberately consumes the local endpoint readout as data: compactness
or finite-dimensional attainment can be proved at the local layer once, then
reused by any projective system whose window is exact. -/
theorem projectiveLimit_exists_endpointPairReadout_cylinder_of_localEndpointPairReadout_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (Rlo : PrecisePrevision (S.cylinders.Local i))
    (hRlo : Rlo ∈ S.localCredal i)
    (Rhi : PrecisePrevision (S.cylinders.Local i))
    (hRhi : Rhi ∈ S.localCredal i)
    (hlo : Rlo X = S.localNaturalExtension i X)
    (hhi : Rhi X = S.localUpperEnvelope i X)
    (hlt : Rlo X < Rhi X)
    (hWidthEq : S.localEnvelopeWidth i X = Rhi X - Rlo X)
    (hCompEq : S.localEnvelopeWidthComplement i X =
      1 - (Rhi X - Rlo X))
    (hMidEq : S.localEnvelopeMidpoint i X =
      (Rlo X + Rhi X) / 2) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ S.projectiveLimitCredalSet ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ S.projectiveLimitCredalSet ∧
        Plo (S.cylinders.cylinderGamble i X) =
          S.globalNaturalExtension (S.cylinders.cylinderGamble i X) ∧
        Phi (S.cylinders.cylinderGamble i X) =
          upperEnvelope S.projectiveLimitCredalSet
            (S.cylinders.cylinderGamble i X) ∧
        Plo (S.cylinders.cylinderGamble i X) <
          Phi (S.cylinders.cylinderGamble i X) ∧
        S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
          Phi (S.cylinders.cylinderGamble i X) -
            Plo (S.cylinders.cylinderGamble i X) ∧
        S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
          1 - (Phi (S.cylinders.cylinderGamble i X) -
            Plo (S.cylinders.cylinderGamble i X)) ∧
        S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
          (Plo (S.cylinders.cylinderGamble i X) +
            Phi (S.cylinders.cylinderGamble i X)) / 2 := by
  rcases hExact Rlo hRlo with ⟨Plo, hPlo, hPloMarg⟩
  rcases hExact Rhi hRhi with ⟨Phi, hPhi, hPhiMarg⟩
  have hPloX :
      Plo (S.cylinders.cylinderGamble i X) = Rlo X := by
    exact congrArg (fun T : PrecisePrevision (S.cylinders.Local i) => T X)
      hPloMarg
  have hPhiX :
      Phi (S.cylinders.cylinderGamble i X) = Rhi X := by
    exact congrArg (fun T : PrecisePrevision (S.cylinders.Local i) => T X)
      hPhiMarg
  have hGlobalNonempty : S.hasCompatibleCompletion := ⟨Plo, hPlo⟩
  have hLocalNonempty : (S.localCredal i).Nonempty := ⟨Rlo, hRlo⟩
  have hGlobalLower :
      S.globalNaturalExtension (S.cylinders.cylinderGamble i X) =
        S.localNaturalExtension i X :=
    S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow hGlobalBddBelow
      hExact
  have hGlobalUpper :
      upperEnvelope S.projectiveLimitCredalSet
          (S.cylinders.cylinderGamble i X) =
        S.localUpperEnvelope i X :=
    S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddAbove hGlobalBddAbove
      hExact
  have hGlobalWidth :
      S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeWidth i X :=
    S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
      hGlobalBddBelow hGlobalBddAbove hExact
  have hGlobalComplement :
      S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeWidthComplement i X :=
    S.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
      hGlobalBddBelow hGlobalBddAbove hExact
  have hGlobalMidpoint :
      S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeMidpoint i X :=
    S.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
      hGlobalBddBelow hGlobalBddAbove hExact
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      Plo (S.cylinders.cylinderGamble i X) = Rlo X := hPloX
      _ = S.localNaturalExtension i X := hlo
      _ = S.globalNaturalExtension (S.cylinders.cylinderGamble i X) :=
        hGlobalLower.symm
  · calc
      Phi (S.cylinders.cylinderGamble i X) = Rhi X := hPhiX
      _ = S.localUpperEnvelope i X := hhi
      _ = upperEnvelope S.projectiveLimitCredalSet
          (S.cylinders.cylinderGamble i X) := hGlobalUpper.symm
  · calc
      Plo (S.cylinders.cylinderGamble i X) = Rlo X := hPloX
      _ < Rhi X := hlt
      _ = Phi (S.cylinders.cylinderGamble i X) := hPhiX.symm
  · calc
      S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
          S.localEnvelopeWidth i X := hGlobalWidth
      _ = Rhi X - Rlo X := hWidthEq
      _ = Phi (S.cylinders.cylinderGamble i X) -
          Plo (S.cylinders.cylinderGamble i X) := by
        rw [hPhiX, hPloX]
  · calc
      S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
          S.localEnvelopeWidthComplement i X := hGlobalComplement
      _ = 1 - (Rhi X - Rlo X) := hCompEq
      _ = 1 - (Phi (S.cylinders.cylinderGamble i X) -
          Plo (S.cylinders.cylinderGamble i X)) := by
        rw [hPhiX, hPloX]
  · calc
      S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
          S.localEnvelopeMidpoint i X := hGlobalMidpoint
      _ = (Rlo X + Rhi X) / 2 := hMidEq
      _ = (Plo (S.cylinders.cylinderGamble i X) +
          Phi (S.cylinders.cylinderGamble i X)) / 2 := by
        rw [hPhiX, hPloX]

/-- Exact local full-unit interval forces the global cylinder midpoint display
to one half. -/
theorem globalEnvelopeMidpoint_cylinder_eq_half_of_localCredal_unitInterval_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
      (1 / 2 : ℝ) := by
  rw [S.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact
    hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hGlobalBddBelow hGlobalBddAbove hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeMidpoint credalEnvelopeMidpoint
  unfold ProjectiveLocalCredalSpec.localNaturalExtension at hL
  unfold ProjectiveLocalCredalSpec.localUpperEnvelope at hU
  rw [hL, hU]
  ring

/-- Exact local full-unit interval forces the global cylinder width to be
maximal. -/
theorem globalEnvelopeWidth_cylinder_eq_one_of_localCredal_unitInterval_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) = 1 := by
  rw [S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
    hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hGlobalBddBelow hGlobalBddAbove hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeWidth credalEnvelopeWidth
  unfold ProjectiveLocalCredalSpec.localNaturalExtension at hL
  unfold ProjectiveLocalCredalSpec.localUpperEnvelope at hU
  rw [hL, hU]
  ring

/-- Exact local full-unit interval forces the global cylinder width-complement
display to zero. -/
theorem globalEnvelopeWidthComplement_cylinder_eq_zero_of_localCredal_unitInterval_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) = 0 := by
  rw [S.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact
    hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hGlobalBddBelow hGlobalBddAbove hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeWidthComplement
    credalEnvelopeWidthComplement
  rw [credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one]
  · ring
  · exact hL
  · exact hU

/-- Finite exact-cylinder interval-width theorem. -/
theorem globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact_finite
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i) :
    S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
      S.localEnvelopeWidth i X :=
  S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
    hGlobalNonempty i X hLocalNonempty
    (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact

/-- Finite exact-cylinder width-complement theorem. -/
theorem globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact_finite
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
      S.localEnvelopeWidthComplement i X :=
  S.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact
    hGlobalNonempty i X hLocalNonempty
    (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact

/-- Finite exact-cylinder midpoint theorem. -/
theorem globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact_finite
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i) :
    S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
      S.localEnvelopeMidpoint i X :=
  S.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact
    hGlobalNonempty i X hLocalNonempty
    (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact

/-- Finite exact local full-unit interval forces the global cylinder midpoint
display to one half. -/
theorem finiteGlobalEnvelopeMidpoint_cylinder_eq_half_of_localCredal_unitInterval_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
      (1 / 2 : ℝ) := by
  rw [S.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact_finite
    hGlobalNonempty i X hLocalNonempty hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeMidpoint credalEnvelopeMidpoint
  unfold ProjectiveLocalCredalSpec.localNaturalExtension at hL
  unfold ProjectiveLocalCredalSpec.localUpperEnvelope at hU
  rw [hL, hU]
  ring

/-- Finite exact local full-unit interval forces the global cylinder width to
be maximal. -/
theorem finiteGlobalEnvelopeWidth_cylinder_eq_one_of_localCredal_unitInterval_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) = 1 := by
  rw [S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact_finite
    hGlobalNonempty i X hLocalNonempty hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeWidth credalEnvelopeWidth
  unfold ProjectiveLocalCredalSpec.localNaturalExtension at hL
  unfold ProjectiveLocalCredalSpec.localUpperEnvelope at hU
  rw [hL, hU]
  ring

/-- Finite exact local full-unit interval forces the global cylinder
width-complement display to zero. -/
theorem finiteGlobalEnvelopeWidthComplement_cylinder_eq_zero_of_localCredal_unitInterval_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hLocalNonempty : (S.localCredal i).Nonempty)
    (hExact : S.localCredalExactAt i)
    (hL : S.localNaturalExtension i X = 0)
    (hU : S.localUpperEnvelope i X = 1) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) = 0 := by
  rw [S.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact_finite
    hGlobalNonempty i X hLocalNonempty hExact]
  unfold ProjectiveLocalCredalSpec.localEnvelopeWidthComplement
    credalEnvelopeWidthComplement
  rw [credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one]
  · ring
  · exact hL
  · exact hU

/-- Under exact local lifting, local credal determination collapses the global
compatible-completion interval width on the corresponding cylinder gamble. -/
theorem globalEnvelopeWidth_cylinder_eq_zero_of_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) = 0 := by
  have hLocalNonempty : (S.localCredal i).Nonempty := by
    rcases hGlobalNonempty with ⟨P, hP⟩
    exact ⟨S.cylinders.marginalPrevision i P, hP i⟩
  rw [S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
    hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
    hGlobalBddBelow hGlobalBddAbove hExact]
  unfold localEnvelopeWidth
  rcases hLocalNonempty with ⟨R, hR⟩
  exact credalEnvelopeWidth_eq_zero_of_credalSetDetermines
    (S.localCredal i) X ⟨R, hR⟩ hLocalBddBelow hLocalBddAbove hR hDet

/-- Under exact local lifting, strict local credal width gives a nontrivial
global compatible-completion interval on the corresponding cylinder gamble. -/
theorem globalLowerUpperEnvelope_cylinder_nontrivial_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.globalNaturalExtension (S.cylinders.cylinderGamble i X) <
      upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) := by
  have hLocalNonempty : (S.localCredal i).Nonempty := by
    rcases hWidth with ⟨P, hP, _Q, _hQ, _hlt⟩
    exact ⟨P, hP⟩
  rw [
    S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddBelow
      hGlobalBddBelow hExact,
    S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
      hGlobalNonempty i X hLocalNonempty hLocalBddAbove
      hGlobalBddAbove hExact]
  change lowerEnvelope (S.localCredal i) X <
    upperEnvelope (S.localCredal i) X
  exact lower_upperEnvelope_nontrivial_of_strictWidth
    (S.localCredal i) X hLocalBddBelow hLocalBddAbove hWidth

/-- Under exact local lifting, strict local credal width gives positive global
compatible-completion width on the corresponding cylinder gamble. -/
theorem globalEnvelopeWidth_cylinder_pos_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    0 < S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) := by
  have hlt :=
    S.globalLowerUpperEnvelope_cylinder_nontrivial_of_localCredal_strictWidth_of_exact
      hGlobalNonempty i X hLocalBddBelow hLocalBddAbove
      hGlobalBddBelow hGlobalBddAbove hExact hWidth
  have hlt' : lowerEnvelope S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X) <
      upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) := by
    simpa [ProjectiveLocalCredalSpec.globalNaturalExtension] using hlt
  unfold globalEnvelopeWidth credalEnvelopeWidth
  linarith

/-- Under exact local lifting, local credal determination makes the global
width-complement coordinate maximal on the corresponding cylinder gamble. -/
theorem globalEnvelopeWidthComplement_cylinder_eq_one_of_localCredal_determines_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) = 1 := by
  have hzero :=
    S.globalEnvelopeWidth_cylinder_eq_zero_of_localCredal_determines_of_exact
      hGlobalNonempty i X hLocalBddBelow hLocalBddAbove hGlobalBddBelow
      hGlobalBddAbove hExact hDet
  unfold globalEnvelopeWidth at hzero
  unfold globalEnvelopeWidthComplement credalEnvelopeWidthComplement
  rw [hzero]
  ring

/-- Under exact local lifting, strict local credal width forces the global
width-complement coordinate below one on the corresponding cylinder gamble. -/
theorem globalEnvelopeWidthComplement_cylinder_lt_one_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hGlobalBddBelow : BddBelow
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hGlobalBddAbove : BddAbove
      ((fun P : PrecisePrevision Global =>
          P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) < 1 := by
  have hpos :=
    S.globalEnvelopeWidth_cylinder_pos_of_localCredal_strictWidth_of_exact
      hGlobalNonempty i X hLocalBddBelow hLocalBddAbove hGlobalBddBelow
      hGlobalBddAbove hExact hWidth
  unfold globalEnvelopeWidth at hpos
  unfold globalEnvelopeWidthComplement credalEnvelopeWidthComplement
  linarith

/-- Finite exact-cylinder global collapse: finite spaces discharge the
boundedness side conditions automatically. -/
theorem finiteGlobalEnvelopeWidth_cylinder_eq_zero_of_localCredal_determines_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) = 0 :=
  S.globalEnvelopeWidth_cylinder_eq_zero_of_localCredal_determines_of_exact
    hGlobalNonempty i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact hDet

/-- Finite exact-cylinder global strict-width split. -/
theorem finiteGlobalLowerUpperEnvelope_cylinder_nontrivial_of_localCredal_strictWidth_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.globalNaturalExtension (S.cylinders.cylinderGamble i X) <
      upperEnvelope S.projectiveLimitCredalSet
        (S.cylinders.cylinderGamble i X) :=
  S.globalLowerUpperEnvelope_cylinder_nontrivial_of_localCredal_strictWidth_of_exact
    hGlobalNonempty i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact hWidth

/-- Finite exact-cylinder global positive-width theorem. -/
theorem finiteGlobalEnvelopeWidth_cylinder_pos_of_localCredal_strictWidth_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    0 < S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) :=
  S.globalEnvelopeWidth_cylinder_pos_of_localCredal_strictWidth_of_exact
    hGlobalNonempty i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact hWidth

/-- Finite exact-cylinder global maximal width-complement theorem. -/
theorem finiteGlobalEnvelopeWidthComplement_cylinder_eq_one_of_localCredal_determines_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCredalExactAt i)
    (hDet : credalSetDetermines (S.localCredal i) X) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) = 1 :=
  S.globalEnvelopeWidthComplement_cylinder_eq_one_of_localCredal_determines_of_exact
    hGlobalNonempty i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact hDet

/-- Finite exact-cylinder global strict-width complement theorem. -/
theorem finiteGlobalEnvelopeWidthComplement_cylinder_lt_one_of_localCredal_strictWidth_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) < 1 :=
  S.globalEnvelopeWidthComplement_cylinder_lt_one_of_localCredal_strictWidth_of_exact
    hGlobalNonempty i X (finite_credalRange_bddBelow (S.localCredal i) X)
    (finite_credalRange_bddAbove (S.localCredal i) X)
    (finite_credalRange_bddBelow S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    (finite_credalRange_bddAbove S.projectiveLimitCredalSet
      (S.cylinders.cylinderGamble i X))
    hExact hWidth

/-- Exact-cylinder endpoint readout for a bounded global natural extension.

If a local window lifts exactly into compatible global completions and has
strict local credal width on a local gamble, then the packaged global natural
extension has lower- and upper-touching dominating precise completions on the
corresponding cylinder gamble.  The endpoint gap computes the local
PLN-facing width, width-complement, and midpoint coordinates. -/
theorem globalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_cylinder_of_localCredal_strictWidth_of_exact
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (hGlobalBddBelow : ∀ Y : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P Y) ''
        S.projectiveLimitCredalSet))
    (hGlobalBddAbove : ∀ Y : Gamble Global,
      BddAbove ((fun P : PrecisePrevision Global => P Y) ''
        S.projectiveLimitCredalSet))
    (i : Window) (X : Gamble (S.cylinders.Local i))
    (hLocalBddBelow : BddBelow
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hLocalBddAbove : BddAbove
      ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
        S.localCredal i))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ dominatingPreciseCompletions
          (S.globalNaturalExtensionPrevision hGlobalNonempty hGlobalBddBelow) ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ dominatingPreciseCompletions
          (S.globalNaturalExtensionPrevision hGlobalNonempty hGlobalBddBelow) ∧
        Plo (S.cylinders.cylinderGamble i X) = S.localNaturalExtension i X ∧
        Phi (S.cylinders.cylinderGamble i X) = S.localUpperEnvelope i X ∧
        Plo (S.cylinders.cylinderGamble i X) <
          Phi (S.cylinders.cylinderGamble i X) ∧
        S.localEnvelopeWidth i X =
          Phi (S.cylinders.cylinderGamble i X) -
            Plo (S.cylinders.cylinderGamble i X) ∧
        S.localEnvelopeWidthComplement i X =
          1 - (Phi (S.cylinders.cylinderGamble i X) -
            Plo (S.cylinders.cylinderGamble i X)) ∧
        S.localEnvelopeMidpoint i X =
          (Plo (S.cylinders.cylinderGamble i X) +
            Phi (S.cylinders.cylinderGamble i X)) / 2 := by
  have hLocalNonempty : (S.localCredal i).Nonempty := by
    rcases hWidth with ⟨P, hP, _Q, _hQ, _hlt⟩
    exact ⟨P, hP⟩
  have hProjectiveWidth :
      S.hasStrictGlobalWidth (S.cylinders.cylinderGamble i X) :=
    (S.hasStrictGlobalWidth_cylinder_iff_localCredal_strictWidth_of_exact
      i hExact X).2 hWidth
  rcases
      S.globalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        hGlobalNonempty hGlobalBddBelow hGlobalBddAbove
        (S.cylinders.cylinderGamble i X) hProjectiveWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hloLocal :
      Plo (S.cylinders.cylinderGamble i X) = S.localNaturalExtension i X :=
    hlo.trans
      (S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
        hGlobalNonempty i X hLocalNonempty hLocalBddBelow
        (hGlobalBddBelow (S.cylinders.cylinderGamble i X)) hExact)
  have hhiLocal :
      Phi (S.cylinders.cylinderGamble i X) = S.localUpperEnvelope i X :=
    hhi.trans
      (S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
        hGlobalNonempty i X hLocalNonempty hLocalBddAbove
        (hGlobalBddAbove (S.cylinders.cylinderGamble i X)) hExact)
  refine ⟨Plo, hPlo, Phi, hPhi, hloLocal, hhiLocal, hlt, ?_, ?_, ?_⟩
  · calc
      S.localEnvelopeWidth i X =
          S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) :=
        (S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
          hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
          (hGlobalBddBelow (S.cylinders.cylinderGamble i X))
          (hGlobalBddAbove (S.cylinders.cylinderGamble i X)) hExact).symm
      _ = Phi (S.cylinders.cylinderGamble i X) -
          Plo (S.cylinders.cylinderGamble i X) := hWidthEq
  · calc
      S.localEnvelopeWidthComplement i X =
          S.globalEnvelopeWidthComplement
            (S.cylinders.cylinderGamble i X) :=
        (S.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact
          hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
          (hGlobalBddBelow (S.cylinders.cylinderGamble i X))
          (hGlobalBddAbove (S.cylinders.cylinderGamble i X)) hExact).symm
      _ = 1 - (Phi (S.cylinders.cylinderGamble i X) -
          Plo (S.cylinders.cylinderGamble i X)) := hCompEq
  · calc
      S.localEnvelopeMidpoint i X =
          S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) :=
        (S.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact
          hGlobalNonempty i X hLocalNonempty hLocalBddBelow hLocalBddAbove
          (hGlobalBddBelow (S.cylinders.cylinderGamble i X))
          (hGlobalBddAbove (S.cylinders.cylinderGamble i X)) hExact).symm
      _ = (Plo (S.cylinders.cylinderGamble i X) +
          Phi (S.cylinders.cylinderGamble i X)) / 2 := hMidEq

/-- Finite exact-cylinder endpoint readout for the global natural extension.

If a local window lifts exactly into compatible global completions and has
strict local credal width on a local gamble, then the finite global natural
extension has lower- and upper-touching dominating precise completions on the
corresponding cylinder gamble.  The endpoint gap computes the local
PLN-facing width, width-complement, and midpoint coordinates. -/
theorem finiteGlobalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_cylinder_of_localCredal_strictWidth_of_exact
    [Fintype Global] [Nonempty Global]
    (S : ProjectiveLocalCredalSpec Window Global)
    (hGlobalNonempty : S.hasCompatibleCompletion)
    (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
    (X : Gamble (S.cylinders.Local i))
    (hExact : S.localCredalExactAt i)
    (hWidth : credalSetHasStrictWidth (S.localCredal i) X) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ dominatingPreciseCompletions
          (S.finiteGlobalNaturalExtensionPrevision hGlobalNonempty) ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ dominatingPreciseCompletions
          (S.finiteGlobalNaturalExtensionPrevision hGlobalNonempty) ∧
        Plo (S.cylinders.cylinderGamble i X) = S.localNaturalExtension i X ∧
        Phi (S.cylinders.cylinderGamble i X) = S.localUpperEnvelope i X ∧
        Plo (S.cylinders.cylinderGamble i X) <
          Phi (S.cylinders.cylinderGamble i X) ∧
        S.localEnvelopeWidth i X =
          Phi (S.cylinders.cylinderGamble i X) -
            Plo (S.cylinders.cylinderGamble i X) ∧
        S.localEnvelopeWidthComplement i X =
          1 - (Phi (S.cylinders.cylinderGamble i X) -
            Plo (S.cylinders.cylinderGamble i X)) ∧
        S.localEnvelopeMidpoint i X =
          (Plo (S.cylinders.cylinderGamble i X) +
            Phi (S.cylinders.cylinderGamble i X)) / 2 := by
  have hLocalNonempty : (S.localCredal i).Nonempty := by
    rcases hWidth with ⟨P, hP, _Q, _hQ, _hlt⟩
    exact ⟨P, hP⟩
  have hProjectiveWidth :
      S.hasStrictGlobalWidth (S.cylinders.cylinderGamble i X) :=
    (S.hasStrictGlobalWidth_cylinder_iff_localCredal_strictWidth_of_exact
      i hExact X).2 hWidth
  rcases
      S.finiteGlobalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        hGlobalNonempty (S.cylinders.cylinderGamble i X) hProjectiveWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hloLocal :
      Plo (S.cylinders.cylinderGamble i X) = S.localNaturalExtension i X :=
    hlo.trans
      (S.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact_finite
        hGlobalNonempty i X hLocalNonempty hExact)
  have hhiLocal :
      Phi (S.cylinders.cylinderGamble i X) = S.localUpperEnvelope i X :=
    hhi.trans
      (S.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact_finite
        hGlobalNonempty i X hLocalNonempty hExact)
  refine ⟨Plo, hPlo, Phi, hPhi, hloLocal, hhiLocal, hlt, ?_, ?_, ?_⟩
  · calc
      S.localEnvelopeWidth i X =
          S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) :=
        (S.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact_finite
          hGlobalNonempty i X hLocalNonempty hExact).symm
      _ = Phi (S.cylinders.cylinderGamble i X) -
          Plo (S.cylinders.cylinderGamble i X) := hWidthEq
  · calc
      S.localEnvelopeWidthComplement i X =
          S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) :=
        (S.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact_finite
          hGlobalNonempty i X hLocalNonempty hExact).symm
      _ = 1 - (Phi (S.cylinders.cylinderGamble i X) -
          Plo (S.cylinders.cylinderGamble i X)) := hCompEq
  · calc
      S.localEnvelopeMidpoint i X =
          S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) :=
        (S.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact_finite
          hGlobalNonempty i X hLocalNonempty hExact).symm
      _ = (Plo (S.cylinders.cylinderGamble i X) +
          Phi (S.cylinders.cylinderGamble i X)) / 2 := hMidEq

/-! ## Compact convex projective systems -/

/-- Compact/FIP package for a projective credal system.  The topology lives on
the global completion space; compactness plus finite satisfiability gives a
genuine inverse-limit completion. -/
structure CompactConvexProjectiveCredalSystem
    (S : ProjectiveLocalCredalSpec Window Global)
    [TopologicalSpace (PrecisePrevision Global)] where
  carrier : CredalPrevisionSet Global
  carrier_compact : IsCompact carrier
  carrier_convex : CredalPrevisionSet.IsConvex carrier
  local_convex : ∀ i, CredalPrevisionSet.IsConvex (S.localCredal i)
  constraint_closed :
    ∀ i, IsClosed {P : PrecisePrevision Global |
      S.cylinders.marginalPrevision i P ∈ S.localCredal i}
  finite_satisfiable :
    ∀ u : Finset Window,
      (carrier ∩ ⋂ i ∈ u,
        {P : PrecisePrevision Global |
          S.cylinders.marginalPrevision i P ∈ S.localCredal i}).Nonempty

namespace CompactConvexProjectiveCredalSystem

variable {Window Global : Type*} [LE Window]
variable {S : ProjectiveLocalCredalSpec Window Global}
variable [TopologicalSpace (PrecisePrevision Global)]

/-- The compact projective-limit set: compatible global completions inside the
chosen compact carrier. -/
def limitSet (K : CompactConvexProjectiveCredalSystem S) :
    CredalPrevisionSet Global :=
  K.carrier ∩ S.projectiveLimitCredalSet

theorem limitSet_eq_projectiveLimitCredalSet_of_carrier_eq_univ
    (K : CompactConvexProjectiveCredalSystem S)
    (hCarrier : K.carrier = Set.univ) :
    K.limitSet = S.projectiveLimitCredalSet := by
  ext P
  simp [limitSet, hCarrier]

theorem projectiveLimitCredalSet_isClosed
    (K : CompactConvexProjectiveCredalSystem S) :
    IsClosed S.projectiveLimitCredalSet :=
  S.projectiveLimitCredalSet_isClosed K.constraint_closed

theorem limitSet_isCompact
    (K : CompactConvexProjectiveCredalSystem S) :
    IsCompact K.limitSet :=
  K.carrier_compact.inter_right K.projectiveLimitCredalSet_isClosed

theorem limitSet_nonempty
    (K : CompactConvexProjectiveCredalSystem S) :
    K.limitSet.Nonempty := by
  have h :
      (K.carrier ∩ ⋂ i,
        {P : PrecisePrevision Global |
          S.cylinders.marginalPrevision i P ∈ S.localCredal i}).Nonempty :=
    K.carrier_compact.inter_iInter_nonempty
      (fun i => {P : PrecisePrevision Global |
        S.cylinders.marginalPrevision i P ∈ S.localCredal i})
      K.constraint_closed K.finite_satisfiable
  rcases h with ⟨P, hPcar, hPconstraints⟩
  exact ⟨P, hPcar, fun i => (Set.mem_iInter.mp hPconstraints) i⟩

/-- Compactness/FIP produces an honest compatible completion. -/
theorem hasCompatibleCompletion
    (K : CompactConvexProjectiveCredalSystem S) :
    S.hasCompatibleCompletion :=
  (K.limitSet_nonempty).mono fun _P hP => hP.2

theorem limitSet_isConvex
    (K : CompactConvexProjectiveCredalSystem S) :
    CredalPrevisionSet.IsConvex K.limitSet :=
  K.carrier_convex.inter (S.projectiveLimitCredalSet_isConvex K.local_convex)

theorem limitSet_lowerEnvelope_exists_mem_eq
    (K : CompactConvexProjectiveCredalSystem S)
    (X : Gamble Global)
    (hCont : ContinuousOn (fun P : PrecisePrevision Global => P X) K.limitSet) :
    ∃ P : PrecisePrevision Global,
      P ∈ K.limitSet ∧ P X = lowerEnvelope K.limitSet X :=
  lowerEnvelope_exists_mem_eq_of_isCompact
    K.limitSet K.limitSet_isCompact K.limitSet_nonempty X hCont

theorem limitSet_upperEnvelope_exists_mem_eq
    (K : CompactConvexProjectiveCredalSystem S)
    (X : Gamble Global)
    (hCont : ContinuousOn (fun P : PrecisePrevision Global => P X) K.limitSet) :
    ∃ P : PrecisePrevision Global,
      P ∈ K.limitSet ∧ P X = upperEnvelope K.limitSet X :=
  upperEnvelope_exists_mem_eq_of_isCompact
    K.limitSet K.limitSet_isCompact K.limitSet_nonempty X hCont

theorem limitSet_exists_endpointPairReadout_of_strictWidth
    (K : CompactConvexProjectiveCredalSystem S)
    (X : Gamble Global)
    (hCont : ContinuousOn (fun P : PrecisePrevision Global => P X) K.limitSet)
    (hWidth : credalSetHasStrictWidth K.limitSet X) :
    ∃ Plo : PrecisePrevision Global, Plo ∈ K.limitSet ∧
      ∃ Phi : PrecisePrevision Global, Phi ∈ K.limitSet ∧
        Plo X = lowerEnvelope K.limitSet X ∧
        Phi X = upperEnvelope K.limitSet X ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth K.limitSet X = Phi X - Plo X ∧
        credalEnvelopeWidthComplement K.limitSet X = 1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint K.limitSet X = (Plo X + Phi X) / 2 :=
  credalEnvelope_exists_endpointPairReadout_of_isCompact_strictWidth
    K.limitSet K.limitSet_isCompact K.limitSet_nonempty X hCont hWidth

omit [TopologicalSpace (PrecisePrevision Global)] in
theorem limitSet_exists_endpointPairReadout_of_finiteEvaluation_strictWidth
    [Fintype Global] [DecidableEq Global]
    (K : @CompactConvexProjectiveCredalSystem Window Global _ S
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)))
    (X : Gamble Global)
    (hWidth : credalSetHasStrictWidth
      (@limitSet Window Global _ S
        (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K) X) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ @limitSet Window Global _ S
        (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ @limitSet Window Global _ S
          (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K ∧
        Plo X = lowerEnvelope
          (@limitSet Window Global _ S
            (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K) X ∧
        Phi X = upperEnvelope
          (@limitSet Window Global _ S
            (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K) X ∧
        Plo X < Phi X ∧
        credalEnvelopeWidth
          (@limitSet Window Global _ S
            (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K) X =
          Phi X - Plo X ∧
        credalEnvelopeWidthComplement
          (@limitSet Window Global _ S
            (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K) X =
          1 - (Phi X - Plo X) ∧
        credalEnvelopeMidpoint
          (@limitSet Window Global _ S
            (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K) X =
          (Plo X + Phi X) / 2 :=
  credalEnvelope_exists_endpointPairReadout_of_finiteEvaluationCompact_strictWidth
    (@limitSet Window Global _ S
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K)
    (@limitSet_isCompact Window Global _ S
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K)
    (@limitSet_nonempty Window Global _ S
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K)
    X hWidth

omit [TopologicalSpace (PrecisePrevision Global)] in
theorem projectiveLimit_exists_endpointPairReadout_of_finiteEvaluation_fullCarrier_strictWidth
    [Fintype Global] [DecidableEq Global]
    (K : @CompactConvexProjectiveCredalSystem Window Global _ S
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)))
    (hCarrier : @carrier Window Global _ S
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)) K =
        Set.univ)
    (X : Gamble Global)
    (hWidth : S.hasStrictGlobalWidth X) :
    ∃ Plo : PrecisePrevision Global,
      Plo ∈ S.projectiveLimitCredalSet ∧
      ∃ Phi : PrecisePrevision Global,
        Phi ∈ S.projectiveLimitCredalSet ∧
        Plo X = lowerEnvelope S.projectiveLimitCredalSet X ∧
        Phi X = upperEnvelope S.projectiveLimitCredalSet X ∧
        Plo X < Phi X ∧
        S.globalEnvelopeWidth X = Phi X - Plo X ∧
        S.globalEnvelopeWidthComplement X = 1 - (Phi X - Plo X) ∧
        S.globalEnvelopeMidpoint X = (Plo X + Phi X) / 2 := by
  letI : TopologicalSpace (PrecisePrevision Global) :=
    PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Global)
  have hEq : K.limitSet = S.projectiveLimitCredalSet :=
    K.limitSet_eq_projectiveLimitCredalSet_of_carrier_eq_univ hCarrier
  have hWidthK : credalSetHasStrictWidth K.limitSet X := by
    rw [hEq]
    exact hWidth
  rcases K.limitSet_exists_endpointPairReadout_of_finiteEvaluation_strictWidth
      X hWidthK with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  refine ⟨Plo, ?_, Phi, ?_, ?_, ?_, hlt, ?_, ?_, ?_⟩
  · simpa [hEq] using hPlo
  · simpa [hEq] using hPhi
  · simpa [hEq] using hlo
  · simpa [hEq] using hhi
  · simpa [ProjectiveLocalCredalSpec.globalEnvelopeWidth, hEq] using hWidthEq
  · simpa [ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement, hEq] using hCompEq
  · simpa [ProjectiveLocalCredalSpec.globalEnvelopeMidpoint, hEq] using hMidEq

end CompactConvexProjectiveCredalSystem

/-- Singleton global completion: the projective-limit lower envelope collapses
to that completion. -/
theorem globalNaturalExtension_singleton
    (S : ProjectiveLocalCredalSpec Window Global)
    (P : PrecisePrevision Global)
    (hEq : S.projectiveLimitCredalSet = ({P} : CredalPrevisionSet Global))
    (X : Gamble Global) :
    S.globalNaturalExtension X = P X := by
  rw [globalNaturalExtension, hEq]
  exact lowerEnvelope_singleton P X

end ProjectiveLocalCredalSpec

/-! ## Projective lower-prevision completion bridge -/

/-- Local Walley lower-prevision data over a projective cylinder system.

The induced local credal set at each window is the set of precise previsions
dominating the local lower prevision.  This is the input shape needed for an
open-ended KB: local finite-window lower assessments are primary, and global
compatible completions are produced by projective compactness/FIP. -/
structure ProjectiveLocalLowerPrevisionSpec.{u, v}
    (Window : Type u) (Global : Type v) [LE Window] where
  cylinders : ProjectiveCylinderSystem.{u, v} Window Global
  localLower : ∀ i : Window, LowerPrevision (cylinders.Local i)

namespace ProjectiveLocalLowerPrevisionSpec

variable {Window Global : Type*} [LE Window]

/-- The projective credal spec generated by taking all precise local
previsions that dominate each local lower prevision. -/
def toCredalSpec (S : ProjectiveLocalLowerPrevisionSpec Window Global) :
    ProjectiveLocalCredalSpec Window Global where
  cylinders := S.cylinders
  localCredal i := dominatingPreciseCompletions (S.localLower i)

@[simp] theorem toCredalSpec_cylinders
    (S : ProjectiveLocalLowerPrevisionSpec Window Global) :
    S.toCredalSpec.cylinders = S.cylinders :=
  rfl

@[simp] theorem toCredalSpec_localCredal
    (S : ProjectiveLocalLowerPrevisionSpec Window Global) (i : Window) :
    S.toCredalSpec.localCredal i =
      dominatingPreciseCompletions (S.localLower i) :=
  rfl

/-- Finite-window compatibility inside a proposed compact carrier.

This is the FIP hypothesis in KB language: every finite set of windows has a
single global precise prevision, drawn from the carrier, whose marginals
dominate the corresponding local lower previsions. -/
def finiteWindowCompatibleInCarrier
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (carrier : CredalPrevisionSet Global) : Prop :=
  ∀ u : Finset Window,
    ∃ P : PrecisePrevision Global,
      P ∈ carrier ∧
        ∀ i ∈ u,
          S.cylinders.marginalPrevision i P ∈
            dominatingPreciseCompletions (S.localLower i)

/-- The local credal sets generated by local lower previsions are convex. -/
theorem localCredal_isConvex
    (S : ProjectiveLocalLowerPrevisionSpec Window Global) (i : Window) :
    CredalPrevisionSet.IsConvex (S.toCredalSpec.localCredal i) :=
  dominatingPreciseCompletions_isConvex (S.localLower i)

/-- A global lower prevision respects local lower-prevision assessments when,
on every pulled-back cylinder gamble, it lies above the stipulated local lower
bound.  These are exactly the global competitors used in the least-committal
natural-extension theorem below. -/
def respectsLocalLower
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (L : LowerPrevision Global) : Prop :=
  ∀ i (X : Gamble (S.cylinders.Local i)),
    S.localLower i X ≤ L (S.cylinders.cylinderGamble i X)

/-- The generated local credal set has the original local lower prevision as
its exact Walley lower envelope. -/
theorem localNaturalExtension_eq_localLower
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.toCredalSpec.localNaturalExtension i X = S.localLower i X := by
  simp [ProjectiveLocalCredalSpec.localNaturalExtension, toCredalSpec,
    lowerEnvelope_dominatingPreciseCompletions_eq]

/-- A precise prevision dominating any global lower prevision that respects all
local lower assessments is a compatible completion of the generated
projective credal specification. -/
theorem dominatingPreciseCompletion_mem_projectiveLimitCredalSet_of_respectsLocalLower
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    {L : LowerPrevision Global} (hL : S.respectsLocalLower L)
    {P : PrecisePrevision Global}
    (hP : P ∈ dominatingPreciseCompletions L) :
    P ∈ S.toCredalSpec.projectiveLimitCredalSet := by
  intro i
  change S.cylinders.marginalPrevision i P ∈
    dominatingPreciseCompletions (S.localLower i)
  intro X
  calc
    S.localLower i X ≤ L (S.cylinders.cylinderGamble i X) := hL i X
    _ ≤ P (S.cylinders.cylinderGamble i X) := hP _

/-- Any global lower prevision respecting the local lower assessments supplies
at least one compatible precise completion, by Walley's touching-completion
theorem. -/
theorem hasCompatibleCompletion_of_respectsLocalLower
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (L : LowerPrevision Global) (hL : S.respectsLocalLower L) :
    S.toCredalSpec.hasCompatibleCompletion := by
  rcases exists_dominatingPreciseCompletion_touching L (0 : Gamble Global) with
    ⟨P, hP, _hTouch⟩
  exact ⟨P,
    S.dominatingPreciseCompletion_mem_projectiveLimitCredalSet_of_respectsLocalLower
      hL hP⟩

/-- The projective natural extension generated by local lower assessments
dominates each local lower assessment on the corresponding cylinder gamble.

This is the direct local-soundness half of the natural-extension crown: finite
window assessments survive into the open-ended global PLN semantics. -/
theorem globalNaturalExtension_dominates_localLower_on_cylinder
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.localLower i X ≤
      S.toCredalSpec.globalNaturalExtension
        (S.cylinders.cylinderGamble i X) := by
  calc
    S.localLower i X =
        S.toCredalSpec.localNaturalExtension i X := by
      exact (S.localNaturalExtension_eq_localLower i X).symm
    _ ≤ S.toCredalSpec.globalNaturalExtension
        (S.cylinders.cylinderGamble i X) := by
      exact
        S.toCredalSpec.localNaturalExtension_le_globalNaturalExtension_on_cylinder
          hGlobal i X
          (by
            simpa [toCredalSpec] using
              (dominatingPreciseCompletions_bddBelow (S.localLower i) X))

/-- Packaged lower-prevision form of local soundness for the generated global
natural extension. -/
theorem globalNaturalExtensionPrevision_dominates_localLower_on_cylinder
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet))
    (i : Window) (X : Gamble (S.cylinders.Local i)) :
    S.localLower i X ≤
      S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd
        (S.cylinders.cylinderGamble i X) := by
  simpa [ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision,
    ProjectiveLocalCredalSpec.globalNaturalExtension] using
    S.globalNaturalExtension_dominates_localLower_on_cylinder hGlobal i X

/-- Least-committal property of the generated projective natural extension.

Any other global lower prevision that respects all local lower assessments is
pointwise above the lower envelope of compatible precise completions.  Thus the
projective natural extension is the conservative global PLN truth semantics
forced by the local assessments. -/
theorem globalNaturalExtensionPrevision_le_of_respectsLocalLower
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet))
    (L : LowerPrevision Global) (hL : S.respectsLocalLower L)
    (X : Gamble Global) :
    S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd X ≤ L X := by
  rcases exists_dominatingPreciseCompletion_touching L X with
    ⟨P, hPdom, hTouch⟩
  have hPcompat :
      P ∈ S.toCredalSpec.projectiveLimitCredalSet :=
    S.dominatingPreciseCompletion_mem_projectiveLimitCredalSet_of_respectsLocalLower
      hL hPdom
  exact
    (S.toCredalSpec.globalNaturalExtensionPrevision_le_completion
      hGlobal hBdd hPcompat X).trans_eq hTouch

/-- Crown form of the projective Walley natural extension: the generated
global lower prevision respects every local lower assessment and is pointwise
below every other global lower prevision with that property.

Thus, once compatible completions exist and their query ranges are bounded
below, the lower envelope over compatible completions is the least-committal
global semantics forced by the local lower-prevision data. -/
theorem globalNaturalExtensionPrevision_isLeast_respectsLocalLower
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet)) :
    S.respectsLocalLower
        (S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd) ∧
      ∀ L : LowerPrevision Global, S.respectsLocalLower L →
        ∀ X : Gamble Global,
          S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd X ≤
            L X := by
  constructor
  · intro i X
    exact S.globalNaturalExtensionPrevision_dominates_localLower_on_cylinder
      hGlobal hBdd i X
  · intro L hL X
    exact S.globalNaturalExtensionPrevision_le_of_respectsLocalLower
      hGlobal hBdd L hL X

/-- The generated projective natural extension has Walley's exact
dominating-precise-completion representation. -/
theorem globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet)) :
    hasExactDominatingPreciseEnvelope
      (S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd) :=
  S.toCredalSpec.globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    hGlobal hBdd

/-- Re-envelope the generated projective natural extension by all precise
previsions dominating it and recover the same PLN-facing interval width. -/
theorem globalNaturalExtensionPrevision_dominatingCompletions_width_eq
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBddBelow : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet))
    (X : Gamble Global) :
    credalEnvelopeWidth
        (dominatingPreciseCompletions
          (S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBddBelow))
        X =
      S.toCredalSpec.globalEnvelopeWidth X := by
  let L : LowerPrevision Global :=
    S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBddBelow
  have hExact : hasExactDominatingPreciseEnvelope L := by
    dsimp [L]
    exact S.globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      hGlobal hBddBelow
  unfold credalEnvelopeWidth ProjectiveLocalCredalSpec.globalEnvelopeWidth
  have hLower :
      lowerEnvelope (dominatingPreciseCompletions L) X =
        lowerEnvelope S.toCredalSpec.projectiveLimitCredalSet X := by
    calc
      lowerEnvelope (dominatingPreciseCompletions L) X = L X :=
        hExact.lowerEnvelope_eq X
      _ = lowerEnvelope S.toCredalSpec.projectiveLimitCredalSet X := by
        rfl
  have hUpper :
      upperEnvelope (dominatingPreciseCompletions L) X =
        upperEnvelope S.toCredalSpec.projectiveLimitCredalSet X := by
    calc
      upperEnvelope (dominatingPreciseCompletions L) X = L.conjugate X :=
        hExact.upperEnvelope_eq_conjugate X
      _ = upperEnvelope S.toCredalSpec.projectiveLimitCredalSet X :=
        S.toCredalSpec.globalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
          hGlobal hBddBelow X
  rw [hLower, hUpper]
  rfl

/-- Re-envelope the generated projective natural extension by all precise
previsions dominating it and recover the same PLN-facing width-complement
confidence coordinate. -/
theorem globalNaturalExtensionPrevision_dominatingCompletions_widthComplement_eq
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBddBelow : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet))
    (X : Gamble Global) :
    credalEnvelopeWidthComplement
        (dominatingPreciseCompletions
          (S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBddBelow))
        X =
      S.toCredalSpec.globalEnvelopeWidthComplement X := by
  unfold credalEnvelopeWidthComplement
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement
  rw [S.globalNaturalExtensionPrevision_dominatingCompletions_width_eq
    hGlobal hBddBelow X]
  rfl

/-- Re-envelope the generated projective natural extension by all precise
previsions dominating it and recover the same PLN-facing midpoint strength
coordinate. -/
theorem globalNaturalExtensionPrevision_dominatingCompletions_midpoint_eq
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (hGlobal : S.toCredalSpec.hasCompatibleCompletion)
    (hBddBelow : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet))
    (X : Gamble Global) :
    credalEnvelopeMidpoint
        (dominatingPreciseCompletions
          (S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBddBelow))
        X =
      S.toCredalSpec.globalEnvelopeMidpoint X := by
  let L : LowerPrevision Global :=
    S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBddBelow
  have hExact : hasExactDominatingPreciseEnvelope L := by
    dsimp [L]
    exact S.globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
      hGlobal hBddBelow
  unfold credalEnvelopeMidpoint ProjectiveLocalCredalSpec.globalEnvelopeMidpoint
  have hLower :
      lowerEnvelope (dominatingPreciseCompletions L) X =
        lowerEnvelope S.toCredalSpec.projectiveLimitCredalSet X := by
    calc
      lowerEnvelope (dominatingPreciseCompletions L) X = L X :=
        hExact.lowerEnvelope_eq X
      _ = lowerEnvelope S.toCredalSpec.projectiveLimitCredalSet X := by
        rfl
  have hUpper :
      upperEnvelope (dominatingPreciseCompletions L) X =
        upperEnvelope S.toCredalSpec.projectiveLimitCredalSet X := by
    calc
      upperEnvelope (dominatingPreciseCompletions L) X = L.conjugate X :=
        hExact.upperEnvelope_eq_conjugate X
      _ = upperEnvelope S.toCredalSpec.projectiveLimitCredalSet X :=
        S.toCredalSpec.globalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
          hGlobal hBddBelow X
  rw [hLower, hUpper]
  rfl

/-- Compact/FIP projective completion for local lower-prevision data.

If every finite window family is satisfiable inside a compact global carrier,
and each local dominance constraint is closed in that carrier topology, then
the generated projective credal spec has an honest compatible global precise
completion.  This is the first infinite bridge needed for growing KB semantics:
coherent finite windows are projections of at least one global completion. -/
theorem hasCompatibleCompletion_of_finiteWindowCompatibleInCarrier
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    [TopologicalSpace (PrecisePrevision Global)]
    (carrier : CredalPrevisionSet Global)
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ i, IsClosed {P : PrecisePrevision Global |
      S.cylinders.marginalPrevision i P ∈
        dominatingPreciseCompletions (S.localLower i)})
    (hFIP : S.finiteWindowCompatibleInCarrier carrier) :
    S.toCredalSpec.hasCompatibleCompletion := by
  let K :
      ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem
        S.toCredalSpec := {
    carrier := carrier
    carrier_compact := hCompact
    carrier_convex := hCarrierConvex
    local_convex := by
      intro i
      exact S.localCredal_isConvex i
    constraint_closed := by
      intro i
      exact hClosed i
    finite_satisfiable := by
      intro u
      rcases hFIP u with ⟨P, hPcarrier, hPwindows⟩
      refine ⟨P, ?_⟩
      constructor
      · exact hPcarrier
      · refine Set.mem_iInter.2 ?_
        intro i
        refine Set.mem_iInter.2 ?_
        intro hi
        exact hPwindows i hi }
  exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.hasCompatibleCompletion K

/-- Compact/FIP crown form for local lower-prevision data.

Under the compact finite-intersection hypotheses, the generated global natural
extension is the least-committal lower prevision respecting all local lower
assessments.  The remaining bounded-below hypothesis is exactly the ordinary
one needed to package the raw lower envelope as a `LowerPrevision` on arbitrary
global gambles. -/
theorem globalNaturalExtensionPrevision_isLeast_respectsLocalLower_of_finiteWindowCompatibleInCarrier
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    [TopologicalSpace (PrecisePrevision Global)]
    (carrier : CredalPrevisionSet Global)
    (hCompact : IsCompact carrier)
    (hCarrierConvex : CredalPrevisionSet.IsConvex carrier)
    (hClosed : ∀ i, IsClosed {P : PrecisePrevision Global |
      S.cylinders.marginalPrevision i P ∈
        dominatingPreciseCompletions (S.localLower i)})
    (hFIP : S.finiteWindowCompatibleInCarrier carrier)
    (hBdd : ∀ X : Gamble Global,
      BddBelow ((fun P : PrecisePrevision Global => P X) ''
        S.toCredalSpec.projectiveLimitCredalSet)) :
    let hGlobal : S.toCredalSpec.hasCompatibleCompletion :=
      S.hasCompatibleCompletion_of_finiteWindowCompatibleInCarrier
        carrier hCompact hCarrierConvex hClosed hFIP
    S.respectsLocalLower
        (S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd) ∧
      ∀ L : LowerPrevision Global, S.respectsLocalLower L →
        ∀ X : Gamble Global,
          S.toCredalSpec.globalNaturalExtensionPrevision hGlobal hBdd X ≤
            L X := by
  exact
    S.globalNaturalExtensionPrevision_isLeast_respectsLocalLower
      (S.hasCompatibleCompletion_of_finiteWindowCompatibleInCarrier
        carrier hCompact hCarrierConvex hClosed hFIP)
      hBdd

end ProjectiveLocalLowerPrevisionSpec

/-! ## Concrete compact/FIP inhabitant -/

/-- One Bool-valued window observing the Bool global state. -/
def boolOneWindowCylinderSystem : ProjectiveCylinderSystem PUnit Bool where
  Local _ := Bool
  project _ ω := ω
  restrict _ x := x
  project_restrict := by
    intro i j hij ω
    rfl

/-- A one-window projective specification whose local credal set accepts only
the `false` Dirac completion. -/
def boolFalseExactProjectiveSpec : ProjectiveLocalCredalSpec PUnit Bool where
  cylinders := boolOneWindowCylinderSystem
  localCredal _ := ({PrecisePrevision.dirac false} : CredalPrevisionSet Bool)

/-- A one-window projective specification whose local credal set accepts every
precise Bool prevision.  This is non-singleton finite credal data. -/
def boolUnrestrictedProjectiveSpec : ProjectiveLocalCredalSpec PUnit Bool where
  cylinders := boolOneWindowCylinderSystem
  localCredal _ := (Set.univ : CredalPrevisionSet Bool)

/-- The singleton Dirac carrier is the zero-dimensional finite-simplex canary
for the compact/FIP projective package.  The topology is taken discrete here;
this is a concrete finite inhabitant, not the full weak* compactness theorem. -/
theorem boolFalseExact_compactFIP_hasCompatibleCompletion :
    boolFalseExactProjectiveSpec.hasCompatibleCompletion := by
  letI : TopologicalSpace (PrecisePrevision Bool) := ⊥
  letI : DiscreteTopology (PrecisePrevision Bool) :=
    discreteTopology_bot (PrecisePrevision Bool)
  let K :
      ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem
        boolFalseExactProjectiveSpec := {
    carrier := ({PrecisePrevision.dirac false} : CredalPrevisionSet Bool)
    carrier_compact := by
      exact isCompact_singleton
    carrier_convex := by
      exact CredalPrevisionSet.isConvex_singleton (PrecisePrevision.dirac false)
    local_convex := by
      intro i
      exact CredalPrevisionSet.isConvex_singleton (PrecisePrevision.dirac false)
    constraint_closed := by
      intro i
      exact isClosed_discrete _
    finite_satisfiable := by
      intro u
      have hcompat :
          ∀ i,
            boolFalseExactProjectiveSpec.cylinders.marginalPrevision i
                (PrecisePrevision.dirac false) ∈
              boolFalseExactProjectiveSpec.localCredal i := by
        intro i
        rw [boolFalseExactProjectiveSpec.marginalPrevision_dirac i false]
        simp only [boolFalseExactProjectiveSpec, boolOneWindowCylinderSystem]
        exact Set.mem_singleton _
      refine ⟨PrecisePrevision.dirac false, ?_⟩
      constructor
      · exact Set.mem_singleton _
      · exact Set.mem_iInter.mpr fun i =>
          Set.mem_iInter.mpr fun _hi => hcompat i
  }
  exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.hasCompatibleCompletion K

/-- The finite-evaluation compact crown inhabited by a non-singleton finite
projective credal system.  The compact carrier is all precise previsions on
`Bool`, transported from the compact standard simplex. -/
theorem boolUnrestricted_finiteEvaluationCompact_hasCompatibleCompletion :
    boolUnrestrictedProjectiveSpec.hasCompatibleCompletion := by
  classical
  letI : TopologicalSpace (PrecisePrevision Bool) :=
    PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Bool)
  let K :
      ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem
        boolUnrestrictedProjectiveSpec := {
    carrier := (Set.univ : CredalPrevisionSet Bool)
    carrier_compact := by
      simpa using
        PrecisePrevision.FiniteWeights.finiteEvaluationTopology_univCompact
          (Ω := Bool)
    carrier_convex := by
      exact CredalPrevisionSet.isConvex_univ
    local_convex := by
      intro i
      exact CredalPrevisionSet.isConvex_univ
    constraint_closed := by
      intro i
      exact isClosed_univ
    finite_satisfiable := by
      intro u
      refine ⟨PrecisePrevision.dirac false, ?_⟩
      constructor
      · simp
      · exact Set.mem_iInter.mpr fun i =>
          Set.mem_iInter.mpr fun _hi => by
            exact Set.mem_univ _
  }
  exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.hasCompatibleCompletion K

/-- One finite identity window observing the full finite global state. -/
def finiteIdentityCylinderSystem (Ω : Type*) :
    ProjectiveCylinderSystem PUnit.{1} Ω where
  Local _ := Ω
  project _ ω := ω
  restrict _ x := x
  project_restrict := by
    intro i j hij ω
    rfl

/-- Identity-window projective specification induced by an arbitrary credal set.
This is the reusable adapter from an ordinary global credal set into the
projective local-credal interface. -/
def identityCredalProjectiveSpec {Ω : Type*}
    (C : CredalPrevisionSet Ω) : ProjectiveLocalCredalSpec PUnit.{1} Ω where
  cylinders := finiteIdentityCylinderSystem Ω
  localCredal _ := C

@[simp] theorem identityCredalProjectiveSpec_projectiveLimitCredalSet
    {Ω : Type*} (C : CredalPrevisionSet Ω) :
    (identityCredalProjectiveSpec C).projectiveLimitCredalSet = C := by
  ext P
  constructor
  · intro hP
    have h := hP PUnit.unit
    have hMarg :
        (identityCredalProjectiveSpec C).cylinders.marginalPrevision
          PUnit.unit P = P := by
      ext X
      rfl
    rwa [hMarg] at h
  · intro hP i
    have hMarg :
        (identityCredalProjectiveSpec C).cylinders.marginalPrevision i P = P := by
      ext X
      rfl
    rwa [hMarg]

@[simp] theorem identityCredalProjectiveSpec_hasCompatibleCompletion_iff
    {Ω : Type*} (C : CredalPrevisionSet Ω) :
    (identityCredalProjectiveSpec C).hasCompatibleCompletion ↔ C.Nonempty := by
  rw [ProjectiveLocalCredalSpec.hasCompatibleCompletion,
    identityCredalProjectiveSpec_projectiveLimitCredalSet]

theorem identityCredalProjectiveSpec_hasCompatibleCompletion_of_mem
    {Ω : Type*} {C : CredalPrevisionSet Ω} {P : PrecisePrevision Ω}
    (hP : P ∈ C) :
    (identityCredalProjectiveSpec C).hasCompatibleCompletion := by
  rw [identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact ⟨P, hP⟩

@[simp] theorem identityCredalProjectiveSpec_hasStrictGlobalWidth_iff
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    (identityCredalProjectiveSpec C).hasStrictGlobalWidth X ↔
      credalSetHasStrictWidth C X := by
  unfold ProjectiveLocalCredalSpec.hasStrictGlobalWidth
  rw [identityCredalProjectiveSpec_projectiveLimitCredalSet]

theorem identityCredalProjectiveSpec_hasStrictGlobalWidth_of_credalSetHasStrictWidth
    {Ω : Type*} {C : CredalPrevisionSet Ω} {X : Gamble Ω}
    (hWidth : credalSetHasStrictWidth C X) :
    (identityCredalProjectiveSpec C).hasStrictGlobalWidth X := by
  rw [identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  exact hWidth

/-- Finite closed identity-window projective specs realize strict global width
by endpoint completions inside their projective-limit credal set.

This transports the finite closed credal endpoint theorem across the identity
projective adapter, so finite canaries can be used directly at the projective
PLN readout layer without rebuilding compactness data. -/
theorem identityCredalProjectiveSpec_exists_endpointPairReadout_of_finiteEvaluationClosed_strictWidth
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (C : CredalPrevisionSet Ω)
    (hClosed : @IsClosed (PrecisePrevision Ω)
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Ω)) C)
    (hC : C.Nonempty) (X : Gamble Ω)
    (hWidth : (identityCredalProjectiveSpec C).hasStrictGlobalWidth X) :
    ∃ Plo : PrecisePrevision Ω,
      Plo ∈ (identityCredalProjectiveSpec C).projectiveLimitCredalSet ∧
      ∃ Phi : PrecisePrevision Ω,
        Phi ∈ (identityCredalProjectiveSpec C).projectiveLimitCredalSet ∧
        Plo X = (identityCredalProjectiveSpec C).globalNaturalExtension X ∧
        Phi X =
          upperEnvelope
            (identityCredalProjectiveSpec C).projectiveLimitCredalSet X ∧
        Plo X < Phi X ∧
        (identityCredalProjectiveSpec C).globalEnvelopeWidth X =
          Phi X - Plo X ∧
        (identityCredalProjectiveSpec C).globalEnvelopeWidthComplement X =
          1 - (Phi X - Plo X) ∧
        (identityCredalProjectiveSpec C).globalEnvelopeMidpoint X =
          (Plo X + Phi X) / 2 := by
  have hRaw : credalSetHasStrictWidth C X := by
    simpa using
      ((identityCredalProjectiveSpec_hasStrictGlobalWidth_iff C X).mp hWidth)
  simpa [ProjectiveLocalCredalSpec.globalNaturalExtension,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    identityCredalProjectiveSpec_projectiveLimitCredalSet] using
    credalEnvelope_exists_endpointPairReadout_of_finiteEvaluationClosed_strictWidth
      C hClosed hC X hRaw

@[simp] theorem identityCredalProjectiveSpec_determinesGlobalGamble_iff
    {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω) :
    (identityCredalProjectiveSpec C).determinesGlobalGamble X ↔
      credalSetDetermines C X := by
  unfold ProjectiveLocalCredalSpec.determinesGlobalGamble
  rw [identityCredalProjectiveSpec_projectiveLimitCredalSet]

/-! ### Projective two-spin magnet witness -/

/-- The finite zero-temperature two-spin magnet as a projective local-credal
specification.  The single local window is the identity window, while the local
credal set is structural: all precise previsions supported on aligned states. -/
def twoSpinZeroTemperatureAlignedProjectiveSpec :
    ProjectiveLocalCredalSpec PUnit TwoSpin :=
  identityCredalProjectiveSpec twoSpinZeroTemperatureAlignedCredalSet

@[simp] theorem twoSpinZeroTemperatureAlignedProjectiveSpec_projectiveLimitCredalSet :
    twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet =
      twoSpinZeroTemperatureAlignedCredalSet :=
  identityCredalProjectiveSpec_projectiveLimitCredalSet
    twoSpinZeroTemperatureAlignedCredalSet

/-- The finite aligned two-spin projective specification is inhabited: the
all-down phase is a compatible completion. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_hasCompatibleCompletion :
    twoSpinZeroTemperatureAlignedProjectiveSpec.hasCompatibleCompletion := by
  exact identityCredalProjectiveSpec_hasCompatibleCompletion_of_mem
    (C := twoSpinZeroTemperatureAlignedCredalSet)
    (P := PrecisePrevision.dirac twoSpinAllDown)
    (PrecisePrevision.supportedOn_dirac (by
      simp [twoSpinAligned, twoSpinAllDown]))

/-- The projective two-spin magnet has strict global width on the first-spin-up
query: all-down and all-up are both compatible completions and disagree. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_hasStrictGlobalWidth :
    twoSpinZeroTemperatureAlignedProjectiveSpec.hasStrictGlobalWidth
      twoSpinFirstUpGamble := by
  exact
    identityCredalProjectiveSpec_hasStrictGlobalWidth_of_credalSetHasStrictWidth
      (C := twoSpinZeroTemperatureAlignedCredalSet)
      (X := twoSpinFirstUpGamble)
      twoSpinZeroTemperatureAlignedCredalSet_hasStrictWidth

/-- Concrete endpoint-readout canary for the finite zero-temperature aligned
two-spin projective spec: strict projective width is realized by actual
compatible endpoint completions, and their values compute the PLN-facing
width, width-complement, and midpoint coordinates. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_exists_endpointPairReadout :
    ∃ Plo : PrecisePrevision TwoSpin,
      Plo ∈ twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet ∧
      ∃ Phi : PrecisePrevision TwoSpin,
        Phi ∈
          twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet ∧
        Plo twoSpinFirstUpGamble =
          twoSpinZeroTemperatureAlignedProjectiveSpec.globalNaturalExtension
            twoSpinFirstUpGamble ∧
        Phi twoSpinFirstUpGamble =
          upperEnvelope
            twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet
            twoSpinFirstUpGamble ∧
        Plo twoSpinFirstUpGamble < Phi twoSpinFirstUpGamble ∧
        twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidth
            twoSpinFirstUpGamble =
          Phi twoSpinFirstUpGamble - Plo twoSpinFirstUpGamble ∧
        twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidthComplement
            twoSpinFirstUpGamble =
          1 - (Phi twoSpinFirstUpGamble - Plo twoSpinFirstUpGamble) ∧
        twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeMidpoint
            twoSpinFirstUpGamble =
          (Plo twoSpinFirstUpGamble + Phi twoSpinFirstUpGamble) / 2 := by
  simpa [twoSpinZeroTemperatureAlignedProjectiveSpec] using
    identityCredalProjectiveSpec_exists_endpointPairReadout_of_finiteEvaluationClosed_strictWidth
      (C := twoSpinZeroTemperatureAlignedCredalSet)
      twoSpinZeroTemperatureAlignedCredalSet_isClosed
      (⟨PrecisePrevision.dirac twoSpinAllDown,
        PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown])⟩)
      twoSpinFirstUpGamble
      twoSpinZeroTemperatureAlignedProjectiveSpec_hasStrictGlobalWidth

/-- Projective magnet canary: the compatible-completion lower and upper
envelopes are genuinely split by the zero-temperature aligned phases. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelope_nontrivial :
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalNaturalExtension
        twoSpinFirstUpGamble <
      upperEnvelope
        twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet
        twoSpinFirstUpGamble := by
  simpa [twoSpinZeroTemperatureAlignedProjectiveSpec,
    ProjectiveLocalCredalSpec.globalNaturalExtension] using
    twoSpinZeroTemperatureMagnetEnvelope_nontrivial

/-- The same projective magnet canary expressed as strictly positive envelope
width. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelopeWidth_pos :
    0 <
      twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidth
        twoSpinFirstUpGamble := by
  have h :=
    credalEnvelopeWidth_pos_of_strictWidth
      twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble
      twoSpinZeroTemperatureAlignedCredalSet_bddBelow
      twoSpinZeroTemperatureAlignedCredalSet_bddAbove
      twoSpinZeroTemperatureAlignedCredalSet_hasStrictWidth
  simpa [twoSpinZeroTemperatureAlignedProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth] using h

/-- In the finite zero-temperature aligned two-spin canary, the lower envelope
of the first-spin-up query is exactly zero: the all-down phase is admissible,
and the query is nonnegative. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalNaturalExtension_eq_zero :
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalNaturalExtension
        twoSpinFirstUpGamble = 0 := by
  apply le_antisymm
  · have hle :=
      lowerEnvelope_le_of_mem twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble twoSpinZeroTemperatureAlignedCredalSet_bddBelow
        (P := PrecisePrevision.dirac twoSpinAllDown)
        (PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown]))
    simpa [twoSpinZeroTemperatureAlignedProjectiveSpec,
      ProjectiveLocalCredalSpec.globalNaturalExtension,
      twoSpinFirstUpGamble, twoSpinAllDown] using hle
  · have hnonempty : twoSpinZeroTemperatureAlignedCredalSet.Nonempty :=
      ⟨PrecisePrevision.dirac twoSpinAllDown,
        PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown])⟩
    have hge :=
      lowerEnvelope_lower_bound twoSpinZeroTemperatureAlignedCredalSet
        hnonempty twoSpinFirstUpGamble 0 (by
          intro σ
          by_cases h : σ.1 <;> simp [twoSpinFirstUpGamble, h])
    simpa [twoSpinZeroTemperatureAlignedProjectiveSpec,
      ProjectiveLocalCredalSpec.globalNaturalExtension] using hge

/-- Raw lower-envelope form of the same finite two-spin canary.  The structural
aligned credal set admits the all-down completion, while the query is
nonnegative everywhere. -/
theorem twoSpinZeroTemperatureAlignedCredalSet_lowerEnvelope_eq_zero :
    lowerEnvelope twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble = 0 := by
  apply le_antisymm
  · have hle :=
      lowerEnvelope_le_of_mem twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble twoSpinZeroTemperatureAlignedCredalSet_bddBelow
        (P := PrecisePrevision.dirac twoSpinAllDown)
        (PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown]))
    simpa [twoSpinFirstUpGamble, twoSpinAllDown] using hle
  · have hnonempty : twoSpinZeroTemperatureAlignedCredalSet.Nonempty :=
      ⟨PrecisePrevision.dirac twoSpinAllDown,
        PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown])
      ⟩
    exact
      lowerEnvelope_lower_bound twoSpinZeroTemperatureAlignedCredalSet
        hnonempty twoSpinFirstUpGamble 0 (by
          intro σ
          by_cases h : σ.1 <;> simp [twoSpinFirstUpGamble, h])

/-- In the finite zero-temperature aligned two-spin canary, the upper envelope
of the first-spin-up query is exactly one: the all-up phase is admissible,
and the query is bounded above by one. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalUpperEnvelope_eq_one :
    upperEnvelope
        twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet
        twoSpinFirstUpGamble = 1 := by
  apply le_antisymm
  · have hnonempty : twoSpinZeroTemperatureAlignedCredalSet.Nonempty :=
      ⟨PrecisePrevision.dirac twoSpinAllDown,
        PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown])⟩
    have hle :=
      upperEnvelope_upper_bound twoSpinZeroTemperatureAlignedCredalSet
        hnonempty twoSpinFirstUpGamble 1 (by
          intro σ
          by_cases h : σ.1 <;> simp [twoSpinFirstUpGamble, h])
    simpa [twoSpinZeroTemperatureAlignedProjectiveSpec] using hle
  · have hle :=
      le_upperEnvelope_of_mem twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble twoSpinZeroTemperatureAlignedCredalSet_bddAbove
        (P := PrecisePrevision.dirac twoSpinAllUp)
        (PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllUp]))
    simpa [twoSpinZeroTemperatureAlignedProjectiveSpec,
      twoSpinFirstUpGamble, twoSpinAllUp] using hle

/-- Raw upper-envelope form of the finite two-spin canary. -/
theorem twoSpinZeroTemperatureAlignedCredalSet_upperEnvelope_eq_one :
    upperEnvelope twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble = 1 := by
  apply le_antisymm
  · have hnonempty : twoSpinZeroTemperatureAlignedCredalSet.Nonempty :=
      ⟨PrecisePrevision.dirac twoSpinAllDown,
        PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllDown])⟩
    exact
      upperEnvelope_upper_bound twoSpinZeroTemperatureAlignedCredalSet
        hnonempty twoSpinFirstUpGamble 1 (by
          intro σ
          by_cases h : σ.1 <;> simp [twoSpinFirstUpGamble, h])
  · have hle :=
      le_upperEnvelope_of_mem twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble twoSpinZeroTemperatureAlignedCredalSet_bddAbove
        (P := PrecisePrevision.dirac twoSpinAllUp)
        (PrecisePrevision.supportedOn_dirac (by
          simp [twoSpinAligned, twoSpinAllUp]))
    simpa [twoSpinFirstUpGamble, twoSpinAllUp] using hle

/-- Raw midpoint-strength form of the finite two-spin canary: the aligned
zero-temperature credal set spans the full `[0,1]` interval, so its midpoint
display coordinate is exactly one half. -/
theorem twoSpinZeroTemperatureAlignedCredalSet_envelopeMidpoint_eq_half :
    credalEnvelopeMidpoint twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble = (1 / 2 : ℝ) := by
  exact credalEnvelopeMidpoint_eq_half_of_lower_eq_zero_upper_eq_one
    twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble
    twoSpinZeroTemperatureAlignedCredalSet_lowerEnvelope_eq_zero
    twoSpinZeroTemperatureAlignedCredalSet_upperEnvelope_eq_one

/-- Raw width form of the finite two-spin canary. -/
theorem twoSpinZeroTemperatureAlignedCredalSet_envelopeWidth_eq_one :
    credalEnvelopeWidth twoSpinZeroTemperatureAlignedCredalSet
        twoSpinFirstUpGamble = 1 := by
  exact credalEnvelopeWidth_eq_one_of_lower_eq_zero_upper_eq_one
    twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble
    twoSpinZeroTemperatureAlignedCredalSet_lowerEnvelope_eq_zero
    twoSpinZeroTemperatureAlignedCredalSet_upperEnvelope_eq_one

/-- The finite zero-temperature aligned two-spin canary has the full unit
credal width on the first-spin-up query. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelopeWidth_eq_one :
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidth
        twoSpinFirstUpGamble = 1 := by
  exact
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidth_eq_one_of_unit_interval
      twoSpinFirstUpGamble
      twoSpinZeroTemperatureAlignedProjectiveSpec_globalNaturalExtension_eq_zero
      twoSpinZeroTemperatureAlignedProjectiveSpec_globalUpperEnvelope_eq_one

/-- The finite zero-temperature aligned two-spin canary has midpoint strength
coordinate one half on the first-spin-up query. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelopeMidpoint_eq_half :
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeMidpoint
        twoSpinFirstUpGamble = (1 / 2 : ℝ) := by
  exact
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeMidpoint_eq_half_of_unit_interval
      twoSpinFirstUpGamble
      twoSpinZeroTemperatureAlignedProjectiveSpec_globalNaturalExtension_eq_zero
      twoSpinZeroTemperatureAlignedProjectiveSpec_globalUpperEnvelope_eq_one

/-- The same finite canary expressed in the PLN width-complement confidence
coordinate: full interval width gives confidence coordinate zero. -/
theorem twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelopeWidthComplement_eq_zero :
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidthComplement
        twoSpinFirstUpGamble = 0 := by
  exact
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidthComplement_eq_zero_of_unit_interval
      twoSpinFirstUpGamble
      twoSpinZeroTemperatureAlignedProjectiveSpec_globalNaturalExtension_eq_zero
      twoSpinZeroTemperatureAlignedProjectiveSpec_globalUpperEnvelope_eq_one

/-- A finite identity-window projective specification whose local credal set is
all finite precise previsions. -/
def finiteUnrestrictedProjectiveSpec (Ω : Type*) :
    ProjectiveLocalCredalSpec PUnit Ω where
  cylinders := finiteIdentityCylinderSystem Ω
  localCredal _ := (Set.univ : CredalPrevisionSet Ω)

/-- Generic finite-evaluation compact crown: every finite nonempty state space
has a concrete non-singleton compact/FIP projective credal inhabitant. -/
theorem finiteUnrestricted_finiteEvaluationCompact_hasCompatibleCompletion
    (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] :
    (finiteUnrestrictedProjectiveSpec Ω).hasCompatibleCompletion := by
  classical
  letI : TopologicalSpace (PrecisePrevision Ω) :=
    PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Ω)
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  let K :
      ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem
        (finiteUnrestrictedProjectiveSpec Ω) := {
    carrier := (Set.univ : CredalPrevisionSet Ω)
    carrier_compact := by
      simpa using
        PrecisePrevision.FiniteWeights.finiteEvaluationTopology_univCompact
          (Ω := Ω)
    carrier_convex := by
      exact CredalPrevisionSet.isConvex_univ
    local_convex := by
      intro i
      exact CredalPrevisionSet.isConvex_univ
    constraint_closed := by
      intro i
      exact isClosed_univ
    finite_satisfiable := by
      intro u
      refine ⟨PrecisePrevision.dirac ω₀, ?_⟩
      constructor
      · simp
      · exact Set.mem_iInter.mpr fun i =>
          Set.mem_iInter.mpr fun _hi => by
            exact Set.mem_univ _
  }
  exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.hasCompatibleCompletion K

/-- Identity-window singleton projective specification induced by one precise
completion.  This is the reusable finite/infinite adapter for "a supplied
completion inhabits the projective credal interface." -/
def singletonIdentityProjectiveSpec {Ω : Type*}
    (P : PrecisePrevision Ω) : ProjectiveLocalCredalSpec PUnit Ω where
  cylinders := finiteIdentityCylinderSystem Ω
  localCredal _ := ({P} : CredalPrevisionSet Ω)

theorem singletonIdentityProjectiveSpec_projectiveLimitCredalSet
    {Ω : Type*} (P : PrecisePrevision Ω) :
    (singletonIdentityProjectiveSpec P).projectiveLimitCredalSet =
      ({P} : CredalPrevisionSet Ω) := by
  ext Q
  constructor
  · intro hQ
    have h := hQ PUnit.unit
    have hMarg :
        (singletonIdentityProjectiveSpec P).cylinders.marginalPrevision
          PUnit.unit Q = Q := by
      ext X
      rfl
    rw [hMarg] at h
    exact h
  · intro hQ i
    have hMarg :
        (singletonIdentityProjectiveSpec P).cylinders.marginalPrevision
          i Q = Q := by
      ext X
      rfl
    rw [hMarg]
    exact hQ

theorem singletonIdentityProjectiveSpec_hasCompatibleCompletion
    {Ω : Type*} (P : PrecisePrevision Ω) :
    (singletonIdentityProjectiveSpec P).hasCompatibleCompletion := by
  refine
    (singletonIdentityProjectiveSpec P).projectiveLimitCredalSet_nonempty_of_completion
      (P := P) ?_
  intro i
  have hMarg :
      (singletonIdentityProjectiveSpec P).cylinders.marginalPrevision i P = P := by
    ext X
    rfl
  rw [hMarg]
  exact Set.mem_singleton _

/-! ## Profile surface -/

/-- Proof-carrying profile for the shared projective credal abstraction.

This packages the reusable spine, including the compact/FIP completion bridge,
without pretending to supply the separate weak-star carrier construction. -/
structure ProjectiveCredalProfile where
  preciseCompletionToLowerPrevision :
    ∀ {Ω : Type*} (_P : PrecisePrevision Ω), LowerPrevision Ω
  preciseCompletionIsPrecise :
    ∀ {Ω : Type*} (P : PrecisePrevision Ω),
      P.toLowerPrevision.isPrecise
  diracPreciseCompletion :
    ∀ {Ω : Type*} (_ω : Ω), PrecisePrevision Ω
  diracCompletionIsPrecise :
    ∀ {Ω : Type*} (ω : Ω),
      (PrecisePrevision.dirac ω).toLowerPrevision.isPrecise
  finiteWeightsToPreciseCompletion :
    ∀ {Ω : Type*} [Fintype Ω],
      PrecisePrevision.FiniteWeights Ω → PrecisePrevision Ω
  finiteWeightsCompletionIsPrecise :
    ∀ {Ω : Type*} [Fintype Ω]
      (w : PrecisePrevision.FiniteWeights Ω),
      w.toPrecisePrevision.toLowerPrevision.isPrecise
  finiteWeightsToStdSimplex :
    ∀ {Ω : Type*} [Fintype Ω],
      PrecisePrevision.FiniteWeights Ω → stdSimplex ℝ Ω
  stdSimplexToFiniteWeights :
    ∀ {Ω : Type*} [Fintype Ω],
      stdSimplex ℝ Ω → PrecisePrevision.FiniteWeights Ω
  finiteWeightsEquivStdSimplex :
    ∀ {Ω : Type*} [Fintype Ω],
      PrecisePrevision.FiniteWeights Ω ≃ stdSimplex ℝ Ω
  finiteWeightsStdSimplexCompact :
    ∀ {Ω : Type*} [Fintype Ω],
      IsCompact (stdSimplex ℝ Ω)
  finitePreciseCompletionToWeights :
    ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
      PrecisePrevision Ω → PrecisePrevision.FiniteWeights Ω
  finitePreciseCompletionRecoveredFromWeights :
    ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
      (P : PrecisePrevision Ω),
      (PrecisePrevision.FiniteWeights.ofPrecisePrevision P).toPrecisePrevision = P
  finiteWeightsRecoveredFromPreciseCompletion :
    ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
      (w : PrecisePrevision.FiniteWeights Ω),
      PrecisePrevision.FiniteWeights.ofPrecisePrevision w.toPrecisePrevision = w
  finiteWeightsEquivPreciseCompletion :
    ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
      PrecisePrevision.FiniteWeights Ω ≃ PrecisePrevision Ω
  finiteEvaluationTopologyCompactCarrier :
    ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω],
      @IsCompact (PrecisePrevision Ω)
        (PrecisePrevision.FiniteWeights.finiteEvaluationTopology (Ω := Ω))
        Set.univ
  boundedMeasurableCoordinateLawSetCompact :
    ∀ {Ω : Type*} [MeasurableSpace Ω],
      IsCompact
        (BoundedMeasurablePrecisePrevision.coordinateLawSet (Ω := Ω))
  boundedMeasurableEvaluationTopologyCompactCarrier :
    ∀ {Ω : Type*} [MeasurableSpace Ω],
      @IsCompact (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        Set.univ
  boundedMeasurableEvaluationCompactSpace :
    ∀ {Ω : Type*} [MeasurableSpace Ω],
      @CompactSpace (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
  boundedMeasurableCredalSetClosure :
    ∀ {Ω : Type*} [MeasurableSpace Ω],
      BoundedMeasurableCredalSet Ω → BoundedMeasurableCredalSet Ω
  boundedMeasurableCredalSetSubsetClosure :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω),
      C ⊆ boundedMeasurableCredalSetEvaluationClosure C
  boundedMeasurableCredalSetClosureIsClosed :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω),
      @IsClosed (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        (boundedMeasurableCredalSetEvaluationClosure C)
  boundedMeasurableCredalSetClosureIsCompact :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω),
      @IsCompact (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        (boundedMeasurableCredalSetEvaluationClosure C)
  boundedMeasurableCredalSetClosureNonempty :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω),
      C.Nonempty → (boundedMeasurableCredalSetEvaluationClosure C).Nonempty
  boundedMeasurableCredalSetClosureIsConvex :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω),
      BoundedMeasurableCredalSet.IsConvex C →
        BoundedMeasurableCredalSet.IsConvex
          (boundedMeasurableCredalSetEvaluationClosure C)
  boundedMeasurableNaturalExtensionDominatingCompletionsIsClosed :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty),
      @IsClosed (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C _hC))
  boundedMeasurableNaturalExtensionDominatingCompletionsIsCompact :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty),
      @IsCompact (BoundedMeasurablePrecisePrevision Ω)
        (BoundedMeasurablePrecisePrevision.evaluationTopology (Ω := Ω))
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C _hC))
  boundedMeasurableNaturalExtensionDominatingCompletionsIsConvex :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty),
      BoundedMeasurableCredalSet.IsConvex
        (boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision C _hC))
  boundedMeasurableNaturalExtensionPrevisionLeCompletion :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty)
      {P : BoundedMeasurablePrecisePrevision Ω},
      P ∈ C → ∀ X : BoundedMeasurableGamble Ω,
        boundedMeasurableNaturalExtensionPrevision C _hC X ≤ P X
  boundedMeasurableNaturalExtensionPrevisionGreatestLowerBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty)
      (L : BoundedMeasurableLowerPrevision Ω),
      (∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
        ∀ X : BoundedMeasurableGamble Ω, L X ≤ P X) →
      ∀ X : BoundedMeasurableGamble Ω,
        L X ≤ boundedMeasurableNaturalExtensionPrevision C _hC X
  boundedMeasurableNaturalUpperEnvelopePrevisionCompletionLe :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty)
      {P : BoundedMeasurablePrecisePrevision Ω},
      P ∈ C → ∀ X : BoundedMeasurableGamble Ω,
        P X ≤ boundedMeasurableNaturalUpperEnvelopePrevision C _hC X
  boundedMeasurableNaturalUpperEnvelopePrevisionLeastUpperBound :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (C : BoundedMeasurableCredalSet Ω) (_hC : C.Nonempty)
      (U : BoundedMeasurableUpperPrevision Ω),
      (∀ P : BoundedMeasurablePrecisePrevision Ω, P ∈ C →
        ∀ X : BoundedMeasurableGamble Ω, P X ≤ U X) →
      ∀ X : BoundedMeasurableGamble Ω,
        boundedMeasurableNaturalUpperEnvelopePrevision C _hC X ≤ U X
  finiteStrictlyPositiveUniformLowerBound :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (X : Gamble Ω),
      (∀ ω, 0 < X ω) → ∃ ε : ℝ, 0 < ε ∧ ∀ ω, ε ≤ X ω
  finiteGambleUniformLowerBound :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (X : Gamble Ω),
      ∃ c : ℝ, ∀ ω, c ≤ X ω
  finiteGambleUniformUpperBound :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (X : Gamble Ω),
      ∃ c : ℝ, ∀ ω, X ω ≤ c
  finiteCredalRangeBddBelow :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (X : Gamble Ω),
      BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)
  finiteCredalRangeBddAbove :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (X : Gamble Ω),
      BddAbove ((fun P : PrecisePrevision Ω => P X) '' C)
  lowerEnvelopeNegEqNegUpperEnvelope :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω),
      lowerEnvelope C (-X) = -upperEnvelope C X
  upperEnvelopeNegEqNegLowerEnvelope :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω),
      upperEnvelope C (-X) = -lowerEnvelope C X
  pmfToFiniteWeights :
    ∀ {Ω : Type*} [Fintype Ω],
      PMF Ω → PrecisePrevision.FiniteWeights Ω
  pmfToPreciseCompletion :
    ∀ {Ω : Type*} [Fintype Ω], PMF Ω → PrecisePrevision Ω
  pmfCompletionIsPrecise :
    ∀ {Ω : Type*} [Fintype Ω] (p : PMF Ω),
      (PrecisePrevision.FiniteWeights.ofPMFPrevision p).toLowerPrevision.isPrecise
  finiteProbabilityMeasureToWeights :
    ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
      [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      PrecisePrevision.FiniteWeights Ω
  finiteProbabilityMeasureToPreciseCompletion :
    ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
      [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      PrecisePrevision Ω
  finiteProbabilityMeasureCompletionIsPrecise :
    ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
      [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      (PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision μ).toLowerPrevision.isPrecise
  lowerEnvelopeBuildsLowerPrevision :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)),
      LowerPrevision Ω
  upperEnvelopeBuildsUpperPrevision :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddAbove ((fun P : PrecisePrevision Ω => P X) '' C)),
      UpperPrevision Ω
  finiteLowerEnvelopeBuildsLowerPrevision :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty),
      LowerPrevision Ω
  finiteUpperEnvelopeBuildsUpperPrevision :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty),
      UpperPrevision Ω
  lowerEnvelopePrevisionConjugateEqUpperEnvelope :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
      (X : Gamble Ω),
      (lowerEnvelopePrevision C _hC _hBdd).conjugate X = upperEnvelope C X
  upperEnvelopePrevisionConjugateEqLowerEnvelope :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
      (X : Gamble Ω),
      (upperEnvelopePrevision C _hC _hBdd).conjugate X = lowerEnvelope C X
  lowerEnvelopePrevisionLeCompletion :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
      {P : PrecisePrevision Ω},
      P ∈ C → ∀ X : Gamble Ω,
        lowerEnvelopePrevision C _hC _hBdd X ≤ P X
  lowerEnvelopePrevisionGreatestLowerBound :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
      (L : LowerPrevision Ω),
      (∀ P : PrecisePrevision Ω, P ∈ C →
        ∀ X : Gamble Ω, L X ≤ P X) →
      ∀ X : Gamble Ω, L X ≤ lowerEnvelopePrevision C _hC _hBdd X
  finiteLowerEnvelopePrevisionLeCompletion :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty)
      {P : PrecisePrevision Ω},
      P ∈ C → ∀ X : Gamble Ω,
        finiteLowerEnvelopePrevision C _hC X ≤ P X
  finiteLowerEnvelopePrevisionGreatestLowerBound :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty)
      (L : LowerPrevision Ω),
      (∀ P : PrecisePrevision Ω, P ∈ C →
        ∀ X : Gamble Ω, L X ≤ P X) →
      ∀ X : Gamble Ω, L X ≤ finiteLowerEnvelopePrevision C _hC X
  upperEnvelopePrevisionCompletionLe :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
      {P : PrecisePrevision Ω},
      P ∈ C → ∀ X : Gamble Ω,
        P X ≤ upperEnvelopePrevision C _hC _hBdd X
  upperEnvelopePrevisionLeastUpperBound :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddAbove ((fun P : PrecisePrevision Ω => P X) '' C))
      (U : UpperPrevision Ω),
      (∀ P : PrecisePrevision Ω, P ∈ C →
        ∀ X : Gamble Ω, P X ≤ U X) →
      ∀ X : Gamble Ω, upperEnvelopePrevision C _hC _hBdd X ≤ U X
  finiteUpperEnvelopePrevisionCompletionLe :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty)
      {P : PrecisePrevision Ω},
      P ∈ C → ∀ X : Gamble Ω,
        P X ≤ finiteUpperEnvelopePrevision C _hC X
  finiteUpperEnvelopePrevisionLeastUpperBound :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty)
      (U : UpperPrevision Ω),
      (∀ P : PrecisePrevision Ω, P ∈ C →
        ∀ X : Gamble Ω, P X ≤ U X) →
      ∀ X : Gamble Ω, finiteUpperEnvelopePrevision C _hC X ≤ U X
  finiteLowerEnvelopeAvoidsSureLoss :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)),
      (lowerEnvelopePrevision C _hC _hBdd).avoidsSureLoss
  finiteLowerEnvelopeAvoidsSureLossAutomatic :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty),
      (finiteLowerEnvelopePrevision C _hC).avoidsSureLoss
  finiteLowerEnvelopeIsCoherent :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)),
      (lowerEnvelopePrevision C _hC _hBdd).isCoherent
  finiteLowerEnvelopeIsCoherentAutomatic :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty),
      (finiteLowerEnvelopePrevision C _hC).isCoherent
  dominatingPreciseCompletionsBddBelow :
    ∀ {Ω : Type*} (L : LowerPrevision Ω) (X : Gamble Ω),
      BddBelow
        ((fun P : PrecisePrevision Ω => P X) ''
          dominatingPreciseCompletions L)
  lowerPrevisionLeDominatingPreciseEnvelope :
    ∀ {Ω : Type*} (L : LowerPrevision Ω)
      (_hD : (dominatingPreciseCompletions L).Nonempty) (X : Gamble Ω),
      L X ≤ lowerEnvelope (dominatingPreciseCompletions L) X
  existsDominatingPreciseCompletionTouching :
    ∀ {Ω : Type*} (L : LowerPrevision Ω) (X : Gamble Ω),
      ∃ P : PrecisePrevision Ω,
        P ∈ dominatingPreciseCompletions L ∧ P X = L X
  lowerPrevisionHasExactDominatingPreciseEnvelope :
    ∀ {Ω : Type*} (L : LowerPrevision Ω),
      hasExactDominatingPreciseEnvelope L
  dominatingPreciseCompletionsNonempty :
    ∀ {Ω : Type*} (L : LowerPrevision Ω),
      (dominatingPreciseCompletions L).Nonempty
  lowerEnvelopeDominatingPreciseCompletionsEq :
    ∀ {Ω : Type*} (L : LowerPrevision Ω) (X : Gamble Ω),
      lowerEnvelope (dominatingPreciseCompletions L) X = L X
  lowerEnvelopePrevisionDominatingPreciseCompletionsEq :
    ∀ {Ω : Type*} (L : LowerPrevision Ω),
      lowerEnvelopePrevision (dominatingPreciseCompletions L)
          (dominatingPreciseCompletions_nonempty L)
          (dominatingPreciseCompletions_bddBelow L) = L
  lowerEnvelopePrevisionHasExactDominatingPreciseEnvelope :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)),
      hasExactDominatingPreciseEnvelope (lowerEnvelopePrevision C _hC _hBdd)
  finiteLowerEnvelopePrevisionHasExactDominatingPreciseEnvelope :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (C : CredalPrevisionSet Ω) (_hC : C.Nonempty),
      hasExactDominatingPreciseEnvelope (finiteLowerEnvelopePrevision C _hC)
  coherentOfExactDominatingPreciseEnvelopeFinite :
    ∀ {Ω : Type*} [Fintype Ω] [Nonempty Ω]
      (L : LowerPrevision Ω),
      hasExactDominatingPreciseEnvelope L → L.isCoherent
  lowerEnvelopeIsSuperadditive :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
      (X Y : Gamble Ω),
      lowerEnvelope C X + lowerEnvelope C Y ≤ lowerEnvelope C (X + Y)
  lowerUpperEnvelopeNontrivialOfDisagreement :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C))
      {P Q : PrecisePrevision Ω},
      P ∈ C → Q ∈ C → P X < Q X →
        lowerEnvelope C X < upperEnvelope C X
  credalEnvelopeWidthNonnegative :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C)),
      0 ≤ credalEnvelopeWidth C X
  credalSetDeterminesSingleton :
    ∀ {Ω : Type*} (P : PrecisePrevision Ω) (X : Gamble Ω),
      credalSetDetermines ({P} : CredalPrevisionSet Ω) X
  lowerUpperEnvelopeCollapseOfDetermines :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C))
      {P : PrecisePrevision Ω},
      P ∈ C → credalSetDetermines C X →
        lowerEnvelope C X = upperEnvelope C X
  credalEnvelopeWidthZeroOfDetermines :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C))
      {P : PrecisePrevision Ω},
      P ∈ C → credalSetDetermines C X →
        credalEnvelopeWidth C X = 0
  credalEnvelopeMidpointEqOfDetermines :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C))
      {P : PrecisePrevision Ω},
      P ∈ C → credalSetDetermines C X →
        credalEnvelopeMidpoint C X = P X
  lowerUpperEnvelopeNontrivialOfStrictWidth :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C)),
      credalSetHasStrictWidth C X →
        lowerEnvelope C X < upperEnvelope C X
  credalEnvelopeWidthPositiveOfStrictWidth :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C)),
      credalSetHasStrictWidth C X →
        0 < credalEnvelopeWidth C X
  credalEnvelopeWidthInUnitOfUnit :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C)),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        credalEnvelopeWidth C X ∈ Set.Icc (0 : ℝ) 1
  credalEnvelopeWidthComplementInUnitOfUnit :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C)),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        credalEnvelopeWidthComplement C X ∈ Set.Icc (0 : ℝ) 1
  credalEnvelopeMidpointInUnitOfUnit :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω)
      (_hC : C.Nonempty)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Ω => P X) '' C))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Ω => P X) '' C)),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        credalEnvelopeMidpoint C X ∈ Set.Icc (0 : ℝ) 1
  strictWidthRefutesDetermination :
    ∀ {Ω : Type*} {C : CredalPrevisionSet Ω} {X : Gamble Ω},
      credalSetHasStrictWidth C X → ¬ credalSetDetermines C X
  strictWidthIffNotDetermines :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω),
      credalSetHasStrictWidth C X ↔ ¬ credalSetDetermines C X
  boolDiracEnvelopeNontrivial :
    lowerEnvelope boolDiracCredalSet boolTrueGamble <
      upperEnvelope boolDiracCredalSet boolTrueGamble
  twoSpinMagnetEnvelopeNontrivial :
    lowerEnvelope twoSpinMagnetCredalSet twoSpinFirstUpGamble <
      upperEnvelope twoSpinMagnetCredalSet twoSpinFirstUpGamble
  twoSpinZeroTemperatureMagnetEnvelopeNontrivial :
    lowerEnvelope twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble <
      upperEnvelope twoSpinZeroTemperatureAlignedCredalSet twoSpinFirstUpGamble
  twoSpinZeroTemperatureAlignedCredalSetStrictWidth :
    credalSetHasStrictWidth twoSpinZeroTemperatureAlignedCredalSet
      twoSpinFirstUpGamble
  identityCredalProjectiveSpecLimitSet :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω),
      (identityCredalProjectiveSpec C).projectiveLimitCredalSet = C
  identityCredalProjectiveSpecCompletionIff :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω),
      (identityCredalProjectiveSpec C).hasCompatibleCompletion ↔ C.Nonempty
  identityCredalProjectiveSpecStrictWidthIff :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω) (X : Gamble Ω),
      (identityCredalProjectiveSpec C).hasStrictGlobalWidth X ↔
        credalSetHasStrictWidth C X
  projectiveStrictWidthIffNotDetermines :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global) (X : Gamble Global),
      S.hasStrictGlobalWidth X ↔ ¬ S.determinesGlobalGamble X
  twoSpinZeroTemperatureAlignedProjectiveCompletion :
    twoSpinZeroTemperatureAlignedProjectiveSpec.hasCompatibleCompletion
  twoSpinZeroTemperatureAlignedProjectiveStrictWidth :
    twoSpinZeroTemperatureAlignedProjectiveSpec.hasStrictGlobalWidth
      twoSpinFirstUpGamble
  twoSpinZeroTemperatureAlignedProjectiveEnvelopeNontrivial :
    twoSpinZeroTemperatureAlignedProjectiveSpec.globalNaturalExtension
        twoSpinFirstUpGamble <
      upperEnvelope
        twoSpinZeroTemperatureAlignedProjectiveSpec.projectiveLimitCredalSet
        twoSpinFirstUpGamble
  twoSpinZeroTemperatureAlignedProjectiveWidthPositive :
    0 <
      twoSpinZeroTemperatureAlignedProjectiveSpec.globalEnvelopeWidth
        twoSpinFirstUpGamble
  projectiveLimitNonemptyOfCompletion :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      {P : PrecisePrevision Global},
      (∀ i, S.cylinders.marginalPrevision i P ∈ S.localCredal i) →
        S.hasCompatibleCompletion
  projectiveLimitNonemptyOfLocalDirac :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (ω : Global),
      (∀ i, PrecisePrevision.dirac (S.cylinders.project i ω) ∈
        S.localCredal i) →
        S.hasCompatibleCompletion
  projectiveLimitConvexOfLocalConvex :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global),
      (∀ i, CredalPrevisionSet.IsConvex (S.localCredal i)) →
        CredalPrevisionSet.IsConvex S.projectiveLimitCredalSet
  dominatingPreciseCompletionsConvex :
    ∀ {Ω : Type*} (L : LowerPrevision Ω),
      CredalPrevisionSet.IsConvex (dominatingPreciseCompletions L)
  projectiveLimitClosedOfClosedConstraints :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      [TopologicalSpace (PrecisePrevision Global)],
      (∀ i, IsClosed {P : PrecisePrevision Global |
        S.cylinders.marginalPrevision i P ∈ S.localCredal i}) →
        IsClosed S.projectiveLimitCredalSet
  compactFIPLimitSetCompact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      [TopologicalSpace (PrecisePrevision Global)]
      (_K : ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem S),
      IsCompact _K.limitSet
  compactFIPProducesCompatibleCompletion :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      [TopologicalSpace (PrecisePrevision Global)]
      (_K : ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem S),
      S.hasCompatibleCompletion
  lowerPrevisionCompactFIPCompletion :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalLowerPrevisionSpec Window Global)
      [TopologicalSpace (PrecisePrevision Global)]
      (carrier : CredalPrevisionSet Global),
      IsCompact carrier →
        CredalPrevisionSet.IsConvex carrier →
          (∀ i, IsClosed {P : PrecisePrevision Global |
            S.cylinders.marginalPrevision i P ∈
              dominatingPreciseCompletions (S.localLower i)}) →
            S.finiteWindowCompatibleInCarrier carrier →
              S.toCredalSpec.hasCompatibleCompletion
  boolFalseExactCompactFIPCompletion :
    boolFalseExactProjectiveSpec.{0}.hasCompatibleCompletion
  boolUnrestrictedFiniteEvaluationCompactCompletion :
    boolUnrestrictedProjectiveSpec.{0}.hasCompatibleCompletion
  finiteUnrestrictedFiniteEvaluationCompactCompletion :
    ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω],
      (finiteUnrestrictedProjectiveSpec Ω).hasCompatibleCompletion
  singletonIdentityProjectiveSpecHasCompatibleCompletion :
    ∀ {Ω : Type*} (P : PrecisePrevision Ω),
      (singletonIdentityProjectiveSpec P).hasCompatibleCompletion
  singletonIdentityProjectiveSpecLimitSet :
    ∀ {Ω : Type*} (P : PrecisePrevision Ω),
      (singletonIdentityProjectiveSpec P).projectiveLimitCredalSet =
        ({P} : CredalPrevisionSet Ω)
  globalNaturalExtensionSuperadditive :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (X Y : Gamble Global),
      S.globalNaturalExtension X + S.globalNaturalExtension Y ≤
        S.globalNaturalExtension (X + Y)
  globalNaturalExtensionPrevisionLeCompletion :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → ∀ X : Gamble Global,
        S.globalNaturalExtensionPrevision _hNonempty _hBdd X ≤ P X
  globalNaturalExtensionPrevisionGreatestLowerBound :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (L : LowerPrevision Global),
      (∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
        ∀ X : Gamble Global, L X ≤ P X) →
      ∀ X : Gamble Global,
        L X ≤ S.globalNaturalExtensionPrevision _hNonempty _hBdd X
  globalUpperEnvelopeBuildsUpperPrevision :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddAbove ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      UpperPrevision Global
  globalUpperEnvelopePrevisionCompletionLe :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddAbove ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → ∀ X : Gamble Global,
        P X ≤ S.globalUpperEnvelopePrevision _hNonempty _hBdd X
  globalUpperEnvelopePrevisionLeastUpperBound :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddAbove ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (U : UpperPrevision Global),
      (∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
        ∀ X : Gamble Global, P X ≤ U X) →
      ∀ X : Gamble Global,
        S.globalUpperEnvelopePrevision _hNonempty _hBdd X ≤ U X
  globalNaturalExtensionConjugateEqUpperEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (X : Gamble Global),
      (S.globalNaturalExtensionPrevision _hNonempty _hBdd).conjugate X =
        upperEnvelope S.projectiveLimitCredalSet X
  globalUpperEnvelopeConjugateEqNaturalExtension :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddAbove ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (X : Gamble Global),
      (S.globalUpperEnvelopePrevision _hNonempty _hBdd).conjugate X =
        S.globalNaturalExtension X
  finiteGlobalNaturalExtensionPrevisionLeCompletion :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → ∀ X : Gamble Global,
        S.finiteGlobalNaturalExtensionPrevision _hNonempty X ≤ P X
  finiteGlobalNaturalExtensionPrevisionGreatestLowerBound :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (L : LowerPrevision Global),
      (∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
        ∀ X : Gamble Global, L X ≤ P X) →
      ∀ X : Gamble Global,
        L X ≤ S.finiteGlobalNaturalExtensionPrevision _hNonempty X
  finiteGlobalUpperEnvelopeBuildsUpperPrevision :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion),
      UpperPrevision Global
  finiteGlobalUpperEnvelopePrevisionCompletionLe :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → ∀ X : Gamble Global,
        P X ≤ S.finiteGlobalUpperEnvelopePrevision _hNonempty X
  finiteGlobalUpperEnvelopePrevisionLeastUpperBound :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (U : UpperPrevision Global),
      (∀ P : PrecisePrevision Global, P ∈ S.projectiveLimitCredalSet →
        ∀ X : Gamble Global, P X ≤ U X) →
      ∀ X : Gamble Global,
        S.finiteGlobalUpperEnvelopePrevision _hNonempty X ≤ U X
  finiteGlobalNaturalExtensionConjugateEqUpperEnvelope :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global),
      (S.finiteGlobalNaturalExtensionPrevision _hNonempty).conjugate X =
        upperEnvelope S.projectiveLimitCredalSet X
  finiteGlobalUpperEnvelopeConjugateEqNaturalExtension :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global),
      (S.finiteGlobalUpperEnvelopePrevision _hNonempty).conjugate X =
        S.globalNaturalExtension X
  globalEnvelopeWidthNonnegative :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      0 ≤ S.globalEnvelopeWidth X
  globalNaturalExtensionEqOfDetermines :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → S.determinesGlobalGamble X →
        S.globalNaturalExtension X = P X
  globalEnvelopeWidthZeroOfDetermines :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → S.determinesGlobalGamble X →
        S.globalEnvelopeWidth X = 0
  globalEnvelopeMidpointEqOfDetermines :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → S.determinesGlobalGamble X →
        S.globalEnvelopeMidpoint X = P X
  globalLowerUpperEnvelopeCollapseOfDetermines :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      {P : PrecisePrevision Global},
      P ∈ S.projectiveLimitCredalSet → S.determinesGlobalGamble X →
        S.globalNaturalExtension X =
          upperEnvelope S.projectiveLimitCredalSet X
  globalLowerUpperEnvelopeNontrivialOfStrictWidth :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      S.hasStrictGlobalWidth X →
        S.globalNaturalExtension X <
          upperEnvelope S.projectiveLimitCredalSet X
  globalEnvelopeWidthPositiveOfStrictWidth :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      S.hasStrictGlobalWidth X →
        0 < S.globalEnvelopeWidth X
  globalEnvelopeWidthInUnitOfUnit :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        S.globalEnvelopeWidth X ∈ Set.Icc (0 : ℝ) 1
  globalEnvelopeWidthComplementInUnitOfUnit :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        S.globalEnvelopeWidthComplement X ∈ Set.Icc (0 : ℝ) 1
  globalEnvelopeMidpointInUnitOfUnit :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global)
      (_hBddBelow : BddBelow
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet))
      (_hBddAbove : BddAbove
        ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        S.globalEnvelopeMidpoint X ∈ Set.Icc (0 : ℝ) 1
  finiteGlobalEnvelopeWidthInUnitOfUnit :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        S.globalEnvelopeWidth X ∈ Set.Icc (0 : ℝ) 1
  finiteGlobalEnvelopeWidthComplementInUnitOfUnit :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        S.globalEnvelopeWidthComplement X ∈ Set.Icc (0 : ℝ) 1
  finiteGlobalEnvelopeMidpointInUnitOfUnit :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (X : Gamble Global),
      (∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) →
        S.globalEnvelopeMidpoint X ∈ Set.Icc (0 : ℝ) 1
  globalNaturalExtensionAvoidsWeakSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      (S.globalNaturalExtensionPrevision _hNonempty _hBdd).avoidsWeakSureLoss
  globalNaturalExtensionHasExactDominatingPreciseEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      hasExactDominatingPreciseEnvelope
        (S.globalNaturalExtensionPrevision _hNonempty _hBdd)
  finiteGlobalNaturalExtensionBuildsLowerPrevision :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion),
      LowerPrevision Global
  finiteGlobalNaturalExtensionAvoidsSureLoss :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion),
      (S.finiteGlobalNaturalExtensionPrevision _hNonempty).avoidsSureLoss
  finiteGlobalNaturalExtensionIsCoherent :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion),
      (S.finiteGlobalNaturalExtensionPrevision _hNonempty).isCoherent
  finiteGlobalNaturalExtensionHasExactDominatingPreciseEnvelope :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion),
      hasExactDominatingPreciseEnvelope
        (S.finiteGlobalNaturalExtensionPrevision _hNonempty)
  cylinderLocalCredalSet :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global) (i : Window),
      CredalPrevisionSet (S.cylinders.Local i)
  cylinderLocalCredalSetNonempty :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion) (i : Window),
      (S.cylinderLocalCredalSet i).Nonempty
  cylinderNaturalExtensionBuildsLowerPrevision :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion) (i : Window)
      (_hBdd : ∀ X : Gamble (S.cylinders.Local i),
        BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i)),
      LowerPrevision (S.cylinders.Local i)
  cylinderNaturalExtensionAvoidsUniformSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion) (i : Window)
      (_hBdd : ∀ X : Gamble (S.cylinders.Local i),
        BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i)),
      (S.cylinderNaturalExtensionPrevision _hNonempty i _hBdd).avoidsUniformSureLoss
  cylinderNaturalExtensionHasExactDominatingPreciseEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion) (i : Window)
      (_hBdd : ∀ X : Gamble (S.cylinders.Local i),
        BddBelow ((fun R : PrecisePrevision (S.cylinders.Local i) => R X) ''
          S.cylinderLocalCredalSet i)),
      hasExactDominatingPreciseEnvelope
        (S.cylinderNaturalExtensionPrevision _hNonempty i _hBdd)
  finiteCylinderNaturalExtensionBuildsLowerPrevision :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)],
      LowerPrevision (S.cylinders.Local i)
  finiteCylinderNaturalExtensionAvoidsSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)],
      (S.finiteCylinderNaturalExtensionPrevision _hNonempty i).avoidsSureLoss
  finiteCylinderNaturalExtensionIsCoherent :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)],
      (S.finiteCylinderNaturalExtensionPrevision _hNonempty i).isCoherent
  finiteCylinderNaturalExtensionHasExactDominatingPreciseEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCylinderCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)],
      hasExactDominatingPreciseEnvelope
        (S.finiteCylinderNaturalExtensionPrevision _hNonempty i)
  cylinderWeakSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global),
      S.hasCompatibleCompletion → S.cylinderGamblesAvoidWeakSureLoss
  cylinderUniformSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global),
      S.hasCompatibleCompletion → S.cylinderGamblesAvoidUniformSureLoss
  cylinderUpperEnvelopeLeLocalUpperEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) (X : Gamble (S.cylinders.Local i))
      (_hLocalBdd : BddAbove
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i)),
      upperEnvelope S.projectiveLimitCredalSet
          (S.cylinders.cylinderGamble i X) ≤
        S.localUpperEnvelope i X
  cylinderDeterminationExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (i : Window) (_hExact : S.localCredalExactAt i)
      (X : Gamble (S.cylinders.Local i)),
      S.determinesGlobalGamble (S.cylinders.cylinderGamble i X) ↔
        credalSetDetermines (S.localCredal i) X
  cylinderStrictWidthExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (i : Window) (_hExact : S.localCredalExactAt i)
      (X : Gamble (S.cylinders.Local i)),
      S.hasStrictGlobalWidth (S.cylinders.cylinderGamble i X) ↔
        credalSetHasStrictWidth (S.localCredal i) X
  cylinderNaturalExtensionExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hLocalBdd : BddBelow
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hGlobalBdd : BddBelow
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hExact : S.localCredalExactAt i),
      S.globalNaturalExtension (S.cylinders.cylinderGamble i X) =
        S.localNaturalExtension i X
  cylinderUpperEnvelopeExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hLocalBdd : BddAbove
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hGlobalBdd : BddAbove
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hExact : S.localCredalExactAt i),
      upperEnvelope S.projectiveLimitCredalSet
          (S.cylinders.cylinderGamble i X) =
        S.localUpperEnvelope i X
  cylinderEnvelopeWidthExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hLocalBddBelow : BddBelow
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hLocalBddAbove : BddAbove
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hGlobalBddBelow : BddBelow
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hGlobalBddAbove : BddAbove
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hExact : S.localCredalExactAt i),
      S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeWidth i X
  cylinderEnvelopeWidthComplementExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hLocalBddBelow : BddBelow
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hLocalBddAbove : BddAbove
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hGlobalBddBelow : BddBelow
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hGlobalBddAbove : BddAbove
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hExact : S.localCredalExactAt i),
      S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeWidthComplement i X
  cylinderEnvelopeMidpointExact :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hLocalBddBelow : BddBelow
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hLocalBddAbove : BddAbove
        ((fun Q : PrecisePrevision (S.cylinders.Local i) => Q X) ''
          S.localCredal i))
      (_hGlobalBddBelow : BddBelow
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hGlobalBddAbove : BddAbove
        ((fun P : PrecisePrevision Global =>
            P (S.cylinders.cylinderGamble i X)) '' S.projectiveLimitCredalSet))
      (_hExact : S.localCredalExactAt i),
      S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeMidpoint i X
  finiteCylinderNaturalExtensionExact :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
      (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hExact : S.localCredalExactAt i),
      S.globalNaturalExtension (S.cylinders.cylinderGamble i X) =
        S.localNaturalExtension i X
  finiteCylinderUpperEnvelopeExact :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
      (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hExact : S.localCredalExactAt i),
      upperEnvelope S.projectiveLimitCredalSet
          (S.cylinders.cylinderGamble i X) =
        S.localUpperEnvelope i X
  finiteCylinderEnvelopeWidthExact :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
      (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hExact : S.localCredalExactAt i),
      S.globalEnvelopeWidth (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeWidth i X
  finiteCylinderEnvelopeWidthComplementExact :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
      (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hExact : S.localCredalExactAt i),
      S.globalEnvelopeWidthComplement (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeWidthComplement i X
  finiteCylinderEnvelopeMidpointExact :
    ∀ {Window Global : Type*} [LE Window] [Fintype Global] [Nonempty Global]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hGlobalNonempty : S.hasCompatibleCompletion)
      (i : Window) [Fintype (S.cylinders.Local i)] [Nonempty (S.cylinders.Local i)]
      (X : Gamble (S.cylinders.Local i))
      (_hLocalNonempty : (S.localCredal i).Nonempty)
      (_hExact : S.localCredalExactAt i),
      S.globalEnvelopeMidpoint (S.cylinders.cylinderGamble i X) =
        S.localEnvelopeMidpoint i X
  singletonCompletionCollapsesEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (P : PrecisePrevision Global)
      (_hEq : S.projectiveLimitCredalSet = ({P} : CredalPrevisionSet Global))
      (X : Gamble Global),
      S.globalNaturalExtension X = P X

/-- The current gap-free shared projective credal profile. -/
noncomputable def projectiveCredalProfile : ProjectiveCredalProfile where
  preciseCompletionToLowerPrevision :=
    PrecisePrevision.toLowerPrevision
  preciseCompletionIsPrecise :=
    PrecisePrevision.toLowerPrevision_precise
  diracPreciseCompletion :=
    PrecisePrevision.dirac
  diracCompletionIsPrecise :=
    PrecisePrevision.dirac_precise
  finiteWeightsToPreciseCompletion :=
    PrecisePrevision.FiniteWeights.toPrecisePrevision
  finiteWeightsCompletionIsPrecise :=
    PrecisePrevision.FiniteWeights.toPrecisePrevision_precise
  finiteWeightsToStdSimplex :=
    PrecisePrevision.FiniteWeights.toStdSimplex
  stdSimplexToFiniteWeights :=
    PrecisePrevision.FiniteWeights.ofStdSimplex
  finiteWeightsEquivStdSimplex :=
    PrecisePrevision.FiniteWeights.equivStdSimplex
  finiteWeightsStdSimplexCompact :=
    by
      intro Ω instFintype
      exact PrecisePrevision.FiniteWeights.stdSimplexCarrierCompact (Ω := Ω)
  finitePreciseCompletionToWeights :=
    PrecisePrevision.FiniteWeights.ofPrecisePrevision
  finitePreciseCompletionRecoveredFromWeights :=
    PrecisePrevision.FiniteWeights.toPrecisePrevision_ofPrecisePrevision
  finiteWeightsRecoveredFromPreciseCompletion :=
    PrecisePrevision.FiniteWeights.ofPrecisePrevision_toPrecisePrevision
  finiteWeightsEquivPreciseCompletion :=
    PrecisePrevision.FiniteWeights.equivPrecisePrevision
  finiteEvaluationTopologyCompactCarrier :=
    by
      intro Ω instFintype instDecidableEq
      exact
        PrecisePrevision.FiniteWeights.finiteEvaluationTopology_univCompact
          (Ω := Ω)
  boundedMeasurableCoordinateLawSetCompact :=
    by
      intro Ω instMeasurableSpace
      exact
        BoundedMeasurablePrecisePrevision.coordinateLawSet_isCompact
          (Ω := Ω)
  boundedMeasurableEvaluationTopologyCompactCarrier :=
    by
      intro Ω instMeasurableSpace
      exact
        BoundedMeasurablePrecisePrevision.evaluationTopology_univCompact
          (Ω := Ω)
  boundedMeasurableEvaluationCompactSpace :=
    by
      intro Ω instMeasurableSpace
      exact
        BoundedMeasurablePrecisePrevision.evaluationCompactSpace
          (Ω := Ω)
  boundedMeasurableCredalSetClosure :=
    by
      intro Ω instMeasurableSpace
      exact boundedMeasurableCredalSetEvaluationClosure
  boundedMeasurableCredalSetSubsetClosure :=
    by
      intro Ω instMeasurableSpace C
      exact boundedMeasurableCredalSet_subset_evaluationClosure C
  boundedMeasurableCredalSetClosureIsClosed :=
    by
      intro Ω instMeasurableSpace C
      exact boundedMeasurableCredalSetEvaluationClosure_isClosed C
  boundedMeasurableCredalSetClosureIsCompact :=
    by
      intro Ω instMeasurableSpace C
      exact boundedMeasurableCredalSetEvaluationClosure_isCompact C
  boundedMeasurableCredalSetClosureNonempty :=
    by
      intro Ω instMeasurableSpace C hC
      exact boundedMeasurableCredalSetEvaluationClosure_nonempty C hC
  boundedMeasurableCredalSetClosureIsConvex :=
    by
      intro Ω instMeasurableSpace C hC
      exact boundedMeasurableCredalSetEvaluationClosure_isConvex C hC
  boundedMeasurableNaturalExtensionDominatingCompletionsIsClosed :=
    by
      intro Ω instMeasurableSpace C hC
      exact
        boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isClosed
          C hC
  boundedMeasurableNaturalExtensionDominatingCompletionsIsCompact :=
    by
      intro Ω instMeasurableSpace C hC
      exact
        boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isCompact
          C hC
  boundedMeasurableNaturalExtensionDominatingCompletionsIsConvex :=
    by
      intro Ω instMeasurableSpace C hC
      exact
        boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isConvex
          C hC
  boundedMeasurableNaturalExtensionPrevisionLeCompletion :=
    by
      intro Ω instMeasurableSpace C hC P hP X
      exact boundedMeasurableNaturalExtensionPrevision_le_completion C hC hP X
  boundedMeasurableNaturalExtensionPrevisionGreatestLowerBound :=
    by
      intro Ω instMeasurableSpace C hC L hL X
      exact
        boundedMeasurableNaturalExtensionPrevision_greatest_lower_bound
          C hC L hL X
  boundedMeasurableNaturalUpperEnvelopePrevisionCompletionLe :=
    by
      intro Ω instMeasurableSpace C hC P hP X
      exact
        boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
          C hC hP X
  boundedMeasurableNaturalUpperEnvelopePrevisionLeastUpperBound :=
    by
      intro Ω instMeasurableSpace C hC U hU X
      exact
        boundedMeasurableNaturalUpperEnvelopePrevision_least_upper_bound
          C hC U hU X
  finiteStrictlyPositiveUniformLowerBound :=
    by
      intro Ω instFintype instNonempty X hX
      exact LowerPrevision.finite_strictlyPositive_uniformLowerBound X hX
  finiteGambleUniformLowerBound :=
    by
      intro Ω instFintype instNonempty X
      exact finite_gamble_uniformLowerBound X
  finiteGambleUniformUpperBound :=
    by
      intro Ω instFintype instNonempty X
      exact finite_gamble_uniformUpperBound X
  finiteCredalRangeBddBelow :=
    by
      intro Ω instFintype instNonempty C X
      exact finite_credalRange_bddBelow C X
  finiteCredalRangeBddAbove :=
    by
      intro Ω instFintype instNonempty C X
      exact finite_credalRange_bddAbove C X
  lowerEnvelopeNegEqNegUpperEnvelope :=
    lowerEnvelope_neg_eq_neg_upperEnvelope
  upperEnvelopeNegEqNegLowerEnvelope :=
    upperEnvelope_neg_eq_neg_lowerEnvelope
  pmfToFiniteWeights :=
    PrecisePrevision.FiniteWeights.ofPMF
  pmfToPreciseCompletion :=
    PrecisePrevision.FiniteWeights.ofPMFPrevision
  pmfCompletionIsPrecise :=
    PrecisePrevision.FiniteWeights.ofPMFPrevision_precise
  finiteProbabilityMeasureToWeights :=
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasure
  finiteProbabilityMeasureToPreciseCompletion :=
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
  finiteProbabilityMeasureCompletionIsPrecise :=
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise
  lowerEnvelopeBuildsLowerPrevision :=
    lowerEnvelopePrevision
  upperEnvelopeBuildsUpperPrevision :=
    upperEnvelopePrevision
  finiteLowerEnvelopeBuildsLowerPrevision :=
    finiteLowerEnvelopePrevision
  finiteUpperEnvelopeBuildsUpperPrevision :=
    finiteUpperEnvelopePrevision
  lowerEnvelopePrevisionConjugateEqUpperEnvelope :=
    lowerEnvelopePrevision_conjugate_eq_upperEnvelope
  upperEnvelopePrevisionConjugateEqLowerEnvelope :=
    upperEnvelopePrevision_conjugate_eq_lowerEnvelope
  lowerEnvelopePrevisionLeCompletion :=
    lowerEnvelopePrevision_le_completion
  lowerEnvelopePrevisionGreatestLowerBound :=
    lowerEnvelopePrevision_greatest_lower_bound
  finiteLowerEnvelopePrevisionLeCompletion :=
    finiteLowerEnvelopePrevision_le_completion
  finiteLowerEnvelopePrevisionGreatestLowerBound :=
    finiteLowerEnvelopePrevision_greatest_lower_bound
  upperEnvelopePrevisionCompletionLe :=
    completion_le_upperEnvelopePrevision
  upperEnvelopePrevisionLeastUpperBound :=
    upperEnvelopePrevision_least_upper_bound
  finiteUpperEnvelopePrevisionCompletionLe :=
    finiteCompletion_le_upperEnvelopePrevision
  finiteUpperEnvelopePrevisionLeastUpperBound :=
    finiteUpperEnvelopePrevision_least_upper_bound
  finiteLowerEnvelopeAvoidsSureLoss :=
    lowerEnvelopePrevision_avoidsSureLoss_of_finite
  finiteLowerEnvelopeAvoidsSureLossAutomatic :=
    finiteLowerEnvelopePrevision_avoidsSureLoss
  finiteLowerEnvelopeIsCoherent :=
    lowerEnvelopePrevision_isCoherent_of_finite
  finiteLowerEnvelopeIsCoherentAutomatic :=
    finiteLowerEnvelopePrevision_isCoherent
  dominatingPreciseCompletionsBddBelow :=
    dominatingPreciseCompletions_bddBelow
  lowerPrevisionLeDominatingPreciseEnvelope :=
    lowerPrevision_le_lowerEnvelope_dominatingPreciseCompletions
  existsDominatingPreciseCompletionTouching :=
    exists_dominatingPreciseCompletion_touching
  lowerPrevisionHasExactDominatingPreciseEnvelope :=
    lowerPrevision_hasExactDominatingPreciseEnvelope
  dominatingPreciseCompletionsNonempty :=
    dominatingPreciseCompletions_nonempty
  lowerEnvelopeDominatingPreciseCompletionsEq :=
    lowerEnvelope_dominatingPreciseCompletions_eq
  lowerEnvelopePrevisionDominatingPreciseCompletionsEq :=
    lowerEnvelopePrevision_dominatingPreciseCompletions_eq
  lowerEnvelopePrevisionHasExactDominatingPreciseEnvelope :=
    lowerEnvelopePrevision_hasExactDominatingPreciseEnvelope
  finiteLowerEnvelopePrevisionHasExactDominatingPreciseEnvelope :=
    finiteLowerEnvelopePrevision_hasExactDominatingPreciseEnvelope
  coherentOfExactDominatingPreciseEnvelopeFinite :=
    isCoherent_of_hasExactDominatingPreciseEnvelope_finite
  lowerEnvelopeIsSuperadditive :=
    lowerEnvelope_superadditive
  lowerUpperEnvelopeNontrivialOfDisagreement :=
    lower_upperEnvelope_nontrivial_of_disagreement
  credalEnvelopeWidthNonnegative :=
    credalEnvelopeWidth_nonneg_of_nonempty
  credalSetDeterminesSingleton :=
    credalSetDetermines_singleton
  lowerUpperEnvelopeCollapseOfDetermines :=
    lower_eq_upperEnvelope_of_credalSetDetermines
  credalEnvelopeWidthZeroOfDetermines :=
    credalEnvelopeWidth_eq_zero_of_credalSetDetermines
  credalEnvelopeMidpointEqOfDetermines :=
    credalEnvelopeMidpoint_eq_of_credalSetDetermines
  lowerUpperEnvelopeNontrivialOfStrictWidth :=
    lower_upperEnvelope_nontrivial_of_strictWidth
  credalEnvelopeWidthPositiveOfStrictWidth :=
    credalEnvelopeWidth_pos_of_strictWidth
  credalEnvelopeWidthInUnitOfUnit :=
    credalEnvelopeWidth_in_unit_of_unit
  credalEnvelopeWidthComplementInUnitOfUnit :=
    credalEnvelopeWidthComplement_in_unit_of_unit
  credalEnvelopeMidpointInUnitOfUnit :=
    credalEnvelopeMidpoint_in_unit_of_unit
  strictWidthRefutesDetermination :=
    not_credalSetDetermines_of_strictWidth
  strictWidthIffNotDetermines :=
    credalSetHasStrictWidth_iff_not_determines
  boolDiracEnvelopeNontrivial :=
    boolDiracCredalEnvelope_nontrivial
  twoSpinMagnetEnvelopeNontrivial :=
    twoSpinMagnetEnvelope_nontrivial
  twoSpinZeroTemperatureMagnetEnvelopeNontrivial :=
    twoSpinZeroTemperatureMagnetEnvelope_nontrivial
  twoSpinZeroTemperatureAlignedCredalSetStrictWidth :=
    twoSpinZeroTemperatureAlignedCredalSet_hasStrictWidth
  identityCredalProjectiveSpecLimitSet :=
    identityCredalProjectiveSpec_projectiveLimitCredalSet
  identityCredalProjectiveSpecCompletionIff :=
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff
  identityCredalProjectiveSpecStrictWidthIff :=
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff
  projectiveStrictWidthIffNotDetermines :=
    @ProjectiveLocalCredalSpec.hasStrictGlobalWidth_iff_not_determinesGlobalGamble
  twoSpinZeroTemperatureAlignedProjectiveCompletion :=
    twoSpinZeroTemperatureAlignedProjectiveSpec_hasCompatibleCompletion
  twoSpinZeroTemperatureAlignedProjectiveStrictWidth :=
    twoSpinZeroTemperatureAlignedProjectiveSpec_hasStrictGlobalWidth
  twoSpinZeroTemperatureAlignedProjectiveEnvelopeNontrivial :=
    twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelope_nontrivial
  twoSpinZeroTemperatureAlignedProjectiveWidthPositive :=
    twoSpinZeroTemperatureAlignedProjectiveSpec_globalEnvelopeWidth_pos
  projectiveLimitNonemptyOfCompletion :=
    ProjectiveLocalCredalSpec.projectiveLimitCredalSet_nonempty_of_completion
  projectiveLimitNonemptyOfLocalDirac :=
    ProjectiveLocalCredalSpec.hasCompatibleCompletion_of_local_dirac
  projectiveLimitConvexOfLocalConvex :=
    ProjectiveLocalCredalSpec.projectiveLimitCredalSet_isConvex
  dominatingPreciseCompletionsConvex :=
    dominatingPreciseCompletions_isConvex
  projectiveLimitClosedOfClosedConstraints :=
    by
      intro Window Global instLE S instTop hClosed
      exact ProjectiveLocalCredalSpec.projectiveLimitCredalSet_isClosed S hClosed
  compactFIPLimitSetCompact :=
    by
      intro Window Global instLE S instTop K
      exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.limitSet_isCompact K
  compactFIPProducesCompatibleCompletion :=
    by
      intro Window Global instLE S instTop K
      exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.hasCompatibleCompletion K
  lowerPrevisionCompactFIPCompletion :=
    ProjectiveLocalLowerPrevisionSpec.hasCompatibleCompletion_of_finiteWindowCompatibleInCarrier
  boolFalseExactCompactFIPCompletion :=
    boolFalseExact_compactFIP_hasCompatibleCompletion
  boolUnrestrictedFiniteEvaluationCompactCompletion :=
    boolUnrestricted_finiteEvaluationCompact_hasCompatibleCompletion
  finiteUnrestrictedFiniteEvaluationCompactCompletion :=
    finiteUnrestricted_finiteEvaluationCompact_hasCompatibleCompletion
  singletonIdentityProjectiveSpecHasCompatibleCompletion :=
    singletonIdentityProjectiveSpec_hasCompatibleCompletion
  singletonIdentityProjectiveSpecLimitSet :=
    singletonIdentityProjectiveSpec_projectiveLimitCredalSet
  globalNaturalExtensionSuperadditive :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_superadditive
  globalNaturalExtensionPrevisionLeCompletion :=
    ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_le_completion
  globalNaturalExtensionPrevisionGreatestLowerBound :=
    ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_greatest_lower_bound
  globalUpperEnvelopeBuildsUpperPrevision :=
    ProjectiveLocalCredalSpec.globalUpperEnvelopePrevision
  globalUpperEnvelopePrevisionCompletionLe :=
    ProjectiveLocalCredalSpec.globalCompletion_le_upperEnvelopePrevision
  globalUpperEnvelopePrevisionLeastUpperBound :=
    ProjectiveLocalCredalSpec.globalUpperEnvelopePrevision_least_upper_bound
  globalNaturalExtensionConjugateEqUpperEnvelope :=
    ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
  globalUpperEnvelopeConjugateEqNaturalExtension :=
    ProjectiveLocalCredalSpec.globalUpperEnvelopePrevision_conjugate_eq_naturalExtension
  finiteGlobalNaturalExtensionPrevisionLeCompletion :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_le_completion
  finiteGlobalNaturalExtensionPrevisionGreatestLowerBound :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_greatest_lower_bound
  finiteGlobalUpperEnvelopeBuildsUpperPrevision :=
    ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision
  finiteGlobalUpperEnvelopePrevisionCompletionLe :=
    ProjectiveLocalCredalSpec.finiteGlobalCompletion_le_upperEnvelopePrevision
  finiteGlobalUpperEnvelopePrevisionLeastUpperBound :=
    ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision_least_upper_bound
  finiteGlobalNaturalExtensionConjugateEqUpperEnvelope :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_conjugate_eq_upperEnvelope
  finiteGlobalUpperEnvelopeConjugateEqNaturalExtension :=
    ProjectiveLocalCredalSpec.finiteGlobalUpperEnvelopePrevision_conjugate_eq_naturalExtension
  globalEnvelopeWidthNonnegative :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_nonneg_of_nonempty
  globalNaturalExtensionEqOfDetermines :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_eq_of_determines
  globalEnvelopeWidthZeroOfDetermines :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_eq_zero_of_determines
  globalEnvelopeMidpointEqOfDetermines :=
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint_eq_of_determines
  globalLowerUpperEnvelopeCollapseOfDetermines :=
    ProjectiveLocalCredalSpec.globalLowerUpperEnvelope_eq_of_determines
  globalLowerUpperEnvelopeNontrivialOfStrictWidth :=
    ProjectiveLocalCredalSpec.globalLowerUpperEnvelope_nontrivial_of_strictWidth
  globalEnvelopeWidthPositiveOfStrictWidth :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_pos_of_strictWidth
  globalEnvelopeWidthInUnitOfUnit :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_in_unit_of_unit
  globalEnvelopeWidthComplementInUnitOfUnit :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement_in_unit_of_unit
  globalEnvelopeMidpointInUnitOfUnit :=
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint_in_unit_of_unit
  finiteGlobalEnvelopeWidthInUnitOfUnit :=
    ProjectiveLocalCredalSpec.finiteGlobalEnvelopeWidth_in_unit_of_unit
  finiteGlobalEnvelopeWidthComplementInUnitOfUnit :=
    ProjectiveLocalCredalSpec.finiteGlobalEnvelopeWidthComplement_in_unit_of_unit
  finiteGlobalEnvelopeMidpointInUnitOfUnit :=
    ProjectiveLocalCredalSpec.finiteGlobalEnvelopeMidpoint_in_unit_of_unit
  globalNaturalExtensionAvoidsWeakSureLoss :=
    ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_avoidsWeakSureLoss
  globalNaturalExtensionHasExactDominatingPreciseEnvelope :=
    ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
  finiteGlobalNaturalExtensionBuildsLowerPrevision :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision
  finiteGlobalNaturalExtensionAvoidsSureLoss :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_avoidsSureLoss
  finiteGlobalNaturalExtensionIsCoherent :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_isCoherent
  finiteGlobalNaturalExtensionHasExactDominatingPreciseEnvelope :=
    ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
  cylinderLocalCredalSet :=
    ProjectiveLocalCredalSpec.cylinderLocalCredalSet
  cylinderLocalCredalSetNonempty :=
    ProjectiveLocalCredalSpec.cylinderLocalCredalSet_nonempty
  cylinderNaturalExtensionBuildsLowerPrevision :=
    ProjectiveLocalCredalSpec.cylinderNaturalExtensionPrevision
  cylinderNaturalExtensionAvoidsUniformSureLoss :=
    ProjectiveLocalCredalSpec.cylinderNaturalExtensionPrevision_avoidsUniformSureLoss
  cylinderNaturalExtensionHasExactDominatingPreciseEnvelope :=
    ProjectiveLocalCredalSpec.cylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
  finiteCylinderNaturalExtensionBuildsLowerPrevision :=
    ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision
  finiteCylinderNaturalExtensionAvoidsSureLoss :=
    ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_avoidsSureLoss
  finiteCylinderNaturalExtensionIsCoherent :=
    ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_isCoherent
  finiteCylinderNaturalExtensionHasExactDominatingPreciseEnvelope :=
    ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
  cylinderWeakSureLoss :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_avoidsWeakSureLoss
  cylinderUniformSureLoss :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_avoidsUniformSureLoss
  cylinderUpperEnvelopeLeLocalUpperEnvelope :=
    ProjectiveLocalCredalSpec.globalUpperEnvelope_le_localUpperEnvelope_on_cylinder
  cylinderDeterminationExact :=
    ProjectiveLocalCredalSpec.determinesGlobalGamble_cylinder_iff_localCredal_determines_of_exact
  cylinderStrictWidthExact :=
    ProjectiveLocalCredalSpec.hasStrictGlobalWidth_cylinder_iff_localCredal_strictWidth_of_exact
  cylinderNaturalExtensionExact :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
  cylinderUpperEnvelopeExact :=
    ProjectiveLocalCredalSpec.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
  cylinderEnvelopeWidthExact :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact
  cylinderEnvelopeWidthComplementExact :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact
  cylinderEnvelopeMidpointExact :=
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact
  finiteCylinderNaturalExtensionExact :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact_finite
  finiteCylinderUpperEnvelopeExact :=
    ProjectiveLocalCredalSpec.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact_finite
  finiteCylinderEnvelopeWidthExact :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_cylinder_eq_localEnvelopeWidth_of_exact_finite
  finiteCylinderEnvelopeWidthComplementExact :=
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement_cylinder_eq_localEnvelopeWidthComplement_of_exact_finite
  finiteCylinderEnvelopeMidpointExact :=
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint_cylinder_eq_localEnvelopeMidpoint_of_exact_finite
  singletonCompletionCollapsesEnvelope :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_singleton

end Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
