import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Data.Real.Pointwise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.Basic

/-!
# Imprecise Probability: Coherent Lower Previsions

This module formalizes Walley's theory of coherent lower previsions, which
provides a framework for imprecise probabilities.

## Main Definitions

* `Gamble Ω` - real-valued functions on outcome space Ω (often assumed bounded)
* `LowerPrevision Ω` - superlinear functional on gambles (lower expectation)
* `UpperPrevision Ω` - sublinear functional on gambles (upper expectation)
* `LowerPrevision.conjugate` - the dual upper prevision
* `LowerPrevision.isPrecise` - when lower = upper (standard probability)
* `LowerPrevision.avoidsSureLoss` - Walley's no-arbitrage condition

## Main Results

* `LowerPrevision.conjugate_conjugate` - double conjugate equals original
* `LowerPrevision.precise_iff_additive` - precision ↔ additivity
* `LowerPrevision.mono` - monotonicity from Walley A1/A3
* `UpperPrevision.subadditive` - upper previsions are subadditive

## Mathematical Background

A **coherent lower prevision** P̲ satisfies:
1. P̲(X + Y) ≥ P̲(X) + P̲(Y)  (superadditivity)
2. P̲(λX) = λ · P̲(X) for λ ≥ 0  (positive homogeneity)
3. inf X ≤ P̲(X) ≤ sup X  (bounds)

The **conjugate upper prevision** is P̅(X) = -P̲(-X).

For standard probability, P̲ = P̅ (the prevision is additive).
For imprecise probability, P̲ < P̅ in general.

## Key Insight for K&S Comparison

Imprecise probabilities do NOT satisfy commutativity in general:
- Fubini's theorem fails for non-additive measures
- Iterated lower expectations depend on order: P̲[P̲[X|Y]] ≠ P̲[P̅[X|Y]]

This makes coherent lower previsions WEAKER than standard probability.
If K&S truly derives standard probability, it must derive commutativity.

## References

* [Walley, *Statistical Reasoning with Imprecise Probabilities*][walley1991]
* [Walley, *Towards a Unified Theory of Imprecise Probability*][walley1999]
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability

/-!
## Gambles: The Domain of Previsions

A gamble is a real-valued function on the outcome space (often assumed bounded).
We define the vector space structure on gambles.
-/

/-- A gamble is a real-valued function on some outcome space Ω (often assumed bounded). -/
def Gamble (Ω : Type*) := Ω → ℝ

namespace Gamble

variable {Ω : Type*}

instance : Zero (Gamble Ω) := ⟨fun _ => 0⟩
instance : Add (Gamble Ω) := ⟨fun X Y ω => X ω + Y ω⟩
instance : Neg (Gamble Ω) := ⟨fun X ω => -X ω⟩
instance : Sub (Gamble Ω) := ⟨fun X Y ω => X ω - Y ω⟩
instance : SMul ℝ (Gamble Ω) := ⟨fun r X ω => r * X ω⟩

instance : AddCommGroup (Gamble Ω) where
  add_assoc X Y Z := funext fun ω => add_assoc (X ω) (Y ω) (Z ω)
  zero_add X := funext fun ω => zero_add (X ω)
  add_zero X := funext fun ω => add_zero (X ω)
  add_comm X Y := funext fun ω => add_comm (X ω) (Y ω)
  neg_add_cancel X := funext fun ω => neg_add_cancel (X ω)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (Gamble Ω) where
  smul_add r X Y := funext fun ω => mul_add r (X ω) (Y ω)
  add_smul r s X := funext fun ω => add_mul r s (X ω)
  mul_smul r s X := funext fun ω => mul_assoc r s (X ω)
  one_smul X := funext fun ω => one_mul (X ω)
  zero_smul X := funext fun ω => zero_mul (X ω)
  smul_zero r := funext fun _ => mul_zero r

/-- Pointwise order on gambles. -/
instance : LE (Gamble Ω) := ⟨fun X Y => ∀ ω, X ω ≤ Y ω⟩

instance : Preorder (Gamble Ω) where
  le_refl X ω := le_refl (X ω)
  le_trans X Y Z hXY hYZ ω := le_trans (hXY ω) (hYZ ω)

/-- A constant gamble that always returns c. -/
def const (c : ℝ) : Gamble Ω := fun _ => c

@[simp]
lemma const_apply (c : ℝ) (ω : Ω) : const c ω = c := rfl

@[simp]
lemma const_zero : const (0 : ℝ) = (0 : Gamble Ω) := rfl

@[simp]
lemma const_add (a b : ℝ) : const (a + b) = const a + (const b : Gamble Ω) :=
  funext fun _ => rfl

@[simp]
lemma const_smul (r c : ℝ) : const (r * c) = r • (const c : Gamble Ω) :=
  funext fun _ => rfl

lemma le_const_iff {X : Gamble Ω} {c : ℝ} : X ≤ const c ↔ ∀ ω, X ω ≤ c := Iff.rfl

lemma const_le_iff {X : Gamble Ω} {c : ℝ} : const c ≤ X ↔ ∀ ω, c ≤ X ω := Iff.rfl

end Gamble

/-!
## Lower Previsions

A lower prevision is a superlinear functional on gambles.
This is the foundational structure of imprecise probability.
-/

/-- A lower prevision is a coherent superlinear functional on gambles.
    This follows Walley's axioms A1-A3 from his 1999 unified theory paper. -/
structure LowerPrevision (Ω : Type*) where
  /-- The lower prevision functional -/
  toFun : Gamble Ω → ℝ
  /-- A1 (Lower bound): P(X) ≥ c for any c that lower-bounds X pointwise.
      This is Walley's key axiom: inf X ≤ P(X). -/
  lower_bound : ∀ (X : Gamble Ω) (c : ℝ), (∀ ω, c ≤ X ω) → c ≤ toFun X
  /-- A2 (Positive homogeneity): P(λX) = λ·P(X) for λ ≥ 0 -/
  pos_homog : ∀ (r : ℝ) (X : Gamble Ω), 0 ≤ r → toFun (r • X) = r * toFun X
  /-- A3 (Superadditivity): P(X + Y) ≥ P(X) + P(Y) -/
  superadd : ∀ (X Y : Gamble Ω), toFun (X + Y) ≥ toFun X + toFun Y

namespace LowerPrevision

variable {Ω : Type*}

instance : CoeFun (LowerPrevision Ω) (fun _ => Gamble Ω → ℝ) := ⟨toFun⟩

@[ext]
lemma ext {P Q : LowerPrevision Ω} (h : ∀ X, P X = Q X) : P = Q := by
  cases P; cases Q; simp only [mk.injEq]; ext X; exact h X

@[simp]
lemma coe_mk (f : Gamble Ω → ℝ) (h₀ h₁ h₂) : (mk f h₀ h₁ h₂ : Gamble Ω → ℝ) = f := rfl

/-!
### Basic Properties
-/

/-- P(0) = 0 for any lower prevision. -/
@[simp]
lemma map_zero (P : LowerPrevision Ω) : P 0 = 0 := by
  have h := P.pos_homog 0 0 (le_refl 0)
  simp only [zero_smul, zero_mul] at h
  exact h

/-- Scaling by positive reals. -/
lemma map_smul_of_nonneg (P : LowerPrevision Ω) {r : ℝ} (hr : 0 ≤ r) (X : Gamble Ω) :
    P (r • X) = r * P X :=
  P.pos_homog r X hr

/-- Non-negative gambles have non-negative prevision.
    This is a direct consequence of Walley's A1 axiom. -/
lemma nonneg_of_nonneg (P : LowerPrevision Ω) {X : Gamble Ω} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ P X :=
  P.lower_bound X 0 h

/-- Monotonicity: if X ≤ Y pointwise, then P(X) ≤ P(Y).
    This follows from superadditivity and the lower bound axiom. -/
lemma mono (P : LowerPrevision Ω) {X Y : Gamble Ω} (h : X ≤ Y) : P X ≤ P Y := by
  -- Y = X + (Y - X), and Y - X ≥ 0
  have hYX : Y = X + (Y - X) := by funext _; simp
  rw [hYX]
  have hsup := P.superadd X (Y - X)
  -- P(Y - X) ≥ 0 since Y - X ≥ 0 pointwise
  have hnonneg : 0 ≤ P (Y - X) := P.nonneg_of_nonneg (fun ω => sub_nonneg.mpr (h ω))
  linarith

/-- The conjugate (dual) upper prevision. -/
def conjugate (P : LowerPrevision Ω) : Gamble Ω → ℝ :=
  fun X => -P (-X)

@[simp]
lemma conjugate_neg (P : LowerPrevision Ω) (X : Gamble Ω) :
    P.conjugate (-X) = -P X := by
  simp only [conjugate, neg_neg]

/-- The conjugate is subadditive (upper bound on addition). -/
lemma conjugate_subadditive (P : LowerPrevision Ω) (X Y : Gamble Ω) :
    P.conjugate (X + Y) ≤ P.conjugate X + P.conjugate Y := by
  simp only [conjugate, neg_add_rev] at *
  have h := P.superadd (-Y) (-X)
  linarith

/-- A lower prevision is always pointwise below its conjugate upper prevision. -/
lemma le_conjugate (P : LowerPrevision Ω) (X : Gamble Ω) :
    P X ≤ P.conjugate X := by
  have h := P.superadd X (-X)
  have hzero : X + -X = (0 : Gamble Ω) := by
    simp
  rw [hzero, P.map_zero] at h
  simp only [conjugate]
  linarith

/-- The conjugate upper prevision is positively homogeneous for nonnegative
scalars. -/
lemma conjugate_pos_homog_of_nonneg (P : LowerPrevision Ω)
    {r : ℝ} (hr : 0 ≤ r) (X : Gamble Ω) :
    P.conjugate (r • X) = r * P.conjugate X := by
  dsimp [conjugate]
  have hneg : -(r • X) = r • (-X : Gamble Ω) := by
    funext ω
    change -(r * X ω) = r * (-X ω)
    ring
  rw [hneg, P.pos_homog r (-X) hr]
  ring

/-- For nonpositive scalars, the conjugate of a scaled gamble is governed by
the lower prevision of the unscaled gamble. -/
lemma conjugate_smul_of_nonpos (P : LowerPrevision Ω)
    {r : ℝ} (hr : r ≤ 0) (X : Gamble Ω) :
    P.conjugate (r • X) = r * P X := by
  dsimp [conjugate]
  have hneg : -(r • X) = (-r) • X := by
    funext ω
    change -(r * X ω) = (-r) * X ω
    ring
  rw [hneg, P.pos_homog (-r) X (by linarith)]
  ring

/-- Double conjugate returns to original. -/
lemma conjugate_conjugate (P : LowerPrevision Ω) (X : Gamble Ω) :
    -(-P (-(-X))) = P X := by
  simp

/-!
### Precision (Standard Probability)
-/

/-- A lower prevision is **precise** if it equals its conjugate.
    This is equivalent to additivity (standard probability). -/
def isPrecise (P : LowerPrevision Ω) : Prop :=
  ∀ X, P X = P.conjugate X

/-- Precision is equivalent to additivity. -/
lemma precise_iff_additive (P : LowerPrevision Ω) :
    P.isPrecise ↔ ∀ X Y, P (X + Y) = P X + P Y := by
  constructor
  · intro hprec X Y
    -- If P = conjugate, then superadd becomes equality
    have hsup := P.superadd X Y
    have hsub := P.conjugate_subadditive X Y
    rw [← hprec X, ← hprec Y, ← hprec (X + Y)] at hsub
    linarith
  · intro hadd X
    -- If additive, P(-X) = -P(X), so conjugate = P
    have h0 : P 0 = P (X + (-X)) := by simp
    rw [hadd X (-X)] at h0
    simp at h0
    simp only [conjugate]
    linarith

/-!
### Avoiding Sure Loss
-/

/-- Walley's avoiding sure loss condition.
    A gamble that is strictly positive everywhere should have positive prevision. -/
def avoidsSureLoss (P : LowerPrevision Ω) : Prop :=
  ∀ (X : Gamble Ω), (∀ ω, X ω > 0) → P X > 0

/-- Equivalent: non-negative gambles have non-negative prevision. -/
def avoidsWeakSureLoss (P : LowerPrevision Ω) : Prop :=
  ∀ (X : Gamble Ω), (∀ ω, X ω ≥ 0) → P X ≥ 0

/-- Uniform strict no-sure-loss.  On infinite spaces, pointwise strict
positivity need not provide a positive lower bound; this property records the
regularity that *uniformly* positive gambles receive strictly positive
prevision. -/
def avoidsUniformSureLoss (P : LowerPrevision Ω) : Prop :=
  ∀ (X : Gamble Ω), (∃ ε : ℝ, 0 < ε ∧ ∀ ω, ε ≤ X ω) → P X > 0

/-!
## Counterexample: A1–A3 do not imply strict positivity

Troffaes’ standard counterexample: on an infinite outcome space, the functional

`P(X) := inf_ω X(ω)`

satisfies Walley’s axioms A1–A3 but does **not** satisfy the “strictly positive gambles have
strictly positive prevision” property.
-/

/-! Note: The infimum lower prevision for infinite Ω is formalized in
`Seminorm.lean` using `sInf` (set infimum) rather than `iInf` (indexed infimum),
since ℝ is conditionally complete but not a complete lattice.

The key result (`coherence_does_not_imply_regularity`) shows that a lower
prevision satisfying A1-A3 can still assign zero to strictly positive gambles. -/

/-!
### Coherence

A lower prevision is coherent if it's the lower envelope of some
credal set (convex set of probability measures).

The main characterization: P is coherent iff it avoids sure loss
and satisfies certain convexity properties.
-/

/-- A lower prevision is coherent if it satisfies Walley's coherence axioms. -/
def isCoherent (P : LowerPrevision Ω) : Prop :=
  P.avoidsSureLoss ∧
  -- Coherent combination: for all finite combinations with positive coefficients
  ∀ (X Y : Gamble Ω) (a b : ℝ), 0 < a → 0 < b →
    P (a • X + b • Y) ≥ a * P X + b * P Y

/-- The combination half of `isCoherent` is already forced by the
`LowerPrevision` structure: positive homogeneity plus superadditivity gives the
finite positive-linear lower bound. -/
lemma coherent_combination (P : LowerPrevision Ω)
    (X Y : Gamble Ω) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    P (a • X + b • Y) ≥ a * P X + b * P Y := by
  have hsuper := P.superadd (a • X) (b • Y)
  rw [P.pos_homog a X (le_of_lt ha),
    P.pos_homog b Y (le_of_lt hb)] at hsuper
  exact hsuper

/-- For this bundled Walley lower-prevision structure, coherence reduces to
strict avoiding-sure-loss: the superlinear algebraic axioms are already fields of
`LowerPrevision`. -/
lemma isCoherent_iff_avoidsSureLoss (P : LowerPrevision Ω) :
    P.isCoherent ↔ P.avoidsSureLoss := by
  constructor
  · exact fun h => h.1
  · intro hAvoid
    exact ⟨hAvoid, P.coherent_combination⟩

/-- A lower prevision satisfying strict avoiding sure loss is coherent in this
bundled Walley sense. -/
lemma isCoherent_of_avoidsSureLoss (P : LowerPrevision Ω)
    (hAvoid : P.avoidsSureLoss) : P.isCoherent :=
  (P.isCoherent_iff_avoidsSureLoss).2 hAvoid

/-- All coherent lower previsions avoid weak sure loss.
    This follows directly from the A1 axiom (lower bound property). -/
lemma avoidsWeakSureLoss_of_lower_bound (P : LowerPrevision Ω) : P.avoidsWeakSureLoss :=
  fun _X hX => P.nonneg_of_nonneg hX

/-- Walley's lower-bound axiom gives the uniform strict version of avoiding
sure loss.  This is the infinite-domain safe replacement for claiming
pointwise strict positivity always has positive lower expectation. -/
lemma avoidsUniformSureLoss_of_lower_bound (P : LowerPrevision Ω) :
    P.avoidsUniformSureLoss := by
  intro X hX
  rcases hX with ⟨ε, hεpos, hε⟩
  exact lt_of_lt_of_le hεpos (P.lower_bound X ε hε)

/-- On a finite nonempty state space, every pointwise-strictly-positive gamble
has a uniform positive lower bound.  This is the finite bridge from Walley's
uniform no-sure-loss condition to pointwise strict avoiding-sure-loss. -/
theorem finite_strictlyPositive_uniformLowerBound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Gamble Ω) (hX : ∀ ω, 0 < X ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ω, ε ≤ X ω := by
  classical
  let values : Finset ℝ := Finset.univ.image X
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  have hvalues : values.Nonempty := by
    refine ⟨X ω₀, ?_⟩
    exact Finset.mem_image.mpr ⟨ω₀, Finset.mem_univ ω₀, rfl⟩
  let ε : ℝ := values.min' hvalues
  refine ⟨ε, ?_, ?_⟩
  · have hεmem : ε ∈ values := Finset.min'_mem values hvalues
    rcases Finset.mem_image.mp hεmem with ⟨ω, _hω, hω⟩
    simpa [hω] using hX ω
  · intro ω
    exact Finset.min'_le values (X ω)
      (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩)

/-- Finite nonempty lower previsions avoid Walley's strict sure loss.  The
finiteness hypothesis is essential: strict pointwise positivity becomes a
uniform positive lower bound. -/
theorem avoidsSureLoss_of_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) : P.avoidsSureLoss := by
  intro X hX
  rcases finite_strictlyPositive_uniformLowerBound X hX with ⟨ε, hεpos, hε⟩
  exact lt_of_lt_of_le hεpos (P.lower_bound X ε hε)

/-- On finite nonempty state spaces, pointwise strict avoiding-sure-loss and
uniform avoiding-sure-loss coincide.  This is the finite/infinite boundary:
only the reverse implication needs finiteness. -/
theorem avoidsSureLoss_iff_avoidsUniformSureLoss_of_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) :
    P.avoidsSureLoss ↔ P.avoidsUniformSureLoss := by
  constructor
  · intro hAvoid X hUniform
    rcases hUniform with ⟨ε, hεpos, hε⟩
    exact hAvoid X (fun ω => lt_of_lt_of_le hεpos (hε ω))
  · intro hUniform X hX
    exact hUniform X (finite_strictlyPositive_uniformLowerBound X hX)

/-- Every finite nonempty bundled lower prevision is coherent in this Walley
interface: the algebraic coherence laws are structure fields, and finite
strict positivity supplies strict avoiding sure loss. -/
theorem isCoherent_of_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : LowerPrevision Ω) : P.isCoherent :=
  P.isCoherent_of_avoidsSureLoss P.avoidsSureLoss_of_finite

/-- Coherent previsions avoid weak sure loss. -/
lemma isCoherent.avoidsWeakSureLoss (P : LowerPrevision Ω) (_hP : P.isCoherent) :
    P.avoidsWeakSureLoss :=
  P.avoidsWeakSureLoss_of_lower_bound

/-- Coherent previsions also avoid uniform sure loss. -/
lemma isCoherent.avoidsUniformSureLoss (P : LowerPrevision Ω) (_hP : P.isCoherent) :
    P.avoidsUniformSureLoss :=
  P.avoidsUniformSureLoss_of_lower_bound

end LowerPrevision

/-!
## Upper Previsions

The dual structure: sublinear functionals.
-/

/-- An upper prevision is a coherent sublinear functional on gambles.
    This follows the dual of Walley's axioms. -/
structure UpperPrevision (Ω : Type*) where
  /-- The upper prevision functional -/
  toFun : Gamble Ω → ℝ
  /-- Upper bound: P(X) ≤ c for any c that upper-bounds X pointwise.
      This is the dual of Walley's A1: P(X) ≤ sup X. -/
  upper_bound : ∀ (X : Gamble Ω) (c : ℝ), (∀ ω, X ω ≤ c) → toFun X ≤ c
  /-- Positive homogeneity -/
  pos_homog : ∀ (r : ℝ) (X : Gamble Ω), 0 ≤ r → toFun (r • X) = r * toFun X
  /-- Subadditivity (upper bound) -/
  subadditive : ∀ (X Y : Gamble Ω), toFun (X + Y) ≤ toFun X + toFun Y

namespace UpperPrevision

variable {Ω : Type*}

instance : CoeFun (UpperPrevision Ω) (fun _ => Gamble Ω → ℝ) := ⟨toFun⟩

/-- The conjugate lower prevision. -/
def conjugate (P : UpperPrevision Ω) : Gamble Ω → ℝ :=
  fun X => -P (-X)

/-- The conjugate is superadditive. -/
lemma conjugate_superadditive (P : UpperPrevision Ω) (X Y : Gamble Ω) :
    P.conjugate (X + Y) ≥ P.conjugate X + P.conjugate Y := by
  simp only [conjugate, ge_iff_le, neg_add_rev]
  have h := P.subadditive (-Y) (-X)
  linarith

/-- Construct a LowerPrevision from an UpperPrevision via conjugation. -/
def toLower (P : UpperPrevision Ω) : LowerPrevision Ω where
  toFun := P.conjugate
  lower_bound := by
    intro X c hc
    simp only [conjugate]
    -- If c ≤ X(ω) for all ω, then -X(ω) ≤ -c for all ω
    -- So P(-X) ≤ -c by upper_bound, hence -P(-X) ≥ c
    have hbound : ∀ ω, (-X) ω ≤ -c := fun ω => neg_le_neg (hc ω)
    have h := P.upper_bound (-X) (-c) hbound
    linarith
  pos_homog := by
    intro r X hr
    simp only [conjugate]
    have h := P.pos_homog r (-X) hr
    simp only [smul_neg] at h
    rw [h]
    ring
  superadd := P.conjugate_superadditive

end UpperPrevision

/-!
## The Imprecision Gap

The difference between upper and lower prevision measures imprecision.
-/

/-- The imprecision of a gamble X under prevision P. -/
def imprecision {Ω : Type*} (P : LowerPrevision Ω) (X : Gamble Ω) : ℝ :=
  P.conjugate X - P X

/-- Imprecision is always non-negative (follows directly from superadditivity). -/
lemma imprecision_nonneg {Ω : Type*} (P : LowerPrevision Ω) (X : Gamble Ω) :
    0 ≤ imprecision P X := by
  simp only [imprecision, LowerPrevision.conjugate]
  -- Need: -P(-X) ≥ P(X), i.e., P(X) + P(-X) ≤ 0
  -- This follows from superadditivity: P(X + (-X)) = P(0) = 0 ≥ P(X) + P(-X)
  have h := P.superadd X (-X)
  simp at h
  linarith

/-- Zero imprecision characterizes precision. -/
lemma imprecision_zero_iff_precise {Ω : Type*} (P : LowerPrevision Ω) :
    (∀ X, imprecision P X = 0) ↔ P.isPrecise := by
  simp only [imprecision, LowerPrevision.isPrecise, sub_eq_zero]
  constructor <;> (intro h X; specialize h X; linarith)

/-!
## Summary: Imprecise Probability in the K&S Context

Standard probability (precise previsions) satisfies:
- Additivity: P(X + Y) = P(X) + P(Y)
- Commutativity of iterated expectations (Fubini)

Imprecise probability (coherent lower previsions) only satisfies:
- Superadditivity: P(X + Y) ≥ P(X) + P(Y)
- NO commutativity in general

This places imprecise probability BELOW standard probability in expressive power.
If K&S derives standard probability, it must derive additivity and commutativity.
If K&S only gives superadditivity, it's equivalent to imprecise probability.
-/

end Mettapedia.ProbabilityTheory.ImpreciseProbability
