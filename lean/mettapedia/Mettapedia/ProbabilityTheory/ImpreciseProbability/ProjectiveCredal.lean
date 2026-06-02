import Mettapedia.ProbabilityTheory.ImpreciseProbability.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Pointwise
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Compactness.Compact
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
open Mettapedia.ProbabilityTheory.ImpreciseProbability

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
        rw [Pi.smul_apply, smul_eq_mul]
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
        rw [Pi.add_apply]
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

end FiniteWeights

end PrecisePrevision

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

theorem IsConvex.inter {C D : CredalPrevisionSet Ω}
    (hC : IsConvex C) (hD : IsConvex D) :
    IsConvex (C ∩ D) := by
  intro P hP Q hQ t ht0 ht1
  exact ⟨hC hP.1 hQ.1 t ht0 ht1, hD hP.2 hQ.2 t ht0 ht1⟩

end CredalPrevisionSet

/-- The lower envelope of a credal set: Walley's conservative forced value. -/
noncomputable def lowerEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  sInf ((fun P : PrecisePrevision Ω => P X) '' C)

/-- The upper envelope, dual to the lower envelope. -/
noncomputable def upperEnvelope {Ω : Type*}
    (C : CredalPrevisionSet Ω) (X : Gamble Ω) : ℝ :=
  sSup ((fun P : PrecisePrevision Ω => P X) '' C)

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

/-! ## Projective cylinder systems -/

/-- A projective cylinder system: finite/local windows have local state spaces,
and every local window has a projection from the global state.

The `restrict` and `project_restrict` fields are the local-to-local
compatibility square. -/
structure ProjectiveCylinderSystem (Window Global : Type*) [LE Window] where
  Local : Window → Type*
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

end ProjectiveCylinderSystem

/-! ## Projective-limit credal sets and natural extension -/

/-- Local credal data over a projective cylinder system. -/
structure ProjectiveLocalCredalSpec (Window Global : Type*) [LE Window] where
  cylinders : ProjectiveCylinderSystem Window Global
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

/-- Local lower envelope at one window. -/
noncomputable def localNaturalExtension
    (S : ProjectiveLocalCredalSpec Window Global)
    (i : Window) : Gamble (S.cylinders.Local i) → ℝ :=
  lowerEnvelope (S.localCredal i)

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

/-- A local credal set is exact at window `i` when every local precise
completion lifts to a compatible global completion with the same marginal. -/
def localCredalExactAt
    (S : ProjectiveLocalCredalSpec Window Global) (i : Window) : Prop :=
  ∀ R : PrecisePrevision (S.cylinders.Local i), R ∈ S.localCredal i →
    ∃ P : PrecisePrevision Global,
      P ∈ S.projectiveLimitCredalSet ∧ S.cylinders.marginalPrevision i P = R

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

/-! ## Profile surface -/

/-- Proof-carrying profile for the shared projective credal abstraction.

This packages the reusable spine without claiming the full compactness-based
inverse-limit existence theorem. -/
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
  pmfToFiniteWeights :
    ∀ {Ω : Type*} [Fintype Ω],
      PMF Ω → PrecisePrevision.FiniteWeights Ω
  pmfToPreciseCompletion :
    ∀ {Ω : Type*} [Fintype Ω], PMF Ω → PrecisePrevision Ω
  pmfCompletionIsPrecise :
    ∀ {Ω : Type*} [Fintype Ω] (p : PMF Ω),
      (PrecisePrevision.FiniteWeights.ofPMFPrevision p).toLowerPrevision.isPrecise
  lowerEnvelopeBuildsLowerPrevision :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C)),
      LowerPrevision Ω
  lowerEnvelopeIsSuperadditive :
    ∀ {Ω : Type*} (C : CredalPrevisionSet Ω)
      (_hC : C.Nonempty)
      (_hBdd : ∀ X : Gamble Ω,
        BddBelow ((fun P : PrecisePrevision Ω => P X) '' C))
      (X Y : Gamble Ω),
      lowerEnvelope C X + lowerEnvelope C Y ≤ lowerEnvelope C (X + Y)
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
  compactFIPProducesCompatibleCompletion :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      [TopologicalSpace (PrecisePrevision Global)]
      (_K : ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem S),
      S.hasCompatibleCompletion
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
  globalNaturalExtensionAvoidsWeakSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (_hNonempty : S.hasCompatibleCompletion)
      (_hBdd : ∀ X : Gamble Global,
        BddBelow ((fun P : PrecisePrevision Global => P X) ''
          S.projectiveLimitCredalSet)),
      (S.globalNaturalExtensionPrevision _hNonempty _hBdd).avoidsWeakSureLoss
  cylinderWeakSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global),
      S.hasCompatibleCompletion → S.cylinderGamblesAvoidWeakSureLoss
  cylinderUniformSureLoss :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global),
      S.hasCompatibleCompletion → S.cylinderGamblesAvoidUniformSureLoss
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
  singletonCompletionCollapsesEnvelope :
    ∀ {Window Global : Type*} [LE Window]
      (S : ProjectiveLocalCredalSpec Window Global)
      (P : PrecisePrevision Global)
      (_hEq : S.projectiveLimitCredalSet = ({P} : CredalPrevisionSet Global))
      (X : Gamble Global),
      S.globalNaturalExtension X = P X

/-- The current sorry-free shared projective credal profile. -/
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
  pmfToFiniteWeights :=
    PrecisePrevision.FiniteWeights.ofPMF
  pmfToPreciseCompletion :=
    PrecisePrevision.FiniteWeights.ofPMFPrevision
  pmfCompletionIsPrecise :=
    PrecisePrevision.FiniteWeights.ofPMFPrevision_precise
  lowerEnvelopeBuildsLowerPrevision :=
    lowerEnvelopePrevision
  lowerEnvelopeIsSuperadditive :=
    lowerEnvelope_superadditive
  projectiveLimitNonemptyOfCompletion :=
    ProjectiveLocalCredalSpec.projectiveLimitCredalSet_nonempty_of_completion
  projectiveLimitNonemptyOfLocalDirac :=
    ProjectiveLocalCredalSpec.hasCompatibleCompletion_of_local_dirac
  projectiveLimitConvexOfLocalConvex :=
    ProjectiveLocalCredalSpec.projectiveLimitCredalSet_isConvex
  compactFIPProducesCompatibleCompletion :=
    by
      intro Window Global instLE S instTop K
      exact ProjectiveLocalCredalSpec.CompactConvexProjectiveCredalSystem.hasCompatibleCompletion K
  globalNaturalExtensionSuperadditive :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_superadditive
  globalNaturalExtensionAvoidsWeakSureLoss :=
    ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_avoidsWeakSureLoss
  cylinderWeakSureLoss :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_avoidsWeakSureLoss
  cylinderUniformSureLoss :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_avoidsUniformSureLoss
  cylinderNaturalExtensionExact :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
  singletonCompletionCollapsesEnvelope :=
    ProjectiveLocalCredalSpec.globalNaturalExtension_singleton

end Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
