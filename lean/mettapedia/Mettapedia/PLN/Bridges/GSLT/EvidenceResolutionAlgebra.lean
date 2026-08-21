import Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout
import Mathlib.Data.Complex.Basic

/-!
# PLN evidence as a resolution algebra: the layered lock-in

A *resolution algebra* (Meredith, graded where-clauses; F1R3FLY fuzzyware and
the rho-mind omnibus) is a commutative semiring of grades together with the
branch-enabling convention: `0` disables, joint conditions multiply,
alternative routes add.  This file settles, at theorem level, in exactly what
sense PLN binary evidence participates:

* **The grade algebra holds.**  `BinaryEvidence` with revision as addition and
  the evidence tensor as multiplication is a genuine `CommSemiring` (the
  instance below bundles laws already proved piecewise in the evidence and
  revision modules).  In these sufficient-statistics coordinates revision is
  associative, commutative, unital, distributive — and *not* idempotent
  (`revision_not_idempotent`).  An idempotent account therefore describes a
  lossy projection (for example strength alone), provenance deduplication, or
  a different fusion operation; an invertible change to (strength, confidence)
  coordinates cannot change this law.

* **The naive support convention is impossible, not merely awkward.**
  Opposite-polarity packets are zero divisors
  (`counter_tensor_positive_eq_zero`), so *no* support predicate with the
  classical laws can read "enabled" as "nonzero pair"
  (`no_naive_evidence_support`).

* **The repair is canonical.**  The positive-count projection is a semiring
  homomorphism (`posHom`, every field `rfl`), and supports pull back along
  semiring homomorphisms (`ResolutionSupport.comap`).  The polarity-aware
  support (`evidenceSupport`) is that pullback: enabled iff positive evidence
  is nonzero.  Pure counterevidence no longer enables a branch.

* **The scalar readout supplies grades, never state.**  `propensity` is not
  additive under revision (`propensity_not_additive`); combined with the
  collision and separation theorems of `EvidenceCostReadout`, the pair is the
  revisable state and every scalar is a declared, lossy view.

* **The classical support laws delimit the non-quantum regime.**  Over any
  nontrivial commutative ring — complex amplitudes included — no classical
  resolution support exists (`no_ring_resolution_support`): destructive
  cancellation (`1 + (-1) = 0`) violates the law that an alternative can never
  disable an enabled branch.  Zerosumfreeness is the formal boundary between
  the additive-evidence regime and the interference regime.

What this file deliberately does **not** claim: that all of PLN inference
(deduction, induction, abduction) is one semiring, or that revision-as-`+` is
sound without provenance — the independence side-condition is formalized
separately by the stamped-witness bridge, which authorizes additive revision
exactly for pairwise-disjoint evidence stamps.

The `CommSemiring` instance lives here (a leaf module) pending adoption into
the core evidence module, so no existing typeclass resolution changes.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
open Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
open Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout
open Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization

noncomputable section

/-! ## The resolution-support interface -/

/-- A branch-enabling discipline over a commutative semiring of grades, in the
classical (positive) reading: zero disables, the unit is neutral and enabled,
a joint condition is enabled exactly when both factors are, and adding an
alternative route can never disable an enabled branch. -/
structure ResolutionSupport (V : Type*) [CommSemiring V] where
  Enabled : V → Prop
  not_enabled_zero : ¬ Enabled 0
  enabled_one : Enabled 1
  enabled_mul_iff : ∀ a b : V, Enabled (a * b) ↔ Enabled a ∧ Enabled b
  enabled_add_left : ∀ a b : V, Enabled a → Enabled (a + b)

/-- The standard nonnegative grade support: enabled iff nonzero.  This is the
fuzzy/Gillespie regime's convention, and it is lawful on `ℝ≥0∞` because the
carrier has no zero divisors and no additive inverses. -/
def nonnegSupport : ResolutionSupport ℝ≥0∞ where
  Enabled v := v ≠ 0
  not_enabled_zero := by simp
  enabled_one := one_ne_zero
  enabled_mul_iff a b := by
    constructor
    · intro h
      exact ⟨fun ha => h (by simp [ha]), fun hb => h (by simp [hb])⟩
    · rintro ⟨ha, hb⟩ h
      rcases mul_eq_zero.mp h with h' | h'
      · exact ha h'
      · exact hb h'
  enabled_add_left a b ha := by
    intro h
    exact ha (add_eq_zero.mp h).1

/-- Supports pull back along semiring homomorphisms.  This is the canonical
way to give a rich carrier a lawful support: project to a positive algebra
first. -/
def ResolutionSupport.comap {R V : Type*} [CommSemiring R] [CommSemiring V]
    (S : ResolutionSupport V) (f : R →+* V) : ResolutionSupport R where
  Enabled r := S.Enabled (f r)
  not_enabled_zero := by
    rw [map_zero]
    exact S.not_enabled_zero
  enabled_one := by
    rw [map_one]
    exact S.enabled_one
  enabled_mul_iff a b := by
    rw [map_mul]
    exact S.enabled_mul_iff _ _
  enabled_add_left a b h := by
    rw [map_add]
    exact S.enabled_add_left _ _ h

/-- Over any nontrivial commutative ring there is NO classical resolution
support: additive inverses let an alternative cancel an enabled branch,
violating `enabled_add_left`.  Complex amplitudes are the intended instance:
destructive interference is precisely the failure of zerosumfreeness, and
this is the formal boundary between the evidence regime and the quantum
regime. -/
theorem no_ring_resolution_support (R : Type*) [CommRing R] :
    IsEmpty (ResolutionSupport R) := by
  constructor
  intro S
  have h := S.enabled_add_left 1 (-1) S.enabled_one
  rw [add_neg_cancel] at h
  exact S.not_enabled_zero h

/-- The amplitude carrier ℂ admits no classical support. -/
example : IsEmpty (ResolutionSupport ℂ) := no_ring_resolution_support ℂ

/-! ## The evidence grade algebra -/

/-- The crown instance: PLN binary evidence with revision as addition and the
evidence tensor as multiplication is a commutative semiring.  All component
laws were already proved in the evidence and revision modules; this bundles
them into the interface a graded where-clause consumes. -/
instance : CommSemiring BinaryEvidence where
  __ := (inferInstance : CommMonoid BinaryEvidence)
  __ := (inferInstance : AddCommMonoid BinaryEvidence)
  left_distrib := fun a b c => tensor_distrib_revision_right a b c
  right_distrib := fun a b c => tensor_distrib_revision a b c
  zero_mul := fun a => by
    ext
    · simp [BinaryEvidence.tensor_def]
    · simp [BinaryEvidence.tensor_def]
  mul_zero := fun a => by
    ext
    · simp [BinaryEvidence.tensor_def]
    · simp [BinaryEvidence.tensor_def]

/-- Revision is NOT idempotent: revising with the same packet again raises
the counts (confidence grows; only the strength projection can appear fixed).
An idempotent operation must therefore be a projection, a provenance-aware
deduplication, or a different fusion operation—not the same revision merely
written in another invertible coordinate chart. -/
theorem revision_not_idempotent : ∃ e : BinaryEvidence, e + e ≠ e := by
  refine ⟨⟨1, 0⟩, ?_⟩
  intro h
  have hpos := congrArg BinaryEvidence.pos h
  simp only [BinaryEvidence.hplus_def] at hpos
  have : (2 : ℝ≥0∞) = 1 := by
    calc (2 : ℝ≥0∞) = 1 + 1 := by norm_num
    _ = 1 := hpos
  norm_num at this

/-! ## Zero divisors and the impossibility of naive support -/

/-- A packet of pure counterevidence. -/
def pureCounterEvidence : BinaryEvidence := ⟨0, 1⟩

/-- A packet of pure positive evidence. -/
def purePositiveEvidence : BinaryEvidence := ⟨1, 0⟩

theorem pureCounterEvidence_ne_zero : pureCounterEvidence ≠ 0 := by
  intro h
  have := congrArg BinaryEvidence.neg h
  simp [pureCounterEvidence] at this

theorem purePositiveEvidence_ne_zero : purePositiveEvidence ≠ 0 := by
  intro h
  have := congrArg BinaryEvidence.pos h
  simp [purePositiveEvidence] at this

/-- Opposite-polarity packets are zero divisors: each is nonzero, their
tensor is the zero evidence. -/
theorem counter_tensor_positive_eq_zero :
    pureCounterEvidence * purePositiveEvidence = 0 := by
  ext
  · simp [BinaryEvidence.tensor_def, pureCounterEvidence, purePositiveEvidence]
  · simp [BinaryEvidence.tensor_def, pureCounterEvidence, purePositiveEvidence]

/-- The naive convention "enabled iff the pair is nonzero" admits no lawful
support on binary evidence at all: the zero divisors above make two enabled
grades whose joint condition is disabled, contradicting `enabled_mul_iff`.
Support over the pair must therefore be polarity-aware. -/
theorem no_naive_evidence_support :
    ¬ ∃ S : ResolutionSupport BinaryEvidence, ∀ v, S.Enabled v ↔ v ≠ 0 := by
  rintro ⟨S, hchar⟩
  have hc : S.Enabled pureCounterEvidence :=
    (hchar _).mpr pureCounterEvidence_ne_zero
  have hp : S.Enabled purePositiveEvidence :=
    (hchar _).mpr purePositiveEvidence_ne_zero
  have hprod : S.Enabled (pureCounterEvidence * purePositiveEvidence) :=
    (S.enabled_mul_iff _ _).mpr ⟨hc, hp⟩
  rw [counter_tensor_positive_eq_zero] at hprod
  exact (hchar 0).mp hprod rfl

/-! ## The canonical polarity repair -/

/-- The positive-count projection is a semiring homomorphism — every field
holds by `rfl`, because both operations are coordinatewise and both units
have positive coordinate the respective unit. -/
def posHom : BinaryEvidence →+* ℝ≥0∞ where
  toFun e := e.pos
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- THE evidence support: the pullback of the standard nonnegative support
along the positive-count homomorphism.  A branch is enabled exactly when its
positive evidence is nonzero. -/
def evidenceSupport : ResolutionSupport BinaryEvidence :=
  nonnegSupport.comap posHom

theorem evidenceSupport_enabled_iff (e : BinaryEvidence) :
    evidenceSupport.Enabled e ↔ e.pos ≠ 0 :=
  Iff.rfl

/-- Positive control: genuine positive evidence enables its branch. -/
theorem purePositiveEvidence_enabled :
    evidenceSupport.Enabled purePositiveEvidence := by
  rw [evidenceSupport_enabled_iff]
  simp [purePositiveEvidence]

/-- Negative control: pure counterevidence — nonzero as a pair — does not
enable a branch under the polarity-aware support.  This is the misfire of the
naive convention, repaired. -/
theorem pureCounterEvidence_not_enabled :
    ¬ evidenceSupport.Enabled pureCounterEvidence := by
  rw [evidenceSupport_enabled_iff]
  simp [pureCounterEvidence]

/-! ## The readout layer: grades are views, the pair is the state -/

/-- The scalar propensity readout is not additive under revision: revising two
identical packets does not add their propensities (`2/3 ≠ 1`).  So propensity
supplies grades to the nonnegative resolution algebra as a *valuation*, not a
homomorphism; with the collision and separation theorems of
`EvidenceCostReadout`, the evidence pair is the revisable state and the scalar
is a declared lossy view of it. -/
theorem propensity_not_additive :
    propensity 1 (concentratedEvidence + concentratedEvidence) ≠
      propensity 1 concentratedEvidence + propensity 1 concentratedEvidence := by
  have hsum : concentratedEvidence + concentratedEvidence =
      (⟨2, 0⟩ : BinaryEvidence) := by
    ext
    · simp only [BinaryEvidence.hplus_def, concentratedEvidence]
      norm_num
    · simp [BinaryEvidence.hplus_def, concentratedEvidence]
  rw [hsum]
  intro equal
  have realEqual := congrArg ENNReal.toReal equal
  norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
    BinaryEvidence.total, concentratedEvidence, ENNReal.toReal_div,
    ENNReal.toReal_add] at realEqual

/-! ## The layered lock-in, as one statement -/

/-- The complete layering in a single theorem, for citation: (i) the grade
algebra distributes (the semiring instance is real); (ii) revision is not
idempotent; (iii) naive nonzero-support is impossible on the pair; (iv) the
polarity support reads positive evidence; (v) the scalar readout is not a
homomorphism.  Each conjunct is proved above; this bundle exists so the
architectural claim has one name. -/
theorem evidence_resolution_layering :
    (∀ a b c : BinaryEvidence, a * (b + c) = a * b + a * c) ∧
    (∃ e : BinaryEvidence, e + e ≠ e) ∧
    (¬ ∃ S : ResolutionSupport BinaryEvidence, ∀ v, S.Enabled v ↔ v ≠ 0) ∧
    (∀ e : BinaryEvidence, evidenceSupport.Enabled e ↔ e.pos ≠ 0) ∧
    (propensity 1 (concentratedEvidence + concentratedEvidence) ≠
      propensity 1 concentratedEvidence + propensity 1 concentratedEvidence) :=
  ⟨mul_add, revision_not_idempotent, no_naive_evidence_support,
    evidenceSupport_enabled_iff, propensity_not_additive⟩

end

end Mettapedia.PLN.Bridges.GSLT.EvidenceResolutionAlgebra
