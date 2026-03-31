import Mettapedia.Computability.PNP.BitVecZABVisibleSurface
import Mettapedia.Computability.PNP.CanonicalZABERMInterface

/-!
# P vs NP grassroots: the canonical exact ERM route when `z` is already bit-valued

This file specializes the final exact `z+a+b` ERM interface to the concrete case
`Z = BitVec r` and `zfeat = id`.

So the remaining burden is now phrased on the raw full visible bit surface
itself: one sample assignment, one equality to the ERM wrapper, and one
agreement bound.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {r k : ℕ} {Index : Type*}

/-- The identity extractor on bit-valued latent data. -/
abbrev identityZExtractor : BitVec r → BitVec r := fun z => z

/-- The exact ERM-selected family on the full raw visible bit surface
`(z, a, b)`. -/
noncomputable def bitVecZABDecisionListERMFamily
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ExactVisibleSwitchedFamily (BitVec r) k Index :=
  exactZABDecisionListERMFamily
    (Z := BitVec r) (r := r) (k := k) identityZExtractor samples

@[simp] theorem bitVecZABDecisionListERMFamily_eq
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    bitVecZABDecisionListERMFamily (r := r) (k := k) samples =
      exactZABDecisionListERMFamily
        (Z := BitVec r) (r := r) (k := k) identityZExtractor samples := by
  rfl

structure BitVecZABERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k))
    (G : ExactVisibleSwitchedFamily (BitVec r) k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool
  exact_family : G = bitVecZABDecisionListERMFamily (r := r) (k := k) samples
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily (BitVec r) r k identityZExtractor).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily (BitVec r) r k identityZExtractor).decode c.1) ≤ q

section

def BitVecZABERMRecoveryData.canonicalData
    [Fintype (BitVec r)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h : BitVecZABERMRecoveryData (r := r) (k := k) (Index := Index) μ G q) :
    CanonicalZABERMRecoveryData
      (Z := BitVec r) (r := r) (k := k) (Index := Index)
      μ identityZExtractor G q := by
  refine ⟨h.samples, ?_, h.agreement_le⟩
  simpa [bitVecZABDecisionListERMFamily, identityZExtractor] using h.exact_family

theorem BitVecZABERMRecoveryData.compressionTarget
    [Fintype (BitVec r)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h : BitVecZABERMRecoveryData (r := r) (k := k) (Index := Index) μ G q) :
    ExactVisibleCompressionTarget
      (Z := BitVec r) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact (h.canonicalData).compressionTarget

theorem BitVecZABERMRecoveryData.recoveryLowerBound
    [Fintype (BitVec r)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec r) k)}
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    {q : ℝ≥0∞}
    (h : BitVecZABERMRecoveryData (r := r) (k := k) (Index := Index) μ G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily (BitVec r) r k identityZExtractor).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact (h.canonicalData).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
