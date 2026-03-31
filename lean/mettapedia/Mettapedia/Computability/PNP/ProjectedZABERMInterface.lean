import Mettapedia.Computability.PNP.CanonicalZABERMInterface

/-!
# P vs NP grassroots: exact ERM routes from projected bit-valued local data

This file specializes the final exact `z+a+b` ERM interface to a concrete class
of local extractors: coordinate projections out of a bit-valued local datum
`z : BitVec n`.

So the remaining extractor burden is reduced from “arbitrary `zfeat`” to “pick a
finite list of coordinates of `z`”.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

/-- Extract `r` visible summary bits from a bit-valued local datum by fixed
coordinate selection. -/
def projectedZExtractor
    (coords : Fin r → Fin n) : BitVec n → BitVec r :=
  fun z i => z (coords i)

@[simp] theorem projectedZExtractor_apply
    (coords : Fin r → Fin n) (z : BitVec n) (i : Fin r) :
    projectedZExtractor (n := n) (r := r) coords z i = z (coords i) := rfl

structure ProjectedZABERMRecoveryData
    [Fintype (BitVec n)]
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (coords : Fin r → Fin n)
    (G : ExactVisibleSwitchedFamily (BitVec n) k Index)
    (q : ℝ≥0∞) where
  samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool
  exact_family :
    G = exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k)
          (projectedZExtractor (n := n) (r := r) coords) samples
  agreement_le :
    ∀ i,
      ∀ c :
        (rawExactZABDecisionListBitFamily
          (BitVec n) r k (projectedZExtractor (n := n) (r := r) coords)).toEncodedFamily.BadCodes
            (G.predict i),
        agreementMass μ (G.predict i)
          ((rawExactZABDecisionListBitFamily
            (BitVec n) r k (projectedZExtractor (n := n) (r := r) coords)).decode c.1) ≤ q

section

variable [Fintype (BitVec n)]

def ProjectedZABERMRecoveryData.canonicalData
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    CanonicalZABERMRecoveryData
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      μ (projectedZExtractor (n := n) (r := r) coords) G q := by
  refine ⟨h.samples, h.exact_family, h.agreement_le⟩

theorem ProjectedZABERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q) :
    ExactVisibleCompressionTarget
      (Z := BitVec n) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  exact (h.canonicalData).compressionTarget

theorem ProjectedZABERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {coords : Fin r → Fin n}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h : ProjectedZABERMRecoveryData
      (n := n) (r := r) (k := k) (Index := Index) μ coords G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 2 * k + 1) : ℝ≥0∞) * q ^ m ≤
      (rawExactZABDecisionListBitFamily
        (BitVec n) r k (projectedZExtractor (n := n) (r := r) coords)).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact (h.canonicalData).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
