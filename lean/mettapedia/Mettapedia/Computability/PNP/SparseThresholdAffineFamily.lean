import Mettapedia.Computability.PNP.AffineFeatureFamily
import Mathlib.Data.Fintype.EquivFin

/-!
# P vs NP grassroots: sparse-threshold affine-feature predictors on the VV view

This file improves on the raw affine-feature family by replacing the arbitrary
truth-table combiner with a much smaller one:

* choose `r` affine GF(2)-style features of the retained VV column bits `a`,
* choose a Boolean mask selecting which of those features are active,
* choose an `r`-bit threshold code,
* predict `true` iff at least that many active features fire.

The exact raw budget is now linear:

`r * (k + 3)`.

So if the switched predictors collapse to a sparse-threshold algebra on the VV
column view, the optimistic route gets a genuinely smaller encoded class than
the full `2^r` truth-table combiner from `AffineFeatureFamily.lean`.
-/

namespace Mettapedia.Computability.PNP

section

variable {r k : ℕ}

/-- One sparse-threshold affine-feature code:
`r` affine GF(2)-style features, an `r`-bit activity mask, and an `r`-bit
threshold code. -/
abbrev SparseThresholdAffineCode (r k : ℕ) :=
  (Fin r → AffineColumnCode k) × BitCode r × BitCode r

/-- Decode the threshold code as a natural in `[0, 2^r)`. -/
noncomputable def thresholdCodeValue (threshold : BitCode r) : ℕ :=
  ((Fintype.equivFinOfCardEq (by
      simp [BitCode] : Fintype.card (BitCode r) = 2 ^ r)) threshold).1

/-- Count how many masked affine features fire on the VV column view `a`. -/
def maskedAffineFeatureCount
    (features : Fin r → AffineColumnCode k) (mask : BitCode r) (a : BitVec k) : ℕ :=
  ((Finset.univ : Finset (Fin r)).filter fun j => mask j && affineFeatureVector features a j).card

/-- Evaluate the sparse-threshold affine-feature predictor on one VV column
vector `a`. -/
noncomputable def sparseThresholdAffinePredict
    (code : SparseThresholdAffineCode r k) (a : BitVec k) : Bool :=
  decide (thresholdCodeValue (r := r) code.2.2 ≤
    maskedAffineFeatureCount (k := k) code.1 code.2.1 a)

theorem card_sparseThresholdAffineCode (r k : ℕ) :
    Fintype.card (SparseThresholdAffineCode r k) = 2 ^ (r * (k + 3)) := by
  calc
    Fintype.card (SparseThresholdAffineCode r k)
      = Fintype.card (Fin r → AffineColumnCode k) *
          (Fintype.card (BitCode r) * Fintype.card (BitCode r)) := by
            simp [SparseThresholdAffineCode]
    _ = (Fintype.card (AffineColumnCode k)) ^ r * (2 ^ r * 2 ^ r) := by
          simp
    _ = (2 ^ (k + 1)) ^ r * (2 ^ r * 2 ^ r) := by
          rw [card_affineColumnCode]
    _ = 2 ^ ((k + 1) * r) * (2 ^ r * 2 ^ r) := by
          rw [← Nat.pow_mul]
    _ = 2 ^ (r * (k + 1)) * (2 ^ r * 2 ^ r) := by
          simp [Nat.mul_comm]
    _ = (2 ^ (r * (k + 1)) * 2 ^ r) * 2 ^ r := by
          rw [Nat.mul_assoc]
    _ = 2 ^ (r * (k + 1) + r) * 2 ^ r := by
          rw [← Nat.pow_add]
    _ = 2 ^ (r * (k + 1) + r + r) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (r * (k + 3)) := by
          have hexp : r * (k + 1) + r + r = r * (k + 3) := by
            calc
              r * (k + 1) + r + r = r * (k + 1) + (r + r) := by
                simp [Nat.add_assoc]
              _ = r * (k + 1) + r * 2 := by
                have hrr : r + r = r * 2 := by
                  simpa [Nat.mul_comm] using (two_mul r).symm
                rw [hrr]
              _ = r * ((k + 1) + 2) := by
                rw [← Nat.mul_add]
              _ = r * (k + 3) := by
                simp [Nat.add_assoc]
          rw [hexp]

/-- Noncomputably collapse the sparse-threshold structured code type to one raw
bit code of the corresponding size. -/
noncomputable def sparseThresholdAffineCodeEquivBitCode (r k : ℕ) :
    SparseThresholdAffineCode r k ≃ BitCode (r * (k + 3)) := by
  apply Fintype.equivOfCardEq
  rw [card_sparseThresholdAffineCode, card_bitCode]

/-- The indexed family whose members are exactly the sparse-threshold affine
predictors on the VV column view. -/
noncomputable def sparseThresholdAffineIndexedFamily (r k : ℕ) :
    IndexedPredictorFamily (SparseThresholdAffineCode r k) (BitVec k) where
  predict code a := sparseThresholdAffinePredict code a

/-- The corresponding raw-bit encoded family. -/
noncomputable def sparseThresholdAffineBitFamily (r k : ℕ) :
    BitEncodedClassifierFamily (BitVec k) (r * (k + 3)) where
  decode raw a := sparseThresholdAffinePredict
    ((sparseThresholdAffineCodeEquivBitCode r k).symm raw) a

theorem sparseThresholdAffineIndexedFamily_hasBitBudget (r k : ℕ) :
    (sparseThresholdAffineIndexedFamily r k).HasBitBudget (r * (k + 3)) := by
  refine ⟨sparseThresholdAffineBitFamily r k, ?_⟩
  intro code
  refine ⟨sparseThresholdAffineCodeEquivBitCode r k code, ?_⟩
  funext a
  change sparseThresholdAffinePredict
      ((sparseThresholdAffineCodeEquivBitCode r k).symm
        (sparseThresholdAffineCodeEquivBitCode r k code)) a
      = sparseThresholdAffinePredict code a
  simp

/-- Any indexed family realized by sparse-threshold affine predictors on one
column-view map inherits the same explicit bit budget. -/
def RealizedBySparseThresholdAffineFamily
    {Index : Type*} {Input : Type*} (view : Input → BitVec k)
    (G : IndexedPredictorFamily Index Input) : Prop :=
  ∀ i, ∃ code : SparseThresholdAffineCode r k,
    G.predict i = fun x => sparseThresholdAffinePredict code (view x)

theorem hasBitBudget_of_realizedBySparseThresholdAffineFamily
    {Index : Type*} {Input : Type*} {view : Input → BitVec k}
    {G : IndexedPredictorFamily Index Input}
    (hreal : RealizedBySparseThresholdAffineFamily (r := r) (k := k) view G) :
    G.HasBitBudget (r * (k + 3)) := by
  refine ⟨IndexedPredictorFamily.pullbackBitFamily view
    (sparseThresholdAffineBitFamily r k), ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sparseThresholdAffineCodeEquivBitCode r k code, ?_⟩
  funext x
  calc
    (IndexedPredictorFamily.pullbackBitFamily view
        (sparseThresholdAffineBitFamily r k)).decode
        (sparseThresholdAffineCodeEquivBitCode r k code) x
      = sparseThresholdAffinePredict code (view x) := by
          simp [IndexedPredictorFamily.pullbackBitFamily, sparseThresholdAffineBitFamily]
    _ = G.predict i x := by
          exact (congrFun hi x).symm

/-- Exact post-switch specialization: the switched family depends only on a
sparse-threshold affine summary of the retained VV column bits. -/
abbrev RealizedByExactSparseThresholdAffineFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedBySparseThresholdAffineFamily (r := r) (k := k)
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a) G

theorem exactVisibleCompressionTarget_of_realizedByExactSparseThresholdAffineFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactSparseThresholdAffineFamily (r := r) (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (r * (k + 3)) := by
  exact hasBitBudget_of_realizedBySparseThresholdAffineFamily (r := r) (k := k) hreal

end

end Mettapedia.Computability.PNP
