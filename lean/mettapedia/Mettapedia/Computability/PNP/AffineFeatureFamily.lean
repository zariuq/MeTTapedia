import Mettapedia.Computability.PNP.AffineColumnFamily
import Mathlib.Data.Fintype.EquivFin

/-!
# P vs NP grassroots: bounded affine-feature predictors on the VV column view

This file extends the one-feature affine column family to a small composite
class:

* choose `r` affine GF(2)-style features of the retained VV column bits `a`,
* evaluate those `r` features to obtain a Boolean vector in `BitVec r`,
* apply an arbitrary truth table on those `r` feature bits.

The resulting family is still explicitly encodable.  Its raw bit budget is

`r * (k + 1) + 2^r`.

So any switched family that collapses to `r` affine VV-column features inherits
this budget automatically.
-/

namespace Mettapedia.Computability.PNP

section

variable {r k : ℕ}

/-- One bounded affine-feature code: `r` affine GF(2)-style features together
with a truth table on the resulting `r` feature bits. -/
abbrev AffineFeatureCode (r k : ℕ) :=
  (Fin r → AffineColumnCode k) × BitCode (2 ^ r)

/-- Evaluate the chosen affine features on one VV column vector `a`. -/
def affineFeatureVector (features : Fin r → AffineColumnCode k) (a : BitVec k) : BitVec r :=
  fun j => affineColumnPredict (features j).1 (features j).2 a

/-- Evaluate the bounded affine-feature predictor on one VV column vector `a`. -/
noncomputable def affineFeaturePredict (code : AffineFeatureCode r k) (a : BitVec k) : Bool :=
  code.2 ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec r) = 2 ^ r))
    (affineFeatureVector code.1 a))

theorem card_affineColumnCode (k : ℕ) :
    Fintype.card (AffineColumnCode k) = 2 ^ (k + 1) := by
  simp [AffineColumnCode, BitVec, Nat.pow_add, Nat.mul_comm]

theorem card_affineFeatureCode (r k : ℕ) :
    Fintype.card (AffineFeatureCode r k) = 2 ^ (r * (k + 1) + 2 ^ r) := by
  calc
    Fintype.card (AffineFeatureCode r k)
      = Fintype.card (Fin r → AffineColumnCode k) * Fintype.card (BitCode (2 ^ r)) := by
          simp [AffineFeatureCode]
    _ = (Fintype.card (AffineColumnCode k)) ^ r * 2 ^ (2 ^ r) := by
          simp
    _ = (2 ^ (k + 1)) ^ r * 2 ^ (2 ^ r) := by
          rw [card_affineColumnCode]
    _ = 2 ^ ((k + 1) * r) * 2 ^ (2 ^ r) := by
          rw [← Nat.pow_mul]
    _ = 2 ^ (r * (k + 1)) * 2 ^ (2 ^ r) := by
          simp [Nat.mul_comm]
    _ = 2 ^ (r * (k + 1) + 2 ^ r) := by
          rw [← Nat.pow_add]

/-- Noncomputably collapse the structured affine-feature code type to one raw
bit code of the corresponding size. -/
noncomputable def affineFeatureCodeEquivBitCode (r k : ℕ) :
    AffineFeatureCode r k ≃ BitCode (r * (k + 1) + 2 ^ r) := by
  apply Fintype.equivOfCardEq
  rw [card_affineFeatureCode, card_bitCode]

/-- The indexed family whose members are exactly the bounded affine-feature
predictors on the VV column view. -/
noncomputable def affineFeatureIndexedFamily (r k : ℕ) :
    IndexedPredictorFamily (AffineFeatureCode r k) (BitVec k) where
  predict code a := affineFeaturePredict code a

/-- The corresponding raw-bit encoded family. -/
noncomputable def affineFeatureBitFamily (r k : ℕ) :
    BitEncodedClassifierFamily (BitVec k) (r * (k + 1) + 2 ^ r) where
  decode raw a := affineFeaturePredict ((affineFeatureCodeEquivBitCode r k).symm raw) a

theorem affineFeatureIndexedFamily_hasBitBudget (r k : ℕ) :
    (affineFeatureIndexedFamily r k).HasBitBudget (r * (k + 1) + 2 ^ r) := by
  refine ⟨affineFeatureBitFamily r k, ?_⟩
  intro code
  refine ⟨affineFeatureCodeEquivBitCode r k code, ?_⟩
  funext a
  change affineFeaturePredict ((affineFeatureCodeEquivBitCode r k).symm
      (affineFeatureCodeEquivBitCode r k code)) a
      = affineFeaturePredict code a
  simp

/-- Any indexed family realized by bounded affine-feature predictors on one
column-view map inherits the same explicit bit budget. -/
def RealizedByAffineFeatureFamily
    {Index : Type*} {Input : Type*} (view : Input → BitVec k)
    (G : IndexedPredictorFamily Index Input) : Prop :=
  ∀ i, ∃ code : AffineFeatureCode r k, G.predict i = fun x => affineFeaturePredict code (view x)

theorem hasBitBudget_of_realizedByAffineFeatureFamily
    {Index : Type*} {Input : Type*} {view : Input → BitVec k}
    {G : IndexedPredictorFamily Index Input}
    (hreal : RealizedByAffineFeatureFamily (r := r) (k := k) view G) :
    G.HasBitBudget (r * (k + 1) + 2 ^ r) := by
  refine ⟨IndexedPredictorFamily.pullbackBitFamily view (affineFeatureBitFamily r k), ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨affineFeatureCodeEquivBitCode r k code, ?_⟩
  funext x
  calc
    (IndexedPredictorFamily.pullbackBitFamily view (affineFeatureBitFamily r k)).decode
        (affineFeatureCodeEquivBitCode r k code) x
      = affineFeaturePredict code (view x) := by
          simp [IndexedPredictorFamily.pullbackBitFamily, affineFeatureBitFamily]
    _ = G.predict i x := by
          exact (congrFun hi x).symm

/-- Exact post-switch specialization: the switched family depends only on a
bounded affine-feature summary of the retained VV column bits. -/
abbrev RealizedByExactAffineFeatureFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByAffineFeatureFamily (r := r) (k := k)
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a) G

theorem exactVisibleCompressionTarget_of_realizedByExactAffineFeatureFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal : RealizedByExactAffineFeatureFamily (r := r) (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (r * (k + 1) + 2 ^ r) := by
  exact hasBitBudget_of_realizedByAffineFeatureFamily (r := r) (k := k) hreal

end

end Mettapedia.Computability.PNP
