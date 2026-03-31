import Mettapedia.Computability.PNP.ExactSwitchedFamily
import Mathlib.Data.Finset.Card

/-!
# P vs NP grassroots: affine GF(2)-style predictors on the VV column view

This file adds one concrete optimistic subclass on top of the exact switched
family framework.  It does **not** prove that the manuscript's switched
predictors land in this class.  It proves the next conditional:

* if the switched predictors collapse to affine parity tests on the retained VV
  column bits `a`,
* then the whole family is encoded by `k + 1` bits.

So a real algebraic rescue can now target a specific small class rather than the
full Boolean rule space on the post-switch surface.
-/

namespace Mettapedia.Computability.PNP

section

variable {k : ℕ}

/-- One affine GF(2)-style predictor on `k` visible column bits consists of a
coefficient vector and a bias bit. -/
abbrev AffineColumnCode (k : ℕ) := BitVec k × Bool

/-- Parity of the support intersection of `coeff` and `a`. -/
def columnParity (coeff a : BitVec k) : Bool :=
  decide <| Odd (((Finset.univ : Finset (Fin k)).filter fun i => coeff i && a i).card)

/-- Affine GF(2)-style prediction on the retained VV column bits. -/
def affineColumnPredict (coeff : BitVec k) (bias : Bool) (a : BitVec k) : Bool :=
  Bool.xor (columnParity coeff a) bias

/-- Encode affine coefficients and bias into `k + 1` raw bits. -/
def encodeAffineColumnIndex (idx : AffineColumnCode k) : BitCode (k + 1) :=
  fun j =>
    if h : j.1 < k then idx.1 ⟨j.1, h⟩ else idx.2

/-- Decode the coefficient vector from `k + 1` raw bits. -/
def decodeAffineColumnCoeffs (code : BitCode (k + 1)) : BitVec k :=
  fun i => code ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self k)⟩

/-- Decode the bias bit from `k + 1` raw bits. -/
def decodeAffineColumnBias (code : BitCode (k + 1)) : Bool :=
  code ⟨k, Nat.lt_succ_self k⟩

@[simp] theorem decodeAffineColumnCoeffs_encodeAffineColumnIndex
    (idx : AffineColumnCode k) :
    decodeAffineColumnCoeffs (encodeAffineColumnIndex idx) = idx.1 := by
  funext i
  dsimp [decodeAffineColumnCoeffs, encodeAffineColumnIndex]
  split_ifs with h
  · rfl
  · exact False.elim (h i.isLt)

@[simp] theorem decodeAffineColumnBias_encodeAffineColumnIndex
    (idx : AffineColumnCode k) :
    decodeAffineColumnBias (encodeAffineColumnIndex idx) = idx.2 := by
  dsimp [decodeAffineColumnBias, encodeAffineColumnIndex]
  split_ifs with h
  · exact False.elim ((Nat.lt_irrefl k) h)
  · rfl

/-- The concrete `k + 1`-bit family of affine GF(2)-style predictors on
`BitVec k`. -/
def affineColumnBitFamily (k : ℕ) : BitEncodedClassifierFamily (BitVec k) (k + 1) where
  decode code a :=
    affineColumnPredict (decodeAffineColumnCoeffs code) (decodeAffineColumnBias code) a

@[simp] theorem affineColumnBitFamily_decode_encodeAffineColumnIndex
    (idx : AffineColumnCode k) :
    (affineColumnBitFamily k).decode (encodeAffineColumnIndex idx)
      = affineColumnPredict idx.1 idx.2 := by
  funext a
  simp [affineColumnBitFamily, affineColumnPredict]

/-- The indexed family whose members are exactly the affine GF(2)-style
predictors on the VV column view. -/
def affineColumnIndexedFamily (k : ℕ) :
    IndexedPredictorFamily (AffineColumnCode k) (BitVec k) where
  predict idx a := affineColumnPredict idx.1 idx.2 a

/-- Any indexed family realized by affine GF(2)-style column predictors has the
explicit bit budget `k + 1`. -/
def RealizedByColumnViewAffineFamily
    {Index : Type*} {Input : Type*} (view : Input → BitVec k)
    (G : IndexedPredictorFamily Index Input) : Prop :=
  ∀ i, ∃ coeff bias, G.predict i = fun x => affineColumnPredict coeff bias (view x)

theorem affineColumnIndexedFamily_hasBitBudget (k : ℕ) :
    (affineColumnIndexedFamily k).HasBitBudget (k + 1) := by
  refine ⟨affineColumnBitFamily k, ?_⟩
  intro idx
  refine ⟨encodeAffineColumnIndex idx, ?_⟩
  exact affineColumnBitFamily_decode_encodeAffineColumnIndex idx

/-- Pulling back the affine column family along any visible-data map preserves
the same `k + 1` bit budget. -/
theorem hasBitBudget_of_realizedByColumnViewAffineFamily
    {Index : Type*} {Input : Type*} {view : Input → BitVec k}
    {G : IndexedPredictorFamily Index Input}
    (hreal : RealizedByColumnViewAffineFamily (k := k) view G) :
    G.HasBitBudget (k + 1) := by
  refine ⟨IndexedPredictorFamily.pullbackBitFamily view (affineColumnBitFamily k), ?_⟩
  intro i
  rcases hreal i with ⟨coeff, bias, hi⟩
  refine ⟨encodeAffineColumnIndex (coeff, bias), ?_⟩
  funext x
  calc
    (IndexedPredictorFamily.pullbackBitFamily view (affineColumnBitFamily k)).decode
        (encodeAffineColumnIndex (coeff, bias)) x
      = affineColumnPredict coeff bias (view x) := by
          simp [IndexedPredictorFamily.pullbackBitFamily, affineColumnBitFamily, affineColumnPredict]
    _ = G.predict i x := by
          exact (congrFun hi x).symm

/-- Exact post-switch families that collapse to affine GF(2)-style tests on the
retained VV column bits inherit the same `k + 1` bit budget. -/
abbrev RealizedByExactAffineColumnFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByColumnViewAffineFamily (k := k)
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a) G

theorem exactVisibleCompressionTarget_of_realizedByExactAffineColumnFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal : RealizedByExactAffineColumnFamily (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (k + 1) := by
  exact hasBitBudget_of_realizedByColumnViewAffineFamily (k := k) hreal

end

end Mettapedia.Computability.PNP
