import Mettapedia.Computability.PNP.AffineFeatureFamily
import Mathlib.Data.Fintype.EquivFin

/-!
# P vs NP grassroots: affine decision-list predictors on the VV column view

This file adds another small combiner class on top of the affine VV probes:

* choose `r` affine GF(2)-style features of the retained VV column bits `a`,
* choose an `r`-bit response vector,
* choose one default output bit,
* evaluate the features in the fixed order `0, 1, ..., r-1`,
* return the response bit attached to the first active feature, or the default
  bit if no feature fires.

The exact raw budget is now

`r * (k + 2) + 1`.

So if the switched predictors collapse to an affine decision-list algebra on
the VV column view, the optimistic route gets an even smaller explicit encoded
class than the sparse-threshold family.
-/

namespace Mettapedia.Computability.PNP

section

variable {r k : ℕ}

/-- One affine decision-list code:
`r` affine GF(2)-style features, an `r`-bit response vector, and one default
output bit. -/
abbrev AffineDecisionListCode (r k : ℕ) :=
  (Fin r → AffineColumnCode k) × BitCode r × Bool

/-- The first active feature in the fixed order `0, 1, ..., r-1`, if any. -/
noncomputable def firstActiveFeature? (featureVec : BitVec r) : Option (Fin r) := by
  classical
  let active : Finset (Fin r) := (Finset.univ : Finset (Fin r)).filter fun j => featureVec j
  exact if h : active.Nonempty then some (active.min' h) else none

/-- Evaluate the affine decision-list predictor on one VV column vector `a`. -/
noncomputable def affineDecisionListPredict
    (code : AffineDecisionListCode r k) (a : BitVec k) : Bool :=
  match firstActiveFeature? (affineFeatureVector code.1 a) with
  | some j => code.2.1 j
  | none => code.2.2

theorem card_affineDecisionListCode (r k : ℕ) :
    Fintype.card (AffineDecisionListCode r k) = 2 ^ (r * (k + 2) + 1) := by
  calc
    Fintype.card (AffineDecisionListCode r k)
      = Fintype.card (Fin r → AffineColumnCode k) *
          (Fintype.card (BitCode r) * Fintype.card Bool) := by
            simp [AffineDecisionListCode]
    _ = (Fintype.card (AffineColumnCode k)) ^ r * (2 ^ r * 2) := by
          simp
    _ = (2 ^ (k + 1)) ^ r * (2 ^ r * 2) := by
          rw [card_affineColumnCode]
    _ = 2 ^ ((k + 1) * r) * (2 ^ r * 2) := by
          rw [← Nat.pow_mul]
    _ = 2 ^ (r * (k + 1)) * (2 ^ r * 2) := by
          simp [Nat.mul_comm]
    _ = (2 ^ (r * (k + 1)) * 2 ^ r) * 2 := by
          rw [Nat.mul_assoc]
    _ = 2 ^ (r * (k + 1) + r) * 2 := by
          rw [← Nat.pow_add]
    _ = 2 ^ (r * (k + 1) + r) * 2 ^ 1 := by
          simp
    _ = 2 ^ (r * (k + 1) + r + 1) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (r * (k + 2) + 1) := by
          have hexp : r * (k + 1) + r + 1 = r * (k + 2) + 1 := by
            calc
              r * (k + 1) + r + 1 = r * (k + 1) + r * 1 + 1 := by simp
              _ = r * ((k + 1) + 1) + 1 := by rw [← Nat.mul_add]
              _ = r * (k + 2) + 1 := by simp [Nat.add_assoc]
          rw [hexp]

/-- Noncomputably collapse the affine decision-list code type to one raw bit
code of the corresponding size. -/
noncomputable def affineDecisionListCodeEquivBitCode (r k : ℕ) :
    AffineDecisionListCode r k ≃ BitCode (r * (k + 2) + 1) := by
  apply Fintype.equivOfCardEq
  rw [card_affineDecisionListCode, card_bitCode]

/-- The indexed family whose members are exactly the affine decision-list
predictors on the VV column view. -/
noncomputable def affineDecisionListIndexedFamily (r k : ℕ) :
    IndexedPredictorFamily (AffineDecisionListCode r k) (BitVec k) where
  predict code a := affineDecisionListPredict code a

/-- The corresponding raw-bit encoded family. -/
noncomputable def affineDecisionListBitFamily (r k : ℕ) :
    BitEncodedClassifierFamily (BitVec k) (r * (k + 2) + 1) where
  decode raw a := affineDecisionListPredict
    ((affineDecisionListCodeEquivBitCode r k).symm raw) a

theorem affineDecisionListIndexedFamily_hasBitBudget (r k : ℕ) :
    (affineDecisionListIndexedFamily r k).HasBitBudget (r * (k + 2) + 1) := by
  refine ⟨affineDecisionListBitFamily r k, ?_⟩
  intro code
  refine ⟨affineDecisionListCodeEquivBitCode r k code, ?_⟩
  funext a
  change affineDecisionListPredict
      ((affineDecisionListCodeEquivBitCode r k).symm
        (affineDecisionListCodeEquivBitCode r k code)) a
      = affineDecisionListPredict code a
  simp

/-- Any indexed family realized by affine decision-list predictors on one
column-view map inherits the same explicit bit budget. -/
def RealizedByAffineDecisionListFamily
    {Index : Type*} {Input : Type*} (view : Input → BitVec k)
    (G : IndexedPredictorFamily Index Input) : Prop :=
  ∀ i, ∃ code : AffineDecisionListCode r k,
    G.predict i = fun x => affineDecisionListPredict code (view x)

theorem hasBitBudget_of_realizedByAffineDecisionListFamily
    {Index : Type*} {Input : Type*} {view : Input → BitVec k}
    {G : IndexedPredictorFamily Index Input}
    (hreal : RealizedByAffineDecisionListFamily (r := r) (k := k) view G) :
    G.HasBitBudget (r * (k + 2) + 1) := by
  refine ⟨IndexedPredictorFamily.pullbackBitFamily view
    (affineDecisionListBitFamily r k), ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨affineDecisionListCodeEquivBitCode r k code, ?_⟩
  funext x
  calc
    (IndexedPredictorFamily.pullbackBitFamily view
        (affineDecisionListBitFamily r k)).decode
        (affineDecisionListCodeEquivBitCode r k code) x
      = affineDecisionListPredict code (view x) := by
          simp [IndexedPredictorFamily.pullbackBitFamily, affineDecisionListBitFamily]
    _ = G.predict i x := by
          exact (congrFun hi x).symm

/-- Exact post-switch specialization: the switched family depends only on an
affine decision-list summary of the retained VV column bits. -/
abbrev RealizedByExactAffineDecisionListFamily
    {Z : Type*} {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index) : Prop :=
  RealizedByAffineDecisionListFamily (r := r) (k := k)
    (fun u : ExactVisiblePostSwitchSurface Z k => u.a) G

theorem exactVisibleCompressionTarget_of_realizedByExactAffineDecisionListFamily
    {Z : Type*} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactAffineDecisionListFamily (r := r) (Z := Z) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (r * (k + 2) + 1) := by
  exact hasBitBudget_of_realizedByAffineDecisionListFamily (r := r) (k := k) hreal

end

end Mettapedia.Computability.PNP
