import Mettapedia.Computability.PNP.SharedExactZABTargetInterface
import Mettapedia.Computability.PNP.CanonicalABTargetRoute

/-!
# P vs NP grassroots: canonical exact `(zfeat(z), a, b)` specialization

This file backward-chains from the shared-basis exact `z+a+b` target interface
to the simplest concrete manuscript-facing route.

The shared-basis route asks for:

* one shared extractor `zfeat`,
* one shared affine basis on the visible bits `(zfeat(z), a, b)`,
* realization by a downstream combiner family.

Here the affine basis is specialized to the canonical coordinate basis on the
raw visible bits themselves.  That collapses the generic shared-basis burden
back to the direct exact decision-list route on `(zfeat(z), a, b)`.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ}

theorem sharedExactZABAffineDecisionListPredict_canonicalAffineBasis
    (zfeat : Z → BitVec r)
    (code : SharedAffineDecisionListCode (r + (k + k))) :
    sharedExactZABAffineDecisionListPredict
      (Z := Z) (p := r + (k + k)) (r := r) (k := k)
      zfeat (canonicalAffineBasis (r + (k + k))) code
      =
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code := by
  funext u
  dsimp [sharedExactZABAffineDecisionListPredict, rawExactZABDecisionListPredict,
    exactZABAffineFeatureSummary]
  rw [affineFeatureVector_canonicalAffineBasis]
  cases h : firstActiveFeature? (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) <;> rfl

theorem realizedBySharedExactZABAffineDecisionListFamily_canonicalAffineBasis_of_rawDecisionList
    {Index : Type*}
    (zfeat : Z → BitVec r)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G) :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := r + (k + k)) (r := r) (k := k)
      zfeat (canonicalAffineBasis (r + (k + k))) G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  calc
    G.predict i = rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code := hi
    _ = sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := r + (k + k)) (r := r) (k := k)
          zfeat (canonicalAffineBasis (r + (k + k))) code := by
            symm
            exact sharedExactZABAffineDecisionListPredict_canonicalAffineBasis
              (Z := Z) (r := r) (k := k) zfeat code

section

variable {Index : Type*}

/-- The direct exact `(zfeat(z), a, b)` decision-list route is a concrete
instance of the shared-basis target interface. -/
def canonicalZABDecisionListTargetData
    (zfeat : Z → BitVec r)
    (G : ExactVisibleSwitchedFamily Z k Index)
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G) :
    SharedExactZABDecisionListTargetData
      (Z := Z) (p := r + (k + k)) (r := r) (k := k) (Index := Index)
      zfeat (canonicalAffineBasis (r + (k + k))) G where
  realized :=
    realizedBySharedExactZABAffineDecisionListFamily_canonicalAffineBasis_of_rawDecisionList
      (Z := Z) (r := r) (k := k) zfeat hreal

theorem exactVisibleCompressionTarget_of_canonicalZABDecisionList
    (zfeat : Z → BitVec r)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + (k + k) + 1) := by
  exact
    (canonicalZABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat G hreal).compressionTarget

theorem exactVisibleCompressionTarget_of_canonicalZABDecisionList_twoMul
    (zfeat : Z → BitVec r)
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByRawExactZABDecisionListFamily
        (Z := Z) (r := r) (k := k) zfeat G) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (r + 2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    exactVisibleCompressionTarget_of_canonicalZABDecisionList
      (Z := Z) (r := r) (k := k) (Index := Index) zfeat hreal

end

end

end Mettapedia.Computability.PNP
