import Mettapedia.Computability.PNP.SharedABFeatureRoutes

/-!
# P vs NP grassroots: unified target interfaces for the shared raw `(a, b)` route

This file packages the current route bottleneck in one explicit interface style.

The mathematical burden is now cleanly separated:

* quotient invariance under the reduced raw visible surface `(a, b)`,
* one fixed shared affine basis on that reduced surface,
* one combiner class on the resulting shared feature vector.

Once those hypotheses are packaged, the exact-surface compression target follows
immediately with the corresponding budget.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- Target data for the shared raw `(a, b)` affine-feature route. -/
structure SharedABAffineFeatureTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

/-- Target data for the shared raw `(a, b)` sparse-threshold route. -/
structure SharedABSparseThresholdTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

/-- Target data for the shared raw `(a, b)` decision-list route. -/
structure SharedABDecisionListTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

section

variable [Inhabited Z]

theorem SharedABAffineFeatureTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedAffineFeature
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABSparseThresholdTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedSparseThreshold
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABDecisionListTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedDecisionList
    (Z := Z) (r := r) (k := k) h.invariant h.realized

end

end

end Mettapedia.Computability.PNP
