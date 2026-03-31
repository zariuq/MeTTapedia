import Mettapedia.Computability.PNP.ABDecisionListRoute
import Mettapedia.Computability.PNP.SharedExactABFeatureFamilies

/-!
# P vs NP grassroots: quotient routes for shared raw `(a, b)` feature families

This file connects the reduced raw visible surface `(a, b)` to the shared-basis
exact-surface families.

If a switched family factors through the reduced surface and the reduced family
is realized using one shared affine basis on the raw `(a, b)` bits, then the
exact-surface family inherits the corresponding combiner-only budget.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ}

/-- Shared affine-feature predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABAffineFeaturePredict
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r))
    (x : ABVisibleSurface k) : Bool :=
  table ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec r) = 2 ^ r))
    (affineFeatureVector features (abVisibleBits (k := k) x)))

/-- Shared sparse-threshold predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABSparseThresholdAffinePredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r)
    (x : ABVisibleSurface k) : Bool :=
  decide (thresholdCodeValue (r := r) code.2 ≤
    maskedAffineFeatureCount (k := k + k) features code.1 (abVisibleBits (k := k) x))

/-- Shared decision-list predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABAffineDecisionListPredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r)
    (x : ABVisibleSurface k) : Bool :=
  match firstActiveFeature? (affineFeatureVector features (abVisibleBits (k := k) x)) with
  | some j => code.1 j
  | none => code.2

theorem sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r)) :
    sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table =
      fun u => sharedABAffineFeaturePredict (k := k) features table (abVisibleData u) := by
  funext u
  cases u
  rfl

theorem sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r) :
    sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code =
      fun u => sharedABSparseThresholdAffinePredict (k := k) features code (abVisibleData u) := by
  funext u
  cases u
  rfl

theorem sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r) :
    sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code =
      fun u => sharedABAffineDecisionListPredict (k := k) features code (abVisibleData u) := by
  funext u
  cases u
  rfl

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and an
arbitrary truth-table combiner. -/
def RealizedBySharedABAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ table : BitCode (2 ^ r),
    H.predict i = sharedABAffineFeaturePredict (k := k) features table

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and a
sparse-threshold combiner. -/
def RealizedBySharedABSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedSparseThresholdCode r,
    H.predict i = sharedABSparseThresholdAffinePredict (k := k) features code

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and a
fixed-order decision-list combiner. -/
def RealizedBySharedABAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode r,
    H.predict i = sharedABAffineDecisionListPredict (k := k) features code

theorem realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABAffineFeaturePredict (k := k) features table (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table u := by
          symm
          exact congrFun
            (sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features table) u

theorem realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABSparseThresholdAffinePredict (k := k) features code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code u := by
          symm
          exact congrFun
            (sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code) u

theorem realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABAffineDecisionListPredict (k := k) features code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code u := by
          symm
          exact congrFun
            (sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code) u

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

section Lift

variable [Inhabited Z]

theorem exactVisibleCompressionTarget_of_invariant_and_sharedAffineFeature
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_sharedSparseThreshold
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_sharedDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

end Lift

end

end Mettapedia.Computability.PNP
