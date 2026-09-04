import Mettapedia.CategoryTheory.GlobularLocalTruncation
import Mettapedia.Logic.WorldModel.FiniteEvidence

/-!
# Cell height and observation horizon are orthogonal

Two independent kinds of “higher” structure recur in open-ended reasoning:

* globular height records cells, comparisons between cells, and further
  comparisons;
* observation horizon records how much of an open-ended world has been seen.

This file packages both axes without identifying them.  Four concrete
profiles realize every Boolean combination of local cell thinness and uniform
finite determination.  Consequently neither axis implies the other.

The examples use the standard thin-below/thick-next globular towers and
Cantor-prefix observations.  They are logical independence controls, not a
claim that these two structures must be combined by a particular product in
the eventual Prime semantics.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality

open Mettapedia.CategoryTheory.Higher
open Mettapedia.CategoryTheory.Higher.GlobularSet
open Mettapedia.Logic.WorldModel.OpenEnded
open Mettapedia.Logic.WorldModel.FiniteEvidence
open Mettapedia.Computability

universe uCell uWorld uSnapshot

/-- A property bag exposing one selected globular boundary and one selected
open-world observation problem.  No relation between the two axes is built
into the record. -/
structure Profile where
  tower : GlobularSet.{uCell}
  dimension : Nat
  World : Type uWorld
  observation : PrefixObservation.{uWorld, uSnapshot} World
  property : World → Prop

namespace Profile

/-- The selected parallel-cell layer is locally thin. -/
def CellThin (profile : Profile.{uCell, uWorld, uSnapshot}) : Prop :=
  profile.tower.LocallyThinAt profile.dimension

/-- The selected world property is determined by one uniform finite
observation horizon. -/
def UniformFinite (profile : Profile.{uCell, uWorld, uSnapshot}) : Prop :=
  FinitelyDetermined profile.observation profile.property

/-- The selected world property retains an unresolved tail at every finite
observation horizon. -/
def OpenTail (profile : Profile.{uCell, uWorld, uSnapshot}) : Prop :=
  HasUnresolvedTail profile.observation profile.property

end Profile

/-! ## All four combinations -/

/-- Thin cell layer and uniformly finite observation. -/
def thinFinite : Profile.{0, 0, 0} where
  tower := ThinBelowThickNext.tower 1
  dimension := 0
  World := CantorSpace
  observation := cantorPrefixObservation
  property := firstBitTrue

/-- Thin cell layer and genuinely open-tail observation. -/
def thinOpen : Profile.{0, 0, 0} where
  tower := ThinBelowThickNext.tower 1
  dimension := 0
  World := CantorSpace
  observation := cantorPrefixObservation
  property := someBitTrue

/-- Thick cell layer and uniformly finite observation. -/
def thickFinite : Profile.{0, 0, 0} where
  tower := ThinBelowThickNext.tower 0
  dimension := 0
  World := CantorSpace
  observation := cantorPrefixObservation
  property := firstBitTrue

/-- Thick cell layer and genuinely open-tail observation. -/
def thickOpen : Profile.{0, 0, 0} where
  tower := ThinBelowThickNext.tower 0
  dimension := 0
  World := CantorSpace
  observation := cantorPrefixObservation
  property := someBitTrue

theorem thinFinite_has_both :
    thinFinite.CellThin ∧ thinFinite.UniformFinite := by
  exact ⟨ThinBelowThickNext.locallyThinAt_of_succ_le 1 0 (by omega),
    firstBitTrue_finitelyDetermined⟩

theorem thinOpen_is_thin_with_openTail :
    thinOpen.CellThin ∧ thinOpen.OpenTail := by
  exact ⟨ThinBelowThickNext.locallyThinAt_of_succ_le 1 0 (by omega),
    someBitTrue_hasUnresolvedTail⟩

theorem thickFinite_is_thick_with_finiteObservation :
    ¬ thickFinite.CellThin ∧ thickFinite.UniformFinite := by
  exact ⟨ThinBelowThickNext.not_locallyThinAt_horizon 0,
    firstBitTrue_finitelyDetermined⟩

theorem thickOpen_has_neither_finite_reduction :
    ¬ thickOpen.CellThin ∧ thickOpen.OpenTail := by
  exact ⟨ThinBelowThickNext.not_locallyThinAt_horizon 0,
    someBitTrue_hasUnresolvedTail⟩

/-! ## Independence consequences -/

/-- Local cell thinness does not imply a uniform finite observation horizon. -/
theorem cellThinness_does_not_imply_uniformFinite :
    ¬ ∀ profile : Profile.{0, 0, 0},
      profile.CellThin → profile.UniformFinite := by
  intro purported
  have finite := purported thinOpen thinOpen_is_thin_with_openTail.1
  exact someBitTrue_not_finitelyDetermined finite

/-- Uniform finite observation does not imply local cell thinness. -/
theorem uniformFinite_does_not_imply_cellThinness :
    ¬ ∀ profile : Profile.{0, 0, 0},
      profile.UniformFinite → profile.CellThin := by
  intro purported
  have thin := purported thickFinite
    thickFinite_is_thick_with_finiteObservation.2
  exact thickFinite_is_thick_with_finiteObservation.1 thin

/-! ## Audited theorem crowns -/

#print axioms thinFinite_has_both
#print axioms thinOpen_is_thin_with_openTail
#print axioms thickFinite_is_thick_with_finiteObservation
#print axioms thickOpen_has_neither_finite_reduction
#print axioms cellThinness_does_not_imply_uniformFinite
#print axioms uniformFinite_does_not_imply_cellThinness

end Mettapedia.TypeTheory.CellHeightObservationHorizonOrthogonality
