import Mettapedia.GSLT.Core.LooseRelationEquipment

/-!
# Companion and conjoint binding laws for proof-relevant relations

The loose-relation core already separates tight functions from
proof-relevant relations and defines the companion and conjoint of every
function.  This module supplies the missing binding cells and their two
triangle equations.

The equations are stated directly in the existing cell calculus.  Horizontal
composition is associative and unital up to the fibre equivalences already
proved in `LooseRelationEquipment`, so the horizontal triangles explicitly
pass through those unitors.  No quotient of relation witnesses is taken.
-/

namespace Mettapedia.GSLT.LooseRelationEquipment

universe u

/-! ## Tight maps as cells between horizontal identities -/

/-- A tight function maps equality witnesses along itself. -/
def tightCell {Source Target : Type u} (map : Source -> Target) :
    Cell map map identity identity where
  map witness := by
    rcases witness with ⟨⟨equal⟩⟩
    exact ⟨⟨congrArg map equal⟩⟩

/-! ## Companion binding cells -/

/-- The first binding cell of the companion of a tight map. -/
def companionUnit {Source Target : Type u} (map : Source -> Target) :
    Cell (_root_.id : Source -> Source) map identity (companion map) where
  map witness := by
    rcases witness with ⟨⟨equal⟩⟩
    exact ⟨⟨congrArg map equal⟩⟩

/-- The second binding cell of the companion of a tight map. -/
def companionCounit {Source Target : Type u} (map : Source -> Target) :
    Cell map (_root_.id : Target -> Target) (companion map) identity where
  map witness := witness

/-- Vertically pasting the companion binding cells gives the equality cell
of the original tight map. -/
theorem companion_vertical_triangle
    {Source Target : Type u} (map : Source -> Target) :
    Cell.vcomp (companionUnit map) (companionCounit map) = tightCell map := by
  apply Cell.ext
  intro source target witness
  exact (instSubsingletonEqWitness _ _).allEq _ _

/-- Horizontally pasting the companion binding cells gives the identity on
the companion after applying the established horizontal unitors. -/
theorem companion_horizontal_triangle
    {Source Target : Type u} (map : Source -> Target)
    (source : Source) (target : Target)
    (witness : companion map source target) :
    compIdentityRight (companion map) source target
        ((Cell.hcomp (companionUnit map) (companionCounit map)).map
          ((compIdentityLeft (companion map) source target).symm witness)) =
      witness := by
  exact (instSubsingletonEqWitness _ _).allEq _ _

/-! ## Conjoint binding cells -/

/-- The first binding cell of the conjoint of a tight map. -/
def conjointUnit {Source Target : Type u} (map : Source -> Target) :
    Cell map (_root_.id : Source -> Source) identity (conjoint map) where
  map witness := by
    rcases witness with ⟨⟨equal⟩⟩
    exact ⟨⟨congrArg map equal⟩⟩

/-- The second binding cell of the conjoint of a tight map. -/
def conjointCounit {Source Target : Type u} (map : Source -> Target) :
    Cell (_root_.id : Target -> Target) map (conjoint map) identity where
  map witness := witness

/-- Vertically pasting the conjoint binding cells again gives the equality
cell of the original tight map. -/
theorem conjoint_vertical_triangle
    {Source Target : Type u} (map : Source -> Target) :
    Cell.vcomp (conjointUnit map) (conjointCounit map) = tightCell map := by
  apply Cell.ext
  intro source target witness
  exact (instSubsingletonEqWitness _ _).allEq _ _

/-- Horizontally pasting the conjoint binding cells gives the identity on
the conjoint after applying the established horizontal unitors. -/
theorem conjoint_horizontal_triangle
    {Source Target : Type u} (map : Source -> Target)
    (source : Target) (target : Source)
    (witness : conjoint map source target) :
    compIdentityLeft (conjoint map) source target
        ((Cell.hcomp (conjointCounit map) (conjointUnit map)).map
          ((compIdentityRight (conjoint map) source target).symm witness)) =
      witness := by
  exact (instSubsingletonEqWitness _ _).allEq _ _

/-! ## Identity and composition coherence -/

/-- The companion of the identity map is the horizontal identity. -/
theorem companion_id {Object : Type u} :
    companion (_root_.id : Object -> Object) = identity :=
  rfl

/-- The conjoint of the identity map is the horizontal identity. -/
theorem conjoint_id {Object : Type u} :
    conjoint (_root_.id : Object -> Object) = identity :=
  rfl

/-- Companions preserve tight composition up to the exact retained-witness
equivalence supplied by representation composition. -/
def companionCompEquiv {First Middle Last : Type u}
    (earlier : First -> Middle) (later : Middle -> Last)
    (source : First) (target : Last) :
    comp (companion earlier) (companion later) source target ≃
      companion (later ∘ earlier) source target :=
  (Representation.horizontalComp
    (Representation.companionSelf earlier)
    (Representation.companionSelf later)).exact source target

/-- Conjoints reverse tight composition.  The intermediate object and both
equality witnesses are retained on the composite side. -/
def conjointCompEquiv {First Middle Last : Type u}
    (earlier : First -> Middle) (later : Middle -> Last)
    (source : Last) (target : First) :
    comp (conjoint later) (conjoint earlier) source target ≃
      conjoint (later ∘ earlier) source target where
  toFun witness := by
    rcases witness with ⟨middle, laterWitness, earlierWitness⟩
    rcases laterWitness with ⟨⟨laterEqual⟩⟩
    rcases earlierWitness with ⟨⟨earlierEqual⟩⟩
    exact ⟨⟨laterEqual.trans (congrArg later earlierEqual)⟩⟩
  invFun witness := by
    rcases witness with ⟨⟨equal⟩⟩
    exact ⟨earlier target, ⟨⟨equal⟩⟩, ⟨⟨rfl⟩⟩⟩
  left_inv witness := by
    apply (show Subsingleton
        (comp (conjoint later) (conjoint earlier) source target) from
      ⟨by
        rintro ⟨firstMiddle, firstLater, firstEarlier⟩
          ⟨secondMiddle, secondLater, secondEarlier⟩
        have firstMiddleEq : firstMiddle = earlier target :=
          firstEarlier.down.down
        have secondMiddleEq : secondMiddle = earlier target :=
          secondEarlier.down.down
        cases firstMiddleEq
        cases secondMiddleEq
        congr
        · exact (instSubsingletonEqWitness _ _).allEq _ _
        · exact (instSubsingletonEqWitness _ _).allEq _ _⟩).allEq
  right_inv witness := (instSubsingletonEqWitness _ _).allEq _ _

/-! ## Uniqueness of represented execution -/

namespace Representation

/-! ## A represented loose arrow is vertically isomorphic to its companion -/

/-- The exact fibre equivalence of a representation is a cell from the
authored loose arrow to the companion of its selected tight map. -/
def toCompanionCell {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation) :
    Cell (_root_.id : Source → Source) (_root_.id : Target → Target)
      relation (companion representation.map) where
  map witness := representation.exact _ _ witness

/-- The inverse exact fibre equivalence is the cell back from the companion
to the original proof-relevant loose arrow. -/
def fromCompanionCell {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation) :
    Cell (_root_.id : Source → Source) (_root_.id : Target → Target)
      (companion representation.map) relation where
  map witness := (representation.exact _ _).symm witness

/-- The two cells recover the identity on the original loose arrow. -/
theorem fromCompanion_vcomp_toCompanion
    {Source Target : Type u} {relation : Loose Source Target}
    (representation : Representation relation) :
    Cell.vcomp representation.toCompanionCell
        representation.fromCompanionCell =
      Cell.id relation := by
  apply Cell.ext
  intro source target witness
  exact (representation.exact source target).symm_apply_apply witness

/-- The same cells recover the identity on the selected companion. -/
theorem toCompanion_vcomp_fromCompanion
    {Source Target : Type u} {relation : Loose Source Target}
    (representation : Representation relation) :
    Cell.vcomp representation.fromCompanionCell
        representation.toCompanionCell =
      Cell.id (companion representation.map) := by
  apply Cell.ext
  intro source target witness
  exact (representation.exact source target).apply_symm_apply witness

/-- Exact representation determines the compiled map uniquely.  Two
admission proofs may retain different proof terms, but they cannot authorize
different executions for the same loose arrow. -/
theorem map_unique {Source Target : Type u} {relation : Loose Source Target}
    (first second : Representation relation) :
    first.map = second.map := by
  funext source
  let witness : relation source (first.map source) :=
    (first.exact source (first.map source)).symm ⟨⟨rfl⟩⟩
  exact (second.exact source (first.map source) witness).down.down.symm

theorem map_apply_unique {Source Target : Type u}
    {relation : Loose Source Target}
    (first second : Representation relation) (source : Source) :
    first.map source = second.map source := by
  rw [map_unique first second]

end Representation

/-! ## Controls -/

namespace CompanionCanary

/-- Boolean negation has both binding triangles. -/
theorem boolNot_triangles :
    Cell.vcomp (companionUnit Bool.not) (companionCounit Bool.not) =
        tightCell Bool.not ∧
      Cell.vcomp (conjointUnit Bool.not) (conjointCounit Bool.not) =
        tightCell Bool.not :=
  ⟨companion_vertical_triangle Bool.not,
    conjoint_vertical_triangle Bool.not⟩

/-- The nondeterministic choice relation remains a genuine loose arrow and
cannot be represented by the companion of any direct map. -/
theorem nondeterministic_choice_has_no_companion :
    ¬ Nonempty (Representation Canary.choice) :=
  Canary.choice_not_representable

end CompanionCanary

#print axioms companion_vertical_triangle
#print axioms companion_horizontal_triangle
#print axioms conjoint_vertical_triangle
#print axioms conjoint_horizontal_triangle
#print axioms Representation.fromCompanion_vcomp_toCompanion
#print axioms Representation.toCompanion_vcomp_fromCompanion
#print axioms Representation.map_unique
#print axioms CompanionCanary.boolNot_triangles
#print axioms CompanionCanary.nondeterministic_choice_has_no_companion

end Mettapedia.GSLT.LooseRelationEquipment
