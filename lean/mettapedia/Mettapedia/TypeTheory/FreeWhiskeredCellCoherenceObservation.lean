import Mettapedia.TypeTheory.FreeWhiskeredCell

/-!
# Observation boundaries for free whiskered-cell coherence

The raw free-cell syntax deliberately retains reflexivity, vertical
composition, and whiskering as constructors.  A later strict, weak, or higher
completion may identify some of those constructor trees, but that
identification is sound only for observations that cannot distinguish them.

This module supplies two generic observations.  `generatorCount` forgets
administrative cell structure and counts only authored comparison generators;
it is invariant under left and right vertical units and reassociation.
`constructorCount` retains every raw constructor and therefore distinguishes
an inserted vertical unit.  The contrast is representation independent and
does not select a global coherence quotient.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace FreeWhiskeredCell
namespace CoherenceObservation

universe uObject uHom uGenerator

variable {base : Base.{uObject, uHom}}
variable {Generator : {source target : base.Object} →
  base.Hom source target → base.Hom source target → Type uGenerator}

/-! ## Unit-insensitive authored-generator observation -/

/-- Count only authored comparison generators.  Reflexivity is administrative,
vertical composition adds counts, and whiskering does not create a new
authored comparison. -/
def generatorCount :
    {source target : base.Object} →
      {first second : base.Hom source target} →
        Cell base Generator first second → Nat
  | _, _, _, _, .refl _ => 0
  | _, _, _, _, .generator _ => 1
  | _, _, _, _, .vertical earlier later =>
      generatorCount earlier + generatorCount later
  | _, _, _, _, .whiskerLeft _ cell => generatorCount cell
  | _, _, _, _, .whiskerRight _ cell => generatorCount cell

@[simp] theorem generatorCount_refl
    {source target : base.Object} (path : base.Hom source target) :
    generatorCount (Generator := Generator) (Cell.refl path) = 0 :=
  rfl

@[simp] theorem generatorCount_generator
    {source target : base.Object} {first second : base.Hom source target}
    (generator : Generator first second) :
    generatorCount (Cell.generator generator) = 1 :=
  rfl

@[simp] theorem generatorCount_vertical
    {source target : base.Object}
    {first middle last : base.Hom source target}
    (earlier : Cell base Generator first middle)
    (later : Cell base Generator middle last) :
    generatorCount (Cell.vertical earlier later) =
      generatorCount earlier + generatorCount later :=
  rfl

@[simp] theorem generatorCount_whiskerLeft
    {source middle target : base.Object}
    (prior : base.Hom source middle)
    {first second : base.Hom middle target}
    (cell : Cell base Generator first second) :
    generatorCount (Cell.whiskerLeft prior cell) = generatorCount cell :=
  rfl

@[simp] theorem generatorCount_whiskerRight
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    (suffix : base.Hom middle target)
    (cell : Cell base Generator first second) :
    generatorCount (Cell.whiskerRight suffix cell) = generatorCount cell :=
  rfl

/-- Authored-generator count is insensitive to a left vertical identity. -/
theorem generatorCount_leftUnit
    {source target : base.Object} {first second : base.Hom source target}
    (cell : Cell base Generator first second) :
    generatorCount
        (Cell.vertical (Cell.refl (Generator := Generator) first) cell) =
      generatorCount cell := by
  simp

/-- Authored-generator count is insensitive to a right vertical identity. -/
theorem generatorCount_rightUnit
    {source target : base.Object} {first second : base.Hom source target}
    (cell : Cell base Generator first second) :
    generatorCount
        (Cell.vertical cell (Cell.refl (Generator := Generator) second)) =
      generatorCount cell := by
  simp

/-- Authored-generator count is insensitive to vertical reassociation. -/
theorem generatorCount_vertical_assoc
    {source target : base.Object}
    {first second third fourth : base.Hom source target}
    (left : Cell base Generator first second)
    (middle : Cell base Generator second third)
    (right : Cell base Generator third fourth) :
    generatorCount
        (Cell.vertical (Cell.vertical left middle) right) =
      generatorCount
        (Cell.vertical left (Cell.vertical middle right)) := by
  simp [Nat.add_assoc]

/-! ## History-sensitive raw-constructor observation -/

/-- The constructor tree of a raw cell, with endpoint and generator payloads
forgotten but all administrative shape retained.  Unlike a mere node count,
this distinguishes alternative parenthesizations. -/
inductive RawShape where
  | refl
  | generator
  | vertical (earlier later : RawShape)
  | whiskerLeft (cell : RawShape)
  | whiskerRight (cell : RawShape)
deriving DecidableEq

/-- Forget payloads while retaining the complete raw constructor shape. -/
def rawShape :
    {source target : base.Object} →
      {first second : base.Hom source target} →
        Cell base Generator first second → RawShape
  | _, _, _, _, .refl _ => .refl
  | _, _, _, _, .generator _ => .generator
  | _, _, _, _, .vertical earlier later =>
      .vertical (rawShape earlier) (rawShape later)
  | _, _, _, _, .whiskerLeft _ cell => .whiskerLeft (rawShape cell)
  | _, _, _, _, .whiskerRight _ cell => .whiskerRight (rawShape cell)

@[simp] theorem rawShape_refl
    {source target : base.Object} (path : base.Hom source target) :
    rawShape (Generator := Generator) (Cell.refl path) = .refl :=
  rfl

@[simp] theorem rawShape_generator
    {source target : base.Object} {first second : base.Hom source target}
    (generator : Generator first second) :
    rawShape (Cell.generator generator) = .generator :=
  rfl

@[simp] theorem rawShape_vertical
    {source target : base.Object}
    {first middle last : base.Hom source target}
    (earlier : Cell base Generator first middle)
    (later : Cell base Generator middle last) :
    rawShape (Cell.vertical earlier later) =
      .vertical (rawShape earlier) (rawShape later) :=
  rfl

@[simp] theorem rawShape_whiskerLeft
    {source middle target : base.Object}
    (prior : base.Hom source middle)
    {first second : base.Hom middle target}
    (cell : Cell base Generator first second) :
    rawShape (Cell.whiskerLeft prior cell) = .whiskerLeft (rawShape cell) :=
  rfl

@[simp] theorem rawShape_whiskerRight
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    (suffix : base.Hom middle target)
    (cell : Cell base Generator first second) :
    rawShape (Cell.whiskerRight suffix cell) = .whiskerRight (rawShape cell) :=
  rfl

/-- Count every raw cell constructor.  This retains administrative
reflexivity, vertical nodes, and whiskering in addition to authored
generators. -/
def constructorCount :
    {source target : base.Object} →
      {first second : base.Hom source target} →
        Cell base Generator first second → Nat
  | _, _, _, _, .refl _ => 1
  | _, _, _, _, .generator _ => 1
  | _, _, _, _, .vertical earlier later =>
      constructorCount earlier + constructorCount later + 1
  | _, _, _, _, .whiskerLeft _ cell => constructorCount cell + 1
  | _, _, _, _, .whiskerRight _ cell => constructorCount cell + 1

@[simp] theorem constructorCount_refl
    {source target : base.Object} (path : base.Hom source target) :
    constructorCount (Generator := Generator) (Cell.refl path) = 1 :=
  rfl

@[simp] theorem constructorCount_generator
    {source target : base.Object} {first second : base.Hom source target}
    (generator : Generator first second) :
    constructorCount (Cell.generator generator) = 1 :=
  rfl

@[simp] theorem constructorCount_vertical
    {source target : base.Object}
    {first middle last : base.Hom source target}
    (earlier : Cell base Generator first middle)
    (later : Cell base Generator middle last) :
    constructorCount (Cell.vertical earlier later) =
      constructorCount earlier + constructorCount later + 1 :=
  rfl

@[simp] theorem constructorCount_whiskerLeft
    {source middle target : base.Object}
    (prior : base.Hom source middle)
    {first second : base.Hom middle target}
    (cell : Cell base Generator first second) :
    constructorCount (Cell.whiskerLeft prior cell) =
      constructorCount cell + 1 :=
  rfl

@[simp] theorem constructorCount_whiskerRight
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    (suffix : base.Hom middle target)
    (cell : Cell base Generator first second) :
    constructorCount (Cell.whiskerRight suffix cell) =
      constructorCount cell + 1 :=
  rfl

/-- A left vertical identity is observably present in the raw constructor
tree. -/
theorem constructorCount_leftUnit_ne
    {source target : base.Object} {first second : base.Hom source target}
    (cell : Cell base Generator first second) :
    constructorCount
        (Cell.vertical (Cell.refl (Generator := Generator) first) cell) ≠
      constructorCount cell := by
  simp
  omega

/-- A right vertical identity is likewise retained in the raw tree. -/
theorem constructorCount_rightUnit_ne
    {source target : base.Object} {first second : base.Hom source target}
    (cell : Cell base Generator first second) :
    constructorCount
        (Cell.vertical cell (Cell.refl (Generator := Generator) second)) ≠
      constructorCount cell := by
  simp
  omega

/-! ## The raw interchange boundary -/

/-- Both raw horizontal readings retain exactly the authored generators of
their two component cells. -/
@[simp] theorem generatorCount_horizontalRightThenLeft
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    generatorCount (Cell.horizontalRightThenLeft left right) =
      generatorCount left + generatorCount right := by
  simp [Cell.horizontalRightThenLeft]

/-- Reversing the raw whiskering order leaves authored-generator count
unchanged. -/
@[simp] theorem generatorCount_horizontalLeftThenRight
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    generatorCount (Cell.horizontalLeftThenRight left right) =
      generatorCount left + generatorCount right := by
  simp [Cell.horizontalLeftThenRight, Nat.add_comm]

/-- Authored-generator count therefore observes the two interchange
candidates identically. -/
theorem generatorCount_identifies_interchange
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    generatorCount (Cell.horizontalRightThenLeft left right) =
      generatorCount (Cell.horizontalLeftThenRight left right) := by
  simp

/-- Even total node count cannot recover which whiskering happened first. -/
theorem constructorCount_identifies_interchange
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    constructorCount (Cell.horizontalRightThenLeft left right) =
      constructorCount (Cell.horizontalLeftThenRight left right) := by
  simp [Cell.horizontalRightThenLeft, Cell.horizontalLeftThenRight]
  omega

/-- The raw constructor tree retains the two whiskering orders.  Thus the
strict interchange equation is not an equality of the free syntax. -/
theorem rawShape_separates_interchange
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    rawShape (Cell.horizontalRightThenLeft left right) ≠
      rawShape (Cell.horizontalLeftThenRight left right) := by
  simp [Cell.horizontalRightThenLeft, Cell.horizontalLeftThenRight]

/-- The two horizontal readings are distinct retained histories even though
both scalar counts agree. -/
theorem horizontalRightThenLeft_ne_horizontalLeftThenRight
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    Cell.horizontalRightThenLeft left right ≠
      Cell.horizontalLeftThenRight left right := by
  intro equality
  exact rawShape_separates_interchange left right
    (congrArg rawShape equality)

/-- Interchange is therefore capability-relative: scalar work-like
observations may validate it, while a construction-history observation
correctly refuses it. -/
theorem interchange_is_observation_relative
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    generatorCount (Cell.horizontalRightThenLeft left right) =
        generatorCount (Cell.horizontalLeftThenRight left right) ∧
      constructorCount (Cell.horizontalRightThenLeft left right) =
        constructorCount (Cell.horizontalLeftThenRight left right) ∧
      rawShape (Cell.horizontalRightThenLeft left right) ≠
        rawShape (Cell.horizontalLeftThenRight left right) :=
  ⟨generatorCount_identifies_interchange left right,
    constructorCount_identifies_interchange left right,
    rawShape_separates_interchange left right⟩

/-! ## A small generic coherence boundary -/

namespace Canary

open FreeWhiskeredCell.Canary

/-- The same proposed left-unit identification is invisible to authored
generator count and visible to raw-constructor count. -/
theorem leftUnit_is_observation_relative :
    generatorCount leftPadded = generatorCount marked ∧
      constructorCount leftPadded ≠ constructorCount marked :=
  ⟨generatorCount_leftUnit marked, constructorCount_leftUnit_ne marked⟩

/-- Three authored comparisons associated to the left. -/
def leftAssociated :
    Cell FreeWhiskeredCell.Canary.base FreeWhiskeredCell.Canary.Generator
      (source := ()) (target := ()) () () :=
  Cell.vertical (Cell.vertical marked marked) marked

/-- The same three authored comparisons associated to the right. -/
def rightAssociated :
    Cell FreeWhiskeredCell.Canary.base FreeWhiskeredCell.Canary.Generator
      (source := ()) (target := ()) () () :=
  Cell.vertical marked (Cell.vertical marked marked)

/-- Authored-generator count cannot observe reassociation. -/
theorem generatorCount_identifies_reassociation :
    generatorCount leftAssociated = generatorCount rightAssociated := by
  exact generatorCount_vertical_assoc marked marked marked

/-- The raw constructor shape does observe reassociation, even though both
trees have the same authored-generator and constructor counts. -/
theorem rawShape_separates_reassociation :
    rawShape leftAssociated ≠ rawShape rightAssociated := by
  decide

/-- Reassociation is therefore another capability-relative coherence law,
not a global equality of the retained free syntax. -/
theorem reassociation_is_observation_relative :
    generatorCount leftAssociated = generatorCount rightAssociated ∧
      constructorCount leftAssociated = constructorCount rightAssociated ∧
      rawShape leftAssociated ≠ rawShape rightAssociated := by
  exact ⟨generatorCount_identifies_reassociation, rfl,
    rawShape_separates_reassociation⟩

end Canary

#print axioms generatorCount_leftUnit
#print axioms generatorCount_rightUnit
#print axioms generatorCount_vertical_assoc
#print axioms constructorCount_leftUnit_ne
#print axioms constructorCount_rightUnit_ne
#print axioms generatorCount_identifies_interchange
#print axioms constructorCount_identifies_interchange
#print axioms rawShape_separates_interchange
#print axioms horizontalRightThenLeft_ne_horizontalLeftThenRight
#print axioms interchange_is_observation_relative
#print axioms Canary.leftUnit_is_observation_relative
#print axioms Canary.generatorCount_identifies_reassociation
#print axioms Canary.rawShape_separates_reassociation
#print axioms Canary.reassociation_is_observation_relative

end CoherenceObservation
end FreeWhiskeredCell
end Mettapedia.TypeTheory
