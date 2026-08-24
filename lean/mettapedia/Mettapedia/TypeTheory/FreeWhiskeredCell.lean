import Mettapedia.TypeTheory.JudgmentalEquality

/-!
# Free raw whiskered cells

This module isolates the representation-independent two-dimensional syntax
shared by retained conversion receipts and authored operational routes.

A `Base` supplies objects, proof-relevant one-cells, and binary composition.
No category laws are assumed.  A family of parallel authored
two-generators then freely generates cells under reflexivity, vertical
composition, and left/right whiskering.

The resulting syntax is deliberately prior to a strict 2-category,
bicategory, or higher completion.  Its universal property says exactly that
an interpretation of the five constructors extends uniquely to every raw
cell.  Coherence equations or higher witnesses are additional structure on a
target algebra; they are not silently imposed by this free syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace FreeWhiskeredCell

universe uObject uHom uGenerator uTarget uOtherGenerator

/-! ## The raw one-dimensional boundary -/

/-- Objects and composable one-cells before any unit or associativity laws are
imposed.  Identities already retained inside a particular one-cell syntax do
not need to be selected again at this common boundary. -/
structure Base where
  Object : Type uObject
  Hom : Object → Object → Type uHom
  compose : {source middle target : Object} →
    Hom source middle → Hom middle target → Hom source target

/-! ## Free generated cells -/

/-- Raw globular two-cells freely generated under vertical composition and
whiskering.  In particular, no unit, associativity, or interchange equation
is built into this inductive syntax. -/
inductive Cell (base : Base.{uObject, uHom})
    (Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator) :
    {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type (max uObject uHom uGenerator) where
  | refl {source target} (path : base.Hom source target) :
      Cell base Generator path path
  | generator {source target} {first second : base.Hom source target} :
      Generator first second → Cell base Generator first second
  | vertical {source target} {first middle last : base.Hom source target} :
      Cell base Generator first middle →
      Cell base Generator middle last →
      Cell base Generator first last
  | whiskerLeft {source middle target}
      (prior : base.Hom source middle)
      {first second : base.Hom middle target} :
      Cell base Generator first second →
      Cell base Generator
        (base.compose prior first) (base.compose prior second)
  | whiskerRight {source middle target}
      {first second : base.Hom source middle}
      (suffix : base.Hom middle target) :
      Cell base Generator first second →
      Cell base Generator
        (base.compose first suffix) (base.compose second suffix)

namespace Cell

/-- Compose parallel cells horizontally by first transporting the left cell
across the source one-cell of the right cell, then transporting the right
cell across the target one-cell of the left cell.  This is one raw
interchange candidate; no equation identifies it with the alternative
constructor tree below. -/
def horizontalRightThenLeft
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    Cell base Generator
      (base.compose first third) (base.compose second fourth) :=
  .vertical (.whiskerRight third left) (.whiskerLeft second right)

/-- Compose the same parallel cells horizontally in the other raw order:
first transport the right cell across the source one-cell of the left cell,
then transport the left cell across the target one-cell of the right cell.
A strict interchange law may identify the two readings in a suitable
observation, but the free syntax retains both histories. -/
def horizontalLeftThenRight
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source middle target : base.Object}
    {first second : base.Hom source middle}
    {third fourth : base.Hom middle target}
    (left : Cell base Generator first second)
    (right : Cell base Generator third fourth) :
    Cell base Generator
      (base.compose first third) (base.compose second fourth) :=
  .vertical (.whiskerLeft first right) (.whiskerRight fourth left)

end Cell

/-! ## The initial cell algebra -/

/-- An interpretation of all five raw cell constructors in an arbitrary
parallel target family over the same retained one-cells. -/
structure Algebra (base : Base.{uObject, uHom})
    (Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator)
    (Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget) where
  onRefl : ∀ {source target} (path : base.Hom source target),
    Target path path
  onGenerator : ∀ {source target} {first second : base.Hom source target},
    Generator first second → Target first second
  onVertical : ∀ {source target}
      {first middle last : base.Hom source target},
    Target first middle → Target middle last → Target first last
  onWhiskerLeft : ∀ {source middle target}
      (prior : base.Hom source middle)
      {first second : base.Hom middle target},
    Target first second →
      Target (base.compose prior first) (base.compose prior second)
  onWhiskerRight : ∀ {source middle target}
      {first second : base.Hom source middle}
      (suffix : base.Hom middle target),
    Target first second →
      Target (base.compose first suffix) (base.compose second suffix)

namespace Algebra

/-- Structural recursion is the canonical interpretation of raw generated
cells. -/
def fold
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target) :
    {source target : base.Object} →
      {first second : base.Hom source target} →
        Cell base Generator first second → Target first second
  | _, _, _, _, .refl path => algebra.onRefl path
  | _, _, _, _, .generator evidence => algebra.onGenerator evidence
  | _, _, _, _, .vertical first second =>
      algebra.onVertical (fold algebra first) (fold algebra second)
  | _, _, _, _, .whiskerLeft prior cell =>
      algebra.onWhiskerLeft prior (fold algebra cell)
  | _, _, _, _, .whiskerRight suffix cell =>
      algebra.onWhiskerRight suffix (fold algebra cell)

@[simp] theorem fold_refl
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target)
    {source target} (path : base.Hom source target) :
    algebra.fold (Cell.refl path) = algebra.onRefl path :=
  rfl

@[simp] theorem fold_generator
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target)
    {source target} {first second : base.Hom source target}
    (evidence : Generator first second) :
    algebra.fold (Cell.generator evidence) = algebra.onGenerator evidence :=
  rfl

@[simp] theorem fold_vertical
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target)
    {source target} {first middle last : base.Hom source target}
    (earlier : Cell base Generator first middle)
    (later : Cell base Generator middle last) :
    algebra.fold (Cell.vertical earlier later) =
      algebra.onVertical (algebra.fold earlier) (algebra.fold later) :=
  rfl

@[simp] theorem fold_whiskerLeft
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target)
    {source middle target} (prior : base.Hom source middle)
    {first second : base.Hom middle target}
    (cell : Cell base Generator first second) :
    algebra.fold (Cell.whiskerLeft prior cell) =
      algebra.onWhiskerLeft prior (algebra.fold cell) :=
  rfl

@[simp] theorem fold_whiskerRight
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target)
    {source middle target} {first second : base.Hom source middle}
    (suffix : base.Hom middle target)
    (cell : Cell base Generator first second) :
    algebra.fold (Cell.whiskerRight suffix cell) =
      algebra.onWhiskerRight suffix (algebra.fold cell) :=
  rfl

end Algebra

/-! ## Existence and uniqueness of structural extensions -/

/-- A complete constructor-preserving interpretation of the generated cell
syntax. -/
structure Extension
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target) where
  onCell : {source target : base.Object} →
    {first second : base.Hom source target} →
      Cell base Generator first second → Target first second
  onRefl : ∀ {source target} (path : base.Hom source target),
    onCell (Cell.refl path) = algebra.onRefl path
  onGenerator : ∀ {source target} {first second : base.Hom source target}
    (evidence : Generator first second),
    onCell (Cell.generator evidence) = algebra.onGenerator evidence
  onVertical : ∀ {source target}
      {first middle last : base.Hom source target}
      (earlier : Cell base Generator first middle)
      (later : Cell base Generator middle last),
    onCell (Cell.vertical earlier later) =
      algebra.onVertical (onCell earlier) (onCell later)
  onWhiskerLeft : ∀ {source middle target}
      (prior : base.Hom source middle)
      {first second : base.Hom middle target}
      (cell : Cell base Generator first second),
    onCell (Cell.whiskerLeft prior cell) =
      algebra.onWhiskerLeft prior (onCell cell)
  onWhiskerRight : ∀ {source middle target}
      {first second : base.Hom source middle}
      (suffix : base.Hom middle target)
      (cell : Cell base Generator first second),
    onCell (Cell.whiskerRight suffix cell) =
      algebra.onWhiskerRight suffix (onCell cell)

namespace Extension

def canonical
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target) : Extension algebra where
  onCell := algebra.fold
  onRefl := Algebra.fold_refl algebra
  onGenerator := Algebra.fold_generator algebra
  onVertical := Algebra.fold_vertical algebra
  onWhiskerLeft := Algebra.fold_whiskerLeft algebra
  onWhiskerRight := Algebra.fold_whiskerRight algebra

theorem onCell_unique
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    {algebra : Algebra base Generator Target}
    (extension : Extension algebra) :
    ∀ {source target} {first second : base.Hom source target}
      (cell : Cell base Generator first second),
      extension.onCell cell = algebra.fold cell
  | _, _, _, _, .refl path => by
      simpa using extension.onRefl path
  | _, _, _, _, .generator evidence => by
      simpa using extension.onGenerator evidence
  | _, _, _, _, .vertical earlier later => by
      rw [extension.onVertical, Algebra.fold_vertical,
        onCell_unique extension earlier, onCell_unique extension later]
  | _, _, _, _, .whiskerLeft prior cell => by
      rw [extension.onWhiskerLeft, Algebra.fold_whiskerLeft,
        onCell_unique extension cell]
  | _, _, _, _, .whiskerRight suffix cell => by
      rw [extension.onWhiskerRight, Algebra.fold_whiskerRight,
        onCell_unique extension cell]

@[ext] theorem ext
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    {algebra : Algebra base Generator Target}
    {first second : Extension algebra}
    (cells : ∀ {source target} {left right : base.Hom source target}
      (cell : Cell base Generator left right),
      first.onCell cell = second.onCell cell) :
    first = second := by
  cases first with
  | mk firstCell firstRefl firstGenerator firstVertical firstLeft firstRight =>
      cases second with
      | mk secondCell secondRefl secondGenerator secondVertical secondLeft secondRight =>
          have cellEqual : @firstCell = @secondCell := by
            funext source target left right cell
            exact cells cell
          cases cellEqual
          rfl

theorem unique
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target)
    (extension : Extension algebra) :
    extension = canonical algebra := by
  apply Extension.ext
  intro source target first second cell
  exact extension.onCell_unique cell

instance
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target) : Unique (Extension algebra) where
  default := canonical algebra
  uniq extension := unique algebra extension

theorem contractible
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {Target : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTarget}
    (algebra : Algebra base Generator Target) :
    Nonempty (Extension algebra) ∧ Subsingleton (Extension algebra) :=
  ⟨⟨canonical algebra⟩, inferInstance⟩

end Extension

/-! ## Structural maps of generator families -/

def generatedAlgebra
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uOtherGenerator}
    (onGenerator : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second → TargetGenerator first second) :
    Algebra base SourceGenerator (Cell base TargetGenerator) where
  onRefl := Cell.refl
  onGenerator := fun evidence => Cell.generator (onGenerator evidence)
  onVertical := Cell.vertical
  onWhiskerLeft := Cell.whiskerLeft
  onWhiskerRight := Cell.whiskerRight

/-- A map of two-generators extends structurally to every raw cell. -/
def mapGenerators
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uOtherGenerator}
    (onGenerator : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second → TargetGenerator first second) :
    {source target : base.Object} →
      {first second : base.Hom source target} →
      Cell base SourceGenerator first second →
        Cell base TargetGenerator first second :=
  (generatedAlgebra onGenerator).fold

@[simp] theorem mapGenerators_refl
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uOtherGenerator}
    (onGenerator : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target} (path : base.Hom source target) :
    mapGenerators (SourceGenerator := SourceGenerator)
        (TargetGenerator := TargetGenerator) onGenerator
        (Cell.refl (Generator := SourceGenerator) path) =
      Cell.refl (Generator := TargetGenerator) path :=
  rfl

@[simp] theorem mapGenerators_generator
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uOtherGenerator}
    (onGenerator : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target} {first second : base.Hom source target}
    (evidence : SourceGenerator first second) :
    mapGenerators (SourceGenerator := SourceGenerator)
        (TargetGenerator := TargetGenerator) onGenerator
        (Cell.generator evidence) =
      Cell.generator (onGenerator evidence) :=
  rfl

/-! ## A refusing control: raw syntax has no silent unit quotient -/

namespace Canary

def base : Base where
  Object := Unit
  Hom := fun _ _ => Unit
  compose := fun _ _ => ()

inductive Generator : {source target : base.Object} →
    base.Hom source target → base.Hom source target → Type where
  | marked : Generator (source := ()) (target := ()) () ()

def marked : Cell base Generator (source := ()) (target := ()) () () :=
  .generator .marked

def leftPadded : Cell base Generator (source := ()) (target := ()) () () :=
  .vertical
    (Cell.refl (Generator := Generator) (source := ()) (target := ()) ())
    marked

/-- The free syntax retains the administrative identity cell rather than
pretending that bicategorical left-unit coherence is definitional. -/
theorem leftPadded_ne_marked : leftPadded ≠ marked := by
  intro equality
  cases equality

def nodeCountAlgebra :
    Algebra base Generator (fun {_ _} _ _ => Nat) where
  onRefl := by intros; exact 1
  onGenerator := by intros; exact 1
  onVertical := by intros; exact ‹Nat› + ‹Nat› + 1
  onWhiskerLeft := by intros; exact ‹Nat› + 1
  onWhiskerRight := by intros; exact ‹Nat› + 1

def nodeCount :
    Cell base Generator (source := ()) (target := ()) () () → Nat :=
  nodeCountAlgebra.fold

@[simp] theorem marked_nodeCount : nodeCount marked = 1 :=
  rfl

@[simp] theorem leftPadded_nodeCount : nodeCount leftPadded = 3 :=
  rfl

/-- Even with identical objects and one-cells, endpoint data cannot recover a
raw cell's construction history. -/
theorem no_endpoint_decoder :
    ¬ ∃ decode : PUnit → Nat,
      ∀ cell : Cell base Generator
        (source := ()) (target := ()) () (),
        decode PUnit.unit = nodeCount cell := by
  rintro ⟨decode, complete⟩
  have first := complete marked
  have second := complete leftPadded
  simp only [marked_nodeCount] at first
  simp only [leftPadded_nodeCount] at second
  omega

end Canary

/-! ## Axiom audit -/

#print axioms Extension.contractible
#print axioms mapGenerators_refl
#print axioms mapGenerators_generator
#print axioms Canary.leftPadded_ne_marked
#print axioms Canary.no_endpoint_decoder

end FreeWhiskeredCell
end Mettapedia.TypeTheory
