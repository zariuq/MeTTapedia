import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mettapedia.TypeTheory.LocallyThinWhiskeredCellBicategory

/-!
# Mapping out of a locally thin authored-cell extension

Let `B` be a bicategory and let `Authored` be a family of additional parallel
two-generators between its one-cells.  A pseudofunctor from `B` whose image is
locally thin on two-cells, together with an image for each authored generator,
extends to a pseudofunctor from the locally thin authored-cell extension.

The construction is explicit.  Structural generators use the original
pseudofunctor's action, authored generators use the supplied action, and raw
cells are interpreted by vertical composition and pseudofunctor-corrected
whiskering.  Local thinness on the image makes this interpretation invariant
under the pointwise reflection and makes the descended action unique on every
fixed parallel-cell fibre.  The ambient target need not be locally thin.

This is the fixed-object-and-one-cell mapping-out property needed by the mode
theory.  It does not claim an equivalence between bicategories of all
pseudofunctors and transformations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace LocallyThinWhiskeredCellMappingOut

open CategoryTheory CategoryTheory.Bicategory
open FreeWhiskeredCell
open LocallyThinCellReflection
open LocallyThinWhiskeredCellBicategory

universe uObject uHom uCell uGenerator
universe uTargetObject uTargetHom uTargetCell

variable {B : Type uObject} [Bicategory.{uCell, uHom} B]
variable (Authored : {source target : B} →
  (source ⟶ target) → (source ⟶ target) → Type uGenerator)

variable {C : Type uTargetObject}
  [Bicategory.{uTargetCell, uTargetHom} C]

/-! ## Raw and descended cell interpretation -/

/-- The target parallel-cell family induced by a pseudofunctor. -/
abbrev TargetCell (baseFunctor : B ⥤ᵖ C)
    {source target : B} (first second : source ⟶ target) :=
  baseFunctor.map first ⟶ baseFunctor.map second

/-- The exact local-thinness hypothesis needed by the extension: only
two-cells between one-cells in the pseudofunctor image must be unique. -/
abbrev ImageCellSubsingleton (baseFunctor : B ⥤ᵖ C) :=
  ∀ {source target : B} (first second : source ⟶ target),
    Subsingleton (TargetCell baseFunctor first second)

/-- Interpret structural and authored cells in a locally thin target.  The
pseudofunctor comparison isomorphisms correct the boundaries of whiskering. -/
def targetAlgebra
    (baseFunctor : B ⥤ᵖ C)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second) :
    FreeWhiskeredCell.Algebra (oneCellBase B)
      (ExtendedGenerator Authored) (TargetCell baseFunctor) where
  onRefl := fun path => 𝟙 (baseFunctor.map path)
  onGenerator := by
    intro source target first second generator
    cases generator with
    | structural structural => exact baseFunctor.map₂ structural
    | authored authored => exact onAuthored authored
  onVertical := fun earlier later => earlier ≫ later
  onWhiskerLeft := @fun _source _middle _target prior first second cell =>
    (baseFunctor.mapComp prior first).hom ≫
      baseFunctor.map prior ◁ cell ≫
      (baseFunctor.mapComp prior second).inv
  onWhiskerRight := @fun _source _middle _target first second suffix cell =>
    (baseFunctor.mapComp first suffix).hom ≫
      cell ▷ baseFunctor.map suffix ≫
      (baseFunctor.mapComp second suffix).inv

/-- Interpret every raw structural/authored cell in the target. -/
def interpretRaw
    (baseFunctor : B ⥤ᵖ C)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} {first second : source ⟶ target} :
    RawGeneratedCell Authored first second →
      TargetCell baseFunctor first second :=
  (targetAlgebra Authored baseFunctor onAuthored).fold

/-- A locally thin target identifies all interpretations in one raw cell
fibre. -/
theorem interpretRaw_fibreInvariant
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} (first second : source ⟶ target) :
    FibreInvariant
      (interpretRaw (source := source) (target := target)
        (first := first) (second := second)
        Authored baseFunctor onAuthored) := by
  intro left right
  exact (imageThin first second).elim _ _

/-- Descend the raw interpretation through the locally thin cell reflection. -/
def interpretThin
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} {first second : source ⟶ target} :
    ThinCell Authored first second → TargetCell baseFunctor first second :=
  descend (interpretRaw Authored baseFunctor onAuthored)
    (interpretRaw_fibreInvariant Authored baseFunctor imageThin onAuthored
      first second)

@[simp] theorem interpretThin_reflect
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} {first second : source ⟶ target}
    (cell : RawGeneratedCell Authored first second) :
    interpretThin Authored baseFunctor imageThin onAuthored (reflect cell) =
      interpretRaw Authored baseFunctor onAuthored cell :=
  rfl

/-! ## The pseudofunctor extension -/

/-- Extend a base pseudofunctor and its authored-generator action across the
locally thin authored-cell bicategory. -/
def extend
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second) :
    Extension B Authored ⥤ᵖ C where
  obj object := baseFunctor.obj object.as
  map path := baseFunctor.map path.as
  map₂ cell := interpretThin Authored baseFunctor imageThin onAuthored cell
  mapId object := baseFunctor.mapId object.as
  mapComp first second := baseFunctor.mapComp first.as second.as
  map₂_id := by
    intro source target path
    exact (imageThin path.as path.as).elim _ _
  map₂_comp := by
    intro source target first middle last earlier later
    exact (imageThin first.as last.as).elim _ _
  map₂_whisker_left := by
    intro source middle target prior first second cell
    exact (imageThin (prior.as ≫ first.as) (prior.as ≫ second.as)).elim _ _
  map₂_whisker_right := by
    intro source middle target first second cell suffix
    exact (imageThin (first.as ≫ suffix.as) (second.as ≫ suffix.as)).elim _ _
  map₂_associator := by
    intro first second third fourth left middle right
    exact (imageThin ((left.as ≫ middle.as) ≫ right.as)
      (left.as ≫ (middle.as ≫ right.as))).elim _ _
  map₂_left_unitor := by
    intro source target path
    exact (imageThin ((𝟙 source.as) ≫ path.as) path.as).elim _ _
  map₂_right_unitor := by
    intro source target path
    exact (imageThin (path.as ≫ (𝟙 target.as)) path.as).elim _ _

@[simp] theorem extend_obj
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    (object : Extension B Authored) :
    (extend Authored baseFunctor imageThin onAuthored).obj object =
      baseFunctor.obj object.as :=
  rfl

@[simp] theorem extend_map
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : Extension B Authored} (path : source ⟶ target) :
    (extend Authored baseFunctor imageThin onAuthored).map path =
      baseFunctor.map path.as :=
  rfl

@[simp] theorem extend_map_structural
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} {first second : source ⟶ target}
    (cell : first ⟶ second) :
    (extend Authored baseFunctor imageThin onAuthored).map₂
        (ofStructural (Authored := Authored) cell) = baseFunctor.map₂ cell :=
  rfl

@[simp] theorem extend_map_authored
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} {first second : source ⟶ target}
    (cell : Authored first second) :
    (extend Authored baseFunctor imageThin onAuthored).map₂
        (ofAuthored (B := B) cell) = onAuthored cell :=
  rfl

/-! ## Fibrewise uniqueness and a negative control -/

/-- Once the object and one-cell action is fixed, a locally thin target admits
only one cell action on each reflected parallel-cell fibre. -/
theorem interpretThin_unique
    (baseFunctor : B ⥤ᵖ C)
    (imageThin : ImageCellSubsingleton baseFunctor)
    (onAuthored : {source target : B} →
      {first second : source ⟶ target} →
        Authored first second → TargetCell baseFunctor first second)
    {source target : B} {first second : source ⟶ target}
    (candidate : ThinCell Authored first second →
      TargetCell baseFunctor first second) :
    candidate = interpretThin Authored baseFunctor imageThin onAuthored := by
  funext cell
  exact (imageThin first second).elim _ _

/-- The local-thinness hypothesis is real: a two-valued cell observation can
distinguish representatives and therefore has no descended action. -/
theorem nonthin_bool_observation_has_no_descent :
    ¬ FactorsThrough (fun value : Bool => value) :=
  LocallyThinCellReflection.Canaries.bool_identity_does_not_factor

/-! ## Axiom audit -/

#print axioms interpretRaw_fibreInvariant
#print axioms extend
#print axioms extend_map_structural
#print axioms extend_map_authored
#print axioms interpretThin_unique
#print axioms nonthin_bool_observation_has_no_descent

end LocallyThinWhiskeredCellMappingOut
end Mettapedia.TypeTheory
