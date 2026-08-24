import Mettapedia.TypeTheory.FreeWhiskeredCell

/-!
# Reflection boundaries for free whiskered cells

The free-cell universal property gives a unique structural interpretation once
the five constructors are interpreted.  It does not imply that the resulting
interpretation is faithful.  This module isolates the additional capability
needed for reflection.

A pointwise map of authored two-generators induces a structural map of all raw
cells.  If the generator map has a pointwise retraction, then the induced cell
map has a structural retraction and is therefore injective.  Conversely, any
collision between two source generators immediately becomes a collision
between two distinct generated cells.  Thus faithfulness is earned from the
two-generator interpretation; it is not a consequence of initiality or of
endpoint agreement.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace FreeWhiskeredCell

universe uObject uHom uSourceGenerator uTargetGenerator uThirdGenerator

/-! ## Functoriality of structural generator maps -/

theorem mapGenerators_id
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uSourceGenerator}
    {source target : base.Object}
    {first second : base.Hom source target}
    (cell : Cell base Generator first second) :
    mapGenerators (fun evidence : Generator _ _ => evidence) cell = cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      exact congrArg₂ Cell.vertical earlierIH laterIH
  | whiskerLeft prior cell cellIH =>
      exact congrArg (Cell.whiskerLeft prior) cellIH
  | whiskerRight suffix cell cellIH =>
      exact congrArg (Cell.whiskerRight suffix) cellIH

theorem mapGenerators_comp
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uSourceGenerator}
    {MiddleGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTargetGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uThirdGenerator}
    (firstMap : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second → MiddleGenerator first second)
    (secondMap : ∀ {source target} {first second : base.Hom source target},
      MiddleGenerator first second → TargetGenerator first second)
    {source target : base.Object}
    {first second : base.Hom source target}
    (cell : Cell base SourceGenerator first second) :
    mapGenerators secondMap (mapGenerators firstMap cell) =
      mapGenerators (fun evidence => secondMap (firstMap evidence)) cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      exact congrArg₂ Cell.vertical earlierIH laterIH
  | whiskerLeft prior cell cellIH =>
      exact congrArg (Cell.whiskerLeft prior) cellIH
  | whiskerRight suffix cell cellIH =>
      exact congrArg (Cell.whiskerRight suffix) cellIH

/-! ## Split generator maps reflect complete cell history -/

/-- A fibrewise split embedding of authored two-generators.  The retraction is
indexed by the same parallel one-cells, so it cannot change endpoints while
recovering source evidence. -/
structure GeneratorRetraction
    (base : Base.{uObject, uHom})
    (SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uSourceGenerator)
    (TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTargetGenerator) where
  forward : ∀ {source target} {first second : base.Hom source target},
    SourceGenerator first second → TargetGenerator first second
  backward : ∀ {source target} {first second : base.Hom source target},
    TargetGenerator first second → SourceGenerator first second
  leftInverse : ∀ {source target} {first second : base.Hom source target}
    (evidence : SourceGenerator first second),
    backward (forward evidence) = evidence

namespace GeneratorRetraction

variable {base : Base.{uObject, uHom}}
variable {SourceGenerator : {source target : base.Object} →
  base.Hom source target → base.Hom source target → Type uSourceGenerator}
variable {TargetGenerator : {source target : base.Object} →
  base.Hom source target → base.Hom source target → Type uTargetGenerator}

/-- Structural interpretation induced by the forward generator map. -/
def map (retraction : GeneratorRetraction base SourceGenerator TargetGenerator)
    {source target : base.Object} {first second : base.Hom source target} :
    Cell base SourceGenerator first second →
      Cell base TargetGenerator first second :=
  mapGenerators retraction.forward

/-- Structural decoding induced by the pointwise generator retraction. -/
def retract
    (retraction : GeneratorRetraction base SourceGenerator TargetGenerator)
    {source target : base.Object} {first second : base.Hom source target} :
    Cell base TargetGenerator first second →
      Cell base SourceGenerator first second :=
  mapGenerators retraction.backward

/-- Retraction holds on the complete raw cell tree, not only on primitive
generators. -/
theorem retract_map
    (retraction : GeneratorRetraction base SourceGenerator TargetGenerator)
    {source target : base.Object} {first second : base.Hom source target}
    (cell : Cell base SourceGenerator first second) :
    retraction.retract (retraction.map cell) = cell := by
  rw [retract, map, mapGenerators_comp]
  have pointwise :
      (fun {source target} {first second : base.Hom source target}
          (evidence : SourceGenerator first second) =>
          retraction.backward (retraction.forward evidence)) =
        (fun {source target} {first second : base.Hom source target}
          (evidence : SourceGenerator first second) => evidence) := by
    funext source target first second evidence
    exact retraction.leftInverse evidence
  rw [pointwise]
  exact mapGenerators_id cell

/-- A split generator interpretation reflects equality of every generated
cell, including vertical association and whiskering history. -/
theorem map_injective
    (retraction : GeneratorRetraction base SourceGenerator TargetGenerator)
    {source target : base.Object} {first second : base.Hom source target} :
    Function.Injective
      (retraction.map (source := source) (target := target)
        (first := first) (second := second)) :=
  (Function.LeftInverse.injective fun cell => retraction.retract_map cell)

end GeneratorRetraction

/-! ## Necessary collision boundary -/

/-- Distinct primitive generators remain distinct as raw generated cells. -/
theorem generator_cells_ne
    {base : Base.{uObject, uHom}}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uSourceGenerator}
    {source target : base.Object} {first second : base.Hom source target}
    {left right : Generator first second} (different : left ≠ right) :
    Cell.generator (base := base) left ≠ Cell.generator right := by
  intro equality
  apply different
  injection equality

/-- A collision at the authored two-generator layer is already a collision of
the induced structural cell interpretation.  Initiality cannot repair it. -/
theorem mapGenerators_not_injective_of_generator_collision
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uSourceGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTargetGenerator}
    (onGenerator : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : base.Object} {first second : base.Hom source target}
    {left right : SourceGenerator first second}
    (different : left ≠ right)
    (collision : onGenerator left = onGenerator right) :
    ¬ Function.Injective
      (mapGenerators onGenerator :
        Cell base SourceGenerator first second →
          Cell base TargetGenerator first second) := by
  intro injective
  apply different
  have cellsEqual :
      (Cell.generator (base := base) left :
          Cell base SourceGenerator first second) =
        Cell.generator right := by
    apply injective
    simpa using congrArg (Cell.generator (base := base)) collision
  injection cellsEqual

/-! ## Exact equivalence as the strongest lossless case -/

/-- A pointwise equivalence of generators induces an exact equivalence of
complete raw cells. -/
def cellEquivOfGeneratorEquiv
    {base : Base.{uObject, uHom}}
    {SourceGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uSourceGenerator}
    {TargetGenerator : {source target : base.Object} →
      base.Hom source target → base.Hom source target →
        Type uTargetGenerator}
    (equivalence : ∀ {source target} {first second : base.Hom source target},
      SourceGenerator first second ≃ TargetGenerator first second)
    {source target : base.Object} (first second : base.Hom source target) :
    Cell base SourceGenerator first second ≃
      Cell base TargetGenerator first second where
  toFun := mapGenerators (fun evidence => equivalence evidence)
  invFun := mapGenerators (fun evidence => equivalence.symm evidence)
  left_inv := by
    intro cell
    rw [mapGenerators_comp]
    have pointwise :
        (fun {source target} {first second : base.Hom source target}
            (evidence : SourceGenerator first second) =>
            equivalence.symm (equivalence evidence)) =
          (fun {source target} {first second : base.Hom source target}
            (evidence : SourceGenerator first second) => evidence) := by
      funext source target first second evidence
      exact Equiv.symm_apply_apply _ evidence
    rw [pointwise]
    exact mapGenerators_id cell
  right_inv := by
    intro cell
    rw [mapGenerators_comp]
    have pointwise :
        (fun {source target} {first second : base.Hom source target}
            (evidence : TargetGenerator first second) =>
            equivalence (equivalence.symm evidence)) =
          (fun {source target} {first second : base.Hom source target}
            (evidence : TargetGenerator first second) => evidence) := by
      funext source target first second evidence
      exact Equiv.apply_symm_apply _ evidence
    rw [pointwise]
    exact mapGenerators_id cell

/-! ## A collision canary -/

namespace Canary

def collapseGenerator :
    FreeWhiskeredCell.Canary.Generator (source := ()) (target := ()) () () →
      Unit :=
  fun _ => ()

/-- A second source generator family with two distinguishable primitive
receipts at the same boundary. -/
inductive TwoGenerators :
    {source target : FreeWhiskeredCell.Canary.base.Object} →
      FreeWhiskeredCell.Canary.base.Hom source target →
      FreeWhiskeredCell.Canary.base.Hom source target → Type where
  | first : TwoGenerators (source := ()) (target := ()) () ()
  | second : TwoGenerators (source := ()) (target := ()) () ()

def collapseTwo
    {source target} {first second :
      FreeWhiskeredCell.Canary.base.Hom source target}
    (evidence : TwoGenerators first second) :
    FreeWhiskeredCell.Canary.Generator first second := by
  cases evidence <;> exact .marked

theorem primitive_receipts_distinct :
    (TwoGenerators.first : TwoGenerators (source := ()) (target := ()) () ()) ≠
      TwoGenerators.second := by
  intro equality
  cases equality

theorem collapsed_generated_cells_not_reflected :
    ¬ Function.Injective
      (mapGenerators collapseTwo :
        Cell FreeWhiskeredCell.Canary.base TwoGenerators
            (source := ()) (target := ()) () () →
          Cell FreeWhiskeredCell.Canary.base
            FreeWhiskeredCell.Canary.Generator () ()) :=
  mapGenerators_not_injective_of_generator_collision collapseTwo
    primitive_receipts_distinct rfl

end Canary

/-! ## Axiom audit -/

#print axioms mapGenerators_id
#print axioms mapGenerators_comp
#print axioms GeneratorRetraction.retract_map
#print axioms GeneratorRetraction.map_injective
#print axioms generator_cells_ne
#print axioms mapGenerators_not_injective_of_generator_collision
#print axioms cellEquivOfGeneratorEquiv
#print axioms Canary.collapsed_generated_cells_not_reflected

end FreeWhiskeredCell
end Mettapedia.TypeTheory
