import Mettapedia.GSLT.Core.GeneratedTwoCellUniversal
import Mettapedia.TypeTheory.FreeWhiskeredCellReflection

/-!
# Reflection of GSLT generated two-cells

The existing GSLT `GeneratedTwoCell` syntax is exactly equivalent to the
representation-independent free whiskered-cell syntax.  This module transports
the latter's reflection boundary back to GSLT routes.

A pointwise interpretation of authored two-generators always extends uniquely,
but it reflects complete cell history only after earning a retraction on those
generators.  Conversely, a primitive generator collision necessarily collapses
two distinct generated GSLT cells.  A pointwise generator equivalence yields
an exact equivalence of complete cells.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Ultrainfinite
namespace GeneratedTwoCellReflection

open Mettapedia.TypeTheory.FreeWhiskeredCell
open GeneratedTwoCellUniversal

universe uObject uStep uSourceGenerator uTargetGenerator

variable {Object : Type uObject}
variable {Step : Object → Object → Type uStep}
variable {SourceGenerator : {source target : Object} →
  Route Step source target → Route Step source target →
    Type uSourceGenerator}
variable {TargetGenerator : {source target : Object} →
  Route Step source target → Route Step source target →
    Type uTargetGenerator}

/-! ## Structural interpretation -/

/-- Interpret complete GSLT cells by mapping primitive two-generators and
retaining every raw constructor. -/
def mapGenerators
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target} :
    GeneratedTwoCell SourceGenerator first second →
      GeneratedTwoCell TargetGenerator first second
  | .refl route =>
      GeneratedTwoCell.refl (Generator := TargetGenerator) route
  | .generator evidence =>
      GeneratedTwoCell.generator (Generator := TargetGenerator)
        (onGenerator evidence)
  | .vertical earlier later =>
      GeneratedTwoCell.vertical (mapGenerators onGenerator earlier)
        (mapGenerators onGenerator later)
  | .whiskerLeft prior cell =>
      GeneratedTwoCell.whiskerLeft prior (mapGenerators onGenerator cell)
  | .whiskerRight suffix cell =>
      GeneratedTwoCell.whiskerRight suffix (mapGenerators onGenerator cell)

@[simp] theorem toCommon_mapGenerators
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target}
    (cell : GeneratedTwoCell SourceGenerator first second) :
    toCommon (mapGenerators onGenerator cell) =
      Mettapedia.TypeTheory.FreeWhiskeredCell.mapGenerators
        onGenerator (toCommon cell) := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      exact congrArg₂ Cell.vertical earlierIH laterIH
  | whiskerLeft prior cell cellIH =>
      exact congrArg (Cell.whiskerLeft prior) cellIH
  | whiskerRight suffix cell cellIH =>
      exact congrArg (Cell.whiskerRight suffix) cellIH

@[simp] theorem mapGenerators_generator
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target}
    (evidence : SourceGenerator first second) :
    mapGenerators onGenerator
        (GeneratedTwoCell.generator (Generator := SourceGenerator) evidence) =
      GeneratedTwoCell.generator (Generator := TargetGenerator)
        (onGenerator evidence) := by
  rfl

/-- The identity interpretation preserves the complete raw GSLT cell tree. -/
@[simp] theorem mapGenerators_id
    {Generator : {source target : Object} →
      Route Step source target → Route Step source target →
        Type uSourceGenerator}
    {source target : Object} {first second : Route Step source target}
    (cell : GeneratedTwoCell Generator first second) :
    mapGenerators
        (fun {source target} {first second : Route Step source target}
          (evidence : Generator first second) => evidence)
        cell = cell := by
  induction cell with
  | refl => rfl
  | generator => rfl
  | vertical earlier later earlierIH laterIH =>
      exact congrArg₂ GeneratedTwoCell.vertical earlierIH laterIH
  | whiskerLeft prior cell cellIH =>
      exact congrArg (GeneratedTwoCell.whiskerLeft prior) cellIH
  | whiskerRight suffix cell cellIH =>
      exact congrArg (GeneratedTwoCell.whiskerRight suffix) cellIH

/-! ## Earned reflection -/

/-- A fibrewise split map of GSLT two-generators.  This route-indexed record
is the public GSLT capability; its structural action agrees with the common
free-cell retraction through `toCommon_mapGenerators`. -/
structure GeneratorRetraction
    {Object : Type uObject}
    (Step : Object → Object → Type uStep)
    (SourceGenerator : {source target : Object} →
      Route Step source target → Route Step source target →
        Type uSourceGenerator)
    (TargetGenerator : {source target : Object} →
      Route Step source target → Route Step source target →
        Type uTargetGenerator) where
  forward : ∀ {source target} {first second : Route Step source target},
    SourceGenerator first second → TargetGenerator first second
  backward : ∀ {source target} {first second : Route Step source target},
    TargetGenerator first second → SourceGenerator first second
  leftInverse : ∀ {source target} {first second : Route Step source target}
    (evidence : SourceGenerator first second),
    backward (forward evidence) = evidence

namespace GeneratorRetraction

/-- Mapping complete cells forward and then structurally backward recovers
the original cell, including all vertical and whiskering history. -/
theorem retract_map
    (retraction : GeneratorRetraction Step SourceGenerator TargetGenerator)
    {source target : Object} {first second : Route Step source target}
    (cell : GeneratedTwoCell SourceGenerator first second) :
    mapGenerators retraction.backward
        (mapGenerators retraction.forward cell) = cell := by
  induction cell with
  | refl => rfl
  | generator evidence =>
      exact congrArg
        (GeneratedTwoCell.generator (Generator := SourceGenerator))
        (retraction.leftInverse evidence)
  | vertical earlier later earlierIH laterIH =>
      exact congrArg₂ GeneratedTwoCell.vertical earlierIH laterIH
  | whiskerLeft prior cell cellIH =>
      exact congrArg (GeneratedTwoCell.whiskerLeft prior) cellIH
  | whiskerRight suffix cell cellIH =>
      exact congrArg (GeneratedTwoCell.whiskerRight suffix) cellIH

end GeneratorRetraction

/-- A pointwise generator retraction reflects equality of complete GSLT
generated cells. -/
theorem mapGenerators_injective
    (retraction : GeneratorRetraction Step SourceGenerator TargetGenerator)
    {source target : Object} {first second : Route Step source target} :
    Function.Injective
      (mapGenerators retraction.forward :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) := by
  exact (Function.LeftInverse.injective fun cell => retraction.retract_map cell)

/-- Any collision of authored two-generators defeats reflection of complete
GSLT cells.  Uniqueness of structural extension does not alter this result. -/
theorem mapGenerators_not_injective_of_generator_collision
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target}
    {left right : SourceGenerator first second}
    (different : left ≠ right)
    (collision : onGenerator left = onGenerator right) :
    ¬ Function.Injective
      (mapGenerators onGenerator :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second) := by
  intro injective
  apply different
  have cellsEqual :
      (GeneratedTwoCell.generator left :
          GeneratedTwoCell SourceGenerator first second) =
        GeneratedTwoCell.generator right := by
    apply injective
    rw [mapGenerators_generator, mapGenerators_generator, collision]
  injection cellsEqual

/-! ## Exact lossless interpretation -/

/-- Pointwise equivalence of authored two-generators is exactly sufficient to
transport complete generated cells in both directions. -/
def equivalenceOfGeneratorEquiv
    (generatorEquiv :
      ∀ {source target} {first second : Route Step source target},
        SourceGenerator first second ≃ TargetGenerator first second)
    {source target : Object} (first second : Route Step source target) :
    GeneratedTwoCell SourceGenerator first second ≃
      GeneratedTwoCell TargetGenerator first second :=
  (equivalence first second).trans
    ((Mettapedia.TypeTheory.FreeWhiskeredCell.cellEquivOfGeneratorEquiv
      (base := routeBase Object Step)
      (SourceGenerator := SourceGenerator)
      (TargetGenerator := TargetGenerator)
      generatorEquiv first second).trans (equivalence first second).symm)

/-! ## GSLT collision canary -/

namespace Canary

open GeneratedTwoCellUniversal.Canary

inductive DuplicateOptimizationGenerator :
    {source target : Node} →
      Route Edge source target → Route Edge source target → Type where
  | first : DuplicateOptimizationGenerator detourRoute directRoute
  | second : DuplicateOptimizationGenerator detourRoute directRoute

def collapseDuplicate :
    ∀ {source target} {first second : Route Edge source target},
      DuplicateOptimizationGenerator first second →
        OptimizationGenerator first second := by
  intro source target first second evidence
  cases evidence <;> exact .collapse

theorem duplicate_generators_distinct :
    (DuplicateOptimizationGenerator.first :
        DuplicateOptimizationGenerator detourRoute directRoute) ≠
      DuplicateOptimizationGenerator.second := by
  intro equality
  cases equality

/-- Two authored optimization receipts with identical routes become two
distinct generated cells, and a target interpretation that identifies the
receipts is provably non-reflecting. -/
theorem collapsed_optimization_cells_not_reflected :
    ¬ Function.Injective
      (mapGenerators collapseDuplicate :
        GeneratedTwoCell DuplicateOptimizationGenerator
            detourRoute directRoute →
          GeneratedTwoCell OptimizationGenerator
            detourRoute directRoute) :=
  mapGenerators_not_injective_of_generator_collision collapseDuplicate
    duplicate_generators_distinct rfl

end Canary

/-! ## Axiom audit -/

#print axioms toCommon_mapGenerators
#print axioms mapGenerators_generator
#print axioms mapGenerators_id
#print axioms GeneratorRetraction.retract_map
#print axioms mapGenerators_injective
#print axioms mapGenerators_not_injective_of_generator_collision
#print axioms equivalenceOfGeneratorEquiv
#print axioms Canary.collapsed_optimization_cells_not_reflected

end GeneratedTwoCellReflection
end Mettapedia.GSLT.Ultrainfinite
