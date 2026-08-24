import Mettapedia.GSLT.LanguageDef.GSLTILUniversalStructure
import Mettapedia.GSLT.Core.GeneratedTwoCellReflection

/-!
# The strongest true generated-cell reflection boundary for GSLT-IL

Free extension and faithful interpretation are different capabilities.  An
authored interpretation always extends uniquely over reflexivity, vertical
composition, and whiskering.  It reflects the resulting proof-relevant cell
history only when its interpretation of primitive two-generators earns
additional structure.

A fibrewise retraction of primitive generators is sufficient for faithfulness
of every complete generated cell.  A fibrewise equivalence gives an exact
equivalence of complete cells.  Conversely, one collision of distinct
primitive generators forces non-faithfulness, even though the structural
extension remains contractible.  This is the capability boundary used by the
layered GSLT-IL waist: initiality supplies interpretation; split or invertible
generator evidence separately supplies reflection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.GeneratedCellReflection

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellUniversal
open Mettapedia.TypeTheory.FreeWhiskeredCell

universe uObject uStep uSourceGenerator uTargetGenerator

variable {Object : Type uObject}
variable {Step : Object → Object → Type uStep}
variable {SourceGenerator : {source target : Object} →
  Route Step source target → Route Step source target →
    Type uSourceGenerator}
variable {TargetGenerator : {source target : Object} →
  Route Step source target → Route Step source target →
    Type uTargetGenerator}

/-! ## The capability, its sufficient witness, and its exact case -/

/-- A primitive-generator interpretation reflects generated cells when it is
injective on every complete cell fibre, including vertical and whiskering
history. -/
def ReflectsGeneratedCells
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second) : Prop :=
  ∀ {source target : Object} (first second : Route Step source target),
    Function.Injective
      (Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.mapGenerators
        onGenerator :
        GeneratedTwoCell SourceGenerator first second →
          GeneratedTwoCell TargetGenerator first second)

/-- A split interpretation of primitive two-generators reflects all complete
generated-cell histories. -/
theorem reflectsGeneratedCells_of_generatorRetraction
    (retraction :
      Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.GeneratorRetraction
      Step SourceGenerator TargetGenerator) :
    ReflectsGeneratedCells
      (Object := Object) (Step := Step)
      (SourceGenerator := SourceGenerator)
      (TargetGenerator := TargetGenerator)
      (fun {source target} {first second : Route Step source target}
        (evidence : SourceGenerator first second) =>
          retraction.forward (source := source) (target := target)
            (first := first) (second := second) evidence) := by
  intro source target first second
  simpa only [] using
    Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.mapGenerators_injective
      retraction

/-- The identity interpretation is the refusing positive control: raw
generated-cell syntax reflects itself without imposing coherence equations. -/
theorem identity_reflectsGeneratedCells :
    ReflectsGeneratedCells
      (fun {source target} {first second : Route Step source target}
        (evidence : SourceGenerator first second) => evidence) := by
  intro source target first second left right equality
  simpa only
    [Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.mapGenerators_id]
    using equality

/-- A pointwise equivalence of primitive generators yields an exact
equivalence, not merely injectivity, of complete generated cells. -/
def exactGeneratedCellEquivalence
    (generatorEquiv :
      ∀ {source target} {first second : Route Step source target},
        SourceGenerator first second ≃ TargetGenerator first second)
    {source target : Object} (first second : Route Step source target) :
    GeneratedTwoCell SourceGenerator first second ≃
      GeneratedTwoCell TargetGenerator first second :=
  Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.equivalenceOfGeneratorEquiv
    generatorEquiv first second

/-! ## Initiality does not imply reflection -/

/-- Every primitive-generator interpretation has a contractible space of
constructor-preserving extensions to the common free-cell syntax. -/
theorem structuralExtension_contractible
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second) :
    Nonempty
        (Extension
          (generatedAlgebra
            (base := routeBase Object Step)
            (SourceGenerator := SourceGenerator)
            (TargetGenerator := TargetGenerator)
            onGenerator)) ∧
      Subsingleton
        (Extension
          (generatedAlgebra
            (base := routeBase Object Step)
            (SourceGenerator := SourceGenerator)
            (TargetGenerator := TargetGenerator)
            onGenerator)) :=
  Extension.contractible _

/-- One primitive collision is enough to refute complete-cell reflection. -/
theorem not_reflectsGeneratedCells_of_generator_collision
    (onGenerator : ∀ {source target} {first second : Route Step source target},
      SourceGenerator first second → TargetGenerator first second)
    {source target : Object} {first second : Route Step source target}
    {left right : SourceGenerator first second}
    (different : left ≠ right)
    (collision : onGenerator left = onGenerator right) :
    ¬ ReflectsGeneratedCells
      (Object := Object) (Step := Step)
      (SourceGenerator := SourceGenerator)
      (TargetGenerator := TargetGenerator)
      onGenerator := by
  intro reflects
  exact
    Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.mapGenerators_not_injective_of_generator_collision
      (Object := Object) (Step := Step)
      (SourceGenerator := SourceGenerator)
      (TargetGenerator := TargetGenerator)
      onGenerator different collision (reflects first second)

/-! ## A permanent GSLT-IL canary -/

namespace Canary

open Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellUniversal.Canary
open Mettapedia.GSLT.Ultrainfinite.GeneratedTwoCellReflection.Canary

/-- Unique structural extension does not entail faithful interpretation.  The
same primitive-collision interpretation has a contractible extension space
and provably fails to reflect complete GSLT cells. -/
theorem unique_extension_does_not_imply_reflection :
    (Nonempty
        (Extension
          (generatedAlgebra
            (base := routeBase Node Edge)
            (SourceGenerator := DuplicateOptimizationGenerator)
            (TargetGenerator := OptimizationGenerator)
            collapseDuplicate)) ∧
      Subsingleton
        (Extension
          (generatedAlgebra
            (base := routeBase Node Edge)
            (SourceGenerator := DuplicateOptimizationGenerator)
            (TargetGenerator := OptimizationGenerator)
            collapseDuplicate))) ∧
    ¬ ReflectsGeneratedCells
      (Object := Node) (Step := Edge)
      (SourceGenerator := DuplicateOptimizationGenerator)
      (TargetGenerator := OptimizationGenerator)
      collapseDuplicate := by
  constructor
  · exact structuralExtension_contractible collapseDuplicate
  · exact not_reflectsGeneratedCells_of_generator_collision
      collapseDuplicate duplicate_generators_distinct rfl

end Canary

/-! ## Axiom audit -/

#print axioms reflectsGeneratedCells_of_generatorRetraction
#print axioms identity_reflectsGeneratedCells
#print axioms exactGeneratedCellEquivalence
#print axioms structuralExtension_contractible
#print axioms not_reflectsGeneratedCells_of_generator_collision
#print axioms Canary.unique_extension_does_not_imply_reflection

end Mettapedia.GSLT.LanguageDef.GSLTIL.GeneratedCellReflection
