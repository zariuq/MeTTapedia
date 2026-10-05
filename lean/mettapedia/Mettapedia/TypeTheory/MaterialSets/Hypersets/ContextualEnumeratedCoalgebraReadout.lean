import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraComparisons
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebras

/-!
# Constructed readouts for uniformly enumerated contextual coalgebras

A possibly larger coalgebra with authored small future-branch enumerations
has an actual readout in the constructed universal small-coalgebra recipient.
Each value is read through its generated small rooted coalgebra. Complete
matching pullbacks prove that these rooted readings agree on common
endpoints, which establishes context naturality and the full coalgebra law.

The enumerations are actual input data. Mere pointwise existence of covers
is not turned into a uniform selection, and indexed finality and internal
Collection are not claimed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open ContextualSmallCoalgebraGenerators
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v
variable {D : Type u} [Category.{u} D] (A : D ⥤ Type v)
variable (source : NaturalHom A (family A))
variable (enumeration : ∀ point argument, Enumeration (source.app point argument).val)

def generatedCode (root : ContextualGeneratedCoalgebras.State A) : Code D :=
  ⟨ContextualGeneratedCoalgebras.family A source enumeration root,
    ContextualGeneratedCoalgebras.generatedCoalgebra A source enumeration root⟩

def value (point : D) (argument : A.obj point) : (quotient (D := D)).obj point :=
  (canonical (generatedCode A source enumeration ⟨point, argument⟩)).app point
    (ContextualGeneratedCoalgebras.rootMember A source enumeration ⟨point, argument⟩)

theorem generated_value (root : ContextualGeneratedCoalgebras.State A) (point : D)
    (receipt : (generatedCode A source enumeration root).carrier.obj point) :
    (canonical (generatedCode A source enumeration root)).app point receipt =
      value A source enumeration point
        ((ContextualGeneratedCoalgebras.endpoint A source enumeration root).app point receipt) := by
  let observed := (ContextualGeneratedCoalgebras.endpoint A source enumeration root).app point receipt
  exact ContextualSmallCoalgebraComparisons.same_reading
    (generatedCode A source enumeration root) (generatedCode A source enumeration ⟨point, observed⟩)
    source (ContextualGeneratedCoalgebras.endpoint A source enumeration root)
    (ContextualGeneratedCoalgebras.endpoint A source enumeration ⟨point, observed⟩)
    (ContextualGeneratedCoalgebras.coalgebra_square A source enumeration root)
    (ContextualGeneratedCoalgebras.coalgebra_square A source enumeration ⟨point, observed⟩)
    point receipt (ContextualGeneratedCoalgebras.rootMember A source enumeration ⟨point, observed⟩)
    (ContextualGeneratedCoalgebras.endpoint_root A source enumeration ⟨point, observed⟩).symm

theorem value_natural {first second : D} (step : first ⟶ second) (argument : A.obj first) :
    (quotient (D := D)).map step (value A source enumeration first argument) =
      value A source enumeration second (A.map step argument) := by
  let root : ContextualGeneratedCoalgebras.State A := ⟨first, argument⟩
  let receipt := ContextualGeneratedCoalgebras.rootMember A source enumeration root
  let moved := (generatedCode A source enumeration root).carrier.map step receipt
  have endpointEq :
      (ContextualGeneratedCoalgebras.endpoint A source enumeration root).app second moved =
        A.map step argument :=
    ((ContextualGeneratedCoalgebras.endpoint A source enumeration root).naturality step receipt).symm.trans
      (congrArg (A.map step) (ContextualGeneratedCoalgebras.endpoint_root A source enumeration root))
  exact ((canonical (generatedCode A source enumeration root)).naturality step receipt).trans
    ((generated_value A source enumeration root second moved).trans
      (congrArg (value A source enumeration second) endpointEq))

def readout : NaturalHom A (quotient (D := D)) where
  app := value A source enumeration
  naturality := value_natural A source enumeration

theorem generated_readout (root : ContextualGeneratedCoalgebras.State A) :
    canonical (generatedCode A source enumeration root) =
      (ContextualGeneratedCoalgebras.endpoint A source enumeration root).comp (readout A source enumeration) := by
  apply NaturalHom.ext
  exact generated_value A source enumeration root

theorem child_image (point : D) (argument : A.obj point) :
    imagePower (readout A source enumeration) point (source.app point argument) =
      imagePower (canonical (generatedCode A source enumeration ⟨point, argument⟩)) point
        ((generatedCode A source enumeration ⟨point, argument⟩).coalgebra.app point
          (ContextualGeneratedCoalgebras.rootMember A source enumeration ⟨point, argument⟩)) := by
  let root : ContextualGeneratedCoalgebras.State A := ⟨point, argument⟩
  let generated := generatedCode A source enumeration root
  let endpoint := ContextualGeneratedCoalgebras.endpoint A source enumeration root
  let receipt := ContextualGeneratedCoalgebras.rootMember A source enumeration root
  have endpointImage := congrArg
    (fun operation : NaturalHom generated.carrier (family A) => operation.app point receipt)
    (ContextualGeneratedCoalgebras.coalgebra_square A source enumeration root)
  have originalImage : imagePower endpoint point (generated.coalgebra.app point receipt) =
      source.app point argument := endpointImage.trans
    (congrArg (source.app point) (ContextualGeneratedCoalgebras.endpoint_root A source enumeration root))
  calc
    imagePower (readout A source enumeration) point (source.app point argument) =
        imagePower (readout A source enumeration) point
          (imagePower endpoint point (generated.coalgebra.app point receipt)) :=
      congrArg (imagePower (readout A source enumeration) point) originalImage.symm
    _ = imagePower (endpoint.comp (readout A source enumeration)) point
          (generated.coalgebra.app point receipt) :=
      imagePower_comp endpoint (readout A source enumeration) point (generated.coalgebra.app point receipt)
    _ = imagePower (canonical generated) point (generated.coalgebra.app point receipt) :=
      congrArg (fun operation : NaturalHom generated.carrier (quotient (D := D)) =>
        imagePower operation point (generated.coalgebra.app point receipt))
          (generated_readout A source enumeration root).symm

theorem readout_square :
    source.comp (imageHom (readout A source enumeration)) =
      (readout A source enumeration).comp quotientCoalgebra := by
  apply NaturalHom.ext
  intro point argument
  exact (child_image A source enumeration point argument).trans
    (congrArg (fun operation : NaturalHom (generatedCode A source enumeration ⟨point, argument⟩).carrier
      (family (quotient (D := D))) => operation.app point
        (ContextualGeneratedCoalgebras.rootMember A source enumeration ⟨point, argument⟩))
      (canonical_square (generatedCode A source enumeration ⟨point, argument⟩)))

theorem value_eq_iff (point : D) (first second : A.obj point) :
    value A source enumeration point first = value A source enumeration point second ↔
      ContextualCoalgebraBisimulation.Bisimilar source point first second := by
  constructor
  · intro same
    apply ContextualCoalgebraBisimulation.bisimilar_reflected source (readout A source enumeration)
      quotientCoalgebra (readout_square A source enumeration)
    change ContextualCoalgebraBisimulation.Bisimilar quotientCoalgebra point
      (value A source enumeration point first) (value A source enumeration point second)
    rw [same]
    exact ContextualCoalgebraBisimulation.bisimilar_refl quotientCoalgebra point _
  · intro related
    exact quotient_separated point _ _
      (ContextualCoalgebraBisimulation.bisimilar_preserved source (readout A source enumeration)
        quotientCoalgebra (readout_square A source enumeration) related)

include enumeration in
theorem unique_readout : ∃! operation : NaturalHom A (quotient (D := D)),
    source.comp (imageHom operation) = operation.comp quotientCoalgebra := by
  refine ⟨readout A source enumeration, readout_square A source enumeration, ?_⟩
  intro candidate square
  exact maps_equal_into_separated source quotientCoalgebra candidate (readout A source enumeration)
    square (readout_square A source enumeration) quotient_separated

theorem readout_enumeration_independent
    (other : ∀ point argument, Enumeration (source.app point argument).val) :
    readout A source enumeration = readout A source other :=
  maps_equal_into_separated source quotientCoalgebra (readout A source enumeration)
    (readout A source other) (readout_square A source enumeration)
    (readout_square A source other) quotient_separated

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout
