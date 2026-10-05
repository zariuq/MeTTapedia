import Mettapedia.GSLT.Logic.ContextualObservedMaterialFamily
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

/-!
# Constructive material interpretation of originally small observed executions

The constructed all-small-coalgebra recipient interprets an authored
execution and its observed quotient over the same context category. The
two actual coalgebra maps commute by separated-target uniqueness. Retaining
the observed class preserves exactly the declared atomic observations;
forgetting that class is adequate precisely when ordinary contextual
bisimilarity already preserves those observations.

Every source here has its actual carrier at the original context universe.
The recipient and its collecting graph live at the next universe. No
representative or branch enumeration is selected from mere existence.
This source-class universal property does not assert full ambient or
slice-indexed finality, or unrestricted witness Collection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ConstructiveObservedMaterialInterpretation

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))

abbrev recipient := ContextualSmallCoalgebraMaterialCarrier.classFamily worlds arrows
abbrev unfold := ContextualSmallCoalgebraMaterialCoalgebra.classCoalgebra worlds arrows

def readout (source : NaturalHom A (CoveredFuturePowerFamilies.family A)) :
    NaturalHom A (recipient worlds arrows) :=
  ContextualSmallCoalgebraMaterialCoalgebra.smallReadout worlds arrows ⟨A, source⟩

theorem readout_square (source : NaturalHom A (CoveredFuturePowerFamilies.family A)) :
    source.comp (CoveredFuturePowerFunctor.imageHom (readout worlds arrows source)) =
      (readout worlds arrows source).comp (unfold worlds arrows) :=
  ContextualSmallCoalgebraMaterialCoalgebra.smallReadout_square worlds arrows ⟨A, source⟩

theorem unique_readout (source : NaturalHom A (CoveredFuturePowerFamilies.family A)) :
    ∃! operation : NaturalHom A (recipient worlds arrows),
      source.comp (CoveredFuturePowerFunctor.imageHom operation) =
        operation.comp (unfold worlds arrows) :=
  ContextualSmallCoalgebraMaterialCoalgebra.unique_smallReadout worlds arrows ⟨A, source⟩

theorem readout_kernel (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (point : D) (first second : A.obj point) :
    (readout worlds arrows source).app point first =
        (readout worlds arrows source).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar source point first second :=
  ContextualSmallCoalgebraMaterialCoalgebra.smallReadout_eq_iff worlds arrows ⟨A, source⟩ point first second

theorem readout_future (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (point : D) (argument : A.obj point) (future : PowerClassPresheafBaseChange.Future.Objects point)
    (child : (recipient worlds arrows).obj future.1) :
    ((unfold worlds arrows).app point ((readout worlds arrows source).app point argument)).val.holds
        ⟨future, child⟩ ↔
      ∃ original : A.obj future.1, (readout worlds arrows source).app future.1 original = child ∧
        (source.app point argument).val.holds ⟨future, original⟩ :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth source (readout worlds arrows source)
    (unfold worlds arrows) (readout_square worlds arrows source) point argument future child

variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (atomCoding : ArgumentCoding Atom)

abbrev observedClasses := ContextualObservedMaterialFamily.classes source atoms worlds arrows atomCoding
abbrev observedProjection := ContextualObservedMaterialFamily.classObservation source atoms worlds arrows atomCoding
abbrev observedCoalgebra := ContextualObservedMaterialFamily.classCoalgebra source atoms worlds arrows atomCoding

def classReadout : NaturalHom (observedClasses worlds arrows source atoms atomCoding) (recipient worlds arrows) :=
  readout worlds arrows (observedCoalgebra worlds arrows source atoms atomCoding)

theorem source_class_square :
    (observedProjection worlds arrows source atoms atomCoding).comp
      (classReadout worlds arrows source atoms atomCoding) = readout worlds arrows source :=
  ContextualSmallCoalgebraGenerators.maps_equal_into_separated source (unfold worlds arrows) _ _
    (ContextualSmallCoalgebraComparisons.compose_square source
      (observedCoalgebra worlds arrows source atoms atomCoding) (unfold worlds arrows) _ _
      (ContextualObservedMaterialFamily.classObservation_square source atoms worlds arrows atomCoding)
      (readout_square worlds arrows _))
    (readout_square worlds arrows source)
    (ContextualSmallCoalgebraMaterialCoalgebra.class_separated worlds arrows)

abbrev structured := CoveredFuturePowerClassifier.product
  (observedClasses worlds arrows source atoms atomCoding) (recipient worlds arrows)

def retainedClass : NaturalHom (structured worlds arrows source atoms atomCoding)
    (observedClasses worlds arrows source atoms atomCoding) where
  app _ receipt := receipt.1
  naturality _ _ := rfl

def materialProjection : NaturalHom (structured worlds arrows source atoms atomCoding) (recipient worlds arrows) where
  app _ receipt := receipt.2
  naturality _ _ := rfl

def retain : NaturalHom (observedClasses worlds arrows source atoms atomCoding)
    (structured worlds arrows source atoms atomCoding) where
  app point receipt := (receipt, (classReadout worlds arrows source atoms atomCoding).app point receipt)
  naturality step receipt := Prod.ext rfl ((classReadout worlds arrows source atoms atomCoding).naturality step receipt)

def interpretation : NaturalHom A (structured worlds arrows source atoms atomCoding) :=
  (observedProjection worlds arrows source atoms atomCoding).comp (retain worlds arrows source atoms atomCoding)

theorem interpretation_kernel (point : D) (first second : A.obj point) :
    (interpretation worlds arrows source atoms atomCoding).app point first =
        (interpretation worlds arrows source atoms atomCoding).app point second ↔
      ObservedBisimilar source atoms point first second := by
  refine Iff.trans ?_
    (ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding point first second)
  constructor
  · exact fun same => congrArg Prod.fst same
  · intro same
    exact Prod.ext same (congrArg ((classReadout worlds arrows source atoms atomCoding).app point) same)

theorem interpretation_material : (interpretation worlds arrows source atoms atomCoding).comp
    (materialProjection worlds arrows source atoms atomCoding) = readout worlds arrows source :=
  source_class_square worlds arrows source atoms atomCoding

/-- The interpretation covers precisely the graph of the actual class
readout, rather than all arbitrary pairs of observations and set values. -/
theorem interpretation_image (point : D)
    (pair : (structured worlds arrows source atoms atomCoding).obj point) :
    (∃ argument, (interpretation worlds arrows source atoms atomCoding).app point argument = pair) ↔
      (classReadout worlds arrows source atoms atomCoding).app point pair.1 = pair.2 := by
  constructor
  · rintro ⟨argument, same⟩
    exact (congrArg ((classReadout worlds arrows source atoms atomCoding).app point)
      (congrArg Prod.fst same)).symm.trans (congrArg Prod.snd same)
  · intro consistent
    obtain ⟨argument, represented⟩ := ContextualMaterialReadoutFamilies.classObservation_cover A
      (ContextualObservedMaterialFamily.graphs source atoms worlds arrows atomCoding)
      (ContextualObservedMaterialFamily.stable source atoms worlds arrows atomCoding) point pair.1
    exact ⟨argument, Prod.ext represented
      ((congrArg ((classReadout worlds arrows source atoms atomCoding).app point) represented).trans consistent)⟩

/-- This is the exact condition for forgetting the observed coordinate. -/
def PreservesDeclaredAtoms : Prop := ∀ point (first second : A.obj point),
  ContextualCoalgebraBisimulation.Bisimilar source point first second →
    ∀ atom, atoms atom ⟨point, first⟩ ↔ atoms atom ⟨point, second⟩

theorem bare_readout_exact_iff :
    (∀ point (first second : A.obj point),
      (readout worlds arrows source).app point first = (readout worlds arrows source).app point second ↔
        ObservedBisimilar source atoms point first second) ↔ PreservesDeclaredAtoms source atoms := by
  constructor
  · intro exactKernel point first second related atom
    exact observed_bisimilar_atoms source atoms
      ((exactKernel point first second).mp ((readout_kernel worlds arrows source point first second).mpr related)) atom
  · intro invariant point first second
    refine (readout_kernel worlds arrows source point first second).trans ?_
    constructor
    · rintro ⟨relation, bisimulation, related⟩
      exact ⟨relation, {
        underlying := bisimulation
        atoms := fun {_ left right} relates atom => invariant _ left right
          ⟨relation, bisimulation, relates⟩ atom }, related⟩
    · exact observed_bisimilar_forgets_atoms source atoms

end Mettapedia.GSLT.ConstructiveObservedMaterialInterpretation
