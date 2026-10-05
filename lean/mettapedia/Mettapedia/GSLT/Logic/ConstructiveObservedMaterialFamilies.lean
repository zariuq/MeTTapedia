import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialInterpretation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeCumulativity
import Mettapedia.TypeTheory.PresheafSiteLift

/-!
# Actual constructive families of observed continuations

The structured execution readout determines a parameter presheaf on the
raised site. Each observed class has its independently constructed graph
dictionary. Stable separation constructs the family of actual observed
children of the retained parent, including its native context action and
complete material member decoder. The precise source comparison retains
all matching observed child classes, without selecting source occurrences.

The two computed seed families generate dependent sums, complete future
products, identity, hereditary W and separation over genuine comprehension.
These constructions instantiate the common authored material CwF and its
cover Collection class. The receipt bound is explicitly raised; full
ambient finality and unrestricted witness Collection are separate claims.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.ConstructiveObservedMaterialFamilies

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra
open ConstructiveObservedMaterialInterpretation
open ContextualAuthoredMaterialFamilies
open PowerClassPresheafBaseChange

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (atomCoding : ArgumentCoding Atom)

abbrev Classes := observedClasses worlds arrows source atoms atomCoding
abbrev Upper := PresheafSiteLift.Site D
abbrev parameters : Upper (D := D) ⥤ Type (u + 1) :=
  PresheafSiteLift.compose PresheafSiteLift.Site.downFunctor
    (structured worlds arrows source atoms atomCoding)

def classModel (point : D) : PresentedType ((Classes worlds arrows source atoms atomCoding).obj point) where
  graph := ContextualMaterialReadoutFamilies.carrierGraph A
    (ContextualObservedMaterialFamily.graphs source atoms worlds arrows atomCoding) point
  decode := (ContextualMaterialReadoutFamilies.memberEquiv A
    (ContextualObservedMaterialFamily.graphs source atoms worlds arrows atomCoding) point).symm

def readingNative : (parameters worlds arrows source atoms atomCoding).Elements ⥤ Type (u + 1) :=
  PresheafSiteLift.compose (CategoryOfElements.π (parameters worlds arrows source atoms atomCoding))
    (PresheafSiteLift.compose PresheafSiteLift.Site.downFunctor
      (PresheafSiteLift.compose (Classes worlds arrows source atoms atomCoding) uliftFunctor.{u + 1, u}))

def readings : Family (parameters worlds arrows source atoms atomCoding) where
  native := readingNative worlds arrows source atoms atomCoding
  models point := PresentedTypeCumulativity.liftModel
    (classModel worlds arrows source atoms atomCoding point.1.down)

def parent : (readings worlds arrows source atoms atomCoding).native.sections :=
  ⟨fun point => ⟨point.2.1⟩, by
    intro first second step
    exact ULift.ext _ _ (congrArg Prod.fst step.2)⟩

def childPredicate : ContextualReceiptFamilyModels.StablePredicate
    (readings worlds arrows source atoms atomCoding).native where
  holds point child :=
    ((observedCoalgebra worlds arrows source atoms atomCoding).app point.1.down point.2.1).val.holds
      (CoveredFuturePowerFamilies.current (Classes worlds arrows source atoms atomCoding) point.1.down child.down)
  map {first second} step child available := by
    let operation := observedCoalgebra worlds arrows source atoms atomCoding
    let classes := Classes worlds arrows source atoms atomCoding
    have future := (operation.app first.1.down first.2.1).val.closed
      (show CoveredFuturePowerFamilies.current classes first.1.down child.down ⟶
        (⟨⟨second.1.down, step.1.down⟩, classes.map step.1.down child.down⟩ :
          CoveredFuturePowerFamilies.Arguments classes first.1.down) from
        ⟨⟨step.1.down, Category.id_comp _⟩, rfl⟩) available
    have now := (CoveredFuturePowerClassifier.classified_future classes classes operation
      first.1.down first.2.1 ⟨⟨second.1.down, step.1.down⟩, classes.map step.1.down child.down⟩).mp future
    have parents : classes.map step.1.down first.2.1 = second.2.1 := congrArg Prod.fst step.2
    exact parents ▸ now

def continuations : Family (parameters worlds arrows source atoms atomCoding) :=
  (readings worlds arrows source atoms atomCoding).separate
    (childPredicate worlds arrows source atoms atomCoding)

theorem continuation_value (point : (parameters worlds arrows source atoms atomCoding).Elements)
    (child : (continuations worlds arrows source atoms atomCoding).native.obj point) :
    ((continuations worlds arrows source atoms atomCoding).models point).value child =
      HSet.lift ((classModel worlds arrows source atoms atomCoding point.1.down).value child.val.down) := rfl

def sourceFamily : Upper (D := D) ⥤ Type (u + 1) where
  obj point := ULift.{u + 1, u} (A.obj point.down)
  map step := TypeCat.ofHom fun value => ⟨A.map step.down value.down⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (A.map_id_apply point.down value.down)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (A.map_comp_apply first.down second.down value.down)

def sourceParameter : NaturalHom (sourceFamily (A := A))
    (parameters worlds arrows source atoms atomCoding) where
  app point value := (interpretation worlds arrows source atoms atomCoding).app point.down value.down
  naturality step value := (interpretation worlds arrows source atoms atomCoding).naturality step.down value.down

theorem source_class_continuation_iff (point : D) (parentArgument : A.obj point)
    (child : (Classes worlds arrows source atoms atomCoding).obj point) :
    (childPredicate worlds arrows source atoms atomCoding).holds
      ⟨⟨point⟩, (interpretation worlds arrows source atoms atomCoding).app point parentArgument⟩
      ⟨child⟩ ↔
      ∃ original : A.obj point,
        (observedProjection worlds arrows source atoms atomCoding).app point original = child ∧
        (source.app point parentArgument).val.holds
          (CoveredFuturePowerFamilies.current A point original) :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth source
    (observedProjection worlds arrows source atoms atomCoding)
    (observedCoalgebra worlds arrows source atoms atomCoding)
    (ContextualObservedMaterialFamily.classObservation_square source atoms worlds arrows atomCoding)
    point parentArgument ⟨point, 𝟙 point⟩ _

theorem source_continuation_iff (point : D) (parentArgument childArgument : A.obj point) :
    (childPredicate worlds arrows source atoms atomCoding).holds
      ⟨⟨point⟩, (interpretation worlds arrows source atoms atomCoding).app point parentArgument⟩
      ⟨(observedProjection worlds arrows source atoms atomCoding).app point childArgument⟩ ↔
      ∃ original : A.obj point,
        (observedProjection worlds arrows source atoms atomCoding).app point original =
          (observedProjection worlds arrows source atoms atomCoding).app point childArgument ∧
        (source.app point parentArgument).val.holds
          (CoveredFuturePowerFamilies.current A point original) :=
  source_class_continuation_iff worlds arrows source atoms atomCoding point parentArgument _

def raisedWorlds : ArgumentCoding (Upper (D := D)) := worlds.lift

def raisedArrows (first second : Upper (D := D)) : ArgumentCoding (first ⟶ second) :=
  (arrows first.down second.down).lift

inductive Seed (base : Upper (D := D) ⥤ Type (u + 1)) : Type (u + 2) where
  | readings (change : NaturalHom base (parameters worlds arrows source atoms atomCoding))
  | continuations (change : NaturalHom base (parameters worlds arrows source atoms atomCoding))

def seedModel (base : Upper (D := D) ⥤ Type (u + 1))
    (seed : Seed worlds arrows source atoms atomCoding base) : Family base :=
  match seed with
  | .readings change => (readings worlds arrows source atoms atomCoding).reindex change
  | .continuations change => (continuations worlds arrows source atoms atomCoding).reindex change

abbrev Code (base : Upper (D := D) ⥤ Type (u + 1)) :=
  ContextualAuthoredGeneratedFamilies.Code.{u + 1, u + 1} (raisedWorlds worlds) (raisedArrows arrows)
    (Seed worlds arrows source atoms atomCoding) (seedModel worlds arrows source atoms atomCoding) base

def readingCode : Code worlds arrows source atoms atomCoding (parameters worlds arrows source atoms atomCoding) :=
  ContextualAuthoredGeneratedFamilies.Code.seed
    (.readings (ContextualSmallMapConstructions.identity _))

def continuationCode : Code worlds arrows source atoms atomCoding (parameters worlds arrows source atoms atomCoding) :=
  ContextualAuthoredGeneratedFamilies.Code.seed
    (.continuations (ContextualSmallMapConstructions.identity _))

/-- Passing to a continuation makes its observed class the next retained
parent. The second coordinate is computed by the actual coalgebra map. -/
def childParameter : NaturalHom (continuationCode worlds arrows source atoms atomCoding).decode.extension
    (parameters worlds arrows source atoms atomCoding) where
  app point argument :=
    (argument.2.val.down,
      (classReadout worlds arrows source atoms atomCoding).app point.down argument.2.val.down)
  naturality step argument := Prod.ext rfl
    ((classReadout worlds arrows source atoms atomCoding).naturality step.down argument.2.val.down)

def continuationBodyCode : Code worlds arrows source atoms atomCoding
    (continuationCode worlds arrows source atoms atomCoding).decode.extension :=
  (continuationCode worlds arrows source atoms atomCoding).reindex
    (childParameter worlds arrows source atoms atomCoding)

def continuationPiCode : Code worlds arrows source atoms atomCoding
    (parameters worlds arrows source atoms atomCoding) :=
  (continuationCode worlds arrows source atoms atomCoding).pi
    (continuationBodyCode worlds arrows source atoms atomCoding)

def continuationSigmaCode : Code worlds arrows source atoms atomCoding
    (parameters worlds arrows source atoms atomCoding) :=
  (continuationCode worlds arrows source atoms atomCoding).sigma
    (continuationBodyCode worlds arrows source atoms atomCoding)

noncomputable def continuationWCode : Code worlds arrows source atoms atomCoding
    (parameters worlds arrows source atoms atomCoding) :=
  (continuationCode worlds arrows source atoms atomCoding).w
    (continuationBodyCode worlds arrows source atoms atomCoding)

/-- Formation uses every contextual continuation and its actual next
continuations. The section equivalence is the native dependent adjunction. -/
def continuationLambda :
    (continuationBodyCode worlds arrows source atoms atomCoding).decode.native.sections ≃
      (continuationPiCode worlds arrows source atoms atomCoding).decode.native.sections :=
  ContextualAuthoredMaterialCwf.lambdaEquiv.{u + 1, u + 1}
    (continuationCode worlds arrows source atoms atomCoding).decode
    (continuationBodyCode worlds arrows source atoms atomCoding).decode
    (raisedWorlds worlds) (raisedArrows arrows)

theorem continuationLambda_eta
    (term : (continuationPiCode worlds arrows source atoms atomCoding).decode.native.sections) :
    continuationLambda worlds arrows source atoms atomCoding
        ((continuationLambda worlds arrows source atoms atomCoding).symm term) = term :=
  (continuationLambda worlds arrows source atoms atomCoding).apply_symm_apply term

theorem continuationLambda_beta
    (term : (continuationBodyCode worlds arrows source atoms atomCoding).decode.native.sections)
    (argument : (continuationCode worlds arrows source atoms atomCoding).decode.native.sections) :
    ContextualAuthoredMaterialCwf.applyTerm.{u + 1, u + 1}
      (continuationCode worlds arrows source atoms atomCoding).decode
      (continuationBodyCode worlds arrows source atoms atomCoding).decode
      (raisedWorlds worlds) (raisedArrows arrows)
      (continuationLambda worlds arrows source atoms atomCoding term) argument =
        ContextualSmallFamilyIdentity.reindexSection
          (ContextualAuthoredMaterialCwf.pair.{u + 1, u + 1} (ContextualSmallMapConstructions.identity _)
            (continuationCode worlds arrows source atoms atomCoding).decode argument)
          (continuationBodyCode worlds arrows source atoms atomCoding).decode.native term :=
  ContextualAuthoredMaterialCwf.apply_lambda.{u + 1, u + 1} _ _ _ _ term argument

def enclosure (base : Upper (D := D) ⥤ Type (u + 1)) (point : base.Elements) : HSet.{u + 2} :=
  HSet.imageUp fun code : Code worlds arrows source atoms atomCoding base => (code.decode.models point).carrier

theorem generated_enclosed {base : Upper (D := D) ⥤ Type (u + 1)}
    (code : Code worlds arrows source atoms atomCoding base) (point : base.Elements) :
    HSet.lift (code.decode.models point).carrier ∈ enclosure worlds arrows source atoms atomCoding base point :=
  HSet.lift_mem_imageUp _ code

end Mettapedia.GSLT.ConstructiveObservedMaterialFamilies
