import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedContextualSubstitution
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialFamilies

/-!
# Constructive observed execution families in the realized graph model

The actual structured execution readout supplies the contextual parameter.
Its observed children and their next continuations instantiate the general
root-receipt construction. An authored source child constructs a receipt
directly; no representative is selected from an erased observed class.

The product carrier is the full compatible future family, and abstraction
acts on whole compatible body sections. Results and declared observations
remain in the structured readout. Occurrences deliberately forgotten by
that readout cannot be recovered for an incompatible dependent consumer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedObservedFamilies

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.GSLT
open GraphRealizedReceiptFamilies GraphRealizedContextualFamilies
open ContextualAuthoredMaterialFamilies

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → ContextualCoalgebraLabelledGraph.State A → Prop)
variable (atomCoding : ArgumentCoding Atom)

abbrev parameters := ConstructiveObservedMaterialFamilies.parameters worlds arrows source atoms atomCoding
abbrev domain := (ConstructiveObservedMaterialFamilies.continuationCode worlds arrows source atoms atomCoding).decode
abbrev body := (ConstructiveObservedMaterialFamilies.continuationBodyCode worlds arrows source atoms atomCoding).decode
abbrev product := (ConstructiveObservedMaterialFamilies.continuationPiCode worlds arrows source atoms atomCoding).decode
abbrev sum := (ConstructiveObservedMaterialFamilies.continuationSigmaCode worlds arrows source atoms atomCoding).decode

abbrev continuations := family.{u + 1, u + 1} (domain worlds arrows source atoms atomCoding)
abbrev continuationBodies := family.{u + 1, u + 1} (body worlds arrows source atoms atomCoding)
abbrev functions := family.{u + 1, u + 1} (product worlds arrows source atoms atomCoding)
abbrev pairs := family.{u + 1, u + 1} (sum worlds arrows source atoms atomCoding)

def sourcePoint (point : D) (parent : A.obj point) :
    (parameters worlds arrows source atoms atomCoding).Elements :=
  ⟨⟨point⟩, (ConstructiveObservedMaterialInterpretation.interpretation worlds arrows source atoms atomCoding).app
    point parent⟩

def sourceChild (point : D) (parent child : A.obj point)
    (available : (source.app point parent).val.holds (CoveredFuturePowerFamilies.current A point child)) :
    (continuations worlds arrows source atoms atomCoding).obj
      (sourcePoint worlds arrows source atoms atomCoding point parent) :=
  (decode.{u + 1, u + 1} (domain worlds arrows source atoms atomCoding) _).symm
    ⟨⟨(ConstructiveObservedMaterialInterpretation.observedProjection worlds arrows source atoms atomCoding).app
      point child⟩,
      (ConstructiveObservedMaterialFamilies.source_continuation_iff worlds arrows source atoms atomCoding
        point parent child).mpr ⟨child, rfl, available⟩⟩

theorem sourceChild_reading (point : D) (parent child : A.obj point)
    (available : (source.app point parent).val.holds (CoveredFuturePowerFamilies.current A point child)) :
    (decode.{u + 1, u + 1} (domain worlds arrows source atoms atomCoding) _
      (sourceChild worlds arrows source atoms atomCoding point parent child available)).val.down =
      (ConstructiveObservedMaterialInterpretation.observedProjection worlds arrows source atoms atomCoding).app
    point child := by
  let nativeChild : (domain worlds arrows source atoms atomCoding).native.obj
      (sourcePoint worlds arrows source atoms atomCoding point parent) :=
    ⟨⟨(ConstructiveObservedMaterialInterpretation.observedProjection worlds arrows source atoms atomCoding).app
      point child⟩,
      (ConstructiveObservedMaterialFamilies.source_continuation_iff worlds arrows source atoms atomCoding
        point parent child).mpr ⟨child, rfl, available⟩⟩
  exact congrArg (fun value : (domain worlds arrows source atoms atomCoding).native.obj
    (sourcePoint worlds arrows source atoms atomCoding point parent) => value.val.down)
      ((decode.{u + 1, u + 1} (domain worlds arrows source atoms atomCoding)
        (sourcePoint worlds arrows source atoms atomCoding point parent)).apply_symm_apply nativeChild)

def abstraction : (continuationBodies worlds arrows source atoms atomCoding).sections ≃
    (functions worlds arrows source atoms atomCoding).sections :=
  lambdaEquiv.{u + 1, u + 1} (domain worlds arrows source atoms atomCoding) (body worlds arrows source atoms atomCoding)
    (ConstructiveObservedMaterialFamilies.raisedWorlds worlds)
    (ConstructiveObservedMaterialFamilies.raisedArrows arrows)

theorem abstraction_native (term : (continuationBodies worlds arrows source atoms atomCoding).sections) :
    sectionEquiv.{u + 1, u + 1} (product worlds arrows source atoms atomCoding)
      (abstraction worlds arrows source atoms atomCoding term) =
        ConstructiveObservedMaterialFamilies.continuationLambda worlds arrows source atoms atomCoding
          (sectionEquiv.{u + 1, u + 1} (body worlds arrows source atoms atomCoding) term) :=
  (sectionEquiv.{u + 1, u + 1} _).apply_symm_apply _

def futureSectionDecoder (point : (parameters worlds arrows source atoms atomCoding).Elements) :
    (functions worlds arrows source atoms atomCoding).obj point ≃
      WiderPresheafDependentFunctions.DependentSection
        (domain worlds arrows source atoms atomCoding).native
        ((domain worlds arrows source atoms atomCoding).bodyNative (body worlds arrows source atoms atomCoding)) point :=
  futureDependentSectionDecoder.{u + 1, u + 1} _ _
    (ConstructiveObservedMaterialFamilies.raisedWorlds worlds)
    (ConstructiveObservedMaterialFamilies.raisedArrows arrows) point

/-- Every genuinely generated observed family is interpreted by the
same receipt construction, including identity, W and stable separation. -/
def generatedFamily {base : ConstructiveObservedMaterialFamilies.Upper (D := D) ⥤ Type (u + 1)}
    (code : ConstructiveObservedMaterialFamilies.Code worlds arrows source atoms atomCoding base) :
    base.Elements ⥤ Type (u + 1) := family.{u + 1, u + 1} code.decode

theorem generated_graph_enclosed
    {base : ConstructiveObservedMaterialFamilies.Upper (D := D) ⥤ Type (u + 1)}
    (code : ConstructiveObservedMaterialFamilies.Code worlds arrows source atoms atomCoding base)
    (point : base.Elements) :
    HSet.lift (HSet.mk (graph.{u + 1, u + 1} code.decode point)) ∈
      ConstructiveObservedMaterialFamilies.enclosure worlds arrows source atoms atomCoding base point := by
  rw [graph_carrier]
  exact ConstructiveObservedMaterialFamilies.generated_enclosed worlds arrows source atoms atomCoding code point

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedObservedFamilies
