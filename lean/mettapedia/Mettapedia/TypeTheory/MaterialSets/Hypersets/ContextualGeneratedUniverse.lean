import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualMaterialization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWTypes

/-!
# Generated contextual families with material decoding

The generating family is an actual displayed presheaf with material fibre
models. Its contextual products contain natural functions at every future
context and arrow. Faithful labels retain those indices externally; they
do not supply a decoder for a host context type. Sums recover their actual
first coordinates, and discrete identities use the constructed small
material equality witnesses.

Derivations record these concrete operations on semantic families. Their
code carrier includes the semantic functors and their material dictionaries.
The raised external enclosure does not assert an internally small inductive-recursive
universe or unrestricted fixed-level collection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]

structure LabelledContext (C : Type u) [Category.{u} C] where
  base : Cᵒᵖ ⥤ Type u
  labels : ArgumentCoding base.Elements

/-- A material interpretation of one actual displayed family. The operations
below construct every new model field from their input interpretations. -/
structure MaterialFamily (context : LabelledContext C) where
  family : DisplayedFamily.{u, u, u, u} context.base
  model : (point : context.base.Elements) → PresentedType (family.obj point)

namespace MaterialFamily

variable {context : LabelledContext C} (domain : MaterialFamily context)

def termCoding (point : context.base.Elements) : ArgumentCoding (domain.family.obj point) where
  graph := (domain.model point).termGraph
  injective := by
    intro first second same
    dsimp only at same
    rw [PresentedType.mk_termGraph, PresentedType.mk_termGraph] at same
    exact (domain.model point).value_injective same

/-- Comprehension retains the whole parent point and material member in its
faithful labels. The underlying context is the actual total presheaf. -/
def extension : LabelledContext C where
  base := totalSpace domain.family
  labels := {
    graph := fun point => AccessiblePointedGraph.kpairGraph
      (context.labels.graph ⟨point.1, point.2.1⟩)
      ((domain.model ⟨point.1, point.2.1⟩).termGraph point.2.2)
    injective := by
      rintro ⟨X, first, firstMember⟩ ⟨Y, second, secondMember⟩ same
      dsimp only at same
      rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
        PresentedType.mk_termGraph, PresentedType.mk_termGraph] at same
      have parents : (⟨X, first⟩ : context.base.Elements) = ⟨Y, second⟩ :=
        context.labels.injective (HSet.kpair_inj.mp same).1
      have worlds : X = Y := congrArg Sigma.fst parents
      subst Y
      have values : first = second := eq_of_heq ((Sigma.mk.inj_iff.mp parents).2)
      subst second
      have members : firstMember = secondMember :=
        (domain.model ⟨X, first⟩).value_injective (HSet.kpair_inj.mp same).2
      subst secondMember
      rfl }

def constant (model : PresentedType (ULift.{u, 0} PUnit)) : MaterialFamily context where
  family := {
    obj _ := ULift.{u, 0} PUnit
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  model _ := model

def unit (context : LabelledContext C) : MaterialFamily context :=
  constant PresentedType.unit

def empty (context : LabelledContext C) : MaterialFamily context where
  family := {
    obj _ := ULift.{u, 0} Empty
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  model _ := PresentedType.empty

variable (body : MaterialFamily domain.extension)

def sigma : MaterialFamily context where
  family := PowerClassPresheafProducts.sigmaFamily domain.family body.family
  model point := PowerClassContextualMaterialization.sigmaModel domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) point
    (domain.model point) (fun argument => body.model ⟨point.1, ⟨point.2, argument⟩⟩)

variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

def elementArrowCoding (first second : context.base.Elements) : ArgumentCoding (first ⟶ second) :=
  (arrows first.1 second.1).subtype (fun step => context.base.map step first.2 = second.2)

/-- The labels preserve the world, the actual arrow and the complete
generated argument value. No inverse for the context labels is introduced. -/
def futureCoding (point : context.base.Elements) :
    ArgumentCoding (PowerClassContextualMaterialization.FutureArguments domain.family point) :=
  ArgumentCoding.contextual context.labels (elementArrowCoding arrows) domain.family
    domain.termCoding point

def futureOutputs (point : context.base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments domain.family point) :
    PresentedType ((PowerClassPresheafBaseChange.Future.result domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family) point).obj argument) :=
  body.model ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩

/-- Full future-dependent Pi formation constructs its entire material
carrier and decoder from the generated output models. -/
def pi : MaterialFamily context where
  family := PowerClassPresheafProducts.piFamily domain.family body.family
  model point := PowerClassContextualMaterialization.piModel domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) point
    (domain.futureCoding arrows point) (domain.futureOutputs body point)

/-- W formation uses the actual hereditary-natural contextual tree functor.
The indexed raw decoder and its separated natural carrier are constructed
at the common graph bound from the generated shape and position models. -/
def w : MaterialFamily context where
  family := ContextualWTypes.family domain.family (PowerClassPresheafProducts.indexedBody domain.family body.family)
  model point := MaterialContextualWTypes.naturalModel domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) context.labels
    (elementArrowCoding arrows) domain.model
    (fun argument => body.model ⟨argument.1.1, ⟨argument.1.2, argument.2⟩⟩) point

def reindex {other : LabelledContext C} (change : NatTrans other.base context.base) : MaterialFamily other where
  family := PowerClassPresheafProducts.reindex change domain.family
  model point := domain.model ((PowerClassPresheafProducts.elementMap change).obj point)

/-- The transported whole-future labels give the material Pi formed after
base change. Arbitrary freshly chosen labels need not give equal graphs. -/
def piUnder {other : LabelledContext C} (change : NatTrans other.base context.base) : MaterialFamily other where
  family := dependentFunctions (PowerClassPresheafProducts.reindex change domain.family)
    (PowerClassPresheafBaseChange.bodyReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family))
  model point := PowerClassContextualMaterialization.piModel
    (PowerClassPresheafProducts.reindex change domain.family)
    (PowerClassPresheafBaseChange.bodyReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family)) point
    (PowerClassContextualMaterialization.BaseChange.codingReindex change domain.family point
      (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point)))
    (PowerClassContextualMaterialization.BaseChange.outputsReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family) point
      (domain.futureOutputs body ((PowerClassPresheafProducts.elementMap change).obj point)))

def piComparison {other : LabelledContext C} (change : NatTrans other.base context.base) (point : other.base.Elements) :
    ((domain.pi body arrows).reindex change).family.obj point ≃ (domain.piUnder body arrows change).family.obj point :=
  PowerClassPresheafBaseChange.piFibreEquiv change domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) point

theorem piUnder_value {other : LabelledContext C} (change : NatTrans other.base context.base)
    (point : other.base.Elements) (function : ((domain.pi body arrows).reindex change).family.obj point) :
    ((domain.piUnder body arrows change).model point).value (domain.piComparison body arrows change point function) =
      (((domain.pi body arrows).reindex change).model point).value function :=
  PowerClassContextualMaterialization.BaseChange.materialPi_reindex_value change domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) point
    (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point))
    (domain.futureOutputs body ((PowerClassPresheafProducts.elementMap change).obj point)) function

theorem piUnder_carrier {other : LabelledContext C} (change : NatTrans other.base context.base)
    (point : other.base.Elements) :
    ((domain.piUnder body arrows change).model point).carrier =
      (((domain.pi body arrows).reindex change).model point).carrier := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    let decoded := ((domain.piUnder body arrows change).model point).decode ⟨value, member⟩
    have preservation := domain.piUnder_value body arrows change point
      ((domain.piComparison body arrows change point).symm decoded)
    rw [Equiv.apply_symm_apply] at preservation
    have recovered := ((domain.piUnder body arrows change).model point).value_decode ⟨value, member⟩
    have same : (((domain.pi body arrows).reindex change).model point).value
        ((domain.piComparison body arrows change point).symm decoded) = value := preservation.symm.trans recovered
    rw [← same]
    exact (((domain.pi body arrows).reindex change).model point).value_mem
      ((domain.piComparison body arrows change point).symm decoded)
  · intro member
    let decoded := (((domain.pi body arrows).reindex change).model point).decode ⟨value, member⟩
    have preservation := domain.piUnder_value body arrows change point decoded
    have recovered := (((domain.pi body arrows).reindex change).model point).value_decode ⟨value, member⟩
    have same : ((domain.piUnder body arrows change).model point).value
        (domain.piComparison body arrows change point decoded) = value := preservation.trans recovered
    rw [← same]
    exact ((domain.piUnder body arrows change).model point).value_mem (domain.piComparison body arrows change point decoded)

def piUnderMember {other : LabelledContext C} (change : NatTrans other.base context.base)
    (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.pi body arrows).reindex change).model point).carrier}) :
    {value : HSet.{u} // value ∈ ((domain.piUnder body arrows change).model point).carrier} :=
  ⟨member.1, by rw [piUnder_carrier]; exact member.2⟩

theorem piUnder_decoder {other : LabelledContext C} (change : NatTrans other.base context.base)
    (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.pi body arrows).reindex change).model point).carrier}) :
    ((domain.piUnder body arrows change).model point).decode
      (domain.piUnderMember body arrows change point member) =
        domain.piComparison body arrows change point
          ((((domain.pi body arrows).reindex change).model point).decode member) := by
  apply ((domain.piUnder body arrows change).model point).value_injective
  exact (((domain.piUnder body arrows change).model point).value_decode
    (domain.piUnderMember body arrows change point member)).trans
    (((((domain.pi body arrows).reindex change).model point).value_decode member).symm.trans
      (domain.piUnder_value body arrows change point
        ((((domain.pi body arrows).reindex change).model point).decode member)).symm)

/-- Dependent sums are formed after base change with the actual pulled-back
first coordinate and dependent body, including its restriction maps. -/
def sigmaUnder {other : LabelledContext C} (change : NatTrans other.base context.base) : MaterialFamily other where
  family := PowerClassPresheafProducts.IndexedSigma.family
    (PowerClassPresheafProducts.reindex change domain.family)
    (PowerClassPresheafBaseChange.bodyReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family))
  model point := PowerClassContextualMaterialization.sigmaModel
    (PowerClassPresheafProducts.reindex change domain.family)
    (PowerClassPresheafBaseChange.bodyReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family)) point
    (domain.model ((PowerClassPresheafProducts.elementMap change).obj point))
    (fun argument => body.model ⟨point.1, ⟨change.app point.1 point.2, argument⟩⟩)

theorem sigmaUnder_formation {other : LabelledContext C} (change : NatTrans other.base context.base) :
    ((domain.sigma body).reindex change).family = (domain.sigmaUnder body change).family :=
  PowerClassPresheafBaseChange.sigmaBaseChange change domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family)

theorem sigmaUnder_value {other : LabelledContext C} (change : NatTrans other.base context.base)
    (point : other.base.Elements) (term : (domain.sigmaUnder body change).family.obj point) :
    ((domain.sigmaUnder body change).model point).value term =
      (((domain.sigma body).reindex change).model point).value term := rfl

def identity (left right : domain.family.sections) : MaterialFamily context where
  family := DisplayedPresheafIdentity.identityFamily domain.family left right
  model point := PowerClassContextualMaterialization.powerClassModel
    (PresheafIdentityWitness.graph (left.val point) (right.val point))

theorem identity_reindex {other : LabelledContext C} (change : NatTrans other.base context.base)
    (left right : domain.family.sections) :
    ((domain.identity left right).reindex change).family =
      ((domain.reindex change).identity
        (PowerClassPresheafProducts.reindexSection change domain.family left)
        (PowerClassPresheafProducts.reindexSection change domain.family right)).family :=
  DisplayedPresheafIdentity.identityFamily_reindex change domain.family left right

/-- Material members have their own actual restriction maps. These maps
decode, apply the authored family restriction, and re-encode the result. -/
def memberRestriction {first second : context.base.Elements} (arrow : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (domain.model first).carrier}) :
    {value : HSet.{u} // value ∈ (domain.model second).carrier} :=
  (domain.model second).decode.symm (domain.family.map arrow ((domain.model first).decode member))

theorem memberRestriction_decode {first second : context.base.Elements} (arrow : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (domain.model first).carrier}) :
    (domain.model second).decode (domain.memberRestriction arrow member) =
      domain.family.map arrow ((domain.model first).decode member) := Equiv.apply_symm_apply _ _

theorem memberRestriction_encode {first second : context.base.Elements} (arrow : first ⟶ second)
    (term : domain.family.obj first) :
    domain.memberRestriction arrow ((domain.model first).decode.symm term) =
      (domain.model second).decode.symm (domain.family.map arrow term) := by
  unfold memberRestriction
  rw [Equiv.apply_symm_apply]

def members : context.base.Elements ⥤ Type (u + 1) where
  obj point := {value : HSet.{u} // value ∈ (domain.model point).carrier}
  map arrow := TypeCat.ofHom (domain.memberRestriction arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro member
    unfold memberRestriction
    rw [domain.family.map_id point]
    exact Equiv.symm_apply_apply _ _
  map_comp {firstPoint middlePoint lastPoint} first later := by
    apply ConcreteCategory.hom_ext
    intro member
    have composite := domain.family.map_comp_apply first later ((domain.model firstPoint).decode member)
    have inverse := (domain.model middlePoint).decode.apply_symm_apply
      (domain.family.map first ((domain.model firstPoint).decode member))
    exact (congrArg (domain.model lastPoint).decode.symm composite).trans
      (congrArg (fun term => (domain.model lastPoint).decode.symm (domain.family.map later term)) inverse).symm

theorem pi_evaluation (point : context.base.Elements)
    (function : (domain.pi body arrows).family.obj point)
    (argument : PowerClassContextualMaterialization.FutureArguments domain.family point) :
    LabelledDependentProducts.evalValue (domain.futureCoding arrows point) (domain.futureOutputs body point)
      (((domain.pi body arrows).model point).value function) argument =
        (domain.futureOutputs body point argument).value
          (function.app argument.1.1 argument.1.2 argument.2) :=
  PowerClassContextualMaterialization.piModel_evaluation _ _ _ _ _ _ _

theorem sigma_first (point : context.base.Elements) (term : (domain.sigma body).family.obj point) :
    HSet.fst (((domain.sigma body).model point).value term) = (domain.model point).value term.1 :=
  PowerClassContextualMaterialization.sigmaModel_first_value _ _ _ _ _ _

theorem sigma_second (point : context.base.Elements) (term : (domain.sigma body).family.obj point) :
    HSet.snd (((domain.sigma body).model point).value term) =
      (body.model ⟨point.1, ⟨point.2, term.1⟩⟩).value term.2 :=
  PowerClassContextualMaterialization.sigmaModel_second_value _ _ _ _ _ _

end MaterialFamily

/-- A seed is a declared interpreted family. Formation derives new families
by the actual contextual operations above. The body is generated over the
domain's real comprehension context. -/
inductive Generation
    (seeds : (context : LabelledContext C) → Type (u + 1))
    (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
    (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second)) :
    {context : LabelledContext C} → MaterialFamily context → Type (u + 1) where
  | seed (context : LabelledContext C) (label : seeds context) : Generation seeds seedModel arrows (seedModel context label)
  | empty (context : LabelledContext C) : Generation seeds seedModel arrows (MaterialFamily.empty context)
  | unit (context : LabelledContext C) : Generation seeds seedModel arrows (MaterialFamily.unit context)
  | pi {context : LabelledContext C} {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
      (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body) :
      Generation seeds seedModel arrows (domain.pi body arrows)
  | sigma {context : LabelledContext C} {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
      (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body) :
      Generation seeds seedModel arrows (domain.sigma body)
  | w {context : LabelledContext C} {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
      (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body) :
      Generation seeds seedModel arrows (domain.w body arrows)
  | identity {context : LabelledContext C} {domain : MaterialFamily context}
      (first : Generation seeds seedModel arrows domain) (left right : domain.family.sections) :
      Generation seeds seedModel arrows (domain.identity left right)
  | reindex {context other : LabelledContext C} {domain : MaterialFamily context}
      (first : Generation seeds seedModel arrows domain) (change : NatTrans other.base context.base) :
      Generation seeds seedModel arrows (domain.reindex change)
  | piUnder {context other : LabelledContext C} {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
      (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body)
      (change : NatTrans other.base context.base) :
      Generation seeds seedModel arrows (domain.piUnder body arrows change)
  | sigmaUnder {context other : LabelledContext C} {domain : MaterialFamily context} {body : MaterialFamily domain.extension}
      (first : Generation seeds seedModel arrows domain) (second : Generation seeds seedModel arrows body)
      (change : NatTrans other.base context.base) :
      Generation seeds seedModel arrows (domain.sigmaUnder body change)

variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev Code (context : LabelledContext C) :=
  Σ domain : MaterialFamily context, Generation seeds seedModel arrows domain

/-- All generated material type values fit in this actual raised range.
The dictionary and every derivation remain in the external code carrier. -/
def enclosure (context : LabelledContext C) (point : context.base.Elements) : HSet.{u + 1} :=
  HSet.imageUp fun code : Code seeds seedModel arrows context => (code.1.model point).carrier

theorem mem_enclosure_iff {context : LabelledContext C} {point : context.base.Elements} {value : HSet.{u + 1}} :
    value ∈ enclosure seeds seedModel arrows context point ↔
      ∃ code : Code seeds seedModel arrows context, HSet.lift (code.1.model point).carrier = value :=
  HSet.mem_imageUp_iff

theorem generated_mem_enclosure {context : LabelledContext C} {domain : MaterialFamily context}
    (derivation : Generation seeds seedModel arrows domain) (point : context.base.Elements) :
    HSet.lift (domain.model point).carrier ∈ enclosure seeds seedModel arrows context point :=
  (mem_enclosure_iff seeds seedModel arrows).mpr ⟨⟨domain, derivation⟩, rfl⟩

/-- Generated decoded terms are equivalent to actual material members;
this includes complete future functions, not only current evaluations. -/
def decode {context : LabelledContext C} {domain : MaterialFamily context}
    (_derivation : Generation seeds seedModel arrows domain) (point : context.base.Elements) :
    {value : HSet.{u} // value ∈ (domain.model point).carrier} ≃ domain.family.obj point :=
  (domain.model point).decode

theorem decode_encode {context : LabelledContext C} {domain : MaterialFamily context}
    (derivation : Generation seeds seedModel arrows domain) (point : context.base.Elements)
    (term : domain.family.obj point) :
    decode seeds seedModel arrows derivation point
      ((decode seeds seedModel arrows derivation point).symm term) = term :=
  (decode seeds seedModel arrows derivation point).apply_symm_apply term

theorem encode_decode {context : LabelledContext C} {domain : MaterialFamily context}
    (derivation : Generation seeds seedModel arrows domain) (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model point).carrier}) :
    (decode seeds seedModel arrows derivation point).symm
      (decode seeds seedModel arrows derivation point member) = member :=
  (decode seeds seedModel arrows derivation point).symm_apply_apply member

/-- Reindexing uses the actual decoded term in the original observed fibre.
Both directions of its material member comparison therefore retain values. -/
theorem reindex_term_value {context other : LabelledContext C} (domain : MaterialFamily context)
    (change : NatTrans other.base context.base) (point : other.base.Elements)
    (term : (domain.reindex change).family.obj point) :
    ((domain.reindex change).model point).value term =
      (domain.model ((PowerClassPresheafProducts.elementMap change).obj point)).value term := rfl

theorem reindex_decoder {context other : LabelledContext C} (domain : MaterialFamily context)
    (change : NatTrans other.base context.base) (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((domain.reindex change).model point).carrier}) :
    ((domain.reindex change).model point).decode member =
      (domain.model ((PowerClassPresheafProducts.elementMap change).obj point)).decode member := rfl

namespace Growing

open PowerClassPresheafDescent
open PowerClassFamilyDescent

abbrev Stages := PowerClassPresheafDescent.Controls.Stages
abbrev profile := PowerClassContextualMaterialization.Growing.profile
abbrev old := PowerClassContextualMaterialization.Growing.old
abbrev later := PowerClassContextualMaterialization.Growing.later

/-- This base is the constructed observation-class presheaf of the actual
growing GSLT system, with independently proved faithful class labels. -/
def context : LabelledContext Stages where
  base := PowerClassContextualMaterialization.Growing.base
  labels := PowerClassContextualMaterialization.Growing.pointCoding

def arrowCoding (first second : Stagesᵒᵖ) : ArgumentCoding (first ⟶ second) where
  graph _ := AccessiblePointedGraph.empty
  injective _ _ _ := Subsingleton.elim _ _

/-- The output decoder is the constructed power-member-class comparison.
The family actually grows from the empty choice to a cyclic alternative. -/
def input : MaterialFamily context where
  family := PowerClassContextualMaterialization.Growing.displayed
  model := PowerClassContextualMaterialization.Growing.memberModel

theorem input_value (point : context.base.Elements) (member : input.family.obj point) :
    (input.model point).value member =
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.valueAt point member :=
  PowerClassContextualMaterialization.Growing.memberModel_value point member

def body : MaterialFamily input.extension :=
  input.reindex (PowerClassPresheafProducts.projection input.family)

def Seeds (declaredContext : LabelledContext Stages) : Type 1 :=
  ULift.{1, 0} (PLift (declaredContext = context))

def observedSeedModel (declaredContext : LabelledContext Stages) (seed : Seeds declaredContext) :
    MaterialFamily declaredContext := by
  cases seed.down.down
  exact input

def inputGenerated : Generation Seeds observedSeedModel arrowCoding input :=
  .seed context ⟨⟨rfl⟩⟩

def bodyGenerated : Generation Seeds observedSeedModel arrowCoding body :=
  Generation.reindex (other := input.extension) inputGenerated (PowerClassPresheafProducts.projection input.family)

def piGenerated : Generation Seeds observedSeedModel arrowCoding (input.pi body arrowCoding) :=
  .pi inputGenerated bodyGenerated

def sigmaGenerated : Generation Seeds observedSeedModel arrowCoding (input.sigma body) :=
  .sigma inputGenerated bodyGenerated

abbrev emptySection := Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed

def positiveSection : input.family.sections :=
  descendContextualSection profile.sourceFace profile.classFace profile.observation
    PowerClassContextualMaterialization.Growing.positiveGraphs
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTransport
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTerm
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTerm_compatible

def identityGenerated : Generation Seeds observedSeedModel arrowCoding
    (input.identity emptySection positiveSection) :=
  .identity inputGenerated _ _

def wGenerated : Generation Seeds observedSeedModel arrowCoding (input.w body arrowCoding) :=
  .w inputGenerated bodyGenerated

theorem pi_enclosed (point : context.base.Elements) :
    HSet.lift ((input.pi body arrowCoding).model point).carrier ∈ enclosure Seeds observedSeedModel arrowCoding context point :=
  generated_mem_enclosure Seeds observedSeedModel arrowCoding piGenerated point

theorem sigma_enclosed (point : context.base.Elements) :
    HSet.lift ((input.sigma body).model point).carrier ∈ enclosure Seeds observedSeedModel arrowCoding context point :=
  generated_mem_enclosure Seeds observedSeedModel arrowCoding sigmaGenerated point

theorem identity_enclosed (point : context.base.Elements) :
    HSet.lift ((input.identity emptySection positiveSection).model point).carrier ∈
        enclosure Seeds observedSeedModel arrowCoding context point :=
  generated_mem_enclosure Seeds observedSeedModel arrowCoding identityGenerated point

theorem w_enclosed (point : context.base.Elements) :
    HSet.lift ((input.w body arrowCoding).model point).carrier ∈ enclosure Seeds observedSeedModel arrowCoding context point :=
  generated_mem_enclosure Seeds observedSeedModel arrowCoding wGenerated point

/-- Full material products over this observed family preserve a distinction
that every evaluation in the original present fibre would erase. -/
theorem future_functions_differ :
    ((input.pi body arrowCoding).model old).value (PowerClassContextualMaterialization.Growing.identityFunction.val old) ≠
      ((input.pi body arrowCoding).model old).value (PowerClassContextualMaterialization.Growing.constantFunction.val old) := by
  intro same
  exact Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.function_components_differ
    (((input.pi body arrowCoding).model old).value_injective same)

theorem present_evaluation_not_injective :
    ¬ Function.Injective (fun function : (input.pi body arrowCoding).family.obj old =>
      fun argument : input.family.obj old => function.app old (𝟙 old) argument) :=
  Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.current_evaluation_not_injective

def terminalBody : MaterialFamily input.extension := MaterialFamily.empty input.extension

def leaf (point : context.base.Elements) (label : input.family.obj point) :
    (input.w terminalBody arrowCoding).family.obj point :=
  ContextualWTypes.sup input.family
    (PowerClassPresheafProducts.indexedBody input.family terminalBody.family) label
    (fun _ _ branch => Empty.elim branch.down)
    (fun _ _ _ _ branch => Empty.elim branch.down)

theorem cyclic_leaf_material_member :
    ((input.w terminalBody arrowCoding).model later).value
      (leaf later PowerClassContextualMaterialization.Growing.futureArgument) ∈
        ((input.w terminalBody arrowCoding).model later).carrier :=
  ((input.w terminalBody arrowCoding).model later).value_mem _

/-- The shape of this well-founded inductive leaf retains an actual cyclic
material argument. Inductivity constrains tree recursion, not its payload. -/
theorem cyclic_leaf_shape :
    (input.model later).value PowerClassContextualMaterialization.Growing.futureArgument = HSet.quineAtom :=
  (input_value later _).trans
    Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.futureArgument_value

def cyclicPair : (input.sigma body).family.obj later :=
  ⟨PowerClassContextualMaterialization.Growing.futureArgument, emptySection.val later⟩

theorem cyclicPair_first :
    HSet.fst (((input.sigma body).model later).value cyclicPair) = HSet.quineAtom :=
  (input.sigma_first body later cyclicPair).trans cyclic_leaf_shape

theorem positiveSection_value (raw : profile.sourceFace.Elements) :
    (input.model ((classElements profile.sourceFace profile.classFace profile.observation).obj raw)).value
      (positiveSection.val ((classElements profile.sourceFace profile.classFace profile.observation).obj raw)) =
        (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTerm raw).1 :=
  (input_value _ _).trans
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.Families.descendedArgument_value profile
      PowerClassContextualMaterialization.Growing.positiveGraphs
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTransport
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTerm
      Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTerm_compatible raw)

theorem emptySection_value (raw : profile.sourceFace.Elements) :
    (input.model ((classElements profile.sourceFace profile.classFace profile.observation).obj raw)).value
      (emptySection.val ((classElements profile.sourceFace profile.classFace profile.observation).obj raw)) = ∅ :=
  (input_value _ _).trans
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.emptyDisplayed_value raw)

def newRaw : profile.sourceFace.Elements :=
  ⟨PowerClassPresheafDescent.Controls.world 1,
    PowerClassPresheafDescent.Controls.stageValue 1 1 (by decide) true⟩

def newPoint : context.base.Elements :=
  (classElements profile.sourceFace profile.classFace profile.observation).obj newRaw

theorem identity_old_carrier : ((input.identity emptySection positiveSection).model old).carrier = {∅} := by
  have left := emptySection_value Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.oldRaw
  have right := positiveSection_value Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.oldRaw
  have same : emptySection.val old = positiveSection.val old :=
    (input.model old).value_injective (left.trans right.symm)
  change HSet.mk (PresheafIdentityWitness.graph (emptySection.val old) (positiveSection.val old)) = {∅}
  rw [same]
  exact PresheafIdentityWitness.graph_reflexive _

/-- New observed positions distinguish two actual natural section values;
the discrete identity carrier detects that difference. -/
theorem identity_new_carrier : ((input.identity emptySection positiveSection).model newPoint).carrier = ∅ := by
  have left := emptySection_value newRaw
  have right : (input.model newPoint).value (positiveSection.val newPoint) = HSet.quineAtom :=
    positiveSection_value newRaw
  have different : emptySection.val newPoint ≠ positiveSection.val newPoint := by
    intro same
    exact HSet.empty_ne_quineAtom (left.symm.trans ((congrArg (input.model newPoint).value same).trans right))
  exact PresheafIdentityWitness.graph_empty_of_distinct different

def unaryBody : MaterialFamily input.extension := MaterialFamily.unit input.extension

theorem unary_w_empty (point : context.base.Elements) :
    ((input.w unaryBody arrowCoding).model point).carrier = ∅ := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    let tree := ((input.w unaryBody arrowCoding).model point).decode ⟨value, member⟩
    have impossible : ∀ {X} (raw : ContextualWTypes.RawTree input.family
        (PowerClassPresheafProducts.indexedBody input.family unaryBody.family) X), False := by
      intro X raw
      induction raw with
      | @sup X _ _ ih => exact ih X (𝟙 X) (ULift.up PUnit.unit)
    exact (impossible tree.val).elim
  · intro member
    exact (HSet.notMem_empty value member).elim

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse
