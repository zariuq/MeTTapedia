import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCumulativity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes
import Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes

/-!
# Generated dependent material families of observed operational systems

An authored contextual system supplies its operational restrictions and
observed labelled behaviour. Its actual value graphs construct faithful
labels for entire observation classes. The dependent source graph family
and its admissible material restrictions then construct all fibre models.
Contextual Pi, Sigma, discrete identity and W formation use the generated
operations and their proved decoders.

World and actual-arrow graph dictionaries are retained input data. They
encode context indices without claiming a host-context decoder. Native
predicate classification concerns the same contextual family readout;
past modal lifting remains a separate operational condition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedGeneratedModel

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualObservedFamilyEnclosure
open ContextualGeneratedUniverse
open PowerClassFamilyDescent

universe u
variable {C : Type u} [Category.{u} C]
variable (profile : ContextualSystem C)
variable (worlds : ArgumentCoding Cᵒᵖ)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (graphs : profile.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : PowerClassPresheafDescent.MaterialTransport
  profile.sourceFace profile.classFace profile.observation graphs)

def valueGraphs (X : Cᵒᵖ) (source : (profile.theory X).Term) : AccessiblePointedGraph.{u} :=
  ObservedFamilyEnclosure.valueGraph (profile.readings X) source

theorem valueGraphs_invariant (X : Cᵒᵖ) :
    FamilyInvariant (profile.observation.app X) (valueGraphs profile X) := by
  intro left right same
  exact (profile.readings X).value_eq_of_bisimilar
    ((profile.observation_eq_iff X left right).mp same)

/-- Class labels are constructed from all the supplied source value graphs.
No source representative or graph presentation is selected. -/
def classCoding (X : Cᵒᵖ) : ArgumentCoding ((Families.observedBase profile).obj X) where
  graph observed := familyGraph (valueGraphs profile X) observed
  injective := by
    intro first second same
    obtain ⟨left, leftEq⟩ := classOf_surjective (profile.observation.app X) first
    obtain ⟨right, rightEq⟩ := classOf_surjective (profile.observation.app X) second
    have leftValue := (familyGraph_decode (valueGraphs profile X) first).trans
      ((congrArg (decodedFamily (valueGraphs profile X)) leftEq.symm).trans
        (family_beta (profile.observation.app X) (valueGraphs profile X)
          (valueGraphs_invariant profile X) left))
    have rightValue := (familyGraph_decode (valueGraphs profile X) second).trans
      ((congrArg (decodedFamily (valueGraphs profile X)) rightEq.symm).trans
        (family_beta (profile.observation.app X) (valueGraphs profile X)
          (valueGraphs_invariant profile X) right))
    have values : (profile.readings X).value left = (profile.readings X).value right :=
      leftValue.symm.trans (same.trans rightValue)
    have observations := (profile.observation_eq_iff X left right).mpr
      (((profile.readings X).value_eq_iff_bisimilar (profile.faithful X) left right).mp values)
    exact leftEq.symm.trans (((classOf_eq_iff _ left right).mpr observations).trans rightEq)

def pointCoding : ArgumentCoding (Families.observedBase profile).Elements where
  graph point := AccessiblePointedGraph.kpairGraph (worlds.graph point.1)
    ((classCoding profile point.1).graph point.2)
  injective := by
    rintro ⟨X, first⟩ ⟨Y, second⟩ same
    dsimp only at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    have contexts : X = Y := worlds.injective (HSet.kpair_inj.mp same).1
    subst Y
    exact Sigma.ext rfl (heq_of_eq ((classCoding profile X).injective (HSet.kpair_inj.mp same).2))

def context : LabelledContext C where
  base := Families.observedBase profile
  labels := pointCoding profile worlds

/-- The seed dictionary is the constructed graph-member-class decoder of
the actual descended source family. No fibre decoding is supplied. -/
def input : MaterialFamily (context profile worlds) where
  family := Families.displayed profile graphs transport
  model point := PowerClassContextualMaterialization.powerClassModel
    (familyGraph (fun source => graphs ⟨point.1, source⟩) point.2)

def observedPoint (source : profile.sourceFace.Elements) : (context profile worlds).base.Elements :=
  (PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj source

theorem input_value (point : (context profile worlds).base.Elements)
    (member : (input profile worlds graphs transport).family.obj point) :
    ((input profile worlds graphs transport).model point).value member =
      (PowerClassPresheafDescent.contextualMemberEquiv profile.sourceFace profile.classFace
        profile.observation graphs point member).1 :=
  (PowerClassContextualMaterialization.powerClassModel_value _ member).trans
    (familyMemberEquiv_value _ _ member).symm

theorem input_source_carrier (source : profile.sourceFace.Elements) :
    ((input profile worlds graphs transport).model (observedPoint profile worlds source)).carrier =
      HSet.mk (graphs source) :=
  (familyGraph_decode (fun value => graphs ⟨source.1, value⟩)
    (classOf (profile.observation.app source.1) source.2)).trans
      (family_beta (profile.observation.app source.1) (fun value => graphs ⟨source.1, value⟩)
        (transport.invariant source.1) source.2)

theorem observedPoint_eq_iff (X : Cᵒᵖ) (left right : (profile.theory X).Term) :
    observedPoint profile worlds ⟨X, left⟩ = observedPoint profile worlds ⟨X, right⟩ ↔
      (profile.system X).Bisimilar left right := by
  constructor
  · intro same
    have classes : classOf (profile.observation.app X) left = classOf (profile.observation.app X) right :=
      eq_of_heq ((Sigma.mk.inj_iff.mp same).2)
    exact (profile.observation_eq_iff X left right).mp ((classOf_eq_iff _ left right).mp classes)
  · intro related
    exact Sigma.ext rfl (heq_of_eq ((classOf_eq_iff _ left right).mpr
      ((profile.observation_eq_iff X left right).mpr related)))

def Seeds (declared : LabelledContext C) : Type (u + 1) :=
  ULift.{u + 1} (PLift (declared = context profile worlds))

def seedModel (declared : LabelledContext C) (label : Seeds profile worlds declared) : MaterialFamily declared := by
  rcases label with ⟨⟨same⟩⟩
  cases same
  exact input profile worlds graphs transport

def inputGenerated : Generation (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows
    (input profile worlds graphs transport) :=
  .seed (context profile worlds) (ULift.up (PLift.up rfl))

/-- The dependent body is the original interpreted family over its actual
comprehension projection. Its decoder is constructed by reindexing. -/
def body : MaterialFamily (input profile worlds graphs transport).extension :=
  (input profile worlds graphs transport).reindex
    (PowerClassPresheafProducts.projection (input profile worlds graphs transport).family)

def bodyGenerated : Generation (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows
    (body profile worlds graphs transport) :=
  .reindex (inputGenerated profile worlds arrows graphs transport) _

def piGenerated : Generation (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows
    ((input profile worlds graphs transport).pi (body profile worlds graphs transport) arrows) :=
  .pi (inputGenerated profile worlds arrows graphs transport) (bodyGenerated profile worlds arrows graphs transport)

def sigmaGenerated : Generation (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows
    ((input profile worlds graphs transport).sigma (body profile worlds graphs transport)) :=
  .sigma (inputGenerated profile worlds arrows graphs transport) (bodyGenerated profile worlds arrows graphs transport)

def wGenerated : Generation (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows
    ((input profile worlds graphs transport).w (body profile worlds graphs transport) arrows) :=
  .w (inputGenerated profile worlds arrows graphs transport) (bodyGenerated profile worlds arrows graphs transport)

def identityGenerated (left right : (input profile worlds graphs transport).family.sections) :
    Generation (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows
      ((input profile worlds graphs transport).identity left right) :=
  .identity (inputGenerated profile worlds arrows graphs transport) left right

theorem identity_enclosed (left right : (input profile worlds graphs transport).family.sections)
    (point : (context profile worlds).base.Elements) :
    HSet.lift (((input profile worlds graphs transport).identity left right).model point).carrier ∈
      enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point :=
  generated_mem_enclosure _ _ _ (identityGenerated profile worlds arrows graphs transport left right) point

theorem pi_sigma_w_enclosed (point : (context profile worlds).base.Elements) :
    HSet.lift (((input profile worlds graphs transport).pi (body profile worlds graphs transport) arrows).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point ∧
    HSet.lift (((input profile worlds graphs transport).sigma (body profile worlds graphs transport)).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point ∧
    HSet.lift (((input profile worlds graphs transport).w (body profile worlds graphs transport) arrows).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point :=
  ⟨generated_mem_enclosure _ _ _ (piGenerated profile worlds arrows graphs transport) point,
    generated_mem_enclosure _ _ _ (sigmaGenerated profile worlds arrows graphs transport) point,
    generated_mem_enclosure _ _ _ (wGenerated profile worlds arrows graphs transport) point⟩

/-- Actual sections of the interpreted seed recover exactly the authored
source sections respecting both observed fibres and restriction maps. -/
def sourceSectionEquiv : (input profile worlds graphs transport).family.sections ≃
    {term : PowerClassPresheafDescent.RawSection profile.sourceFace graphs //
      PowerClassPresheafDescent.ContextualCompatible profile.sourceFace profile.classFace
        profile.observation graphs transport term} :=
  PowerClassPresheafDescent.contextualSectionEquiv profile.sourceFace profile.classFace
    profile.observation graphs transport

theorem sourceSectionEquiv_value
    (chosen : (input profile worlds graphs transport).family.sections)
    (source : profile.sourceFace.Elements) :
    ((input profile worlds graphs transport).model (observedPoint profile worlds source)).value
      (chosen.val (observedPoint profile worlds source)) =
        ((sourceSectionEquiv profile worlds graphs transport chosen).val source).1 :=
  (input_value profile worlds graphs transport _ _).trans
    (PowerClassPresheafDescent.pullContextualSection_value profile.sourceFace profile.classFace
      profile.observation graphs transport chosen source).symm

theorem sourceSectionEquiv_inverse_value
    (term : PowerClassPresheafDescent.RawSection profile.sourceFace graphs)
    (compatible : PowerClassPresheafDescent.ContextualCompatible profile.sourceFace profile.classFace
      profile.observation graphs transport term) (source : profile.sourceFace.Elements) :
    ((input profile worlds graphs transport).model (observedPoint profile worlds source)).value
      (((sourceSectionEquiv profile worlds graphs transport).symm ⟨term, compatible⟩).val
        (observedPoint profile worlds source)) = (term source).1 :=
  (input_value profile worlds graphs transport _ _).trans
    (Families.descendedArgument_value profile graphs transport term compatible source)

/-- The generated material full-future Pi realizes abstraction of the
actual last variable. Evaluation recovers the complete authored member. -/
theorem identity_application_source_value
    (term : PowerClassPresheafDescent.RawSection profile.sourceFace graphs)
    (compatible : PowerClassPresheafDescent.ContextualCompatible profile.sourceFace profile.classFace
      profile.observation graphs transport term) (source : profile.sourceFace.Elements) :
    ((input profile worlds graphs transport).model (observedPoint profile worlds source)).value
      ((PowerClassPresheafProducts.piApply
        (ConstructiveFamilies.identityFunction profile graphs transport)
        ((sourceSectionEquiv profile worlds graphs transport).symm ⟨term, compatible⟩)).val
          (observedPoint profile worlds source)) = (term source).1 :=
  (input_value profile worlds graphs transport _ _).trans
    (ConstructiveFamilies.identityApplication_source_value profile graphs transport term compatible source)

theorem identity_function_entry (point : (context profile worlds).base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments
      (input profile worlds graphs transport).family point) :
    LabelledDependentProducts.evalValue
      ((input profile worlds graphs transport).futureCoding arrows point)
      ((input profile worlds graphs transport).futureOutputs (body profile worlds graphs transport) point)
      ((((input profile worlds graphs transport).pi (body profile worlds graphs transport) arrows).model point).value
        ((ConstructiveFamilies.identityFunction profile graphs transport).val point)) argument =
      ((input profile worlds graphs transport).model argument.1.1).value argument.2 :=
  ((input profile worlds graphs transport).pi_evaluation (body profile worlds graphs transport) arrows point _ argument).trans
    (congrArg ((input profile worlds graphs transport).model argument.1.1).value
      (ConstructiveFamilies.identityFunction_future profile graphs transport _ _ _ _))

def sourceFamily (domain : MaterialFamily (context profile worlds)) :=
  PowerClassPresheafProducts.reindex
    (PowerClassPresheafDescent.classObservation profile.sourceFace profile.classFace profile.observation) domain.family

theorem source_support_kernel (domain : MaterialFamily (context profile worlds)) (X : Cᵒᵖ)
    (left right : profile.sourceFace.obj X) (related : (profile.system X).Bisimilar left right) :
    (left ∈ (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds domain)).obj X ↔
      right ∈ (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds domain)).obj X) := by
  change Nonempty (domain.family.obj (observedPoint profile worlds ⟨X, left⟩)) ↔
    Nonempty (domain.family.obj (observedPoint profile worlds ⟨X, right⟩))
  exact (observedPoint_eq_iff profile worlds X left right).mpr related ▸ Iff.rfl

/-- Every generated family, including complete future functions and trees,
has its source comprehension support classified on the actual observed
system. This predicate factorization does not select a dependent term. -/
theorem source_classifier_factors (domain : MaterialFamily (context profile worlds)) :
    ∃ classifier : NatTrans profile.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ X source, classifier.app X (profile.observation.app X source) =
        (Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes.Classifier.characteristic
          (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds domain))).app X source :=
  (Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes.classifier_factors_iff profile _).mpr
    (source_support_kernel profile worlds domain)

abbrev Code (declared : LabelledContext C) :=
  ContextualUniverseCodes.Code (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows declared

def inputCode : Code profile worlds arrows graphs transport (context profile worlds) :=
  ContextualUniverseCodes.ofRaw _ _ _ ⟨input profile worlds graphs transport,
    inputGenerated profile worlds arrows graphs transport⟩

def decodeCode {declared : LabelledContext C} :
    Code profile worlds arrows graphs transport declared → MaterialFamily declared :=
  ContextualUniverseCodes.decodeFamily _ _ _

def substituteCode {declared other : LabelledContext C} (change : NatTrans other.base declared.base) :
    Code profile worlds arrows graphs transport declared → Code profile worlds arrows graphs transport other :=
  ContextualUniverseCodes.reindex _ _ _ change

theorem decodeCode_substitution {declared other : LabelledContext C}
    (change : NatTrans other.base declared.base) (code : Code profile worlds arrows graphs transport declared) :
    decodeCode profile worlds arrows graphs transport (substituteCode profile worlds arrows graphs transport change code) =
      (decodeCode profile worlds arrows graphs transport code).reindex change :=
  ContextualUniverseCodes.decodeFamily_reindex _ _ _ change code

theorem code_enclosed {declared : LabelledContext C}
    (code : Code profile worlds arrows graphs transport declared) (point : declared.base.Elements) :
    HSet.lift ((decodeCode profile worlds arrows graphs transport code).model point).carrier ∈
      enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows declared point := by
  obtain ⟨formed⟩ := ContextualUniverseCodes.formed (Seeds profile worlds)
    (seedModel profile worlds graphs transport) arrows code
  exact generated_mem_enclosure _ _ _ formed point

theorem code_cumulative_decoder {declared : LabelledContext C}
    (code : Code profile worlds arrows graphs transport declared) (point : declared.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeCode profile worlds arrows graphs transport code).model point).carrier}) :
    ((ContextualGeneratedCumulativity.model (decodeCode profile worlds arrows graphs transport code) point).decode
      (ContextualGeneratedCumulativity.memberEquiv (decodeCode profile worlds arrows graphs transport code) point member)).down =
        ((decodeCode profile worlds arrows graphs transport code).model point).decode member :=
  ContextualGeneratedCumulativity.memberEquiv_decode _ _ _

/-- The joined construction has a concrete observed seed, actual material
Pi/Sigma/identity/W carriers, formation-preserving code substitution and
native classification for every interpreted generated family. -/
theorem observed_generated_model :
    (∀ source, ((input profile worlds graphs transport).model (observedPoint profile worlds source)).carrier =
      HSet.mk (graphs source)) ∧
    (∀ X left right, observedPoint profile worlds ⟨X, left⟩ = observedPoint profile worlds ⟨X, right⟩ ↔
      (profile.system X).Bisimilar left right) ∧
    (∀ point, HSet.lift (((input profile worlds graphs transport).pi (body profile worlds graphs transport) arrows).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point ∧
      HSet.lift (((input profile worlds graphs transport).sigma (body profile worlds graphs transport)).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point ∧
      HSet.lift (((input profile worlds graphs transport).w (body profile worlds graphs transport) arrows).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point) ∧
    (∀ left right point, HSet.lift (((input profile worlds graphs transport).identity left right).model point).carrier ∈
      enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows (context profile worlds) point) ∧
    (∀ {declared} (code : Code profile worlds arrows graphs transport declared) point,
      HSet.lift ((decodeCode profile worlds arrows graphs transport code).model point).carrier ∈
        enclosure (Seeds profile worlds) (seedModel profile worlds graphs transport) arrows declared point) ∧
    (∀ code : Code profile worlds arrows graphs transport (context profile worlds),
      ∃ classifier : NatTrans profile.classFace (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
        ∀ X source, classifier.app X (profile.observation.app X source) =
          (Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes.Classifier.characteristic
            (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds
              (decodeCode profile worlds arrows graphs transport code)))).app X source) :=
  ⟨input_source_carrier profile worlds graphs transport, observedPoint_eq_iff profile worlds,
    pi_sigma_w_enclosed profile worlds arrows graphs transport, identity_enclosed profile worlds arrows graphs transport,
    code_enclosed profile worlds arrows graphs transport,
    fun code => source_classifier_factors profile worlds (decodeCode profile worlds arrows graphs transport code)⟩

namespace Modal

open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities
open Mettapedia.OSLF.Bridges.TypeTheory
open Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes

variable (occurrences : ∀ X, ObservedMaterialization.ActionOccurrences (profile.system X))
variable (action : Events.EventAction profile occurrences)

/-- Generated family support commutes with the actual future diamond of
the source event presheaf. Its complete authored event fibres are retained. -/
theorem generated_diamond
    (code : Code profile worlds arrows graphs transport (context profile worlds)) :
    preimage profile.observation
      (diamond (ContextualObservedNativeTypes.Modal.observedGraph profile occurrences action)
        (observedImage profile (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds
          (decodeCode profile worlds arrows graphs transport code))))) =
      diamond (ContextualObservedNativeTypes.Modal.sourceGraph profile occurrences action)
        (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds
          (decodeCode profile worlds arrows graphs transport code))) :=
  ContextualObservedNativeTypes.Modal.diamond_image_exact profile occurrences action _
    (source_support_kernel profile worlds _)

/-- Incoming event matching is the precise additional condition for the
predecessor box, including all later contextual restrictions. -/
theorem generated_box
    (incoming : ∀ X, ((occurrences X).observation (profile.readings X)).TargetLifts)
    (code : Code profile worlds arrows graphs transport (context profile worlds)) :
    preimage profile.observation
      (box (ContextualObservedNativeTypes.Modal.observedGraph profile occurrences action)
        (observedImage profile (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds
          (decodeCode profile worlds arrows graphs transport code))))) =
      box (ContextualObservedNativeTypes.Modal.sourceGraph profile occurrences action)
        (Mettapedia.GSLT.Topos.support (sourceFamily profile worlds
          (decodeCode profile worlds arrows graphs transport code))) :=
  ContextualObservedNativeTypes.Modal.box_image_exact profile occurrences action incoming _
    (source_support_kernel profile worlds _)

end Modal

end Mettapedia.GSLT.ObservedGeneratedModel
