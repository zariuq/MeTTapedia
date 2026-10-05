import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosure

/-!
# Full-family generated contextual member codes over wider parameters

Primitive families are the constructed original-bound members of actual
set-valued parameter maps. Dependent sum, complete future product,
discrete identity, contextual W and parameter substitution generate
whole displayed functors. Dependent bodies live on genuine comprehension
presheaves. Codes retain both that full functor and its formation recipe.

The fixed external parameter bound contains the material set presheaf and
the supplied wider parameters. The recipe type lives at its successor;
every decoded member/type fibre remains at the original context bound.
This is a generated external code system with an actual small-family
classifier. It neither identifies host type carriers with internal set
values nor asserts that the recipe system is an internally small universe.
External choice is inherited specifically through the member factory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamilies

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetModel HostChoiceContextualHypersetFamilyClosure
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality

universe u v
variable {D : Type u} [Category.{u} D]

abbrev Parameters (D : Type u) [Category.{u} D] := D ⥤ Type (max (u+1) v)

/-- Every formation constructor produces the full contextual family, with
its actual maps. The seed constructor accepts an authored material map,
not an arbitrary ambient family or a supplied closure theorem. -/
inductive Generation : {parameters : Parameters.{u,v} D} →
    (parameters.Elements ⥤ Type u) → Type ((max (u+1) v)+1)
  | member {parameters : Parameters.{u,v} D} (parent : NaturalHom parameters sets) :
      Generation (memberFamilyUnder parent)
  | sigma {parameters : Parameters.{u,v} D} {domain : parameters.Elements ⥤ Type u}
      {body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u}
      (first : Generation domain) (second : Generation body) :
      Generation (ContextualSmallFamilyTypeFormers.sigma domain
        (ContextualSmallFamilyComprehension.indexedBody domain body))
  | pi {parameters : Parameters.{u,v} D} {domain : parameters.Elements ⥤ Type u}
      {body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u}
      (first : Generation domain) (second : Generation body) :
      Generation (ContextualSmallFamilyTypeFormers.pi domain
        (ContextualSmallFamilyComprehension.indexedBody domain body))
  | identity {parameters : Parameters.{u,v} D} {domain : parameters.Elements ⥤ Type u}
      (first : Generation domain) (left right : domain.sections) :
      Generation (ContextualSmallFamilyIdentity.identityFamily domain left right)
  | w {parameters : Parameters.{u,v} D} {domain : parameters.Elements ⥤ Type u}
      {body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u}
      (first : Generation domain) (second : Generation body) :
      Generation (ContextualSmallFamilyWTypes.w domain
        (ContextualSmallFamilyComprehension.indexedBody domain body))
  | reindex {parameters other : Parameters.{u,v} D} {domain : parameters.Elements ⥤ Type u}
      (first : Generation domain) (change : NaturalHom other parameters) :
      Generation (ContextualSmallFamilyUniverse.substitutedFamily domain change)

abbrev Code (parameters : Parameters.{u,v} D) : Type ((max (u+1) v)+1) :=
  Σ family : parameters.Elements ⥤ Type u, Generation family

def decodeFamily {parameters : Parameters.{u,v} D} (code : Code parameters) : parameters.Elements ⥤ Type u :=
  code.1

def formationTag {parameters : Parameters.{u,v} D} {family : parameters.Elements ⥤ Type u} :
    Generation family → Nat
  | .member _ => 0
  | .sigma _ _ => 1
  | .pi _ _ => 2
  | .identity _ _ _ => 3
  | .w _ _ => 4
  | .reindex _ _ => 5

def codeTag {parameters : Parameters.{u,v} D} (code : Code parameters) : Nat := formationTag code.2

noncomputable def memberCode {parameters : Parameters.{u,v} D} (parent : NaturalHom parameters sets) :
    Code parameters := ⟨memberFamilyUnder parent, .member parent⟩

def sigmaCode {parameters : Parameters.{u,v} D} (domain : Code parameters)
    (body : Code (ContextualSmallFamilyUniverse.total (decodeFamily domain))) : Code parameters :=
  ⟨ContextualSmallFamilyTypeFormers.sigma (decodeFamily domain)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily domain) (decodeFamily body)),
      .sigma domain.2 body.2⟩

def piCode {parameters : Parameters.{u,v} D} (domain : Code parameters)
    (body : Code (ContextualSmallFamilyUniverse.total (decodeFamily domain))) : Code parameters :=
  ⟨ContextualSmallFamilyTypeFormers.pi (decodeFamily domain)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily domain) (decodeFamily body)),
      .pi domain.2 body.2⟩

def identityCode {parameters : Parameters.{u,v} D} (domain : Code parameters)
    (left right : (decodeFamily domain).sections) : Code parameters :=
  ⟨ContextualSmallFamilyIdentity.identityFamily (decodeFamily domain) left right,
    .identity domain.2 left right⟩

noncomputable def wCode {parameters : Parameters.{u,v} D} (domain : Code parameters)
    (body : Code (ContextualSmallFamilyUniverse.total (decodeFamily domain))) : Code parameters :=
  ⟨ContextualSmallFamilyWTypes.w (decodeFamily domain)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily domain) (decodeFamily body)),
      .w domain.2 body.2⟩

def substitute {parameters other : Parameters.{u,v} D}
    (code : Code parameters) (change : NaturalHom other parameters) : Code other :=
  ⟨ContextualSmallFamilyUniverse.substitutedFamily (decodeFamily code) change,
    .reindex code.2 change⟩

def classifier {parameters : Parameters.{u,v} D} (code : Code parameters) :
    NaturalHom parameters ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (decodeFamily code)

theorem full_decoder {parameters : Parameters.{u,v} D} (code : Code parameters) :
    ContextualSmallFamilyUniverse.decodedFamily (classifier code) = decodeFamily code :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

def classificationForward {parameters : Parameters.{u,v} D} (code : Code parameters) :
    NaturalHom (ContextualSmallFamilyUniverse.total (decodeFamily code))
      (ContextualSmallFamilyUniverse.GenericPullback (classifier code)) :=
  ContextualSmallFamilyUniverse.classificationForward (decodeFamily code)

def classificationBackward {parameters : Parameters.{u,v} D} (code : Code parameters) :
    NaturalHom (ContextualSmallFamilyUniverse.GenericPullback (classifier code))
      (ContextualSmallFamilyUniverse.total (decodeFamily code)) :=
  ContextualSmallFamilyUniverse.classificationBackward (decodeFamily code)

theorem classification_left {parameters : Parameters.{u,v} D} (code : Code parameters)
    (point : D) (receipt : (ContextualSmallFamilyUniverse.total (decodeFamily code)).obj point) :
    (classificationBackward code).app point ((classificationForward code).app point receipt) = receipt :=
  ContextualSmallFamilyUniverse.classification_left _ _ _

theorem classification_right {parameters : Parameters.{u,v} D} (code : Code parameters)
    (point : D) (receipt : (ContextualSmallFamilyUniverse.GenericPullback (classifier code)).obj point) :
    (classificationForward code).app point ((classificationBackward code).app point receipt) = receipt :=
  ContextualSmallFamilyUniverse.classification_right _ _ _

def classificationSections {parameters : Parameters.{u,v} D} (code : Code parameters) :
    (ContextualSmallFamilyUniverse.total (decodeFamily code)).sections ≃
      (ContextualSmallFamilyUniverse.GenericPullback (classifier code)).sections :=
  ContextualSmallFamilyUniverse.classificationSectionEquiv _

theorem full_decode_restriction {parameters : Parameters.{u,v} D} (code : Code parameters)
    {first second : parameters.Elements} (step : first ⟶ second)
    (term : ContextualSmallFamilyUniverse.decode
      (ContextualSmallFamilyUniverse.familyCode (decodeFamily code) first.1 first.2)) :
    ContextualSmallFamilyUniverse.evaluationEquiv (decodeFamily code) second.1 second.2
      ((ContextualSmallFamilyUniverse.decodedFamily (classifier code)).map step term) =
    (decodeFamily code).map step
      (ContextualSmallFamilyUniverse.evaluationEquiv (decodeFamily code) first.1 first.2 term) := by
  have source := ContextualSmallFamilyUniverse.evaluationPoint_eq first.1 first.2
  have target : (ContextualSmallFamilyUniverse.futureElement first.1 first.2).obj
      ((ContextualSmallFamilyUniverse.futurePrefix step.1).obj
        (ContextualSmallFamilyUniverse.root second.1)) = second :=
    Sigma.ext rfl (heq_of_eq ((congrArg (fun arrow => parameters.map arrow first.2)
      (Category.comp_id step.1)).trans step.2))
  have moved := ContextualSmallFamilyUniverse.familyMap_heq (decodeFamily code) source target
    ((ContextualSmallFamilyUniverse.futureElement first.1 first.2).map
      (ContextualSmallFamilyUniverse.rootArrow step.1)) step
    (ContextualSmallFamilyUniverse.elementsArrow_heq source target _ step (heq_of_eq rfl))
    term (ContextualSmallFamilyUniverse.evaluationEquiv (decodeFamily code) first.1 first.2 term)
    (ContextualSmallFamilyUniverse.cast_heq _ _).symm
  exact eq_of_heq ((ContextualSmallFamilyUniverse.cast_heq _ _).trans
    ((ContextualSmallFamilyUniverse.decoder_map_heq
      ((ContextualSmallFamilyUniverse.elementMap (classifier code)).map step) term).trans moved))

theorem classifier_substitution {parameters other : Parameters.{u,v} D}
    (code : Code parameters) (change : NaturalHom other parameters) :
    classifier (substitute code change) = change.comp (classifier code) :=
  ContextualSmallFamilyUniverse.classifier_parameter_substitution _ _

theorem decoder_substitution_id {parameters : Parameters.{u,v} D} (code : Code parameters) :
    decodeFamily (substitute code (ContextualSmallMapConstructions.identity parameters)) = decodeFamily code :=
  ContextualSmallFamilyUniverse.substitutedFamily_id _

theorem decoder_substitution_comp {parameters other third : Parameters.{u,v} D}
    (code : Code parameters) (change : NaturalHom other parameters) (earlier : NaturalHom third other) :
    decodeFamily (substitute (substitute code change) earlier) =
      decodeFamily (substitute code (earlier.comp change)) :=
  ContextualSmallFamilyUniverse.substitutedFamily_comp _ _ _

/-- Even identity substitution retains an authored recipe step. Its
decoder is unchanged, while its formation provenance need not be equal. -/
theorem seed_identity_recipe_distinct {parameters : Parameters.{u,v} D}
    (parent : NaturalHom parameters sets) :
    substitute (memberCode parent) (ContextualSmallMapConstructions.identity parameters) ≠ memberCode parent := by
  intro same
  have tags := congrArg codeTag same
  change 5 = 0 at tags
  exact Nat.noConfusion tags

section ActualMemberBody

variable {parameters : Parameters.{u,v} D} (parent : NaturalHom parameters sets)
variable (bodyMap : NaturalHom (comprehension parent) sets)

noncomputable def memberSigmaCode : Code parameters := sigmaCode (memberCode parent) (memberCode bodyMap)
noncomputable def memberPiCode : Code parameters := piCode (memberCode parent) (memberCode bodyMap)
noncomputable def memberWCode : Code parameters := wCode (memberCode parent) (memberCode bodyMap)

theorem memberSigma_full_decode :
    ContextualSmallFamilyUniverse.decodedFamily (classifier (memberSigmaCode parent bodyMap)) =
      sigmaFamily parent bodyMap := full_decoder _

theorem memberPi_full_decode :
    ContextualSmallFamilyUniverse.decodedFamily (classifier (memberPiCode parent bodyMap)) =
      piFamily parent bodyMap := full_decoder _

theorem memberW_full_decode :
    ContextualSmallFamilyUniverse.decodedFamily (classifier (memberWCode parent bodyMap)) =
      wFamily parent bodyMap := full_decoder _

noncomputable def memberPiLiteralEquiv (parameter : parameters.Elements) :
    (decodeFamily (memberPiCode parent bodyMap)).obj parameter ≃
      (futureLiteralBody parent bodyMap parameter).sections := piDecoder parent bodyMap parameter

noncomputable def memberPiLiteralSections :
    (decodeFamily (memberPiCode parent bodyMap)).sections ≃ LiteralProducts parent bodyMap :=
  piSectionDecoder parent bodyMap

theorem memberPiLiteral_value (parameter : parameters.Elements)
    (term : (decodeFamily (memberPiCode parent bodyMap)).obj parameter)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (domain parent) parameter).Elements) :
    ((memberPiLiteralEquiv parent bodyMap parameter term).val argument).val =
      (bodyDecoder parent bodyMap ((ContextualSmallFamilyTypeFormers.futureArguments (domain parent) parameter).obj
        argument) (term.val argument)).val := piDecoder_value parent bodyMap parameter term argument

end ActualMemberBody

section FormerSubstitution

variable {parameters other : Parameters.{u,v} D}
variable (input : Code parameters)
variable (output : Code (ContextualSmallFamilyUniverse.total (decodeFamily input)))
variable (change : NaturalHom other parameters)

def bodyUnderCode : Code (ContextualSmallFamilyUniverse.total (decodeFamily (substitute input change))) :=
  substitute output (ContextualSmallFamilyComprehension.totalChange (decodeFamily input) change)

theorem indexed_body_substitution :
    ContextualSmallFamilyComprehension.indexedBody (decodeFamily (substitute input change))
      (decodeFamily (bodyUnderCode input output change)) =
    ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (decodeFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output)) :=
  ContextualSmallFamilyComprehension.indexedBody_substitution _ _ _

def freshSigmaCode : Code other := sigmaCode (substitute input change) (bodyUnderCode input output change)
def freshPiCode : Code other := piCode (substitute input change) (bodyUnderCode input output change)
noncomputable def freshWCode : Code other := wCode (substitute input change) (bodyUnderCode input output change)

theorem sigmaCode_decoder_substitution :
    decodeFamily (freshSigmaCode input output change) =
      decodeFamily (substitute (sigmaCode input output) change) := by
  change ContextualSmallFamilyTypeFormers.sigma _ _ = _
  rw [indexed_body_substitution]
  exact ContextualSmallFamilyTypeFormerCoherence.sigma_substitution change _ _

theorem wCode_decoder_substitution :
    decodeFamily (substitute (wCode input output) change) =
      decodeFamily (freshWCode input output change) := by
  change _ = ContextualSmallFamilyWTypes.w _ _
  rw [indexed_body_substitution]
  exact ContextualSmallFamilyWSubstitutionCoherence.w_substitution_eq change _ _

theorem freshPiCode_family_eq :
    decodeFamily (freshPiCode input output change) =
      ContextualSmallFamilyTypeFormers.pi (decodeFamily (substitute input change))
        (ContextualSmallFamilyTypeFormerCoherence.bodyUnder change (decodeFamily input)
          (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output))) :=
  congrArg (ContextualSmallFamilyTypeFormers.pi (decodeFamily (substitute input change)))
    (indexed_body_substitution input output change)

def piCodeSubstitution : NatTrans (decodeFamily (substitute (piCode input output) change))
    (decodeFamily (freshPiCode input output change)) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution change (decodeFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output)))
    (familyEqHom (freshPiCode_family_eq input output change).symm)

def piCodeSubstitutionInverse : NatTrans (decodeFamily (freshPiCode input output change))
    (decodeFamily (substitute (piCode input output) change)) :=
  ContextualSmallFamilyTypeFormers.composeNat
    (familyEqHom (freshPiCode_family_eq input output change))
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitutionInverse change (decodeFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output)))

theorem piCodeSubstitution_left :
    ContextualSmallFamilyTypeFormers.composeNat (piCodeSubstitution input output change)
      (piCodeSubstitutionInverse input output change) = ContextualSmallFamilyTypeFormers.identityNat
        (decodeFamily (substitute (piCode input output) change)) :=
  inverseAfterFamilyEquality (freshPiCode_family_eq input output change) _ _
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_left change (decodeFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output)))

theorem piCodeSubstitution_right :
    ContextualSmallFamilyTypeFormers.composeNat (piCodeSubstitutionInverse input output change)
      (piCodeSubstitution input output change) = ContextualSmallFamilyTypeFormers.identityNat
        (decodeFamily (freshPiCode input output change)) :=
  equalityAfterInverse (freshPiCode_family_eq input output change) _ _
    (ContextualSmallFamilyTypeFormerCoherence.piSubstitution_right change (decodeFamily input)
      (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output)))

def piCodeSubstitutionSections :
    (decodeFamily (substitute (piCode input output) change)).sections ≃
      (decodeFamily (freshPiCode input output change)).sections :=
  (ContextualSmallFamilyTypeFormerCoherence.productSectionComparison change (decodeFamily input)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily input) (decodeFamily output))).trans
    (ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun family : other.Elements ⥤ Type u =>
        (family.sections : Type (max (u+1) v))) (freshPiCode_family_eq input output change).symm))

def freshIdentityCode (left right : (decodeFamily input).sections) : Code other :=
  identityCode (substitute input change)
    (ContextualSmallFamilyIdentity.reindexSection change (decodeFamily input) left)
    (ContextualSmallFamilyIdentity.reindexSection change (decodeFamily input) right)

theorem identityCode_decoder_substitution (left right : (decodeFamily input).sections) :
    decodeFamily (substitute (identityCode input left right) change) =
      decodeFamily (freshIdentityCode input change left right) :=
  ContextualSmallFamilyIdentity.identityFamily_substitution _ _ _ _

end FormerSubstitution

section WiderParameters

variable (parameters : D ⥤ Type v)

/-- This explicit wrapper puts arbitrary supplied parameters at the
grammar's fixed bound; it neither enumerates nor shrinks those parameters. -/
def raisedParameters : Parameters.{u,v} D where
  obj point := ULift.{u+1} (parameters.obj point)
  map arrow := TypeCat.ofHom fun value => ULift.up (parameters.map arrow value.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (parameters.map_id_apply point value.down)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (parameters.map_comp_apply earlier later value.down)

def lowerParameters : NaturalHom (raisedParameters parameters) parameters where
  app _ value := value.down
  naturality _ _ := rfl

def upperParameters : NaturalHom parameters (raisedParameters parameters) where
  app _ value := ULift.up value
  naturality _ _ := rfl

theorem parameter_lower_upper : (lowerParameters parameters).comp (upperParameters parameters) =
    ContextualSmallMapConstructions.identity (raisedParameters parameters) := by
  apply NaturalHom.ext
  intro _ value
  cases value
  rfl

theorem parameter_upper_lower : (upperParameters parameters).comp (lowerParameters parameters) =
    ContextualSmallMapConstructions.identity parameters := by
  apply NaturalHom.ext
  intro _ _
  rfl

def raisedElement : parameters.Elements ⥤ (raisedParameters parameters).Elements where
  obj point := ⟨point.1, ULift.up point.2⟩
  map arrow := CategoryOfElements.homMk _ _ arrow.1 (congrArg ULift.up arrow.2)
  map_id _ := rfl
  map_comp _ _ := rfl

def raisedSectionsEquiv (family : parameters.Elements ⥤ Type u) :
    (ContextualSmallFamilyUniverse.substitutedFamily family (lowerParameters parameters)).sections ≃ family.sections where
  toFun term := ⟨fun point => term.val ((raisedElement parameters).obj point),
    fun arrow => term.property ((raisedElement parameters).map arrow)⟩
  invFun term := ContextualSmallFamilyComprehension.sectionPull
    (ContextualSmallFamilyUniverse.elementMap (lowerParameters parameters)) family term
  left_inv term := by
    apply Subtype.ext
    funext point
    rcases point with ⟨world, ⟨value⟩⟩
    rfl
  right_inv term := by
    apply Subtype.ext
    funext point
    rfl

noncomputable def raisedMemberCode (parent : NaturalHom parameters sets) :
    Code (raisedParameters parameters) := memberCode ((lowerParameters parameters).comp parent)

noncomputable def raisedMemberSections (parent : NaturalHom parameters sets) :
    (decodeFamily (raisedMemberCode parameters parent)).sections ≃
      (memberFamilyUnder parent).sections :=
  raisedSectionsEquiv parameters (memberFamilyUnder parent)

theorem raisedMember_literal_value (parent : NaturalHom parameters sets)
    (term : (decodeFamily (raisedMemberCode parameters parent)).sections) (parameter : parameters.Elements) :
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj parameter)
      ((raisedMemberSections parameters parent term).val parameter)).val =
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap
      ((lowerParameters parameters).comp parent)).obj ((raisedElement parameters).obj parameter))
      (term.val ((raisedElement parameters).obj parameter))).val := rfl

end WiderParameters

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamilies
