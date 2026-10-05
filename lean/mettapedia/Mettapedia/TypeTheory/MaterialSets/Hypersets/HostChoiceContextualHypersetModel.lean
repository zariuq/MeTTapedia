import Mettapedia.TypeTheory.HostChoiceContextualPresheafProfile
import Mettapedia.TypeTheory.ContextualSmallFamilyIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInfinity

/-!
# Actual member families in the optional contextual hyperset model

The final covered-power coalgebra and the fixed-successor ambient profile
live over the same small site. Its actual membership projection constructs
an original-bound coherent displayed family using the explicitly priced
host decoder. This family decodes to literal material members, preserves
their authored restrictions, and compares whole compatible sections.

The member family is classified by the constructed small-family universe.
Its dependent type formers retain the complete future cone. All data below
are constructed from the site; no model, decoder or closure provider is an
additional parameter. External host choice remains part of this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization ContextualCoherentSmallMaps
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open CoveredFuturePowerClassifier

universe u v
variable {D : Type u} [Category.{u} D]

abbrev memberTotal : D ⥤ Type (u + 1) :=
  ContextualCoveredRelationClassifier.total sets sets membershipRelation.predicate

abbrev memberProjection : NaturalHom (memberTotal (D := D)) sets :=
  ContextualCoveredRelationClassifier.parameterProjection sets sets membershipRelation.predicate

noncomputable def memberData : Data (memberProjection (D := D)) :=
  HostChoiceContextualSmallMapRepresentation.selectedModel memberProjection membershipRelation.small

noncomputable abbrev memberFamily : (sets (D := D)).Elements ⥤ Type u := memberData.family

abbrev ActualMember (point : (sets (D := D)).Elements) : Type (u + 1) :=
  {child : sets.obj point.1 // Member point.1 child point.2}

def actualMemberMap {first second : (sets (D := D)).Elements} (step : first ⟶ second)
    (member : ActualMember first) : ActualMember second :=
  ⟨sets.map step.1 member.val, by
    have transported := member_transport step.1 member.property
    exact (congrArg (fun parent => Member second.1 (sets.map step.1 member.val) parent) step.2) ▸ transported⟩

def actualMemberFamily : (sets (D := D)).Elements ⥤ Type (u + 1) where
  obj := ActualMember
  map step := TypeCat.ofHom (actualMemberMap step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro member
    apply Subtype.ext
    change sets.map (𝟙 point.1) member.val = member.val
    exact sets.map_id_apply point.1 member.val
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro member
    apply Subtype.ext
    change sets.map (first.1 ≫ second.1) member.val = sets.map second.1 (sets.map first.1 member.val)
    exact sets.map_comp_apply first.1 second.1 member.val

/-- Both directions preserve the actual child value; no covering receipt
is chosen by this row comparison. The preceding family factory is optional. -/
noncomputable def memberDecoder (point : (sets (D := D)).Elements) :
    memberFamily.obj point ≃ ActualMember point :=
  (memberData.decoder point).trans
    (ContextualCoveredRelationClassifier.parameterFibreEquiv sets sets membershipRelation.predicate
      point.1 point.2)

theorem memberDecoder_restriction {first second : (sets (D := D)).Elements}
    (step : first ⟶ second) (code : memberFamily.obj first) :
    actualMemberMap step (memberDecoder first code) = memberDecoder second (memberFamily.map step code) := by
  apply Subtype.ext
  exact congrArg (fun receipt : Fibre memberProjection second.1 second.2 => receipt.val.val.2)
    (memberData.naturality step code)

theorem memberDecoder_restriction_value {first second : (sets (D := D)).Elements}
    (step : first ⟶ second) (code : memberFamily.obj first) :
    sets.map step.1 (memberDecoder first code).val =
      (memberDecoder second (memberFamily.map step code)).val :=
  congrArg Subtype.val (memberDecoder_restriction step code)

noncomputable def memberSectionEquiv : (memberFamily (D := D)).sections ≃ (actualMemberFamily (D := D)).sections where
  toFun term := ⟨fun point => memberDecoder point (term.val point), by
    intro first second step
    exact (memberDecoder_restriction step (term.val first)).trans
      (congrArg (memberDecoder second) (term.property step))⟩
  invFun term := ⟨fun point => (memberDecoder point).symm (term.val point), by
    intro first second step
    apply (memberDecoder second).injective
    exact (memberDecoder_restriction step ((memberDecoder first).symm (term.val first))).symm.trans
      ((congrArg (actualMemberMap step) ((memberDecoder first).apply_symm_apply (term.val first))).trans
        ((term.property step).trans ((memberDecoder second).apply_symm_apply (term.val second)).symm))⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (memberDecoder point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (memberDecoder point).apply_symm_apply (term.val point)

theorem memberSection_value (term : memberFamily.sections) (point : (sets (D := D)).Elements) :
    (memberSectionEquiv term).val point = memberDecoder point (term.val point) := rfl

noncomputable def memberClassifier : NaturalHom (sets (D := D)) ContextualSmallFamilyUniverse.universeFamily :=
  memberData.classifier

theorem memberClassifier_fullDecode : ContextualSmallFamilyUniverse.decodedFamily
    (memberClassifier (D := D)) = memberFamily :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq memberFamily

theorem membership_classification_square :
    @IsPullback (D ⥤ Type (u + 1)) _ memberTotal ContextualSmallFamilyUniverse.universalTotal sets
      ContextualSmallFamilyUniverse.universeFamily
      (HostChoiceContextualSmallMapRepresentation.classified memberProjection membershipRelation.small).toNatTrans
      memberProjection.toNatTrans ContextualSmallFamilyUniverse.universalProjection.toNatTrans
      memberClassifier.toNatTrans :=
  HostChoiceContextualPresheafAmbient.classification_isPullback memberProjection membershipRelation.small

noncomputable def memberBody : (memberFamily (D := D)).Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.overArguments memberFamily memberFamily

noncomputable def memberPairFamily : (sets (D := D)).Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.sigma memberFamily memberBody

noncomputable def memberFunctionFamily : (sets (D := D)).Elements ⥤ Type u :=
  ContextualSmallFamilyTypeFormers.pi memberFamily memberBody

/-- The actual small dependent sum encodes two literal members of the same
material set. The body varies with that set and its contextual action. -/
noncomputable def memberPairDecoder (point : (sets (D := D)).Elements) :
    memberPairFamily.obj point ≃ ActualMember point × ActualMember point where
  toFun pair := (memberDecoder point pair.1, memberDecoder point pair.2)
  invFun pair := ⟨(memberDecoder point).symm pair.1, (memberDecoder point).symm pair.2⟩
  left_inv pair := Sigma.ext ((memberDecoder point).symm_apply_apply pair.1)
    (heq_of_eq ((memberDecoder point).symm_apply_apply pair.2))
  right_inv pair := Prod.ext ((memberDecoder point).apply_symm_apply pair.1)
    ((memberDecoder point).apply_symm_apply pair.2)

theorem memberPair_restriction {first second : (sets (D := D)).Elements} (step : first ⟶ second)
    (pair : memberPairFamily.obj first) :
    memberPairDecoder second (memberPairFamily.map step pair) =
      (actualMemberMap step (memberPairDecoder first pair).1,
        actualMemberMap step (memberPairDecoder first pair).2) :=
  Prod.ext (memberDecoder_restriction step pair.1).symm (memberDecoder_restriction step pair.2).symm

def unitParameters : (sets (D := D)).Elements ⥤ Type u where
  obj _ := PUnit.{u+1}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def lastMemberOperation :
    NatTrans (ContextualSmallFamilyTypeFormers.overArguments (memberFamily (D := D)) unitParameters) memberBody where
  app argument := TypeCat.ofHom fun _ => argument.2
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro _
    exact step.2.symm

/-- Lambda abstracts the real member variable over the entire compatible
future cone. It is not an independently selected pointwise function. -/
noncomputable def memberIdentity : (memberFunctionFamily (D := D)).sections :=
  ⟨fun point => (ContextualSmallFamilyTypeFormers.piCurry memberFamily memberBody lastMemberOperation).app point PUnit.unit, by
    intro first second step
    exact (congrArg (fun operation => operation PUnit.unit)
      ((ContextualSmallFamilyTypeFormers.piCurry memberFamily memberBody lastMemberOperation).naturality step)).symm⟩

theorem memberIdentity_future (point : (sets (D := D)).Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain memberFamily point).Elements) :
    (memberIdentity.val point).val argument = argument.2 := rfl

theorem memberIdentity_apply (point : (sets (D := D)).Elements) (argument : memberFamily.obj point) :
    ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody point (memberIdentity.val point) argument =
      argument :=
  congrArg (fun operation : NatTrans
    (ContextualSmallFamilyTypeFormers.overArguments memberFamily unitParameters) memberBody =>
      operation.app ⟨point, argument⟩ PUnit.unit)
    (ContextualSmallFamilyTypeFormers.pi_uncurry_curry memberFamily memberBody lastMemberOperation)

theorem memberIdentity_apply_material (point : (sets (D := D)).Elements) (argument : memberFamily.obj point) :
    (memberDecoder point (ContextualSmallFamilyTypeFormers.evaluateValue memberFamily memberBody point
      (memberIdentity.val point) argument)).val = (memberDecoder point argument).val :=
  congrArg (fun code => (memberDecoder point code).val) (memberIdentity_apply point argument)

theorem memberFunction_eta (operation : NatTrans (unitParameters (D := D)) memberFunctionFamily) :
    ContextualSmallFamilyTypeFormers.piCurry memberFamily memberBody
      (ContextualSmallFamilyTypeFormers.piUncurry memberFamily memberBody operation) = operation :=
  ContextualSmallFamilyTypeFormers.pi_curry_uncurry memberFamily memberBody operation

noncomputable def memberIdentityFamily :
    (ContextualSmallFamilyIdentity.endpoints (memberFamily (D := D))).Elements ⥤ Type u :=
  ContextualSmallFamilyIdentity.witnessFamily memberFamily

/-- Identity witnesses identify decoded member values. Formation and
authored term provenance are not equated by this extensional interpretation. -/
theorem memberIdentity_value_iff
    (point : (ContextualSmallFamilyIdentity.endpoints (memberFamily (D := D))).Elements) :
    Nonempty (memberIdentityFamily.obj point) ↔
      (memberDecoder ⟨point.1, point.2.1.1⟩ point.2.1.2).val =
        (memberDecoder ⟨point.1, point.2.1.1⟩ point.2.2).val := by
  constructor
  · rintro ⟨witness⟩
    exact congrArg (fun code => (memberDecoder ⟨point.1, point.2.1.1⟩ code).val)
      (PresheafIdentityWitness.decode witness)
  · intro same
    have codes := (memberDecoder ⟨point.1, point.2.1.1⟩).injective (Subtype.ext same)
    exact ⟨PresheafIdentityWitness.encode codes⟩

theorem memberJ_material
    (point : (ContextualSmallFamilyIdentity.identityContext (memberFamily (D := D))).Elements) :
    (memberDecoder ⟨point.1, point.2.1.1.1⟩
      ((ContextualSmallFamilyIdentity.J memberFamily
        (ContextualSmallFamilyIdentity.endpointMotive memberFamily)
        (ContextualSmallFamilyIdentity.endpointMethod memberFamily)).val point)).val =
      (memberDecoder ⟨point.1, point.2.1.1.1⟩ point.2.1.1.2).val :=
  congrArg (fun code => (memberDecoder ⟨point.1, point.2.1.1.1⟩ code).val)
    (ContextualSmallFamilyIdentity.J_endpoint_value memberFamily point)

theorem memberJ_beta
    (motive : (ContextualSmallFamilyIdentity.identityContext (memberFamily (D := D))).Elements ⥤ Type v)
    (method : (ContextualSmallFamilyIdentity.reindex motive
      (ContextualSmallFamilyIdentity.diagonal memberFamily)).sections) :
    ContextualSmallFamilyIdentity.reindexSection (ContextualSmallFamilyIdentity.diagonal memberFamily) motive
      (ContextualSmallFamilyIdentity.J memberFamily motive method) = method :=
  ContextualSmallFamilyIdentity.J_beta memberFamily motive method

section Parameters

variable {P : D ⥤ Type v} (parent : NaturalHom P sets)

noncomputable def memberFamilyUnder : P.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.elementMap parent) memberFamily

def actualMemberFamilyUnder : P.Elements ⥤ Type (u+1) :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.elementMap parent) actualMemberFamily

/-- The full section comparison applies to any authored family of parent
sets, including inhabited nonconstant families and wider parameters. -/
noncomputable def memberSectionEquivUnder :
    (memberFamilyUnder parent).sections ≃ (actualMemberFamilyUnder parent).sections where
  toFun term := ⟨fun point => memberDecoder
    ((ContextualSmallFamilyUniverse.elementMap parent).obj point) (term.val point), by
    intro first second step
    exact (memberDecoder_restriction ((ContextualSmallFamilyUniverse.elementMap parent).map step)
      (term.val first)).trans (congrArg (memberDecoder _) (term.property step))⟩
  invFun term := ⟨fun point => (memberDecoder
    ((ContextualSmallFamilyUniverse.elementMap parent).obj point)).symm (term.val point), by
    intro first second step
    apply (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj second)).injective
    exact (memberDecoder_restriction ((ContextualSmallFamilyUniverse.elementMap parent).map step)
      ((memberDecoder _).symm (term.val first))).symm.trans
      ((congrArg (actualMemberMap ((ContextualSmallFamilyUniverse.elementMap parent).map step))
        ((memberDecoder _).apply_symm_apply (term.val first))).trans
        ((term.property step).trans ((memberDecoder _).apply_symm_apply (term.val second)).symm))⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (memberDecoder _).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (memberDecoder _).apply_symm_apply (term.val point)

theorem memberSectionUnder_value (term : (memberFamilyUnder parent).sections) (point : P.Elements) :
    ((memberSectionEquivUnder parent term).val point).val =
      (memberDecoder ((ContextualSmallFamilyUniverse.elementMap parent).obj point) (term.val point)).val := rfl

end Parameters

/-- The ambient profile, terminal coalgebra and actual member-family
classification are realized over one site at one fixed successor bound. -/
theorem jointModel : HostChoiceContextualPresheafProfile.VerifiedProfile D ∧
    Nonempty (IsTerminal (HostChoiceContextualCoalgebraFinality.finalCoalgebra.{u,0} (D := D))) ∧
    @IsPullback (D ⥤ Type (u + 1)) _ memberTotal ContextualSmallFamilyUniverse.universalTotal sets
      ContextualSmallFamilyUniverse.universeFamily
      (HostChoiceContextualSmallMapRepresentation.classified memberProjection membershipRelation.small).toNatTrans
      memberProjection.toNatTrans ContextualSmallFamilyUniverse.universalProjection.toNatTrans
      memberClassifier.toNatTrans ∧
    Nonempty ((memberFamily (D := D)).sections ≃ (actualMemberFamily (D := D)).sections) :=
  ⟨HostChoiceContextualPresheafProfile.verifiedProfile D,
    ⟨HostChoiceContextualCoalgebraFinality.isTerminal.{u,0}⟩,
    membership_classification_square, ⟨memberSectionEquiv⟩⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModel
