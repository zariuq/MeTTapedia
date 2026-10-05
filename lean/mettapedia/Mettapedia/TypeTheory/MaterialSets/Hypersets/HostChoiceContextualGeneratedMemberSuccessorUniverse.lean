import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamilies

/-!
# A generated fixed-site successor of actual member-family codes

The lower whole-family codes are retained as actual cumulative seed data.
Their parameter presheaves are explicitly raised, and their decoded
original-bound families are pulled along the constructed inverse wrapper.
Independent sum, complete future product, identity, W and substitution
construct the upper grammar. No ambient family or enclosing universe is
supplied as a seed or closure operator.

The context category and member/type fibre bound remain `u`. If the lower
external parameter bound is `L = max (u+1) v`, the upper parameters are at
`L+1` and the upper code type is at `L+2`. This fixed-site successor retains
recipes and whole functors. It is distinct from a material site lift, an
internal small universe or a transfinite closure construction. Optional
host dependencies are inherited from the lower actual member model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorUniverse

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetFamilyClosure


universe u v
variable {D : Type u} [Category.{u} D]

abbrev LowerParameters := HostChoiceContextualGeneratedHypersetFamilies.Parameters.{u,v} D
abbrev UpperParameters := D ⥤ Type ((max (u+1) v)+1)

def parametersUp (parameters : LowerParameters.{u,v} (D := D)) : UpperParameters.{u,v} (D := D) where
  obj point := ULift.{(max (u+1) v)+1} (parameters.obj point)
  map step := TypeCat.ofHom fun value => ULift.up (parameters.map step value.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (parameters.map_id_apply point value.down)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    exact congrArg ULift.up (parameters.map_comp_apply first second value.down)

def parametersDown (parameters : LowerParameters.{u,v} (D := D)) :
    NaturalHom (parametersUp parameters) parameters where
  app _ value := value.down
  naturality _ _ := rfl

def parametersRaise (parameters : LowerParameters.{u,v} (D := D)) :
    NaturalHom parameters (parametersUp parameters) where
  app _ value := ULift.up value
  naturality _ _ := rfl

theorem parameters_down_raise (parameters : LowerParameters.{u,v} (D := D)) :
    (parametersDown parameters).comp (parametersRaise parameters) =
      ContextualSmallMapConstructions.identity (parametersUp parameters) := by
  apply NaturalHom.ext
  intro _ value
  cases value
  rfl

theorem parameters_raise_down (parameters : LowerParameters.{u,v} (D := D)) :
    (parametersRaise parameters).comp (parametersDown parameters) =
      ContextualSmallMapConstructions.identity parameters := by
  apply NaturalHom.ext
  intro _ _
  rfl

def familyUp {parameters : LowerParameters.{u,v} (D := D)}
    (family : parameters.Elements ⥤ Type u) : (parametersUp parameters).Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.substitutedFamily family (parametersDown parameters)

inductive Generation : {parameters : UpperParameters.{u,v} (D := D)} →
    (parameters.Elements ⥤ Type u) → Type ((max (u+1) v)+2)
  | lift {parameters : LowerParameters.{u,v} (D := D)} (code : HostChoiceContextualGeneratedHypersetFamilies.Code parameters) :
      Generation (familyUp (HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code))
  | sigma {parameters : UpperParameters.{u,v} (D := D)} {domain : parameters.Elements ⥤ Type u}
      {body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u}
      (first : Generation domain) (second : Generation body) :
      Generation (ContextualSmallFamilyTypeFormers.sigma domain
        (ContextualSmallFamilyComprehension.indexedBody domain body))
  | pi {parameters : UpperParameters.{u,v} (D := D)} {domain : parameters.Elements ⥤ Type u}
      {body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u}
      (first : Generation domain) (second : Generation body) :
      Generation (ContextualSmallFamilyTypeFormers.pi domain
        (ContextualSmallFamilyComprehension.indexedBody domain body))
  | identity {parameters : UpperParameters.{u,v} (D := D)} {domain : parameters.Elements ⥤ Type u}
      (first : Generation domain) (left right : domain.sections) :
      Generation (ContextualSmallFamilyIdentity.identityFamily domain left right)
  | w {parameters : UpperParameters.{u,v} (D := D)} {domain : parameters.Elements ⥤ Type u}
      {body : (ContextualSmallFamilyUniverse.total domain).Elements ⥤ Type u}
      (first : Generation domain) (second : Generation body) :
      Generation (ContextualSmallFamilyWTypes.w domain
        (ContextualSmallFamilyComprehension.indexedBody domain body))
  | reindex {parameters other : UpperParameters.{u,v} (D := D)} {domain : parameters.Elements ⥤ Type u}
      (first : Generation domain) (change : NaturalHom other parameters) :
      Generation (ContextualSmallFamilyUniverse.substitutedFamily domain change)

abbrev Code (parameters : UpperParameters.{u,v} (D := D)) : Type ((max (u+1) v)+2) :=
  Σ family : parameters.Elements ⥤ Type u, Generation family

def decodeFamily {parameters : UpperParameters.{u,v} (D := D)} (code : Code parameters) :
    parameters.Elements ⥤ Type u := code.1

def liftCode {parameters : LowerParameters.{u,v} (D := D)} (code : HostChoiceContextualGeneratedHypersetFamilies.Code parameters) :
    Code (parametersUp parameters) := ⟨familyUp (HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code), .lift code⟩

abbrev Origin : Type ((max (u+1) v)+1) :=
  Σ parameters : LowerParameters.{u,v} (D := D), HostChoiceContextualGeneratedHypersetFamilies.Code parameters

def headOrigin {parameters : UpperParameters.{u,v} (D := D)} {family : parameters.Elements ⥤ Type u} :
    Generation family → Option (Origin.{u,v} (D := D))
  | .lift (parameters := parameters) code => some ⟨parameters, code⟩
  | .sigma _ _ => none
  | .pi _ _ => none
  | .identity _ _ _ => none
  | .w _ _ => none
  | .reindex _ _ => none

def origin {parameters : UpperParameters.{u,v} (D := D)} (code : Code parameters) :
    Option (Origin.{u,v} (D := D)) := headOrigin code.2

/-- Injectivity retains the exact lower family and formation recipe. It
does not follow from injectivity of a material carrier observer. -/
theorem liftCode_injective (parameters : LowerParameters.{u,v} (D := D)) :
    Function.Injective (liftCode (parameters := parameters)) := by
  intro first second same
  have payloads := Option.some.inj (congrArg origin same)
  exact eq_of_heq (Sigma.mk.inj_iff.mp payloads).2

def sigmaCode {parameters : UpperParameters.{u,v} (D := D)} (domain : Code parameters)
    (body : Code.{u,v} (ContextualSmallFamilyUniverse.total (decodeFamily domain))) : Code parameters :=
  ⟨ContextualSmallFamilyTypeFormers.sigma (decodeFamily domain)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily domain) (decodeFamily body)), .sigma domain.2 body.2⟩

def piCode {parameters : UpperParameters.{u,v} (D := D)} (domain : Code parameters)
    (body : Code.{u,v} (ContextualSmallFamilyUniverse.total (decodeFamily domain))) : Code parameters :=
  ⟨ContextualSmallFamilyTypeFormers.pi (decodeFamily domain)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily domain) (decodeFamily body)), .pi domain.2 body.2⟩

def identityCode {parameters : UpperParameters.{u,v} (D := D)} (domain : Code parameters)
    (left right : (decodeFamily domain).sections) : Code parameters :=
  ⟨ContextualSmallFamilyIdentity.identityFamily (decodeFamily domain) left right, .identity domain.2 left right⟩

noncomputable def wCode {parameters : UpperParameters.{u,v} (D := D)} (domain : Code parameters)
    (body : Code.{u,v} (ContextualSmallFamilyUniverse.total (decodeFamily domain))) : Code parameters :=
  ⟨ContextualSmallFamilyWTypes.w (decodeFamily domain)
    (ContextualSmallFamilyComprehension.indexedBody (decodeFamily domain) (decodeFamily body)), .w domain.2 body.2⟩

def substitute {parameters other : UpperParameters.{u,v} (D := D)}
    (code : Code parameters) (change : NaturalHom other parameters) : Code other :=
  ⟨ContextualSmallFamilyUniverse.substitutedFamily (decodeFamily code) change, .reindex code.2 change⟩

def classifier {parameters : UpperParameters.{u,v} (D := D)} (code : Code parameters) :
    NaturalHom parameters ContextualSmallFamilyUniverse.universeFamily :=
  ContextualSmallFamilyUniverse.classifier (decodeFamily code)

theorem classifier_lift {parameters : LowerParameters.{u,v} (D := D)}
    (code : HostChoiceContextualGeneratedHypersetFamilies.Code parameters) :
    classifier (liftCode code) =
      (parametersDown parameters).comp (HostChoiceContextualGeneratedHypersetFamilies.classifier code) :=
  ContextualSmallFamilyUniverse.classifier_parameter_substitution _ _

theorem full_decoder {parameters : UpperParameters.{u,v} (D := D)} (code : Code parameters) :
    ContextualSmallFamilyUniverse.decodedFamily (classifier code) = decodeFamily code :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

def classificationSections {parameters : UpperParameters.{u,v} (D := D)} (code : Code parameters) :
    (ContextualSmallFamilyUniverse.total (decodeFamily code)).sections ≃
      (ContextualSmallFamilyUniverse.GenericPullback (classifier code)).sections :=
  ContextualSmallFamilyUniverse.classificationSectionEquiv _

theorem classifier_substitution {parameters other : UpperParameters.{u,v} (D := D)}
    (code : Code parameters) (change : NaturalHom other parameters) :
    classifier (substitute code change) = change.comp (classifier code) :=
  ContextualSmallFamilyUniverse.classifier_parameter_substitution _ _

theorem decoder_substitution_id {parameters : UpperParameters.{u,v} (D := D)} (code : Code parameters) :
    decodeFamily (substitute code (ContextualSmallMapConstructions.identity parameters)) = decodeFamily code :=
  ContextualSmallFamilyUniverse.substitutedFamily_id _

theorem decoder_substitution_comp {parameters other third : UpperParameters.{u,v} (D := D)}
    (code : Code parameters) (change : NaturalHom other parameters) (earlier : NaturalHom third other) :
    decodeFamily (substitute (substitute code change) earlier) = decodeFamily (substitute code (earlier.comp change)) :=
  ContextualSmallFamilyUniverse.substitutedFamily_comp _ _ _

def elementRaise (parameters : LowerParameters.{u,v} (D := D)) :
    parameters.Elements ⥤ (parametersUp parameters).Elements where
  obj point := ⟨point.1, ULift.up point.2⟩
  map arrow := CategoryOfElements.homMk _ _ arrow.1 (congrArg ULift.up arrow.2)
  map_id _ := rfl
  map_comp _ _ := rfl

def sectionEquiv {parameters : LowerParameters.{u,v} (D := D)} (code : HostChoiceContextualGeneratedHypersetFamilies.Code parameters) :
    (HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code).sections ≃ (decodeFamily (liftCode code)).sections where
  toFun term := ContextualSmallFamilyComprehension.sectionPull
    (ContextualSmallFamilyUniverse.elementMap (parametersDown parameters)) (HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code) term
  invFun term := ⟨fun point => term.val ((elementRaise parameters).obj point),
    fun step => term.property ((elementRaise parameters).map step)⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    rfl
  right_inv term := by
    apply Subtype.ext
    funext point
    rcases point with ⟨world, ⟨value⟩⟩
    rfl

theorem section_value {parameters : LowerParameters.{u,v} (D := D)} (code : HostChoiceContextualGeneratedHypersetFamilies.Code parameters)
    (term : (HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code).sections) (point : (parametersUp parameters).Elements) :
    (sectionEquiv code term).val point = term.val
      ((ContextualSmallFamilyUniverse.elementMap (parametersDown parameters)).obj point) := rfl

theorem member_restriction {parameters : LowerParameters.{u,v} (D := D)} (code : HostChoiceContextualGeneratedHypersetFamilies.Code parameters)
    {first second : (parametersUp parameters).Elements} (step : first ⟶ second)
    (term : (decodeFamily (liftCode code)).obj first) :
    (decodeFamily (liftCode code)).map step term =
      (HostChoiceContextualGeneratedHypersetFamilies.decodeFamily code).map ((ContextualSmallFamilyUniverse.elementMap (parametersDown parameters)).map step) term := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorUniverse
