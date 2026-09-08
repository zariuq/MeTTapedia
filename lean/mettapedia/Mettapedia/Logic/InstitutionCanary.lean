import Mettapedia.Logic.PredicateInstitution

/-!
# A membership institution and a reduct falsifier

Types serve as signatures, their elements as sentences, and predicates as
models.  A function translates an element forward and reduces a predicate by
inverse image.  Satisfaction is membership, so the institution law states the
elementary equivalence `f x ∈ P ↔ x ∈ f⁻¹(P)`.

The final theorem checks that replacing inverse image by direct image breaks
the satisfaction condition, even for a two-element type.  Thus the variance
in `Institution.model` is semantic content rather than bookkeeping.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InstitutionCanary

open CategoryTheory
open scoped CategoryTheory

universe u

/-- Sentences of a type-signature are its elements. -/
def elementSentence : CategoryTheory.Functor (Type u) (Type u) :=
  CategoryTheory.Functor.id (Type u)

/-- The membership institution is the predicate institution of the identity
carrier functor. -/
def membershipInstitution : Institution (Type u) :=
  PredicateInstitution.ofCarrier elementSentence

@[simp]
theorem membership_satisfaction_condition
    {source target : Type u} (translation : source ⟶ target)
    (targetModel : Set target) (sourceSentence : source) :
    membershipInstitution.satisfies target
        (CategoryTheory.Discrete.mk targetModel)
        (membershipInstitution.sentence.map translation sourceSentence) ↔
      membershipInstitution.satisfies source
        (membershipInstitution.reduct translation
          (CategoryTheory.Discrete.mk targetModel))
        sourceSentence :=
  membershipInstitution.satisfaction_condition translation
    (CategoryTheory.Discrete.mk targetModel) sourceSentence

/-- In the membership institution, entailment says precisely that the
intersection of all premise predicates is contained in the conclusion. -/
theorem membership_entails_iff (signature : Type u)
    (premises : Set signature) (conclusion : signature) :
    membershipInstitution.Entails signature premises conclusion ↔
      conclusion ∈ premises := by
  constructor
  · intro entails
    let model : Set signature := premises
    exact entails (CategoryTheory.Discrete.mk model) fun premise member => member
  · intro member model satisfies
    exact satisfies conclusion member

/-! ## Negative control: direct image is not model reduct -/

/-- A deliberately non-injective signature translation. -/
def constantFalse : Bool → Bool := fun _ => false

/-- Direct image has the wrong semantic variance for model reduct. -/
def wrongDirectImageReduct (model : Set Bool) : Set Bool :=
  constantFalse '' model

/-- The proposed direct-image reduct violates satisfaction: translating
`false` yields `false`, which is absent from the target singleton `{true}`,
while the wrong reduct contains `false`. -/
theorem directImage_fails_satisfaction_condition :
    ¬ ∀ (model : Set Bool) (sentence : Bool),
      constantFalse sentence ∈ model ↔
        sentence ∈ wrongDirectImageReduct model := by
  intro purportedLaw
  have law := purportedLaw ({true} : Set Bool) false
  have right : false ∈ wrongDirectImageReduct ({true} : Set Bool) := by
    exact ⟨true, Set.mem_singleton true, rfl⟩
  have left : false ∈ ({true} : Set Bool) := law.mpr right
  exact Bool.false_ne_true (Set.mem_singleton_iff.mp left)

/-! ## Model coverage is stronger than satisfaction preservation -/

/-- One discrete signature is enough to test coverage of model reducts. -/
abbrev OneSignature := CategoryTheory.Discrete Unit

/-- A Boolean sentence carrier over the unique signature. -/
def boolCarrier : OneSignature ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A singleton sentence carrier over the unique signature. -/
def unitCarrier : OneSignature ⥤ Type where
  obj _ := Unit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Collapse both Boolean sentences to the unique target sentence. -/
def collapseCarrier : boolCarrier ⟶ (𝟭 OneSignature) ⋙ unitCarrier where
  app _ := TypeCat.ofHom fun _ => ()
  naturality := by
    intro source target translation
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    rfl

/-- The collapse map induces a valid institution comorphism because models
are reduced by inverse image. -/
def collapseComorphism :
    (PredicateInstitution.ofCarrier boolCarrier).Comorphism
      (PredicateInstitution.ofCarrier unitCarrier) :=
  PredicateInstitution.comorphism boolCarrier unitCarrier
    (𝟭 OneSignature) collapseCarrier

/-- Negative control: satisfaction preservation alone does not imply model
coverage.  No predicate on the singleton carrier can reduce to the singleton
Boolean predicate `{false}`, because its inverse image must treat `false` and
`true` alike. -/
theorem collapseComorphism_not_coversModels :
    ¬ collapseComorphism.CoversModels := by
  intro coverage
  rcases coverage (CategoryTheory.Discrete.mk ())
      (CategoryTheory.Discrete.mk ({false} : Set Bool)) with
    ⟨targetModel, reductEquality⟩
  change CategoryTheory.Discrete.mk
      (Set.preimage (fun _ : Bool => ())
        (show Set Unit from targetModel.as)) =
    CategoryTheory.Discrete.mk ({false} : Set Bool) at reductEquality
  have predicateEquality :
      Set.preimage (fun _ : Bool => ())
          (show Set Unit from targetModel.as) = ({false} : Set Bool) := by
    exact congrArg CategoryTheory.Discrete.as reductEquality
  have falseMember :
      false ∈ Set.preimage (fun _ : Bool => ())
        (show Set Unit from targetModel.as) := by
    rw [predicateEquality]
    exact Set.mem_singleton false
  have trueMember :
      true ∈ Set.preimage (fun _ : Bool => ())
        (show Set Unit from targetModel.as) := by
    exact falseMember
  have impossible : true ∈ ({false} : Set Bool) := by
    rw [← predicateEquality]
    exact trueMember
  exact Bool.false_ne_true (Set.mem_singleton_iff.mp impossible).symm

/-- The missing model is semantically observable: after collapse, translated
`false` entails translated `true`, although `false` does not entail `true` in
the source institution. -/
theorem collapseComorphism_does_not_reflect_entailment :
    (PredicateInstitution.ofCarrier unitCarrier).Entails
        (collapseComorphism.mapSignature.obj
          (CategoryTheory.Discrete.mk ()))
        (Set.image
          (collapseComorphism.mapSentence.app
            (CategoryTheory.Discrete.mk ()))
          ({false} : Set Bool))
        (collapseComorphism.mapSentence.app
          (CategoryTheory.Discrete.mk ()) true) ∧
      ¬ (PredicateInstitution.ofCarrier boolCarrier).Entails
        (CategoryTheory.Discrete.mk ()) ({false} : Set Bool) true := by
  constructor
  · intro targetModel satisfiesPremises
    exact satisfiesPremises
      (collapseComorphism.mapSentence.app
        (CategoryTheory.Discrete.mk ()) false)
      ⟨false, Set.mem_singleton false, rfl⟩
  · intro purportedEntailment
    have trueMember := purportedEntailment
      (CategoryTheory.Discrete.mk ({false} : Set Bool)) <| by
        intro premise premiseMember
        exact Set.mem_singleton_iff.mp premiseMember
    exact Bool.false_ne_true
      (Set.mem_singleton_iff.mp trueMember).symm

/-! ## Why coverage up to isomorphism needs satisfaction invariance -/

/-- Two model objects connected by a unique arrow in each direction. -/
inductive IsoAliasedModel where
  | retained
  | omitted

instance isoAliasedModelCategory : CategoryTheory.Category IsoAliasedModel where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def retainedIsoOmitted :
    IsoAliasedModel.retained ≅ IsoAliasedModel.omitted where
  hom := ()
  inv := ()
  hom_inv_id := rfl
  inv_hom_id := rfl

def isoAliasedModels : OneSignatureᵒᵖ ⥤ CategoryTheory.Cat :=
  (CategoryTheory.Functor.const OneSignatureᵒᵖ).obj
    (CategoryTheory.Cat.of IsoAliasedModel)

def representativeModels : OneSignatureᵒᵖ ⥤ CategoryTheory.Cat :=
  (CategoryTheory.Functor.const OneSignatureᵒᵖ).obj
    (CategoryTheory.Cat.of (CategoryTheory.Discrete Unit))

/-- A bare institution is allowed to distinguish two isomorphic native model
objects; the additional invariance property below rules this out. -/
def isoSensitiveInstitution : Institution OneSignature where
  sentence := unitCarrier
  model := isoAliasedModels
  satisfies := fun _ model _ => model = .retained
  satisfaction_condition := by
    intro source target translation targetModel sourceSentence
    change targetModel = IsoAliasedModel.retained ↔
      targetModel = IsoAliasedModel.retained
    exact Iff.rfl

/-- The target retains only the representative model and validates its unique
sentence. -/
def representativeInstitution : Institution OneSignature where
  sentence := unitCarrier
  model := representativeModels
  satisfies := fun _ _ _ => True
  satisfaction_condition := by
    intro source target translation targetModel sourceSentence
    exact Iff.rfl

def selectRepresentative (signature : OneSignatureᵒᵖ) :
    (((𝟭 OneSignature).op ⋙ representativeInstitution.model).obj signature) ⥤
      isoSensitiveInstitution.model.obj signature where
  obj _ := .retained
  map _ := ()
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The target model is read as the retained source representative. -/
def representativeComorphism :
    Institution.Comorphism isoSensitiveInstitution representativeInstitution where
  mapSignature := 𝟭 OneSignature
  mapSentence :=
    (CategoryTheory.Functor.leftUnitor representativeInstitution.sentence).inv
  mapModel :=
    { app := fun signature => (selectRepresentative signature).toCatHom
      naturality := by
        intro source target translation
        rfl }
  satisfaction_condition := by
    intro signature targetModel sourceSentence
    constructor
    · intro _
      rfl
    · intro _
      trivial

/-- Every source model is isomorphic to the selected representative. -/
theorem representativeComorphism_coversModelsUpToIso :
    representativeComorphism.CoversModelsUpToIso := by
  intro signature sourceModel
  refine ⟨CategoryTheory.Discrete.mk (), ⟨?_⟩⟩
  cases sourceModel
  · exact
      { hom := ()
        inv := ()
        hom_inv_id := rfl
        inv_hom_id := rfl }
  · exact
      { hom := ()
        inv := ()
        hom_inv_id := rfl
        inv_hom_id := rfl }

/-- The same route does not cover models by literal equality. -/
theorem representativeComorphism_not_coversModels :
    ¬representativeComorphism.CoversModels := by
  intro coverage
  rcases coverage (CategoryTheory.Discrete.mk ()) IsoAliasedModel.omitted with
    ⟨targetModel, reductEquality⟩
  change CategoryTheory.Discrete Unit at targetModel
  rcases targetModel with ⟨targetModel⟩
  cases targetModel
  have impossible :
      IsoAliasedModel.retained = IsoAliasedModel.omitted := by
    simp [representativeComorphism, selectRepresentative] at reductEquality
  cases impossible

/-- The source institution fails the exact premise that would make
isomorphism-level coverage semantically safe. -/
theorem isoSensitiveInstitution_not_satisfactionIsoInvariant :
    ¬isoSensitiveInstitution.SatisfactionIsoInvariant := by
  intro invariant
  have transferred := invariant (CategoryTheory.Discrete.mk ())
    IsoAliasedModel.retained IsoAliasedModel.omitted retainedIsoOmitted ()
  have omittedSatisfies :
      isoSensitiveInstitution.satisfies (CategoryTheory.Discrete.mk ())
        IsoAliasedModel.omitted () := transferred.mp rfl
  change IsoAliasedModel.omitted = IsoAliasedModel.retained at omittedSatisfies
  cases omittedSatisfies

/-- Negative control: coverage up to isomorphism alone does not reflect
consequence when a purported institution lets isomorphic models disagree. -/
theorem upToIso_without_invariance_does_not_reflect_entailment :
    representativeInstitution.Entails (CategoryTheory.Discrete.mk ()) ∅ () ∧
      ¬isoSensitiveInstitution.Entails
        (CategoryTheory.Discrete.mk ()) ∅ () := by
  constructor
  · intro model satisfiesPremises
    trivial
  · intro sourceEntails
    have omittedSatisfies := sourceEntails IsoAliasedModel.omitted <| by
      intro premise membership
      exact False.elim membership
    change IsoAliasedModel.omitted = IsoAliasedModel.retained at omittedSatisfies
    cases omittedSatisfies

/-! ## Positive control: genuinely representation-independent truth -/

/-- The same two model representations, now observed only through a truth
relation that is invariant under their isomorphism. -/
def isoInvariantInstitution : Institution OneSignature where
  sentence := unitCarrier
  model := isoAliasedModels
  satisfies := fun _ _ _ => True
  satisfaction_condition := by
    intro source target translation targetModel sourceSentence
    exact Iff.rfl

theorem isoInvariantInstitution_satisfactionIsoInvariant :
    isoInvariantInstitution.SatisfactionIsoInvariant := by
  intro signature sourceModel targetModel isomorphism sentence
  exact Iff.rfl

/-- Select the retained representative exactly as above, but from an
isomorphism-invariant source institution. -/
def invariantRepresentativeComorphism :
    Institution.Comorphism isoInvariantInstitution representativeInstitution where
  mapSignature := 𝟭 OneSignature
  mapSentence :=
    (CategoryTheory.Functor.leftUnitor representativeInstitution.sentence).inv
  mapModel :=
    { app := fun signature => (selectRepresentative signature).toCatHom
      naturality := by
        intro source target translation
        rfl }
  satisfaction_condition := by
    intro signature targetModel sourceSentence
    exact Iff.rfl

/-- This route covers all source models up to isomorphism. -/
theorem invariantRepresentativeComorphism_coversModelsUpToIso :
    invariantRepresentativeComorphism.CoversModelsUpToIso := by
  intro signature sourceModel
  refine ⟨CategoryTheory.Discrete.mk (), ⟨?_⟩⟩
  cases sourceModel <;>
    exact
      { hom := ()
        inv := ()
        hom_inv_id := rfl
        inv_hom_id := rfl }

/-- It still cannot cover the omitted representation by literal equality. -/
theorem invariantRepresentativeComorphism_not_coversModels :
    ¬invariantRepresentativeComorphism.CoversModels := by
  intro coverage
  rcases coverage (CategoryTheory.Discrete.mk ()) IsoAliasedModel.omitted with
    ⟨targetModel, reductEquality⟩
  change CategoryTheory.Discrete Unit at targetModel
  rcases targetModel with ⟨targetModel⟩
  cases targetModel
  have impossible :
      IsoAliasedModel.retained = IsoAliasedModel.omitted := by
    simp [invariantRepresentativeComorphism, selectRepresentative] at reductEquality
  cases impossible

/-- Positive control: the strictly weaker, isomorphism-level coverage
hypothesis is sufficient when satisfaction is representation-independent. -/
theorem invariantRepresentative_entails_iff
    (premises : Set Unit) (conclusion : Unit) :
    isoInvariantInstitution.Entails (CategoryTheory.Discrete.mk ())
        premises conclusion ↔
      representativeInstitution.Entails (CategoryTheory.Discrete.mk ())
        (Set.image
          (invariantRepresentativeComorphism.mapSentence.app
            (CategoryTheory.Discrete.mk ())) premises)
        (invariantRepresentativeComorphism.mapSentence.app
          (CategoryTheory.Discrete.mk ()) conclusion) :=
  Institution.Comorphism.entails_mapped_iff_of_coversModelsUpToIso
    invariantRepresentativeComorphism
    isoInvariantInstitution_satisfactionIsoInvariant
    invariantRepresentativeComorphism_coversModelsUpToIso
    (CategoryTheory.Discrete.mk ()) premises conclusion

/-- Coverage up to isomorphism is strictly more applicable than literal model
coverage, even while consequence transport remains exact. -/
theorem isomorphismCoverage_strictly_extends_literalCoverage :
    invariantRepresentativeComorphism.CoversModelsUpToIso ∧
      ¬invariantRepresentativeComorphism.CoversModels :=
  ⟨invariantRepresentativeComorphism_coversModelsUpToIso,
    invariantRepresentativeComorphism_not_coversModels⟩

/-- Positive control: ordinary predicate institutions satisfy the model
isomorphism invariance premise. -/
theorem membershipInstitution_satisfactionIsoInvariant :
    membershipInstitution.SatisfactionIsoInvariant :=
  PredicateInstitution.satisfactionIsoInvariant elementSentence

#print axioms membershipInstitution
#print axioms membership_satisfaction_condition
#print axioms membership_entails_iff
#print axioms directImage_fails_satisfaction_condition
#print axioms collapseComorphism
#print axioms collapseComorphism_not_coversModels
#print axioms collapseComorphism_does_not_reflect_entailment
#print axioms representativeComorphism_coversModelsUpToIso
#print axioms representativeComorphism_not_coversModels
#print axioms isoSensitiveInstitution_not_satisfactionIsoInvariant
#print axioms upToIso_without_invariance_does_not_reflect_entailment
#print axioms isoInvariantInstitution_satisfactionIsoInvariant
#print axioms invariantRepresentativeComorphism_coversModelsUpToIso
#print axioms invariantRepresentativeComorphism_not_coversModels
#print axioms invariantRepresentative_entails_iff
#print axioms isomorphismCoverage_strictly_extends_literalCoverage
#print axioms membershipInstitution_satisfactionIsoInvariant

end Mettapedia.Logic.InstitutionCanary
