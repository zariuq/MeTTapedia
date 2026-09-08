import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Order.Closure

/-!
# Institutions

An institution separates four pieces of a logical system:

* a category of signatures;
* a covariant translation of sentences;
* a contravariant reduct of models; and
* a satisfaction relation invariant under simultaneous sentence translation
  and model reduct.

The satisfaction condition is the seam that permits theories implemented in
different logics to be compared without identifying their syntax, proof
objects, or model representations.  The semantic consequence operator below
is derived from models rather than supplied as independent data.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

open CategoryTheory
open scoped CategoryTheory

universe uSignature uSignatureHom uSentence uModel uModelHom

/-- A model-valued institution in the standard variance: sentences translate
forward along signature morphisms, while models reduce backward. -/
structure Institution (Signature : Type uSignature)
    [CategoryTheory.Category.{uSignatureHom} Signature] where
  sentence : CategoryTheory.Functor Signature (Type uSentence)
  model : CategoryTheory.Functor Signatureᵒᵖ
    CategoryTheory.Cat.{uModelHom, uModel}
  satisfies : (signature : Signature) →
    model.obj (Opposite.op signature) → sentence.obj signature → Prop
  satisfaction_condition :
    ∀ {source target : Signature} (translation : source ⟶ target)
      (targetModel : model.obj (Opposite.op target))
      (sourceSentence : sentence.obj source),
      satisfies target targetModel
          (sentence.map translation sourceSentence) ↔
        satisfies source
          ((model.map translation.op).toFunctor.obj targetModel)
          sourceSentence

namespace Institution

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uSignatureHom} Signature]
  (institution : Institution.{uSignature, uSignatureHom, uSentence,
    uModel, uModelHom} Signature)

/-- Reduct of a target model along a signature translation. -/
abbrev reduct {source target : Signature} (translation : source ⟶ target)
    (targetModel : institution.model.obj (Opposite.op target)) :
    institution.model.obj (Opposite.op source) :=
  (institution.model.map translation.op).toFunctor.obj targetModel

/-- A set of premises semantically entails a conclusion when every model of
the premises is a model of the conclusion. -/
def Entails (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (conclusion : institution.sentence.obj signature) : Prop :=
  ∀ model, (∀ premise, premise ∈ premises →
      institution.satisfies signature model premise) →
    institution.satisfies signature model conclusion

/-- Semantic entailment induces the Tarski closure operator of an
institution. -/
def semanticConsequence (signature : Signature) :
    ClosureOperator (Set (institution.sentence.obj signature)) where
  toFun premises := { conclusion | institution.Entails signature premises conclusion }
  monotone' := by
    intro source target subset conclusion entailsTarget model satisfiesSource
    exact entailsTarget model fun premise member =>
      satisfiesSource premise (subset member)
  le_closure' := by
    intro premises conclusion member model satisfies
    exact satisfies conclusion member
  idempotent' := by
    intro premises
    ext conclusion
    constructor
    · intro entailsConsequences model satisfiesPremises
      apply entailsConsequences model
      intro consequence consequenceMember
      exact consequenceMember model satisfiesPremises
    · intro entailsPremises model satisfiesConsequences
      exact satisfiesConsequences conclusion entailsPremises

@[simp]
theorem mem_semanticConsequence_iff (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (conclusion : institution.sentence.obj signature) :
    conclusion ∈ institution.semanticConsequence signature premises ↔
      institution.Entails signature premises conclusion :=
  Iff.rfl

/-- The institution satisfaction condition makes semantic consequence
invariant under signature translation. -/
theorem map_semanticConsequence
    {source target : Signature} (translation : source ⟶ target)
    (premises : Set (institution.sentence.obj source)) :
    Set.image (institution.sentence.map translation)
        (institution.semanticConsequence source premises) ⊆
      institution.semanticConsequence target
        (Set.image (institution.sentence.map translation) premises) := by
  intro mappedConclusion mappedMember
  rcases mappedMember with ⟨conclusion, entailsConclusion, rfl⟩
  intro targetModel satisfiesMappedPremises
  rw [institution.satisfaction_condition]
  exact entailsConclusion (institution.reduct translation targetModel) <| by
    intro premise premiseMember
    rw [← institution.satisfaction_condition translation targetModel premise]
    exact satisfiesMappedPremises
      (institution.sentence.map translation premise)
      ⟨premise, premiseMember, rfl⟩

/-- Semantic validity is consequence from the empty set of premises. -/
def Valid (signature : Signature)
    (sentence : institution.sentence.obj signature) : Prop :=
  institution.Entails signature ∅ sentence

/-- Valid sentences remain valid under signature translation. -/
theorem valid_map {source target : Signature}
    (translation : source ⟶ target)
    {sentence : institution.sentence.obj source}
    (valid : institution.Valid source sentence) :
    institution.Valid target (institution.sentence.map translation sentence) := by
  change institution.sentence.map translation sentence ∈
    institution.semanticConsequence target ∅
  have mapped := institution.map_semanticConsequence translation ∅
    (Set.mem_image_of_mem (institution.sentence.map translation) valid)
  simpa using mapped

/-! ## Invariance under native model isomorphism -/

/-- Satisfaction is invariant under isomorphism of models at one signature.
This is standard for mathematical model classes, but is kept as an explicit
property because the bare institution laws only govern change of signature. -/
def SatisfactionIsoInvariant : Prop :=
  ∀ (signature : Signature)
    (sourceModel targetModel :
      institution.model.obj (Opposite.op signature))
    (_isomorphism : sourceModel ≅ targetModel)
    (sentence : institution.sentence.obj signature),
    institution.satisfies signature sourceModel sentence ↔
      institution.satisfies signature targetModel sentence

/-! ## Inter-institution routes -/

/-- A comorphism embeds a source logic into a target logic.  Signatures and
sentences move forward, target models are viewed as source models, and the
two readings of satisfaction agree.  This is the model-valued route used by
the little-theories method and by biform theory graphs. -/
structure Comorphism
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    (source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature)
    (target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature) where
  mapSignature : SourceSignature ⥤ TargetSignature
  mapSentence : source.sentence ⟶ mapSignature ⋙ target.sentence
  mapModel : mapSignature.op ⋙ target.model ⟶ source.model
  satisfaction_condition :
    ∀ (signature : SourceSignature)
      (targetModel : target.model.obj
        (Opposite.op (mapSignature.obj signature)))
      (sourceSentence : source.sentence.obj signature),
      target.satisfies (mapSignature.obj signature) targetModel
          (mapSentence.app signature sourceSentence) ↔
        source.satisfies signature
          ((mapModel.app (Opposite.op signature)).toFunctor.obj targetModel)
          sourceSentence

namespace Comorphism

/-- A model-valued institution route is determined by its signature,
sentence, and model translations.  The satisfaction square is a proposition
and hence contributes no additional arrow identity. -/
@[ext]
theorem ext
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    {left right : Comorphism source target}
    (signature : left.mapSignature = right.mapSignature)
    (sentence : HEq left.mapSentence right.mapSentence)
    (model : HEq left.mapModel right.mapModel) :
    left = right := by
  cases left
  cases right
  cases signature
  cases sentence
  cases model
  rfl

/-- The identity embedding changes neither syntax nor models. -/
def identity
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} Signature]
    (institution : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} Signature) :
    Comorphism institution institution where
  mapSignature := 𝟭 Signature
  mapSentence := (CategoryTheory.Functor.leftUnitor institution.sentence).inv
  mapModel :=
    ((CategoryTheory.Functor.isoWhiskerRight
        (CategoryTheory.Functor.opId Signature) institution.model) ≪≫
      CategoryTheory.Functor.leftUnitor institution.model).hom
  satisfaction_condition := by
    intro signature model sentence
    change institution.satisfies signature model sentence ↔
      institution.satisfies signature
        ((institution.model.map
          (CategoryTheory.CategoryStruct.id
            (Opposite.op signature))).toFunctor.obj model) sentence
    simpa only [institution.sentence.map_id_apply,
      CategoryTheory.op_id] using
      institution.satisfaction_condition
        (CategoryTheory.CategoryStruct.id signature) model sentence

/-- Institution comorphisms compose: sentence embeddings compose forward,
while the corresponding model views compose in the reverse semantic
direction. -/
def comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} FirstSignature]
    [CategoryTheory.Category.{uSignatureHom} MiddleSignature]
    [CategoryTheory.Category.{uSignatureHom} LastSignature]
    {first : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} FirstSignature}
    {middle : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} MiddleSignature}
    {last : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} LastSignature}
    (earlier : Comorphism first middle)
    (later : Comorphism middle last) :
    Comorphism first last where
  mapSignature := earlier.mapSignature ⋙ later.mapSignature
  mapSentence := earlier.mapSentence ≫
    CategoryTheory.Functor.whiskerLeft earlier.mapSignature later.mapSentence
  mapModel :=
    CategoryTheory.Functor.whiskerLeft earlier.mapSignature.op later.mapModel ≫
      earlier.mapModel
  satisfaction_condition := by
    intro signature targetModel sentence
    exact (later.satisfaction_condition
      (earlier.mapSignature.obj signature) targetModel
      (earlier.mapSentence.app signature sentence)).trans
        (earlier.satisfaction_condition signature
          ((later.mapModel.app
            (Opposite.op (earlier.mapSignature.obj signature))).toFunctor.obj
              targetModel)
          sentence)

/-! ## Model coverage and consequence reflection -/

/-- A comorphism covers models when every source model is literally the reduct
of some target model at the translated signature.  Equality, rather than only
model isomorphism, is required because a bare institution does not assume that
satisfaction is invariant under model isomorphisms.

This is the semantic analogue of the lifting clause in a covered operational
translation. -/
def CoversModels
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    (translation : Comorphism source target) : Prop :=
  ∀ (signature : SourceSignature)
    (sourceModel : source.model.obj (Opposite.op signature)),
    ∃ targetModel : target.model.obj
        (Opposite.op (translation.mapSignature.obj signature)),
      ((translation.mapModel.app
        (Opposite.op signature)).toFunctor.obj targetModel) = sourceModel

/-- Model coverage up to native model isomorphism.  This is the structurally
appropriate grade when satisfaction itself is invariant under isomorphism;
without that separate law it is too weak to imply consequence reflection. -/
def CoversModelsUpToIso
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    (translation : Comorphism source target) : Prop :=
  ∀ (signature : SourceSignature)
    (sourceModel : source.model.obj (Opposite.op signature)),
    ∃ targetModel : target.model.obj
        (Opposite.op (translation.mapSignature.obj signature)),
      Nonempty
        (((translation.mapModel.app
          (Opposite.op signature)).toFunctor.obj targetModel) ≅ sourceModel)

/-- Literal model coverage is a sufficient, but deliberately stronger,
way to obtain coverage up to isomorphism. -/
theorem CoversModels.toUpToIso
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    {translation : Comorphism source target}
    (coverage : translation.CoversModels) :
    translation.CoversModelsUpToIso := by
  intro signature sourceModel
  rcases coverage signature sourceModel with ⟨targetModel, reductEquality⟩
  exact ⟨targetModel, ⟨eqToIso reductEquality⟩⟩

/-- The identity comorphism covers every model. -/
theorem coversModels_identity
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} Signature]
    (institution : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} Signature) :
    (identity institution).CoversModels := by
  intro signature model
  refine ⟨model, ?_⟩
  change
    (institution.model.map
      (CategoryTheory.CategoryStruct.id
        (Opposite.op signature))).toFunctor.obj model = model
  rw [institution.model.map_id]
  rfl

/-- Identity coverage also has the weaker isomorphism-respecting grade. -/
theorem coversModelsUpToIso_identity
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} Signature]
    (institution : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} Signature) :
    (identity institution).CoversModelsUpToIso :=
  (coversModels_identity institution).toUpToIso

/-- Model coverage is closed under composition.  A source model is lifted
first to the middle institution and then to the target institution. -/
theorem CoversModels.comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} FirstSignature]
    [CategoryTheory.Category.{uSignatureHom} MiddleSignature]
    [CategoryTheory.Category.{uSignatureHom} LastSignature]
    {first : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} FirstSignature}
    {middle : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} MiddleSignature}
    {last : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} LastSignature}
    {earlier : Comorphism first middle}
    {later : Comorphism middle last}
    (earlierCoverage : earlier.CoversModels)
    (laterCoverage : later.CoversModels) :
    (earlier.comp later).CoversModels := by
  intro signature sourceModel
  rcases earlierCoverage signature sourceModel with
    ⟨middleModel, middleReduct⟩
  rcases laterCoverage (earlier.mapSignature.obj signature) middleModel with
    ⟨lastModel, lastReduct⟩
  refine ⟨lastModel, ?_⟩
  change
    ((earlier.mapModel.app
      (Opposite.op signature)).toFunctor.obj
        ((later.mapModel.app
          (Opposite.op (earlier.mapSignature.obj signature))).toFunctor.obj
            lastModel)) = sourceModel
  rw [lastReduct, middleReduct]

/-- Coverage up to model isomorphism composes.  The first model-reduct
functor transports the later isomorphism before the earlier isomorphism is
applied. -/
theorem CoversModelsUpToIso.comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} FirstSignature]
    [CategoryTheory.Category.{uSignatureHom} MiddleSignature]
    [CategoryTheory.Category.{uSignatureHom} LastSignature]
    {first : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} FirstSignature}
    {middle : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} MiddleSignature}
    {last : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} LastSignature}
    {earlier : Comorphism first middle}
    {later : Comorphism middle last}
    (earlierCoverage : earlier.CoversModelsUpToIso)
    (laterCoverage : later.CoversModelsUpToIso) :
    (earlier.comp later).CoversModelsUpToIso := by
  intro signature sourceModel
  rcases earlierCoverage signature sourceModel with
    ⟨middleModel, ⟨middleIso⟩⟩
  rcases laterCoverage (earlier.mapSignature.obj signature) middleModel with
    ⟨lastModel, ⟨lastIso⟩⟩
  refine ⟨lastModel, ⟨?_⟩⟩
  exact
    ((earlier.mapModel.app (Opposite.op signature)).toFunctor.mapIso lastIso).trans
      middleIso

/-- A model-covering comorphism is conservative on the image of its sentence
translation.  The forward implication uses the satisfaction condition; the
reverse implication additionally lifts an arbitrary source model. -/
theorem entails_mapped_iff_of_coversModels
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    (translation : Comorphism source target)
    (coverage : translation.CoversModels)
    (signature : SourceSignature)
    (premises : Set (source.sentence.obj signature))
    (conclusion : source.sentence.obj signature) :
    source.Entails signature premises conclusion ↔
      target.Entails (translation.mapSignature.obj signature)
        (Set.image (translation.mapSentence.app signature) premises)
        (translation.mapSentence.app signature conclusion) := by
  constructor
  · intro sourceEntails targetModel satisfiesMappedPremises
    rw [translation.satisfaction_condition]
    exact sourceEntails
      ((translation.mapModel.app
        (Opposite.op signature)).toFunctor.obj targetModel) <| by
      intro premise premiseMember
      rw [← translation.satisfaction_condition signature targetModel premise]
      exact satisfiesMappedPremises
        (translation.mapSentence.app signature premise)
        ⟨premise, premiseMember, rfl⟩
  · intro targetEntails sourceModel satisfiesPremises
    rcases coverage signature sourceModel with
      ⟨targetModel, reductEquality⟩
    have targetSatisfies :
        target.satisfies (translation.mapSignature.obj signature) targetModel
          (translation.mapSentence.app signature conclusion) :=
      targetEntails targetModel <| by
        intro mappedPremise mappedMember
        rcases mappedMember with ⟨premise, premiseMember, rfl⟩
        rw [translation.satisfaction_condition, reductEquality]
        exact satisfiesPremises premise premiseMember
    rw [translation.satisfaction_condition, reductEquality] at targetSatisfies
    exact targetSatisfies

/-- Coverage up to isomorphism yields the same consequence exactness when
source satisfaction is invariant under native model isomorphism.  Keeping the
two premises separate prevents a merely categorical model equivalence from
silently changing truth. -/
theorem entails_mapped_iff_of_coversModelsUpToIso
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    (translation : Comorphism source target)
    (sourceIsoInvariant : source.SatisfactionIsoInvariant)
    (coverage : translation.CoversModelsUpToIso)
    (signature : SourceSignature)
    (premises : Set (source.sentence.obj signature))
    (conclusion : source.sentence.obj signature) :
    source.Entails signature premises conclusion ↔
      target.Entails (translation.mapSignature.obj signature)
        (Set.image (translation.mapSentence.app signature) premises)
        (translation.mapSentence.app signature conclusion) := by
  constructor
  · intro sourceEntails targetModel satisfiesMappedPremises
    rw [translation.satisfaction_condition]
    exact sourceEntails
      ((translation.mapModel.app
        (Opposite.op signature)).toFunctor.obj targetModel) <| by
      intro premise premiseMember
      rw [← translation.satisfaction_condition signature targetModel premise]
      exact satisfiesMappedPremises
        (translation.mapSentence.app signature premise)
        ⟨premise, premiseMember, rfl⟩
  · intro targetEntails sourceModel satisfiesPremises
    rcases coverage signature sourceModel with
      ⟨targetModel, ⟨reductIso⟩⟩
    have targetSatisfies :
        target.satisfies (translation.mapSignature.obj signature) targetModel
          (translation.mapSentence.app signature conclusion) :=
      targetEntails targetModel <| by
        intro mappedPremise mappedMember
        rcases mappedMember with ⟨premise, premiseMember, rfl⟩
        rw [translation.satisfaction_condition]
        exact (sourceIsoInvariant signature _ _ reductIso premise).mpr
          (satisfiesPremises premise premiseMember)
    have reductSatisfies :
        source.satisfies signature
          ((translation.mapModel.app
            (Opposite.op signature)).toFunctor.obj targetModel)
          conclusion :=
      (translation.satisfaction_condition signature targetModel conclusion).mp
        targetSatisfies
    exact (sourceIsoInvariant signature _ _ reductIso conclusion).mp
      reductSatisfies

#print axioms ext
#print axioms identity
#print axioms comp
#print axioms CoversModels
#print axioms CoversModelsUpToIso
#print axioms CoversModels.toUpToIso
#print axioms coversModels_identity
#print axioms coversModelsUpToIso_identity
#print axioms CoversModels.comp
#print axioms CoversModelsUpToIso.comp
#print axioms entails_mapped_iff_of_coversModels
#print axioms entails_mapped_iff_of_coversModelsUpToIso

end Comorphism

#print axioms semanticConsequence
#print axioms map_semanticConsequence
#print axioms valid_map
#print axioms SatisfactionIsoInvariant

end Institution

end Mettapedia.Logic
