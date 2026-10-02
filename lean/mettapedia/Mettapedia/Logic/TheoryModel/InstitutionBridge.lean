import Mettapedia.Logic.TheoryModel.Universe
import Mettapedia.Logic.InstitutionCanary

/-!
# Institutions: consequence, translation and conservativity through hosting

At a fixed signature the satisfaction relation of an institution is a
theory/model polarity, and its semantic consequence is `theoryOf ∘ models`.
The satisfaction condition says that sentence translation and model reduct
form a satisfaction-preserving pair, so a translated theory has as models
exactly the models whose reducts are models.

For a comorphism into a target logic, the reducts of target models form a
universe of source models. Translating a source theory and pulling back the
consequences computed in the target gives the source consequences computed in
that universe. Hence a comorphism is conservative on a theory exactly when its
universe of reducts hosts the theory faithfully. Coverage of models makes the
universe of reducts the full universe; coverage up to isomorphism, with
isomorphism-invariant satisfaction, gives every source model an elementarily
equivalent reduct; either way every theory is hosted faithfully.

Controls: the collapsing comorphism of the canary module has a universe of
reducts that validates an extra sentence, and the representative comorphism
hosts every theory faithfully.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.InstitutionBridge

open CategoryTheory
open Mettapedia.Logic (Institution)

universe uSignature uSignatureHom uSentence uModel uModelHom

/-! ## One institution -/

section Single

variable {Signature : Type uSignature} [Category.{uSignatureHom} Signature]
  (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} Signature)

/-- Entailment in an institution is entailment in its satisfaction polarity. -/
theorem entails_iff (signature : Signature) (T : Set (institution.sentence.obj signature))
    (φ : institution.sentence.obj signature) :
    institution.Entails signature T φ ↔ Entails (institution.satisfies signature) T φ :=
  ⟨fun entails _ model => entails _ fun _ member => model member,
    fun entails _ satisfied => entails fun _ member => satisfied _ member⟩

/-- **The semantic consequence of an institution is `theoryOf ∘ models`.** -/
theorem semanticConsequence_eq (signature : Signature)
    (T : Set (institution.sentence.obj signature)) :
    institution.semanticConsequence signature T =
      theoryOf (institution.satisfies signature) (models (institution.satisfies signature) T) :=
  Set.ext fun φ => entails_iff institution signature T φ

/-- The satisfaction condition in model-class form: the models of a translated
theory are the models whose reducts are models of the theory. -/
theorem models_map_eq_preimage_reduct {source target : Signature}
    (translation : source ⟶ target) (T : Set (institution.sentence.obj source)) :
    models (institution.satisfies target) (institution.sentence.map translation '' T) =
      institution.reduct translation ⁻¹' models (institution.satisfies source) T :=
  models_image_eq_preimage (institution.reduct translation) (institution.sentence.map translation)
    (institution.satisfaction_condition translation) T

end Single

/-! ## Comorphisms -/

section Comorphism

variable {SourceSignature TargetSignature : Type uSignature}
  [Category.{uSignatureHom} SourceSignature] [Category.{uSignatureHom} TargetSignature]
  {source : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} SourceSignature}
  {target : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} TargetSignature}
  (translation : Institution.Comorphism source target) (signature : SourceSignature)

/-- The model reduct of a comorphism at a signature. -/
abbrev modelReduct :
    target.model.obj (Opposite.op (translation.mapSignature.obj signature)) →
      source.model.obj (Opposite.op signature) :=
  (translation.mapModel.app (Opposite.op signature)).toFunctor.obj

/-- The source models that are reducts of target models. -/
def reductUniverse : Set (source.model.obj (Opposite.op signature)) :=
  Set.range (modelReduct translation signature)

/-- **Translating a theory into the target and pulling back the target's
consequences computes the source consequences in the universe of reducts.** -/
theorem preimage_targetConsequence (T : Set (source.sentence.obj signature)) :
    translation.mapSentence.app signature ⁻¹'
        target.semanticConsequence (translation.mapSignature.obj signature)
          (translation.mapSentence.app signature '' T) =
      consequencesIn (source.satisfies signature) (reductUniverse translation signature) T := by
  ext φ
  constructor
  · rintro entails _ ⟨⟨targetModel, rfl⟩, model⟩
    apply (translation.satisfaction_condition signature targetModel φ).mp
    apply entails targetModel
    rintro _ ⟨ψ, member, rfl⟩
    exact (translation.satisfaction_condition signature targetModel ψ).mpr (model member)
  · intro validated targetModel satisfied
    apply (translation.satisfaction_condition signature targetModel φ).mpr
    apply validated
    refine ⟨⟨targetModel, rfl⟩, fun ψ member => ?_⟩
    exact (translation.satisfaction_condition signature targetModel ψ).mp
      (satisfied _ ⟨ψ, member, rfl⟩)

/-- **A comorphism is conservative on a theory exactly when its universe of
reducts hosts the theory faithfully.** -/
theorem conservative_iff_hostsFaithfully (T : Set (source.sentence.obj signature)) :
    (∀ φ, source.Entails signature T φ ↔
        target.Entails (translation.mapSignature.obj signature)
          (translation.mapSentence.app signature '' T)
          (translation.mapSentence.app signature φ)) ↔
      HostsFaithfully (source.satisfies signature) (reductUniverse translation signature) T := by
  unfold HostsFaithfully
  rw [← preimage_targetConsequence, ← semanticConsequence_eq]
  constructor
  · intro conservative
    ext φ
    exact (conservative φ).symm
  · intro equal φ
    exact (Set.ext_iff.mp equal φ).symm

/-- With coverage of models the universe of reducts is every source model. -/
theorem reductUniverse_eq_univ (coverage : translation.CoversModels) :
    reductUniverse translation signature = Set.univ :=
  Set.eq_univ_of_forall fun sourceModel =>
    let ⟨targetModel, equal⟩ := coverage signature sourceModel
    ⟨targetModel, equal⟩

theorem hostsFaithfully_of_coversModels (coverage : translation.CoversModels)
    (T : Set (source.sentence.obj signature)) :
    HostsFaithfully (source.satisfies signature) (reductUniverse translation signature) T := by
  rw [reductUniverse_eq_univ translation signature coverage]
  exact hostsFaithfully_univ T

/-- With coverage up to isomorphism and isomorphism-invariant satisfaction,
every source model has an elementarily equivalent reduct, so every theory is
hosted faithfully. -/
theorem hostsFaithfully_of_coversModelsUpToIso (invariant : source.SatisfactionIsoInvariant)
    (coverage : translation.CoversModelsUpToIso) (T : Set (source.sentence.obj signature)) :
    HostsFaithfully (source.satisfies signature) (reductUniverse translation signature) T :=
  hostsFaithfully_of_twins (fun sourceModel => by
    obtain ⟨targetModel, ⟨isomorphism⟩⟩ := coverage signature sourceModel
    exact ⟨modelReduct translation signature targetModel, ⟨targetModel, rfl⟩,
      fun φ => invariant signature _ _ isomorphism φ⟩) T

end Comorphism

/-! ## Controls -/

namespace Control

open Mettapedia.Logic.InstitutionCanary

/-- The source sentences of the collapsing comorphism: `false` and `true`. -/
abbrev BoolSentence :=
  (Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).sentence.obj (Discrete.mk ())

/-- Negative control: the universe of reducts of the collapsing comorphism
validates `true` as a consequence of `{false}`, which the source does not
entail, so it does not host `{false}` faithfully. -/
theorem collapse_not_hostsFaithfully :
    ¬ HostsFaithfully
      ((Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies
        (Discrete.mk ()))
      (reductUniverse collapseComorphism (Discrete.mk ())) ({false} : Set BoolSentence) := by
  intro faithful
  have conservative :=
    (conservative_iff_hostsFaithfully collapseComorphism (Discrete.mk ()) {false}).mpr faithful
  exact collapseComorphism_does_not_reflect_entailment.2
    ((conservative true).mpr collapseComorphism_does_not_reflect_entailment.1)

/-- The extra sentence is validated by the universe of reducts. -/
theorem collapse_validates_true :
    (true : BoolSentence) ∈ consequencesIn
      ((Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies
        (Discrete.mk ()))
      (reductUniverse collapseComorphism (Discrete.mk ())) ({false} : Set BoolSentence) :=
  (Set.ext_iff.mp (preimage_targetConsequence collapseComorphism (Discrete.mk ()) {false})
    true).mp collapseComorphism_does_not_reflect_entailment.1

/-- Positive control: the representative comorphism hosts every theory
faithfully. -/
theorem representative_hostsFaithfully (T : Set Unit) :
    HostsFaithfully (isoInvariantInstitution.satisfies (Discrete.mk ()))
      (reductUniverse invariantRepresentativeComorphism (Discrete.mk ())) T :=
  hostsFaithfully_of_coversModelsUpToIso invariantRepresentativeComorphism (Discrete.mk ())
    isoInvariantInstitution_satisfactionIsoInvariant
    invariantRepresentativeComorphism_coversModelsUpToIso T

end Control

end Mettapedia.Logic.TheoryModel.InstitutionBridge
