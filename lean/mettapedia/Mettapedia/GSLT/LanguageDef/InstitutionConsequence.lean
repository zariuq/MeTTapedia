import Mettapedia.Logic.InstitutionCategory
import Mettapedia.GSLT.LanguageDef.PiInstitutionCategory
import Mettapedia.GSLT.LanguageDef.OperationalModel

/-!
# Model-valued institutions at the logical/operational seam

Every model-valued institution induces a Pi-institution by semantic
consequence.  This is a forgetful projection: it retains sentences and
consequence but deliberately forgets the model categories, reduct functors,
and satisfaction relation from which consequence arose.

An operational model can be qualified by the stronger structure.  Each
equation class of machine states denotes a native model, and the machine
interpretation of a sentence is defined by satisfaction in that model.  This
makes the logical/operational commuting law constructional instead of an
additional assertion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InstitutionConsequence

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uSignature uSignatureHom uSentence uModel uModelHom uTerm

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uSignatureHom} Signature]

/-- Forget explicit models while retaining their semantic consequence. -/
def consequenceProjection
    (institution : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} Signature) :
    PiInstitution.{uSignature, uSignatureHom, uSentence} Signature where
  sentence := institution.sentence
  consequence := institution.semanticConsequence
  translation := institution.map_semanticConsequence

@[simp]
theorem derives_iff_entails
    (institution : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} Signature)
    (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (conclusion : institution.sentence.obj signature) :
    (consequenceProjection institution).Derives signature premises conclusion ↔
      institution.Entails signature premises conclusion :=
  Iff.rfl

/-- Forgetting explicit models maps a genuine institution comorphism to the
corresponding consequence-preserving Pi-institution comorphism.  Thus the
existing little-theories graph is a projection of the model-valued graph,
not a competing route formalism. -/
def comorphismProjection
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    (route : Institution.Comorphism source target) :
    PiInstitution.Comorphism
      (consequenceProjection source) (consequenceProjection target) where
  mapSignature := route.mapSignature
  mapSentence := fun signature => route.mapSentence.app signature
  mapSentence_natural := by
    intro sourceSignature targetSignature translation formula
    have naturality := route.mapSentence.naturality translation
    exact congrArg (fun function => function formula) naturality.symm
  preserves := by
    intro signature premises conclusion derives targetModel satisfiesMappedPremises
    rw [route.satisfaction_condition]
    exact (derives_iff_entails source signature premises conclusion).mp derives
      ((route.mapModel.app (Opposite.op signature)).toFunctor.obj targetModel) <| by
        intro premise premiseMember
        rw [← route.satisfaction_condition signature targetModel premise]
        exact satisfiesMappedPremises
          (route.mapSentence.app signature premise)
          ⟨premise, premiseMember, rfl⟩

@[simp]
theorem comorphismProjection_mapSignature
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uSignatureHom} SourceSignature]
    [CategoryTheory.Category.{uSignatureHom} TargetSignature]
    {source : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} SourceSignature}
    {target : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} TargetSignature}
    (route : Institution.Comorphism source target) :
    (comorphismProjection route).mapSignature = route.mapSignature :=
  rfl

/-! ## The model-to-consequence projection is functorial -/

/-- Forget the models of one bundled institution while retaining its native
signature category and semantic consequence. -/
def consequenceObject
    (source : Mettapedia.Logic.InstitutionCategory.Object.{uSignature,
      uSignatureHom, uSentence, uModel, uModelHom}) :
    Mettapedia.GSLT.LanguageDef.PiInstitutionCategory.Object.{uSignature,
      uSignatureHom, uSentence} where
  Signature := source.Signature
  logic := consequenceProjection source.logic

/-- Model erasure is an actual functor between the heterogeneous institution
atlas and the heterogeneous consequence atlas.  In particular, erasing models
after composing native routes agrees with composing their erasures. -/
def consequenceFunctor :
    CategoryTheory.Functor
      Mettapedia.Logic.InstitutionCategory.Object.{uSignature,
        uSignatureHom, uSentence, uModel, uModelHom}
      Mettapedia.GSLT.LanguageDef.PiInstitutionCategory.Object.{uSignature,
        uSignatureHom, uSentence} where
  obj := consequenceObject
  map route := comorphismProjection route
  map_id source := by
    apply PiInstitution.Comorphism.ext
    · rfl
    · rfl
  map_comp earlier later := by
    apply PiInstitution.Comorphism.ext
    · rfl
    · rfl

@[simp]
theorem consequenceFunctor_obj_logic
    (source : Mettapedia.Logic.InstitutionCategory.Object.{uSignature,
      uSignatureHom, uSentence, uModel, uModelHom}) :
    (consequenceFunctor.obj source).logic =
      consequenceProjection source.logic :=
  rfl

@[simp]
theorem consequenceFunctor_mapSignature
    {source target : Mettapedia.Logic.InstitutionCategory.Object.{uSignature,
      uSignatureHom, uSentence, uModel, uModelHom}}
    (route : source ⟶ target) :
    (consequenceFunctor.map route).mapSignature = route.mapSignature :=
  rfl

/-- A model-qualified operational semantics for one closed theory.  Machine
states are first quotiented by the GSLT equations; each resulting semantic
state denotes a model of the native theory. -/
structure StateIndexedModel
    (institution : Institution.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} Signature)
    (logical : PiInstitution.TheoryObject
      (consequenceProjection institution)) where
  system : GSLT.{uTerm}
  stateModel : SemanticTerm system →
    institution.model.obj (Opposite.op logical.signature)
  models_theory : ∀ {formula}, formula ∈ logical.theory.1 →
    ∀ state, institution.satisfies logical.signature
      (stateModel state) formula

namespace StateIndexedModel

variable
  {institution : Institution.{uSignature, uSignatureHom, uSentence,
    uModel, uModelHom} Signature}
  {logical : PiInstitution.TheoryObject (consequenceProjection institution)}

/-- Satisfaction in the state-indexed native model is automatically an
equation-invariant predicate on authored machine terms. -/
def interpret
    (face : StateIndexedModel.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom, uTerm} institution logical)
    (formula : institution.sentence.obj logical.signature) :
    EquationPredicate face.system :=
  ⟨fun state => institution.satisfies logical.signature
    (face.stateModel (Quotient.mk face.system.equations state)) formula, by
    intro source target equivalent
    have equalClasses :
        (Quotient.mk face.system.equations source : SemanticTerm face.system) =
          Quotient.mk face.system.equations target :=
      Quotient.sound equivalent
    change institution.satisfies logical.signature
        (face.stateModel (Quotient.mk face.system.equations source)) formula ↔
      institution.satisfies logical.signature
        (face.stateModel (Quotient.mk face.system.equations target)) formula
    rw [equalClasses]
  ⟩

/-- Forget models only after they have generated the operational
interpretation and discharged consequence soundness. -/
def toOperationalModel
    (face : StateIndexedModel.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom, uTerm} institution logical) :
    OperationalModel (consequenceProjection institution) logical where
  system := face.system
  interpret := face.interpret
  consequence_sound := by
    intro premises conclusion derives state satisfiesPremises
    exact derives_iff_entails institution logical.signature premises conclusion
      |>.mp derives
      (face.stateModel (Quotient.mk face.system.equations state)) <| by
        intro premise premiseMember
        simpa only [interpret] using satisfiesPremises premise premiseMember
  theory_sound := by
    intro formula theoremhood state
    simpa only [interpret] using face.models_theory theoremhood
      (Quotient.mk face.system.equations state)

/-- A model-qualified face supplies an modelled node in the existing atlas;
the theory graph is therefore the consequence-level projection of the stronger
model semantics. -/
def toModelledTheory
    (face : StateIndexedModel.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom, uTerm} institution logical) :
    ModelledTheory (consequenceProjection institution) :=
  ⟨logical, face.toOperationalModel⟩

@[simp]
theorem interpret_iff_satisfies
    (face : StateIndexedModel.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom, uTerm} institution logical)
    (formula : institution.sentence.obj logical.signature)
    (state : face.system.Term) :
    face.interpret formula state ↔
      institution.satisfies logical.signature
        (face.stateModel (Quotient.mk face.system.equations state)) formula :=
  by simp only [interpret]

#print axioms consequenceProjection
#print axioms derives_iff_entails
#print axioms comorphismProjection
#print axioms consequenceObject
#print axioms consequenceFunctor
#print axioms consequenceFunctor_obj_logic
#print axioms consequenceFunctor_mapSignature
#print axioms interpret
#print axioms toOperationalModel
#print axioms toModelledTheory
#print axioms interpret_iff_satisfies

end StateIndexedModel

end Mettapedia.GSLT.LanguageDef.InstitutionConsequence
