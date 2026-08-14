import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation

/-!
# Prime language change as an indexed, admitted operation

The returned-fibre comparison in `NativeTypeTheoryDerivation` proves an exact
open-clone equivalence for Prime Need steps, but deliberately excludes pending
`via` commands.  This module supplies the missing indexed layer without
weakening that boundary:

* today's Zero and Prime operational points are distinct objects of a small
  category with one nonidentity forward route;
* the live Zero-to-Prime operational translation is the image of that route;
* route application is simultaneously a GSLT-IL command step and a
  certificate-free arrow in NIK's common admission algebra;
* an occurrence request can cross the language boundary, enter Prime Need,
  and then use the already-proved correct-by-construction Need proof flow;
* no reverse route exists, and the returned fragment still cannot decode all
  commands of even its one-stage diagram.

This is a typed extension of the returned fragment, not an implementation
extracted from it.  In particular, it does not infer a runtime backend,
scheduler, or dialect calculus from the fragment alone.
-/

namespace Mettapedia.Languages.MeTTa.Prime.IndexedLanguageChange

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The current two-point language-change category -/

/-- The two currently selected language-code points.  The type is local to
this concrete witness; the native theory itself remains open to further
language values. -/
inductive Stage where
  | zero
  | prime
  deriving DecidableEq, Repr

/-- Exactly one proper language-changing route, from today's Zero point to
today's Prime point, in addition to identities. -/
inductive StageHom : Stage → Stage → Type
  | idZero : StageHom .zero .zero
  | promote : StageHom .zero .prime
  | idPrime : StageHom .prime .prime

instance stageCategory : CategoryTheory.Category Stage where
  Hom := StageHom
  id
    | .zero => .idZero
    | .prime => .idPrime
  comp first second := by
    cases first <;> cases second
    · exact .idZero
    · exact .promote
    · exact .promote
    · exact .idPrime
  id_comp := by intro first second route; cases route <;> rfl
  comp_id := by intro first second route; cases route <;> rfl
  assoc := by
    intro first second third fourth one two three
    cases one <;> cases two <;> cases three <;> rfl

instance stageHomSubsingleton (source target : Stage) :
    Subsingleton (source ⟶ target) where
  allEq first second := by
    cases first <;> cases second <;> rfl

def zeroStage : Stage := .zero
def primeStage : Stage := .prime
def promote : zeroStage ⟶ primeStage := .promote

/-- There is no reverse language route in the selected current diagram. -/
theorem no_prime_to_zero_route : IsEmpty (primeStage ⟶ zeroStage) := by
  constructor
  intro route
  cases route

/-! ## Connection to the native universe of language codes -/

/-- The selected native language handle at each operational stage. -/
def languageHandle : Stage → CurrentLanguageHandle
  | .zero => .zero
  | .prime => .prime

/-- The validated authored presentation named by each stage. -/
def presentation (stage : Stage) :
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef :=
  currentLanguagePresentation (languageHandle stage)

/-- The exact Pattern code named by each stage. -/
def languagePattern (stage : Stage) : Pattern :=
  currentLanguagePattern (languageHandle stage)

theorem languageHandle_injective : Function.Injective languageHandle := by
  intro first second equal
  cases first <;> cases second <;> cases equal <;> rfl

theorem presentation_injective : Function.Injective presentation :=
  currentLanguagePresentation_injective.comp languageHandle_injective

/-- The nonidentity route really changes the selected language code. -/
theorem promote_changes_language_code :
    languagePattern zeroStage ≠ languagePattern primeStage := by
  decide

/-- Both endpoint codes inhabit the exact selected image of the native
Tarski-style universe. -/
theorem endpoint_codes_are_language_patterns (stage : Stage) :
    familiesLanguageCodeWitness.IsLanguagePattern (languagePattern stage) := by
  exact ⟨languageHandle stage, rfl⟩

/-! ## The live Zero-to-Prime operational diagram -/

/-- Today's Zero and Prime are objects of one operational diagram.  The sole
proper map is the already-proved live Zero-to-Prime operational arrow. -/
def diagram (model : QueryFirstModel) : Diagram Stage where
  obj
    | .zero => ⟨(Mettapedia.Languages.MeTTa.MeTTaZero.currentOperationalPoint
        model.zero).host⟩
    | .prime => ⟨(currentOperationalPoint model).total⟩
  map route := by
    cases route with
    | idZero =>
        exact OperationalTranslation.id
          (Mettapedia.Languages.MeTTa.MeTTaZero.currentOperationalPoint
            model.zero).host
    | promote => exact currentZeroToPrimeOperationalArrow model
    | idPrime =>
        exact OperationalTranslation.id (currentOperationalPoint model).total
  map_id stage := by
    cases stage <;> apply OperationalTranslation.ext <;> rfl
  map_comp first second := by
    cases first <;> cases second <;>
      apply OperationalTranslation.ext <;> rfl

abbrev ZeroTheory (model : QueryFirstModel) :=
  (diagram model).obj zeroStage |>.theory

abbrev PrimeTheory (model : QueryFirstModel) :=
  (diagram model).obj primeStage |>.theory

/-- Quote a Zero host term into its semantic fibre. -/
def quoteZero (model : QueryFirstModel) (term : (ZeroTheory model).Term) :
    SemanticTerm (ZeroTheory model) :=
  Quotient.mk (ZeroTheory model).equations term

/-- Quote a Prime host term into its semantic fibre. -/
def quotePrime (model : QueryFirstModel) (term : (PrimeTheory model).Term) :
    SemanticTerm (PrimeTheory model) :=
  Quotient.mk (PrimeTheory model).equations term

/-- A source term waiting at an explicit language-change boundary. -/
def pendingPromotion (model : QueryFirstModel)
    (state : SemanticTerm (ZeroTheory model)) : Command (diagram model) :=
  .via promote state

/-- The exact target state obtained by applying the authored language route. -/
def promotedState (model : QueryFirstModel)
    (state : SemanticTerm (ZeroTheory model)) : Command (diagram model) :=
  .at primeStage (transportTerm (diagram model) promote state)

/-- Route application is a genuine GSLT-IL command step. -/
def applyPromotion (model : QueryFirstModel)
    (state : SemanticTerm (ZeroTheory model)) :
    Command.Step (diagram model) (pendingPromotion model state)
      (promotedState model state) :=
  .applyVia promote state

/-! ## The same route in NIK's certificate-free admission algebra -/

/-- A source semantic predicate and its direct image under the selected
language-changing map.  The image remembers both the source witness and its
property; it is not the indiscriminate `True` predicate. -/
def imageMeaning (model : QueryFirstModel)
    (sourceMeaning : SemanticTerm (ZeroTheory model) → Prop)
    (target : SemanticTerm (PrimeTheory model)) : Prop :=
  ∃ source, sourceMeaning source ∧
    transportTerm (diagram model) promote source = target

def sourceAdmissionObject (model : QueryFirstModel)
    (sourceMeaning : SemanticTerm (ZeroTheory model) → Prop) :
    AdmissionObject where
  Carrier := SemanticTerm (ZeroTheory model)
  Meaning := sourceMeaning

def targetImageAdmissionObject (model : QueryFirstModel)
    (sourceMeaning : SemanticTerm (ZeroTheory model) → Prop) :
    AdmissionObject where
  Carrier := SemanticTerm (PrimeTheory model)
  Meaning := imageMeaning model sourceMeaning

/-- The operational language route induces the canonical certificate-free
pushforward admission map.  Its target predicate is explicitly the direct
image; the stronger request-specific arrow below uses an independently stated
Prime predicate. -/
def promotionPushforwardAdmission (model : QueryFirstModel)
    (sourceMeaning : SemanticTerm (ZeroTheory model) → Prop) :
    sourceAdmissionObject model sourceMeaning ⟶
      targetImageAdmissionObject model sourceMeaning where
  run := transportTerm (diagram model) promote
  preserves := by
    intro source meaningful
    exact ⟨source, meaningful, rfl⟩

/-- The GSLT-IL transport and NIK admitted operation are definitionally the
same computation on semantic terms. -/
theorem promotion_command_admission_square
    (model : QueryFirstModel)
    (sourceMeaning : SemanticTerm (ZeroTheory model) → Prop)
    (state : SemanticTerm (ZeroTheory model)) :
    (promotionPushforwardAdmission model sourceMeaning).run state =
      transportTerm (diagram model) promote state :=
  rfl

/-- Language transport preserves a genuinely selected source state through
the common admission algebra. -/
theorem selected_state_is_admitted_after_promotion
    (model : QueryFirstModel)
    (selected : SemanticTerm (ZeroTheory model)) :
    (targetImageAdmissionObject model (fun state => state = selected)).Meaning
      ((promotionPushforwardAdmission model
        (fun state => state = selected)).run selected) :=
  ⟨selected, rfl, rfl⟩

/-! ## Crossing from Zero evaluation into Prime Need -/

/-- The selected Zero occurrence request as a term of the current Zero host. -/
def zeroEvaluationRequest (model : QueryFirstModel)
    (space : model.Space) (subject : Pattern) : (ZeroTheory model).Term :=
  (Mettapedia.Languages.MeTTa.MeTTaZero.currentOperationalPoint model.zero).occurrenceEmbedding.toFun
    (.request space subject)

/-- The same request after it has entered Prime's Need component. -/
def primeNeedRequest (model : QueryFirstModel)
    (space : model.Space) (subject : Pattern) : (PrimeTheory model).Term :=
  (needEmbedding model.toPrimeModel).toFun (.request space subject)

/-- Applying the language map to an occurrence request lands exactly at the
Prime base copy of that request. -/
theorem transport_evaluation_request (model : QueryFirstModel)
    (space : model.Space) (subject : Pattern) :
    transportTerm (diagram model) promote
        (quoteZero model (zeroEvaluationRequest model space subject)) =
      quotePrime model
        ((evaluationKernelEmbedding model.toPrimeModel).toFun
          (.request space subject)) := by
  rfl

/-- Independently stated Zero-side request predicate. -/
def IsZeroEvaluationRequest (model : QueryFirstModel)
    (state : SemanticTerm (ZeroTheory model)) : Prop :=
  ∃ (space : model.Space) (subject : Pattern),
    state = quoteZero model (zeroEvaluationRequest model space subject)

/-- Independently stated Prime-side base-request predicate. -/
def IsPrimeBaseRequest (model : QueryFirstModel)
    (state : SemanticTerm (PrimeTheory model)) : Prop :=
  ∃ (space : model.Space) (subject : Pattern),
    state = quotePrime model
      ((evaluationKernelEmbedding model.toPrimeModel).toFun
        (.request space subject))

def zeroRequestAdmissionObject (model : QueryFirstModel) : AdmissionObject where
  Carrier := SemanticTerm (ZeroTheory model)
  Meaning := IsZeroEvaluationRequest model

def primeBaseRequestAdmissionObject (model : QueryFirstModel) : AdmissionObject where
  Carrier := SemanticTerm (PrimeTheory model)
  Meaning := IsPrimeBaseRequest model

/-- The live Zero-to-Prime route preserves an independently stated request
class, not merely a predicate defined as its direct image. -/
def requestPromotionAdmission (model : QueryFirstModel) :
    zeroRequestAdmissionObject model ⟶ primeBaseRequestAdmissionObject model where
  run := transportTerm (diagram model) promote
  preserves := by
    intro state request
    obtain ⟨space, subject, rfl⟩ := request
    exact ⟨space, subject, transport_evaluation_request model space subject⟩

theorem requestPromotionAdmission_run (model : QueryFirstModel)
    (state : SemanticTerm (ZeroTheory model)) :
    (requestPromotionAdmission model).run state =
      transportTerm (diagram model) promote state :=
  rfl

/-- Positive nondegenerate canary for the independent target predicate. -/
theorem concrete_request_is_admitted_after_promotion
    (model : QueryFirstModel) (space : model.Space) (subject : Pattern) :
    (primeBaseRequestAdmissionObject model).Meaning
      ((requestPromotionAdmission model).run
        (quoteZero model (zeroEvaluationRequest model space subject))) :=
  (requestPromotionAdmission model).preserves _ ⟨space, subject, rfl⟩

/-- After crossing the language boundary, the live Prime interaction takes
the request into Need as an ordinary fibre step. -/
def promotedRequestEntersNeed (model : QueryFirstModel)
    (space : model.Space) (subject : Pattern) :
    Command.Step (diagram model)
      (promotedState model
        (quoteZero model (zeroEvaluationRequest model space subject)))
      (.at primeStage (quotePrime model
        (primeNeedRequest model space subject))) := by
  unfold promotedState
  rw [transport_evaluation_request]
  exact .fibre (semanticStep_mk
    (evaluation_enters_need model.toPrimeModel space subject))

/-- A concrete two-edge route: explicit language transport followed by the
live Prime base-to-Need interaction. -/
def zeroRequestToPrimeNeedRoute (model : QueryFirstModel)
    (space : model.Space) (subject : Pattern) :
    Route (Command.Step (diagram model))
      (pendingPromotion model
        (quoteZero model (zeroEvaluationRequest model space subject)))
      (.at primeStage (quotePrime model
        (primeNeedRequest model space subject))) :=
  .cons (applyPromotion model _)
    (.cons (promotedRequestEntersNeed model space subject) (.refl _))

/-! ## Correct-by-construction proof flow after language change -/

open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeNeedProofFlow
open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeGSLTILReturnedFibre

/-- Once the request has entered Need, a real occurrence flows through the
admitted operation algebra with no interior checker invocation.  The theorem
combines the indexed operational route with the existing semantic flow law;
neither side invents a second evaluator. -/
theorem language_change_enables_native_need_flow
    (model : QueryFirstModel) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.toPrimeModel.base.source.occurrences space subject)) :
    Nonempty
        (Route (Command.Step (diagram model))
          (pendingPromotion model
            (quoteZero model (zeroEvaluationRequest model space subject)))
          (.at primeStage (quotePrime model
            (primeNeedRequest model space subject)))) ∧
      Meaning model.toPrimeModel
        (answerClaim model.toPrimeModel space subject result occurrence) := by
  exact ⟨⟨zeroRequestToPrimeNeedRoute model space subject⟩,
    found_flows_without_recheck model.toPrimeModel space subject result
      occurrence copy⟩

/-- The admitted Need operation still commutes with the exact returned-fibre
GSLT-IL representation after the indexed language change has made Need
available. -/
theorem need_admission_still_commutes
    (model : QueryFirstModel)
    (rule : OperationalRule (Step model.toPrimeModel))
    (prior : (Clone model.toPrimeModel).Hom [] rule.source) :
    toReturned model.toPrimeModel
        ((admittedRules model.toPrimeModel).toAdmissionHom rule |>.run
          (singletonEnvironment model.toPrimeModel prior)) =
      ((returnedAdmittedRules model.toPrimeModel).toAdmissionHom
          (toReturnedRule model.toPrimeModel rule) |>.run
        (returnedSingletonEnvironment model.toPrimeModel
          (toReturned model.toPrimeModel prior))) :=
  admission_square_commutes model.toPrimeModel rule prior

/-! ## Negative boundaries -/

/-- The returned-fibre encoder has no right inverse on the full command
language.  Even a one-stage diagram contains pending route commands that no
returned Need claim encodes. -/
theorem no_full_command_decode_from_returned_fragment
    (model : Model) (_claim : Claim model) :
    ¬ ∃ decode : Command (PrimeGSLTILReturnedFibre.diagram model) → Claim model,
      ∀ command,
        encodeClaim model (decode command) = command := by
  rintro ⟨decode, rightInverse⟩
  exact pendingClaim_not_encoded model _claim
    (decode (pendingClaim model _claim))
    (rightInverse (pendingClaim model _claim)).symm

/-- No inverse language change can be manufactured from the selected indexed
diagram: the reverse hom type is empty. -/
theorem no_reverse_language_change :
    ¬ Nonempty (primeStage ⟶ zeroStage) := by
  rintro ⟨route⟩
  cases route

/-! ## Audit package -/

/-- The live nondegenerate witness tying together native language codes,
indexed operational transport, NIK admission, and Prime's zero-recheck Need
flow while retaining both negative boundaries. -/
structure Witness where
  codesDistinct : languagePattern zeroStage ≠ languagePattern primeStage
  sourceCodeInUniverse :
    familiesLanguageCodeWitness.IsLanguagePattern (languagePattern zeroStage)
  targetCodeInUniverse :
    familiesLanguageCodeWitness.IsLanguagePattern (languagePattern primeStage)
  route : zeroStage ⟶ primeStage
  routeChangesCode : languagePattern zeroStage ≠ languagePattern primeStage
  noReverse : IsEmpty (primeStage ⟶ zeroStage)
  requestAdmission : ∀ model : QueryFirstModel,
    zeroRequestAdmissionObject model ⟶ primeBaseRequestAdmissionObject model
  returnedFragmentStrict : ∀ (model : Model), Nonempty (Claim model) →
    ¬ ∃ decode : Command (PrimeGSLTILReturnedFibre.diagram model) → Claim model,
      ∀ command, encodeClaim model (decode command) = command
  nativeFlow : ∀ (model : QueryFirstModel) (space : model.Space)
      (subject result : Pattern) (occurrence : Nat),
    occurrence < Multiset.count result
        (model.toPrimeModel.base.source.occurrences space subject) →
      Meaning model.toPrimeModel
        (answerClaim model.toPrimeModel space subject result occurrence)

def witness : Witness where
  codesDistinct := promote_changes_language_code
  sourceCodeInUniverse := endpoint_codes_are_language_patterns .zero
  targetCodeInUniverse := endpoint_codes_are_language_patterns .prime
  route := promote
  routeChangesCode := promote_changes_language_code
  noReverse := no_prime_to_zero_route
  requestAdmission := requestPromotionAdmission
  returnedFragmentStrict := by
    intro model inhabited
    exact no_full_command_decode_from_returned_fragment model
      (Classical.choice inhabited)
  nativeFlow := by
    intro model space subject result occurrence copy
    exact found_flows_without_recheck model.toPrimeModel space subject result
      occurrence copy

end Mettapedia.Languages.MeTTa.Prime.IndexedLanguageChange
