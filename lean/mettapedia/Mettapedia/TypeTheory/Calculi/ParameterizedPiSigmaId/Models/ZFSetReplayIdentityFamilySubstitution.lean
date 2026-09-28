import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContextComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayReflexivityAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContextSubstitution

/-!
# Computed substitution into independently checked identity families

The ordinary neutral-endpoint case is handled by the general computed-family
comparison. A diagonal identity family can also have computed, non-neutral
endpoints: using one retained endpoint certificate twice makes its fibre true
regardless of the endpoint's value. The extension below uses the existing
checked substitution operation for arbitrary computed arguments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- A checked reflexivity proof over a supported source endpoint remains a
member of its independently checked identity formation after the existing
certificate-substitution algorithm inserts arbitrary checked computations.
The substituted endpoint need not itself be structurally supported. Each
image must inhabit its substituted lookup type; no erased-term certificate
reconstruction or global certificate-coherence principle is used. -/
theorem supported_reflexivity_substitute_membership
    {k m : Nat} (sourceContext : Ctx Head k)
    (contextCode : ContextCode Head NoConversion k)
    (sourceValid : Environment.{u} k → Prop)
    (targetContext : Ctx Head m) (targetValid : Environment.{u} m → Prop)
    (A term : Tm Head k) (level : Head)
    (termCode identityCode : Code Head NoConversion k)
    (contextChecked : checkContext R noConversionCheck sourceContext contextCode = true)
    (atContext : assembleContext heads constants contextCode sourceContext = some sourceValid)
    (supported : ZFSetTypeExpressionInterpretation.supported term = true)
    (proofChecked : check R noConversionCheck sourceContext (.refl term)
      (.id A term term) (.reflIntro A termCode) = true)
    (identityChecked : check R noConversionCheck sourceContext (.id A term term)
      (.head level) identityCode = true)
    (σ : Sub Head k m) (codes : Fin k → Code Head NoConversion m)
    (images imageTypes : Fin k → Meaning.{u} m)
    (imagesChecked : ∀ index, check R noConversionCheck targetContext (σ index)
      (subst σ (sourceContext.lookup index)) (codes index) = true)
    (atImages : ∀ index, assemble heads constants (codes index) (σ index)
      (subst σ (sourceContext.lookup index)) = some (images index))
    (atImageTypes : ∀ index, assemble heads constants
      ((contextCode.lookupFormation noConversionRename index).2.substitute
        noConversionRename noConversionSubstitute σ codes (sourceContext.lookup index)
        (.head (contextCode.lookupFormation noConversionRename index).1))
      (subst σ (sourceContext.lookup index))
      (.head (contextCode.lookupFormation noConversionRename index).1) =
        some (imageTypes index))
    (imagesTyped : ∀ env, targetValid env →
      ∀ index, (images index).value env ∈ (imageTypes index).value env) :
    let proof := Tm.refl term
    let identity := Tm.id A term term
    let resultCode := (Code.reflIntro A termCode).substitute
      noConversionRename noConversionSubstitute σ codes proof identity
    let resultFormation := identityCode.substitute
      noConversionRename noConversionSubstitute σ codes identity (.head level)
    check R noConversionCheck targetContext (subst σ proof) (subst σ identity)
      resultCode = true ∧
    check R noConversionCheck targetContext (subst σ identity) (.head level)
      resultFormation = true ∧
    ∃ result formed,
      assemble heads constants resultCode (subst σ proof) (subst σ identity) = some result ∧
      assemble heads constants resultFormation (subst σ identity) (.head level) =
        some formed ∧
      ∀ env, targetValid env → result.value env ∈ formed.value env := by
  obtain ⟨proofMeaning, identityMeaning, atProof, atIdentity, sourceMember⟩ :=
    supported_reflexivity_in_independent_identity heads constants R sourceContext A term
      level termCode identityCode supported proofChecked identityChecked
  exact substitute_membership noConversionRename heads constants
    noConversionSubstitute R noConversionCheck
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible)
    sourceContext contextCode targetContext sourceValid targetValid
    (.refl term) (.id A term term) level (.reflIntro A termCode) identityCode
    proofMeaning identityMeaning contextChecked proofChecked identityChecked
    atContext atProof atIdentity (fun env _ => sourceMember env)
    σ codes images imageTypes imagesChecked atImages atImageTypes imagesTyped

/-- A diagonal identity family is true at every environment even when its
endpoint expression computes and the two accepted endpoint certificates
differ. Thus independently checked substitutions of arbitrary arguments
produce equal fibres without requiring argument-value agreement or neutral
eliminations. This is specific to the diagonal, not general coherence. -/
theorem computed_arguments_diagonal_identity_family_values
    {context : Ctx Head n} {A leftArgument rightArgument : Tm Head n}
    (leftCode rightCode : Code Head NoConversion n)
    (leftArgumentMeaning rightArgumentMeaning : Meaning.{u} n)
    (leftChecked : check R noConversionCheck context leftArgument A leftCode = true)
    (rightChecked : check R noConversionCheck context rightArgument A rightCode = true)
    (atLeftArgument : assemble heads constants leftCode leftArgument A = some leftArgumentMeaning)
    (atRightArgument : assemble heads constants rightCode rightArgument A = some rightArgumentMeaning)
    (carrier endpoint : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftCarrier rightCarrier leftEndpoint rightEndpoint : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier endpoint endpoint) (.head leftLevel)
      (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint) = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier endpoint endpoint) (.head rightLevel)
      (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint) = true) :
    let family := Tm.id carrier endpoint endpoint
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftArgument
      (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint) leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightArgument
      (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint) rightCode
    check R noConversionCheck context (inst0 leftArgument family)
        (.head leftLevel) leftFormation = true ∧
      check R noConversionCheck context (inst0 rightArgument family)
        (.head rightLevel) rightFormation = true ∧
      ∃ left right,
        assemble heads constants leftFormation (inst0 leftArgument family)
          (.head leftLevel) = some left ∧
        assemble heads constants rightFormation (inst0 rightArgument family)
          (.head rightLevel) = some right ∧
        ∀ env, left.value env = right.value env := by
  dsimp only
  have leftFormationChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) leftFamilyChecked leftChecked
  have rightFormationChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) rightFamilyChecked rightChecked
  obtain ⟨leftFamilyMeaning, atLeftFamily, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint)
    leftFamilyChecked
  obtain ⟨rightFamilyMeaning, atRightFamily, _⟩ := accepted_assembles heads constants R
    noConversionCheck (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint)
    rightFamilyChecked
  obtain ⟨leftEnd, leftEndAgain, atLeftEnd, atLeftEndAgain, leftValue⟩ :=
    assemble_identity_endpoints heads constants
      (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint)
      carrier endpoint endpoint (.head leftLevel) leftLevel leftCarrier
      leftEndpoint leftEndpoint .hole leftFamilyMeaning rfl atLeftFamily
  obtain ⟨rightEnd, rightEndAgain, atRightEnd, atRightEndAgain, rightValue⟩ :=
    assemble_identity_endpoints heads constants
      (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint)
      carrier endpoint endpoint (.head rightLevel) rightLevel rightCarrier
      rightEndpoint rightEndpoint .hole rightFamilyMeaning rfl atRightFamily
  obtain ⟨left, atLeft, leftValues⟩ := assemble_instantiate
    noConversionRename noConversionSubstitute heads constants R noConversionCheck
    (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint) leftCode
    leftFamilyMeaning leftArgumentMeaning leftFamilyChecked atLeftFamily atLeftArgument
  obtain ⟨right, atRight, rightValues⟩ := assemble_instantiate
    noConversionRename noConversionSubstitute heads constants R noConversionCheck
    (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint) rightCode
    rightFamilyMeaning rightArgumentMeaning rightFamilyChecked atRightFamily atRightArgument
  refine ⟨leftFormationChecked, rightFormationChecked, left, right, atLeft, atRight, ?_⟩
  intro env
  have leftSame : leftEnd = leftEndAgain := by
    rw [atLeftEnd] at atLeftEndAgain
    exact Option.some.inj atLeftEndAgain
  have rightSame : rightEnd = rightEndAgain := by
    rw [atRightEnd] at atRightEndAgain
    exact Option.some.inj atRightEndAgain
  rw [leftValues, rightValues, leftValue, rightValue]
  rw [leftSame, rightSame]
  simp only [Meaning.plain]

/-- The two different substituted identity types define the same dependent
context extension. This follows from the checked generated certificates, not
from identifying their raw type expressions. -/
theorem computed_arguments_diagonal_identity_family_contexts
    {context : Ctx Head n} {A leftArgument rightArgument : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (leftCode rightCode : Code Head NoConversion n)
    (leftArgumentMeaning rightArgumentMeaning : Meaning.{u} n)
    (valid : Environment.{u} n → Prop)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (leftChecked : check R noConversionCheck context leftArgument A leftCode = true)
    (rightChecked : check R noConversionCheck context rightArgument A rightCode = true)
    (atLeftArgument : assemble heads constants leftCode leftArgument A = some leftArgumentMeaning)
    (atRightArgument : assemble heads constants rightCode rightArgument A = some rightArgumentMeaning)
    (carrier endpoint : Tm Head (n + 1)) (leftLevel rightLevel : Head)
    (leftUniverse : R.isUniverse leftLevel) (rightUniverse : R.isUniverse rightLevel)
    (leftCarrier rightCarrier leftEndpoint rightEndpoint : Code Head NoConversion (n + 1))
    (leftFamilyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier endpoint endpoint) (.head leftLevel)
      (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint) = true)
    (rightFamilyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier endpoint endpoint) (.head rightLevel)
      (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint) = true) :
    let family := Tm.id carrier endpoint endpoint
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head leftLevel) leftArgument
      (.idForm leftLevel leftCarrier leftEndpoint leftEndpoint) leftCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      family (.head rightLevel) rightArgument
      (.idForm rightLevel rightCarrier rightEndpoint rightEndpoint) rightCode
    checkContext R noConversionCheck (.snoc context (inst0 leftArgument family))
      (.snoc contextCode leftLevel leftFormation) = true ∧
    checkContext R noConversionCheck (.snoc context (inst0 rightArgument family))
      (.snoc contextCode rightLevel rightFormation) = true ∧
    ∃ leftValid rightValid,
      assembleContext heads constants (.snoc contextCode leftLevel leftFormation)
        (.snoc context (inst0 leftArgument family)) = some leftValid ∧
      assembleContext heads constants (.snoc contextCode rightLevel rightFormation)
        (.snoc context (inst0 rightArgument family)) = some rightValid ∧
      leftValid = rightValid := by
  dsimp only
  obtain ⟨leftChecked', rightChecked', left, right, atLeft, atRight, equal⟩ :=
    computed_arguments_diagonal_identity_family_values heads constants R
      leftCode rightCode leftArgumentMeaning rightArgumentMeaning
      leftChecked rightChecked atLeftArgument atRightArgument
      carrier endpoint leftLevel rightLevel leftCarrier rightCarrier
      leftEndpoint rightEndpoint leftFamilyChecked rightFamilyChecked
  refine ⟨?_, ?_,
    (fun env => valid (env ∘ wk) ∧ env 0 ∈ left.value (env ∘ wk)),
    (fun env => valid (env ∘ wk) ∧ env 0 ∈ right.value (env ∘ wk)), ?_, ?_, ?_⟩
  · simpa only [checkContext, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro contextChecked leftUniverse) leftChecked'
  · simpa only [checkContext, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro contextChecked rightUniverse) rightChecked'
  · simp only [assembleContext, atContext, atLeft, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  · simp only [assembleContext, atContext, atRight, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  · apply assembleContext_extensions_eq heads constants context context
      (inst0 leftArgument (.id carrier endpoint endpoint))
      (inst0 rightArgument (.id carrier endpoint endpoint))
      contextCode contextCode leftLevel rightLevel _ _ valid valid left right _ _
      atContext atContext atLeft atRight
    · simp only [assembleContext, atContext, atLeft, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    · simp only [assembleContext, atContext, atRight, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    · exact fun _ => Iff.rfl
    · exact fun env _ => equal env

/-- Substitution of an arbitrary checked argument produces both a checked
diagonal identity formation and a checked reflexivity proof. The resulting
proof belongs to that *generated* dependent type at every environment. No
neutrality or value agreement of independently checked arguments is used. -/
theorem computed_argument_diagonal_reflexivity_membership
    {context : Ctx Head n} {A argument : Tm Head n}
    (argumentCode : Code Head NoConversion n)
    (argumentChecked : check R noConversionCheck context argument A argumentCode = true)
    (carrier endpoint : Tm Head (n + 1)) (level : Head)
    (carrierCode endpointCode : Code Head NoConversion (n + 1))
    (familyChecked : check R noConversionCheck (.snoc context A)
      (.id carrier endpoint endpoint) (.head level)
      (.idForm level carrierCode endpointCode endpointCode) = true) :
    let family := Tm.id carrier endpoint endpoint
    let proof := Tm.refl endpoint
    let familyCode := Code.instantiate noConversionRename noConversionSubstitute
      family (.head level) argument
      (.idForm level carrierCode endpointCode endpointCode) argumentCode
    let proofCode := Code.instantiate noConversionRename noConversionSubstitute
      proof family argument (.reflIntro carrier endpointCode) argumentCode
    check R noConversionCheck context (inst0 argument family) (.head level) familyCode = true ∧
      check R noConversionCheck context (inst0 argument proof)
        (inst0 argument family) proofCode = true ∧
      ∃ familyMeaning proofMeaning,
        assemble heads constants familyCode (inst0 argument family)
          (.head level) = some familyMeaning ∧
        assemble heads constants proofCode (inst0 argument proof)
          (inst0 argument family) = some proofMeaning ∧
        ∀ env, proofMeaning.value env ∈ familyMeaning.value env := by
  dsimp only
  obtain ⟨endpointChecked, _⟩ := identity_endpoint_checks R
    (.idForm level carrierCode endpointCode endpointCode) level
    carrierCode endpointCode endpointCode .hole familyChecked rfl
  have proofChecked : check R noConversionCheck (.snoc context A)
      (.refl endpoint) (.id carrier endpoint endpoint)
      (.reflIntro carrier endpointCode) = true := by
    simp [check, endpointChecked]
  have familyInstanceChecked := Code.instantiate_checked noConversionRename
    noConversionSubstitute R noConversionCheck
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) familyChecked argumentChecked
  have proofInstanceChecked := Code.instantiate_checked noConversionRename
    noConversionSubstitute R noConversionCheck
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) proofChecked argumentChecked
  obtain ⟨familyMeaning, atFamily, _⟩ := accepted_assembles heads constants R
    noConversionCheck _ familyInstanceChecked
  obtain ⟨proofMeaning, atProof, _⟩ := accepted_assembles heads constants R
    noConversionCheck _ proofInstanceChecked
  refine ⟨familyInstanceChecked, proofInstanceChecked, familyMeaning,
    proofMeaning, atFamily, atProof, ?_⟩
  have familyCodeShape :
      Code.instantiate noConversionRename noConversionSubstitute
        (.id carrier endpoint endpoint) (.head level) argument
        (.idForm level carrierCode endpointCode endpointCode) argumentCode =
      .idForm level
        (Code.instantiate noConversionRename noConversionSubstitute
          carrier (.head level) argument carrierCode argumentCode)
        (Code.instantiate noConversionRename noConversionSubstitute
          endpoint carrier argument endpointCode argumentCode)
        (Code.instantiate noConversionRename noConversionSubstitute
          endpoint carrier argument endpointCode argumentCode) := by rfl
  have proofCodeShape :
      Code.instantiate noConversionRename noConversionSubstitute
        (.refl endpoint) (.id carrier endpoint endpoint) argument
        (.reflIntro carrier endpointCode) argumentCode =
      .reflIntro (inst0 argument carrier)
        (Code.instantiate noConversionRename noConversionSubstitute
          endpoint carrier argument endpointCode argumentCode) := by rfl
  rw [familyCodeShape] at atFamily
  rw [proofCodeShape] at atProof
  exact reflexivity_in_same_endpoint_formation heads constants
    (inst0 argument carrier) (inst0 argument endpoint) level
    _ _ _ proofMeaning familyMeaning atProof atFamily

/-- Off the diagonal the identity fibre can be empty, so the preceding law
cannot be silently extended to arbitrary identity endpoints. -/
theorem diagonal_restriction_necessary {x y : ZFSet.{u}} (different : x ≠ y) :
    (truthCode (x = x) : ZFSet.{u}) ≠ (truthCode (x = y) : ZFSet.{u}) := by
  intro same
  have inside : (∅ : ZFSet.{u}) ∈ (truthCode (x = x) : ZFSet.{u}) :=
    (mem_truthCode _ _).mpr ⟨rfl, rfl⟩
  have inside' : (∅ : ZFSet.{u}) ∈ (truthCode (x = y) : ZFSet.{u}) := by
    rw [same] at inside
    exact inside
  exact different ((mem_truthCode _ _).mp inside').2

#print axioms computed_arguments_diagonal_identity_family_values
#print axioms supported_reflexivity_substitute_membership
#print axioms computed_arguments_diagonal_identity_family_contexts
#print axioms computed_argument_diagonal_reflexivity_membership
#print axioms diagonal_restriction_necessary

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
