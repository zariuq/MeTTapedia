import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayDeclaredJAgreement
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayFormation

/-!
# Checked substitution of the declared J-iota semantic square

The native checker transports both retained trees through supplied, checked
dependent substitutions. The existing replay assembly-substitution law then
transports the J-iota value agreement to target environments whose left image
meets the actual set-code admission condition and whose two interpreted method
values agree.
No certificate is reconstructed from an erased subject, and the target
validity premise does not assert soundness of arbitrary target programs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open NativeIndexedFamilies
open NativeIndexedFamilies.Intrinsic (identityEliminateApp)
open NativeJudgmentReplay
open ZFSetTraceIdentityTypeInterpretation
open ZFSetReplayDeclaredJAgreement

universe u

/-- The declared J redex and its method may be transported through two
independently checked dependent substitutions. Their resulting values agree
when the two interpreted method values agree and the left image environment
admits J's carrier, endpoint, motive and method set codes. Other context
components, the substitutions and their retained certificates may differ. -/
theorem checked_j_iota_independent_substitutions
    (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (i j : Nat)
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    {n m : Nat} (sourceContext : Tower.Ctx n) (sourceContextCode : ContextCode n)
    (targetContext : Tower.Ctx m) (targetContextCode : ContextCode m)
    (A X P D displayed : Tower.Tm n)
    (hA : ZFSetTypeExpressionInterpretation.supported A = true)
    (hX : ZFSetTypeExpressionInterpretation.supported X = true)
    (hP : ZFSetTypeExpressionInterpretation.supported P = true)
    (hD : ZFSetTypeExpressionInterpretation.supported D = true)
    (sourceCode resultCode : Code n)
    (sourceAccepted : NativeJudgmentReplay.check sourceContext
      (identityEliminateApp A X P D X (.refl X)) displayed sourceContextCode sourceCode = true)
    (resultAccepted : NativeJudgmentReplay.check sourceContext D displayed
      sourceContextCode resultCode = true)
    (targetFormed : StructuralTypingReplay.checkContext IntrinsicRelator.rules
      NativeRelatorConversionChecking.check targetContext targetContextCode = true)
    (leftSub rightSub : Sub Tower.Head n m)
    (leftImageCodes rightImageCodes : Fin n → Code m)
    (leftImagesChecked : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check targetContext)
      sourceContext leftSub leftImageCodes = true)
    (rightImagesChecked : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check targetContext)
      sourceContext rightSub rightImageCodes = true)
    (leftImageMeanings rightImageMeanings : Fin n → Meaning.{u} m)
    (atLeftImages : ∀ index,
      assemble heads (identityConstants h seed i j constants)
        (leftImageCodes index) (leftSub index)
        (subst leftSub (sourceContext.lookup index)) =
        some (leftImageMeanings index))
    (atRightImages : ∀ index,
      assemble heads (identityConstants h seed i j constants)
        (rightImageCodes index) (rightSub index)
        (subst rightSub (sourceContext.lookup index)) =
        some (rightImageMeanings index))
    (targetValid : Environment.{u} m → Prop)
    (methodValuesAgree : ∀ env, targetValid env →
      ZFSetTypeExpressionInterpretation.interpret heads
        (identityConstants h seed i j constants) D hD
        (imageEnvironment leftImageMeanings env) =
      ZFSetTypeExpressionInterpretation.interpret heads
        (identityConstants h seed i j constants) D hD
        (imageEnvironment rightImageMeanings env))
    (admittedLeft : ∀ env, targetValid env →
      AdmittedJArguments h seed i j heads constants A X P D hA hX hP hD
        (imageEnvironment leftImageMeanings env)) :
    NativeJudgmentReplay.check targetContext
      (subst leftSub (identityEliminateApp A X P D X (.refl X)))
      (subst leftSub displayed) targetContextCode
      (NativeJudgmentReplay.substitute leftSub leftImageCodes
        (identityEliminateApp A X P D X (.refl X)) displayed sourceCode) = true ∧
    NativeJudgmentReplay.check targetContext (subst rightSub D) (subst rightSub displayed)
      targetContextCode
      (NativeJudgmentReplay.substitute rightSub rightImageCodes D displayed resultCode) = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h seed i j constants)
        (NativeJudgmentReplay.substitute leftSub leftImageCodes
          (identityEliminateApp A X P D X (.refl X)) displayed sourceCode)
        (subst leftSub (identityEliminateApp A X P D X (.refl X)))
        (subst leftSub displayed) = some sourceAfter ∧
      assemble heads (identityConstants h seed i j constants)
        (NativeJudgmentReplay.substitute rightSub rightImageCodes D displayed resultCode)
        (subst rightSub D) (subst rightSub displayed) = some resultAfter ∧
      ∀ env, targetValid env → sourceAfter.value env = resultAfter.value env := by
  have sourceChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check sourceContext
      (identityEliminateApp A X P D X (.refl X)) displayed sourceCode = true := by
    have accepted := sourceAccepted
    change checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
      sourceContext (identityEliminateApp A X P D X (.refl X)) displayed
      sourceContextCode sourceCode = true at accepted
    simp only [checkJudgment, Bool.and_eq_true] at accepted
    exact accepted.2
  have resultChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check sourceContext D displayed resultCode = true := by
    have accepted := resultAccepted
    change checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
      sourceContext D displayed sourceContextCode resultCode = true at accepted
    simp only [checkJudgment, Bool.and_eq_true] at accepted
    exact accepted.2
  obtain ⟨sourceMeaning, resultMeaning, atSource, atResult, sourceAgreement⟩ :=
    accepted_declared_j_iota_on_admitted_environments h seed i j heads constants
      sourceContext A X P D displayed hA hX hP hD sourceCode resultCode
      sourceChecked resultChecked
  have sourceAfterChecked := NativeJudgmentReplay.check_substitute sourceAccepted
    targetContextCode targetFormed leftSub leftImageCodes leftImagesChecked
  have resultAfterChecked := NativeJudgmentReplay.check_substitute resultAccepted
    targetContextCode targetFormed rightSub rightImageCodes rightImagesChecked
  let sourceRelation : Environment.{u} n → Environment.{u} n → Prop :=
    fun left right =>
      AdmittedJArguments h seed i j heads constants A X P D hA hX hP hD left ∧
      ZFSetTypeExpressionInterpretation.interpret heads
        (identityConstants h seed i j constants) D hD left =
      ZFSetTypeExpressionInterpretation.interpret heads
        (identityConstants h seed i j constants) D hD right
  let targetRelation : Environment.{u} m → Environment.{u} m → Prop :=
    fun left right => left = right ∧ targetValid left
  have sourcesRelated : ∀ left right, sourceRelation left right →
      sourceMeaning.value left = resultMeaning.value right := by
    intro left right related
    rcases related with ⟨admitted, methodsAgree⟩
    calc
      sourceMeaning.value left = resultMeaning.value left := sourceAgreement left admitted
      _ = ZFSetTypeExpressionInterpretation.interpret heads
          (identityConstants h seed i j constants) D hD left :=
        agrees_with_type_expressions heads (identityConstants h seed i j constants)
          resultCode D displayed resultMeaning hD atResult left
      _ = ZFSetTypeExpressionInterpretation.interpret heads
          (identityConstants h seed i j constants) D hD right := methodsAgree
      _ = resultMeaning.value right :=
        (agrees_with_type_expressions heads (identityConstants h seed i j constants)
          resultCode D displayed resultMeaning hD atResult right).symm
  have imagesRelated : ∀ left right, targetRelation left right →
      sourceRelation (imageEnvironment leftImageMeanings left)
        (imageEnvironment rightImageMeanings right) := by
    intro left right related
    rcases related with ⟨rfl, valid⟩
    exact ⟨admittedLeft left valid, methodValuesAgree left valid⟩
  obtain ⟨sourceAfter, resultAfter, atSourceAfter, atResultAfter, afterAgreement⟩ :=
    assemble_substitute_related
      heads (identityConstants h seed i j constants)
      NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
      IntrinsicRelator.rules NativeRelatorConversionChecking.check
      sourceContext sourceContext
      (identityEliminateApp A X P D X (.refl X)) displayed D displayed
      sourceCode resultCode sourceMeaning resultMeaning
      sourceChecked resultChecked atSource atResult
      leftSub rightSub leftImageCodes rightImageCodes
      leftImageMeanings rightImageMeanings atLeftImages atRightImages
      sourceRelation targetRelation Eq sourcesRelated imagesRelated
  exact ⟨sourceAfterChecked, resultAfterChecked, sourceAfter, resultAfter,
    atSourceAfter, atResultAfter, fun env valid =>
      afterAgreement env env ⟨rfl, valid⟩⟩

/-- A genuine checked dependent substitution preserves the two accepted J
trees and their set values. The target-environment predicate is explicit:
its image must give the carrier, endpoint, motive and method values their
stated J set-code memberships. No syntactic equality of the resulting
subject and method is inferred. -/
theorem checked_j_iota_substitute
    (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (i j : Nat)
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    {n m : Nat} (sourceContext : Tower.Ctx n) (sourceContextCode : ContextCode n)
    (targetContext : Tower.Ctx m) (targetContextCode : ContextCode m)
    (A X P D displayed : Tower.Tm n)
    (hA : ZFSetTypeExpressionInterpretation.supported A = true)
    (hX : ZFSetTypeExpressionInterpretation.supported X = true)
    (hP : ZFSetTypeExpressionInterpretation.supported P = true)
    (hD : ZFSetTypeExpressionInterpretation.supported D = true)
    (sourceCode resultCode : Code n)
    (sourceAccepted : NativeJudgmentReplay.check sourceContext
      (identityEliminateApp A X P D X (.refl X)) displayed sourceContextCode sourceCode = true)
    (resultAccepted : NativeJudgmentReplay.check sourceContext D displayed
      sourceContextCode resultCode = true)
    (targetFormed : StructuralTypingReplay.checkContext IntrinsicRelator.rules
      NativeRelatorConversionChecking.check targetContext targetContextCode = true)
    (σ : Sub Tower.Head n m) (imageCodes : Fin n → Code m)
    (imagesChecked : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check targetContext)
      sourceContext σ imageCodes = true)
    (imageMeanings : Fin n → Meaning.{u} m)
    (atImages : ∀ index,
      assemble heads (identityConstants h seed i j constants)
        (imageCodes index) (σ index) (subst σ (sourceContext.lookup index)) =
        some (imageMeanings index))
    (targetValid : Environment.{u} m → Prop)
    (admittedImages : ∀ env, targetValid env →
      AdmittedJArguments h seed i j heads constants A X P D hA hX hP hD
        (imageEnvironment imageMeanings env)) :
    NativeJudgmentReplay.check targetContext
      (subst σ (identityEliminateApp A X P D X (.refl X))) (subst σ displayed)
      targetContextCode
      (NativeJudgmentReplay.substitute σ imageCodes
        (identityEliminateApp A X P D X (.refl X)) displayed sourceCode) = true ∧
    NativeJudgmentReplay.check targetContext (subst σ D) (subst σ displayed)
      targetContextCode (NativeJudgmentReplay.substitute σ imageCodes D displayed resultCode) = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h seed i j constants)
        (NativeJudgmentReplay.substitute σ imageCodes
          (identityEliminateApp A X P D X (.refl X)) displayed sourceCode)
        (subst σ (identityEliminateApp A X P D X (.refl X))) (subst σ displayed) =
        some sourceAfter ∧
      assemble heads (identityConstants h seed i j constants)
        (NativeJudgmentReplay.substitute σ imageCodes D displayed resultCode)
        (subst σ D) (subst σ displayed) = some resultAfter ∧
      ∀ env, targetValid env → sourceAfter.value env = resultAfter.value env := by
  exact checked_j_iota_independent_substitutions h seed i j heads constants
    sourceContext sourceContextCode targetContext targetContextCode
    A X P D displayed hA hX hP hD sourceCode resultCode
    sourceAccepted resultAccepted targetFormed
    σ σ imageCodes imageCodes imagesChecked imagesChecked
    imageMeanings imageMeanings atImages atImages targetValid
    (by intro _ _; rfl) admittedImages

namespace Controls

private def methodType : Tower.Tm 4 := Intrinsic.identityIotaResultType
private def identityFunctionType : Tower.Tm 4 := .pi methodType (rename wk methodType)
private def computedMethod : Tower.Tm 4 := .app (.lam (.var 0)) (.var 0)

private def functionProposal : Tower.Tm 4 × Code 4 :=
  (CertificateProposal.term 64 Intrinsic.contextAXPD identityFunctionType).get
    (by decide +kernel)

private def functionLevel? : Option Tower.Head :=
  match functionProposal.1 with
  | .head level => some level
  | _ => none

private def functionLevel : Tower.Head := functionLevel?.get (by decide +kernel)

private theorem proposal_is_formation :
    functionProposal.1 = .head functionLevel := by
  rfl

private theorem function_formation_checked :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      identityFunctionType (.head functionLevel) functionProposal.2 = true := by
  decide +kernel

private theorem method_supported :
    ZFSetTypeExpressionInterpretation.supported methodType = true := by
  decide

private def computedMethodCode : Code 4 :=
  .appElim methodType (rename wk methodType)
    (.lamIntro functionLevel functionProposal.2 .var) .var

theorem computed_method_checks :
    StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
      Intrinsic.contextAXPD computedMethod methodType computedMethodCode = true := by
  decide +kernel

def computedMethodSubstitution : Sub Tower.Head 4 4 :=
  fun index => if index = 0 then computedMethod else .var index

private theorem substituted_method_type :
    subst computedMethodSubstitution (Intrinsic.contextAXPD.lookup 0) = methodType := by
  decide +kernel

def computedMethodImageCodes : Fin 4 → Code 4 :=
  fun index => if index = 0 then computedMethodCode else .var

theorem computed_method_images_check :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD computedMethodSubstitution computedMethodImageCodes = true := by
  decide +kernel

/-- The comparison's second substitution keeps the original variables and
their own retained variable certificates. -/
def identityImageCodes : Fin 4 → Code 4 := fun _ => .var

theorem identity_images_check :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
      Intrinsic.contextAXPD ids identityImageCodes = true := by
  apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
  intro index
  simp only [identityImageCodes, ids, subst_ids, StructuralTypingReplay.check, decide_true]

def identityImageMeaning (index : Fin 4) : Meaning.{u} 4 :=
  .plain (fun env => env index)

theorem identity_image_assembles (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 4) :
    assemble heads (identityConstants h ∅ 0 1 constants) (identityImageCodes index)
      (ids index) (subst ids (Intrinsic.contextAXPD.lookup index)) =
        some (identityImageMeaning index) := by
  rfl

theorem identity_image_environment (env : Environment.{u} 4) :
    imageEnvironment identityImageMeaning env = env := by
  funext index
  rfl

private theorem image_checked (index : Fin 4) :
    StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      (computedMethodSubstitution index)
      (subst computedMethodSubstitution (Intrinsic.contextAXPD.lookup index))
      (computedMethodImageCodes index) = true :=
  (TelescopeArgumentChecking.checkArguments_eq_true_iff
    (StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD)
    Intrinsic.contextAXPD computedMethodSubstitution computedMethodImageCodes).mp
      computed_method_images_check index

noncomputable def imageMeaning (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 4) : Meaning.{u} 4 :=
  Classical.choose (accepted_assembles heads (identityConstants h ∅ 0 1 constants)
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    (computedMethodImageCodes index) (image_checked index))

theorem image_assembles (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 4) :
    assemble heads (identityConstants h ∅ 0 1 constants)
      (computedMethodImageCodes index) (computedMethodSubstitution index)
      (subst computedMethodSubstitution (Intrinsic.contextAXPD.lookup index)) =
      some (imageMeaning h heads constants index) :=
  (Classical.choose_spec (accepted_assembles heads
    (identityConstants h ∅ 0 1 constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check (computedMethodImageCodes index)
    (image_checked index))).1

theorem unchanged_image_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (index : Fin 4) (different : index ≠ 0) (env : Environment.{u} 4) :
    (imageMeaning h heads constants index).value env = env index := by
  have assembled := image_assembles h heads constants index
  simp only [computedMethodImageCodes, computedMethodSubstitution, if_neg different] at assembled
  exact agrees_with_type_expressions heads (identityConstants h ∅ 0 1 constants)
    (.var : Code 4) (.var index)
    (subst computedMethodSubstitution (Intrinsic.contextAXPD.lookup index))
    (imageMeaning h heads constants index) rfl assembled env

/-- The computed method is an identity application only on the admitted
domain of its retained function formation. No beta value law is asserted
outside that set. -/
theorem computed_image_value_of_domain (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (formed : Meaning.{u} 4) (domain : Value.{u} 4)
    (atFormation : assemble heads (identityConstants h ∅ 0 1 constants)
      functionProposal.2 identityFunctionType (.head functionLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (env : Environment.{u} 4) (inside : env 0 ∈ domain env) :
    (imageMeaning h heads constants 0).value env = env 0 := by
  have atResult := image_assembles h heads constants 0
  have atBody : assemble heads (identityConstants h ∅ 0 1 constants)
      (.var : Code 5) (.var 0) (rename wk methodType) =
      some (.plain (fun environment => environment 0) : Meaning.{u} 5) := rfl
  have atArgument : assemble heads (identityConstants h ∅ 0 1 constants)
      (.var : Code 4) (.var 0) methodType =
      some (.plain (fun environment => environment 0) : Meaning.{u} 4) := rfl
  have atComputed : assemble heads (identityConstants h ∅ 0 1 constants)
      computedMethodCode computedMethod methodType =
      some (imageMeaning h heads constants 0) := by
    rw [substituted_method_type] at atResult
    simpa [computedMethodImageCodes, computedMethodSubstitution]
      using atResult
  have value := application_lambda_value heads (identityConstants h ∅ 0 1 constants)
    functionLevel methodType (rename wk methodType) (.var 0) (.var 0)
    functionProposal.2 (.var : Code 4) (.var : Code 5)
    formed (.plain (fun environment => environment 0))
    (imageMeaning h heads constants 0) (.plain (fun environment => environment 0))
    domain atFormation atDomain atBody atArgument atComputed env inside
  simpa [Meaning.plain, ZFSetTypeExpressionInterpretation.extend] using value

theorem method_domain_value (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (formed : Meaning.{u} 4) (domain : Value.{u} 4)
    (atFormation : assemble heads (identityConstants h ∅ 0 1 constants)
      functionProposal.2 identityFunctionType (.head functionLevel) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (env : Environment.{u} 4) :
    domain env = ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h ∅ 0 1 constants) methodType method_supported env := by
  obtain ⟨uLevel, vLevel, domainCode, bodyCode, extracted, _, _, _, _⟩ :=
    functionProposal.2.piFormation_checked IntrinsicRelator.rules
      NativeRelatorConversionChecking.check function_formation_checked
  obtain ⟨domainMeaning, bodyMeaning, atDomainMeaning, _, _, domainEquals⟩ :=
    assemble_piFormation heads (identityConstants h ∅ 0 1 constants)
      functionProposal.2 extracted atFormation
  rw [atDomain] at domainEquals
  cases Option.some.inj domainEquals
  exact agrees_with_type_expressions heads (identityConstants h ∅ 0 1 constants)
    domainCode methodType (.head uLevel) domainMeaning method_supported atDomainMeaning env

theorem universe_method_in_domain (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) 0 ∈
      ZFSetTypeExpressionInterpretation.interpret heads
        (identityConstants h ∅ 0 1 constants) methodType method_supported
        (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
  change (ZFSetTraceIdentityDeclaration.Controls.universeMethod h).1 ∈
    ZFSetTraceProducts.traceApp
      (ZFSetTraceProducts.traceApp
        (ZFSetTraceIdentityDeclaration.Controls.universeMotive h).1
        (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h).1)
      (ZFSetTraceIdentityDeclaration.reflValue
        (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h)
        (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h)).1
  rw [← ZFSetTraceIdentityDeclaration.motiveAt_value
    (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h)
    (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h)
    (ZFSetTraceIdentityDeclaration.Controls.universeMotive h)
    (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h)
    (ZFSetTraceIdentityDeclaration.reflValue
      (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h)
      (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h))]
  exact (ZFSetTraceIdentityDeclaration.Controls.universeMethod h).2

/-- Every image denotes the original value at the typed universe environment,
including the method image that is an actual beta-redex. -/
theorem universe_image_environment_eq (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    imageEnvironment (imageMeaning h heads constants)
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
      ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h := by
  obtain ⟨formed, atFormation, domainExists⟩ := accepted_assembles heads
    (identityConstants h ∅ 0 1 constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check functionProposal.2 function_formation_checked
  obtain ⟨domain, atDomain⟩ := domainExists methodType (rename wk methodType) rfl
  let env := ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h
  have inside : env 0 ∈ domain env := by
    rw [method_domain_value h heads constants formed domain atFormation atDomain env]
    exact universe_method_in_domain h heads constants
  have computed : (imageMeaning h heads constants 0).value env = env 0 :=
    computed_image_value_of_domain h heads constants formed domain
      atFormation atDomain env inside
  funext index
  change (imageMeaning h heads constants index).value env = env index
  by_cases isZero : index = 0
  · subst index
    exact computed
  · exact unchanged_image_value h heads constants index isZero env

/-- The computed-image admission predicate really contains the previously
constructed typed universe environment; it is not an empty-domain device. -/
theorem universe_environment_admitted (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide)
      (imageEnvironment (imageMeaning h heads constants)
        (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h)) := by
  let env := ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h
  have original : AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide) env := by
    exact ⟨Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h,
      ZFSetTraceIdentityDeclaration.Controls.zeroPoint h,
      ZFSetTraceIdentityDeclaration.Controls.universeMotive h,
      ZFSetTraceIdentityDeclaration.Controls.universeMethod h,
      rfl, rfl, rfl, rfl⟩
  change AdmittedJArguments h ∅ 0 1 heads constants
    (.var 3) (.var 2) (.var 1) (.var 0)
    (by decide) (by decide) (by decide) (by decide)
    (imageEnvironment (imageMeaning h heads constants) env)
  rw [universe_image_environment_eq h heads constants]
  exact original

def admissibleTargetEnvironment (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 4) : Prop :=
  AdmittedJArguments h ∅ 0 1 heads constants
    (.var 3) (.var 2) (.var 1) (.var 0)
    (by decide) (by decide) (by decide) (by decide)
    (imageEnvironment (imageMeaning h heads constants) env)

/-- The independent comparison requires agreement only at the method slot,
plus admission of the left image to J's actual set codes. The other image
components are not equated by this predicate. -/
def independentTargetEnvironment (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} 4) : Prop :=
  (imageMeaning h heads constants 0).value env = env 0 ∧
    AdmittedJArguments h ∅ 0 1 heads constants
      (.var 3) (.var 2) (.var 1) (.var 0)
      (by decide) (by decide) (by decide) (by decide)
      (imageEnvironment (imageMeaning h heads constants) env)

theorem universe_independent_target (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    independentTargetEnvironment h heads constants
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
  have fixed := universe_image_environment_eq h heads constants
  have admitted := universe_environment_admitted h heads constants
  exact ⟨congrFun fixed 0, admitted⟩

def identityReturnedCode : Code 4 :=
  NativeJudgmentReplay.substitute ids identityImageCodes
    Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
    ZFSetReplayDeclaredJAgreement.returnedReceipt.2

theorem identity_returned_code_eq_original :
    identityReturnedCode = ZFSetReplayDeclaredJAgreement.returnedReceipt.2 := by
  exact NativeJudgmentReplay.substitute_ids
    ZFSetReplayDeclaredJAgreement.returned_accepted

/-- J's checked source uses the computed method image, while its returned
method uses a different checked substitution with variable image codes.
The two transformed programs agree on every independently admitted target
environment. The source certificate, target certificate and both telescope
checks remain explicit in the generic theorem used here. -/
theorem independent_method_j_agrees (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode) = true ∧
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
      ZFSetReplayDeclaredJAgreement.contextCode identityReturnedCode = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants) identityReturnedCode
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType = some resultAfter ∧
      ∀ env, independentTargetEnvironment h heads constants env →
        sourceAfter.value env = resultAfter.value env := by
  have result := checked_j_iota_independent_substitutions h ∅ 0 1 heads constants
    Intrinsic.contextAXPD ZFSetReplayDeclaredJAgreement.contextCode
    Intrinsic.contextAXPD ZFSetReplayDeclaredJAgreement.contextCode
    (.var 3) (.var 2) (.var 1) (.var 0) Intrinsic.identityIotaResultType
    (by decide) (by decide) (by decide) (by decide)
    ZFSetReplayDeclaredJAgreement.sourceCode ZFSetReplayDeclaredJAgreement.returnedReceipt.2
    ZFSetReplayDeclaredJAgreement.proposal_accepted
    ZFSetReplayDeclaredJAgreement.returned_accepted
    ZFSetReplayDeclaredJAgreement.context_formed
    computedMethodSubstitution ids computedMethodImageCodes identityImageCodes
    computed_method_images_check identity_images_check
    (imageMeaning h heads constants) identityImageMeaning
    (image_assembles h heads constants) (identity_image_assembles h heads constants)
    (independentTargetEnvironment h heads constants)
    (by
      intro env admitted
      apply interpret_imageEnvironment_eq_of_freeVariables
        heads (identityConstants h ∅ 0 1 constants)
        (.var 0) (by decide) (imageMeaning h heads constants) identityImageMeaning env
      intro index free
      have atMethod : index = 0 := by simpa [Tm.freeVariables] using free
      subst index
      exact admitted.1)
    (by intro _ admitted; exact admitted.2)
  exact result

/-- The method supplied to J is now an actual beta-redex. All four image
certificates check as one dependent telescope, the substituted J source and
returned method both check, and their assembled values agree on admissible
target environments. -/
theorem computed_method_j_agrees (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode) = true ∧
    NativeJudgmentReplay.check Intrinsic.contextAXPD
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      ZFSetReplayDeclaredJAgreement.contextCode
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.returnedReceipt.2) = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
        (subst computedMethodSubstitution Intrinsic.identityIotaRight)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some resultAfter ∧
      ∀ env, admissibleTargetEnvironment h heads constants env →
        sourceAfter.value env = resultAfter.value env := by
  exact checked_j_iota_substitute h ∅ 0 1 heads constants
    Intrinsic.contextAXPD ZFSetReplayDeclaredJAgreement.contextCode
    Intrinsic.contextAXPD ZFSetReplayDeclaredJAgreement.contextCode
    (.var 3) (.var 2) (.var 1) (.var 0) Intrinsic.identityIotaResultType
    (by decide) (by decide) (by decide) (by decide)
    ZFSetReplayDeclaredJAgreement.sourceCode ZFSetReplayDeclaredJAgreement.returnedReceipt.2
    ZFSetReplayDeclaredJAgreement.proposal_accepted
    ZFSetReplayDeclaredJAgreement.returned_accepted
    ZFSetReplayDeclaredJAgreement.context_formed
    computedMethodSubstitution computedMethodImageCodes computed_method_images_check
    (imageMeaning h heads constants) (image_assembles h heads constants)
    (admissibleTargetEnvironment h heads constants) (by intro env admitted; exact admitted)

theorem computed_method_is_not_variable : computedMethod ≠ (.var 0 : Tower.Tm 4) := by
  decide

theorem independent_substitutions_differ : computedMethodSubstitution ≠ ids := by
  intro same
  have atMethod := congrFun same (0 : Fin 4)
  exact computed_method_is_not_variable (by simpa [computedMethodSubstitution, ids] using atMethod)

/-- The selected J root is transported with the actual checked substitution.
The returned endpoint is the computed method, not an invented normal form. -/
theorem computed_method_j_executes :
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD
      ZFSetReplayDeclaredJAgreement.contextCode
      (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode)
      [.root (NativeRelatorRootConversionCode.substitute computedMethodSubstitution
        NativeRelatorRootConversionCode.Examples.identityCode)] = true := by
  decide +kernel

theorem untransported_j_root_rejected :
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD
      ZFSetReplayDeclaredJAgreement.contextCode
      (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode)
      [.root NativeRelatorRootConversionCode.Examples.identityCode] = false := by
  decide +kernel

/-- At the explicitly inhabited universe environment, the two certified
programs obtained by substituting a computed method have equal set values.
The source and result assemblies remain the exact transformed receipts. -/
theorem computed_method_j_universe_values (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
        (subst computedMethodSubstitution Intrinsic.identityIotaRight)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some resultAfter ∧
      sourceAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
        resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) := by
  obtain ⟨_, _, sourceAfter, resultAfter, atSource, atResult, agree⟩ :=
    computed_method_j_agrees h heads constants
  refine ⟨sourceAfter, resultAfter, atSource, atResult, ?_⟩
  apply agree
  change AdmittedJArguments h ∅ 0 1 heads constants
    (.var 3) (.var 2) (.var 1) (.var 0)
    (by decide) (by decide) (by decide) (by decide)
    (imageEnvironment (imageMeaning h heads constants)
      (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h))
  exact universe_environment_admitted h heads constants

/-- The returned computed method still denotes the actual two-element type
code, rather than merely agreeing with an unknown J source value. -/
theorem computed_return_is_two_code (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (resultAfter : Meaning.{u} 4)
    (atResultAfter : assemble heads (identityConstants h ∅ 0 1 constants)
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some resultAfter) :
    resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
      (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 := by
  obtain ⟨_, original, _, atOriginal, _, originalValue, _⟩ :=
    ZFSetReplayDeclaredJAgreement.checked_j_source_and_result_agree h heads constants
  have originalChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD
      Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
      ZFSetReplayDeclaredJAgreement.returnedReceipt.2 = true := by
    have accepted := ZFSetReplayDeclaredJAgreement.returned_accepted
    change checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
      Intrinsic.contextAXPD Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
      ZFSetReplayDeclaredJAgreement.contextCode
      ZFSetReplayDeclaredJAgreement.returnedReceipt.2 = true at accepted
    simp only [checkJudgment, Bool.and_eq_true] at accepted
    exact accepted.2
  obtain ⟨transported, atTransported, valueTransport, _⟩ :=
    assemble_substitute
      NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
      heads (identityConstants h ∅ 0 1 constants) IntrinsicRelator.rules
      NativeRelatorConversionChecking.check
      ZFSetReplayDeclaredJAgreement.returnedReceipt.2 original
      originalChecked atOriginal computedMethodSubstitution computedMethodImageCodes
      (imageMeaning h heads constants) (image_assembles h heads constants)
  change assemble heads (identityConstants h ∅ 0 1 constants)
      (ZFSetReplayDeclaredJAgreement.returnedReceipt.2.substitute
        NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
        computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType)
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some resultAfter
    at atResultAfter
  rw [atResultAfter] at atTransported
  cases Option.some.inj atTransported
  rw [valueTransport, universe_image_environment_eq h heads constants]
  exact originalValue

/-- The independently substituted J result uses the original checked method
certificate. Its denotation is the actual two-element set code. -/
theorem independent_return_is_two_code (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (resultAfter : Meaning.{u} 4)
    (atResultAfter : assemble heads (identityConstants h ∅ 0 1 constants)
      identityReturnedCode Intrinsic.identityIotaRight
      Intrinsic.identityIotaResultType = some resultAfter) :
    resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
      (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 := by
  obtain ⟨_, original, _, atOriginal, _, originalValue, _⟩ :=
    ZFSetReplayDeclaredJAgreement.checked_j_source_and_result_agree h heads constants
  rw [identity_returned_code_eq_original] at atResultAfter
  rw [atOriginal] at atResultAfter
  cases Option.some.inj atResultAfter
  exact originalValue

/-- Two distinct checked substitution routes meet at a computed J source:
the left method is a beta-redex, the right method is an independently checked
variable. At the inhabited universe environment, the checked J root executes
and both assembled results denote the same two-element set code. -/
theorem checked_independent_method_j_square (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD
      ZFSetReplayDeclaredJAgreement.contextCode
      (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode)
      [.root (NativeRelatorRootConversionCode.substitute computedMethodSubstitution
        NativeRelatorRootConversionCode.Examples.identityCode)] = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        identityReturnedCode Intrinsic.identityIotaRight
        Intrinsic.identityIotaResultType = some resultAfter ∧
      sourceAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
        (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 ∧
      resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
        (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 := by
  refine ⟨computed_method_j_executes, ?_⟩
  obtain ⟨_, _, sourceAfter, resultAfter, atSource, atResult, agree⟩ :=
    independent_method_j_agrees h heads constants
  have target := universe_independent_target h heads constants
  have resultValue := independent_return_is_two_code h heads constants resultAfter atResult
  exact ⟨sourceAfter, resultAfter, atSource, atResult,
    (agree _ target).trans resultValue, resultValue⟩

/-- One artifact connects a non-identity dependent substitution, checked
native J execution, the retained returned certificate, and the constructed
set code. The `CofinalInaccessibles` model strength remains explicit. -/
theorem checked_computed_method_j_square (h : CofinalInaccessibles.{u})
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD
      ZFSetReplayDeclaredJAgreement.contextCode
      (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
      (subst computedMethodSubstitution Intrinsic.identityIotaResultType)
      (subst computedMethodSubstitution Intrinsic.identityIotaRight)
      (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
        ZFSetReplayDeclaredJAgreement.sourceCode)
      [.root (NativeRelatorRootConversionCode.substitute computedMethodSubstitution
        NativeRelatorRootConversionCode.Examples.identityCode)] = true ∧
    ∃ sourceAfter resultAfter,
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.sourceCode)
        (subst computedMethodSubstitution Intrinsic.identityIotaLeft)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some sourceAfter ∧
      assemble heads (identityConstants h ∅ 0 1 constants)
        (NativeJudgmentReplay.substitute computedMethodSubstitution computedMethodImageCodes
          Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
          ZFSetReplayDeclaredJAgreement.returnedReceipt.2)
        (subst computedMethodSubstitution Intrinsic.identityIotaRight)
        (subst computedMethodSubstitution Intrinsic.identityIotaResultType) = some resultAfter ∧
      sourceAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
        (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 ∧
      resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) =
        (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 ∧
      resultAfter.value (ZFSetTraceIdentityTypeInterpretation.Controls.universeEnvironment h) ≠ ∅ := by
  refine ⟨computed_method_j_executes, ?_⟩
  obtain ⟨sourceAfter, resultAfter, atSource, atResult, agree⟩ :=
    computed_method_j_universe_values h heads constants
  have resultValue := computed_return_is_two_code h heads constants resultAfter atResult
  refine ⟨sourceAfter, resultAfter, atSource, atResult, agree.trans resultValue, resultValue, ?_⟩
  rw [resultValue]
  intro empty
  have member : (∅ : ZFSet.{u}) ∈
      (Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls.twoCode h).1 :=
    ZFSetDependentProducts.Controls.empty_mem_two
  rw [empty] at member
  exact ZFSet.notMem_empty _ member

end Controls

#print axioms checked_j_iota_independent_substitutions
#print axioms checked_j_iota_substitute
#print axioms Controls.computed_method_checks
#print axioms Controls.computed_method_images_check
#print axioms Controls.computed_method_j_agrees
#print axioms Controls.independent_method_j_agrees
#print axioms Controls.universe_independent_target
#print axioms Controls.computed_method_is_not_variable
#print axioms Controls.independent_substitutions_differ
#print axioms Controls.computed_method_j_executes
#print axioms Controls.untransported_j_root_rejected
#print axioms Controls.computed_method_j_universe_values
#print axioms Controls.computed_return_is_two_code
#print axioms Controls.independent_return_is_two_code
#print axioms Controls.checked_independent_method_j_square
#print axioms Controls.checked_computed_method_j_square

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJSubstitution
