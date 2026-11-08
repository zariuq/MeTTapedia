import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSubtypeReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengthening

/-!
# Checking certificates for independently typed normal inputs

Normal terms replay the existing complete kernel typing relation in the
CheckingAlgorithm relation used by executable certificates. The redex case
is excluded by normality, rather than by narrowing the original typed input.
Normal body recovery can therefore transport a checking certificate through
an exact context inclusion without a second bounded checker search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCheckingReplay

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (complete : AlgorithmicComplete S.R S.roles)

include facts algebra headTypingUnique complete in
theorem kernel_replay {mode : Mode} {n : Nat} {Γ : Ctx Head n} {term type : Tm Head n}
    (proof : KernelTyping S.R S.roles mode Γ term type) :
    CtxFormed S.R Γ → Normal (S := S) term → CheckingAlgorithm S.R mode Γ term type := by
  induction proof with
  | var index => intros; exact .var index
  | const declared _ _ => intros; exact .const declared
  | head typed => intros; exact .head typed
  | @pi n Γ domain domainType body bodyType first second level domainSynth firstRed firstUniverse
      bodySynth secondRed secondUniverse join ihDomain ihBody =>
      intro formed normal
      have domainTyped := (Synth.principal facts algebra headTypingUnique domainSynth formed).1
      have domainFormed : IsType S.R Γ domain := ⟨first, firstUniverse, Typed.convType domainTyped firstRed.typeEq⟩
      exact .pi (ihDomain formed (fun _ step => normal _ (.congPiDom step))) firstRed.red.reduces firstUniverse
        (ihBody (.snoc formed domainFormed) (fun _ step => normal _ (.congPiCod step)))
        secondRed.red.reduces secondUniverse join
  | @sigma n Γ domain domainType body bodyType first second level domainSynth firstRed firstUniverse
      bodySynth secondRed secondUniverse join ihDomain ihBody =>
      intro formed normal
      have domainTyped := (Synth.principal facts algebra headTypingUnique domainSynth formed).1
      have domainFormed : IsType S.R Γ domain := ⟨first, firstUniverse, Typed.convType domainTyped firstRed.typeEq⟩
      exact .sigma (ihDomain formed (fun _ step => normal _ (.congSigmaDom step))) firstRed.red.reduces firstUniverse
        (ihBody (.snoc formed domainFormed) (fun _ step => normal _ (.congSigmaCod step)))
        secondRed.red.reduces secondUniverse join
  | id _ red universeWitness _ _ ihCarrier ihFirst ihSecond =>
      intro formed normal
      exact .id (ihCarrier formed (fun _ step => normal _ (.congIdTy step))) red.red.reduces universeWitness
        (ihFirst formed (fun _ step => normal _ (.congIdLeft step)))
        (ihSecond formed (fun _ step => normal _ (.congIdRight step)))
  | refl _ _ ih =>
      intro formed normal
      exact .refl (ih formed (fun _ step => normal _ (.congRefl step)))
  | app _ red _ ihFunction ihArgument =>
      intro formed normal
      exact .app (ihFunction formed (fun _ step => normal _ (.congAppFun step))) red.red.reduces
        (ihArgument formed (fun _ step => normal _ (.congAppArg step)))
  | fst _ red ih =>
      intro formed normal
      exact .fst (ih formed (fun _ step => normal _ (.congFst step))) red.red.reduces
  | snd _ red ih =>
      intro formed normal
      exact .snd (ih formed (fun _ step => normal _ (.congSnd step))) red.red.reduces
  | redex =>
      intro formed normal
      exact False.elim (normal _ (.betaPi _ _))
  | lamCheck red _ ih =>
      intro formed normal
      have domainFormed := (IsType.pi_parts red.targetType).1
      exact .lamCheck red.red.reduces (ih (.snoc formed domainFormed) (fun _ step => normal _ (.congLam step)))
  | pairCheck red _ _ ihFirst ihSecond =>
      intro formed normal
      exact .pairCheck red.red.reduces
        (ihFirst formed (fun _ step => normal _ (.congPairFst step)))
        (ihSecond formed (fun _ step => normal _ (.congPairSnd step)))
  | reflCheck red _ firstSame secondSame ih =>
      intro formed normal
      exact .reflCheck red.red.reduces (ih formed (fun _ step => normal _ (.congRefl step)))
        (Equal.algorithm (S := S) complete firstSame formed)
        (Equal.algorithm (S := S) complete secondSame formed)
  | switch _ below ih =>
      intro formed normal
      have types := Below.isTypes (S := S) below formed
      exact .switch (ih formed normal)
        (ContextualDependentSubtypeReplay.below_replay facts algebra complete formed types.1 types.2 below)

include facts algebra headTypingUnique complete in
theorem normal_certificate {n : Nat} {Γ : Ctx Head n} {term type : Tm Head n}
    (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ term type) (normal : Normal (S := S) term) :
    CheckingAlgorithm S.R .check Γ term type :=
  kernel_replay facts algebra headTypingUnique complete
    (normal_checked facts algebra headTypingUnique formed typed normal) formed normal

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)

include facts algebra headTypingUnique complete roots heads declared reflects in
theorem normal_typing_reflects {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (body : Tm Head source.arity)
    (typed : Typed S.R target.raw (Presentation.rename inclusion.forward body)
      (Presentation.rename inclusion.forward type.code))
    (normal : Normal (S := S) (Presentation.rename inclusion.forward body)) :
    Typed S.R source.raw body type.code :=
  ContextualDependentStrengthening.checked_body_typed facts roots heads algebra reflects declared
    inclusion compatible type body
    (normal_certificate facts algebra headTypingUnique complete target.formed typed normal)

/-- A typed normal endpoint supplies the certificate needed by strengthening.
Only syntax inversion executes; there is no smaller-context checker budget. -/
def recover_normal {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (value : Term target (type.reindex inclusion.hom)) (normal : Normal (S := S) value.code) :
    Option (Recovery inclusion type value.code) :=
  ContextualDependentStrengthening.recover facts roots heads algebra reflects declared inclusion compatible type value.code
    (normal_certificate facts algebra headTypingUnique complete target.formed (by
      have typed := value.typed
      change Typed S.R target.raw value.code (subst (renSub inclusion.forward) type.code) at typed
      rwa [subst_renSub] at typed) normal)

theorem recover_normal_code {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (value : Term target (type.reindex inclusion.hom)) (normal : Normal (S := S) value.code)
    {body : Tm Head source.arity}
    (found : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) value.code = some body) :
    (recover_normal facts algebra headTypingUnique complete roots heads declared reflects
      inclusion compatible type value normal).map (fun recovered => recovered.body.code) = some body :=
  ContextualDependentStrengthening.recover_code facts roots heads algebra reflects declared
    inclusion compatible type value.code _ found

end ContextualDependentCheckingReplay
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
