import Mettapedia.Languages.Agda.Structural.AdministrativeConsGeneration
import Mettapedia.Languages.Agda.Structural.AdministrativeSpineLinearization

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.BetaPreparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm RawTy RawContext TypeParameter TypeBody TermBody)

noncomputable def betaOfComponents {n : Nat} {Γ : RawContext n} {body : TermBody n}
    {input output : RawTy n} {argument : RawTm n} {rest : Spine (scope n)}
    (headTyped : CoreDerivation (Statics.typed Γ body.lambda input))
    (lambda : LambdaTyping Γ body input) (spine : ConsTyping Γ input argument rest output)
    (domains : CoreDerivation (Statics.typeEqual Γ lambda.domain.code spine.domain.code))
    (codomains : CoreDerivation (Statics.typeEqual (Γ.snoc lambda.domain.code)
      lambda.codomain.open.code spine.codomain.open.code)) :
    CoreDerivation (Statics.termEqual Γ (eliminate body.lambda (cons (apply argument) rest))
      (eliminate (body.instantiate argument) rest) output) := by
  let argumentTyped := Derivation.core (.conversion Γ argument spine.domain.code lambda.domain.code)
    (consEvidence CoreDerivation spine.argumentTyped
      (consEvidence CoreDerivation domains.typeSymmetry (noEvidence CoreDerivation)))
  let beta := Derivation.core (.beta Γ lambda.domain lambda.codomain body argument)
    (consEvidence CoreDerivation lambda.domainFormed
      (consEvidence CoreDerivation lambda.codomainFormed
        (consEvidence CoreDerivation lambda.bodyTyped
          (consEvidence CoreDerivation argumentTyped (noEvidence CoreDerivation)))))
  let substitution := administrativeOperations.singleSubstitution lambda.domainFormed argumentTyped
  have resultTypes := codomains.substitution Γ (Statics.single argument) substitution
  change CoreDerivation (Statics.typeEqual Γ (lambda.codomain.instantiate argument).code
    (spine.codomain.instantiate argument).code) at resultTypes
  let converted := Derivation.core (.equalityConversion Γ (Statics.app body.lambda argument)
    (body.instantiate argument) (lambda.codomain.instantiate argument).code (spine.codomain.instantiate argument).code)
    (consEvidence CoreDerivation beta (consEvidence CoreDerivation resultTypes (noEvidence CoreDerivation)))
  let underTail := Derivation.eliminationCongruence converted (Derivation.spineRefl spine.tail)
  let linearized := CanonizationPreparation.consToNested (spine.conversions.typing headTyped)
    spine.argumentTyped spine.tail
  exact Derivation.core (.transitivity Γ (eliminate body.lambda (cons (apply argument) rest))
    (eliminate (Statics.app body.lambda argument) rest) (eliminate (body.instantiate argument) rest) output)
    (consEvidence CoreDerivation linearized (consEvidence CoreDerivation underTail (noEvidence CoreDerivation)))

noncomputable def piComparison {n : Nat} {Γ : RawContext n} {body : TermBody n}
    {input output : RawTy n} {argument : RawTm n} {rest : Spine (scope n)}
    (lambda : LambdaTyping Γ body input) (spine : ConsTyping Γ input argument rest output) :
    CoreDerivation (Statics.typeEqual Γ (Statics.piType lambda.domain lambda.codomain).code
      (Statics.piType spine.domain spine.codomain).code) :=
  chainEquality (lambda.conversions.append spine.conversions)
    (administrativeOperations.piFormed lambda.domainFormed lambda.codomainFormed)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.BetaPreparation
