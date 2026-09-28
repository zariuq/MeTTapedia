import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayNeutralCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation

/-!
# Computation against independently supplied reduct certificates

Certificate instantiation computes one particular typing tree for a beta
reduct. Neutral-elimination coherence compares it with any independently
supplied qualifying tree for the same reduct. Thus the semantic computation
law no longer requires the consumer to use the reducer's particular tree.
Pair projections use the same comparison with their component certificates.
For a dependent second projection, the displayed source and reduct types
are different substitutions into the family; value agreement does not assert
conversion between these two type expressions.

Membership of the argument in the lambda's retained domain is explicit.
Neither global semantic typing nor unrestricted conversion soundness is an
assumption hidden in this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]

/-- The source is an actual checked beta redex; the target certificate is
independent of the certificate-instantiation algorithm. Its qualification is
finite and syntactic, while the argument-domain premise is semantic. -/
theorem application_lambda_normal_reduct_value
    (context : Ctx Head n) (level : Head) (A : Tm Head n) (B body : Tm Head (n + 1))
    (argument : Tm Head n) (formation argumentCode : Code Head NoConversion n)
    (bodyCode : Code Head NoConversion (n + 1)) (targetCode : Code Head NoConversion n)
    (formed arg result target : Meaning.{u} n) (bodyMeaning : Meaning.{u} (n + 1))
    (domain : Value.{u} n)
    (sourceAccepted : check R noConversionCheck context (.app (.lam body) argument)
      (inst0 argument B) (.appElim A B (.lamIntro level formation bodyCode) argumentCode) = true)
    (targetAccepted : check R noConversionCheck context (inst0 argument body)
      (inst0 argument B) targetCode = true)
    (normal : targetCode.neutralEliminations (inst0 argument body) (inst0 argument B) = true)
    (atFormation : assemble heads constants formation (.pi A B) (.head level) = some formed)
    (atDomain : formed.productDomain? = some domain)
    (atBody : assemble heads constants bodyCode body B = some bodyMeaning)
    (atArgument : assemble heads constants argumentCode argument A = some arg)
    (atResult : assemble heads constants
      (.appElim A B (.lamIntro level formation bodyCode) argumentCode)
      (.app (.lam body) argument) (inst0 argument B) = some result)
    (atTarget : assemble heads constants targetCode (inst0 argument body) (inst0 argument B) = some target)
    (environment : Environment.{u} n) (inside : arg.value environment ∈ domain environment) :
    result.value environment = target.value environment := by
  simp only [check, Bool.and_eq_true] at sourceAccepted
  have computedAccepted := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) sourceAccepted.1.1.2 sourceAccepted.1.2
  obtain ⟨computed, atComputed, computation⟩ :=
    application_lambda_instantiated_value heads constants noConversionRename noConversionSubstitute
      R noConversionCheck context level A B body argument formation argumentCode bodyCode
      formed arg result bodyMeaning domain sourceAccepted.1.1.2 atFormation atDomain atBody
      atArgument atResult environment inside
  have comparison := assemble_neutralEliminations_coherent heads constants R targetCode
    targetAccepted normal atTarget computedAccepted atComputed (EqualOrHeads.refl _)
  exact computation.trans (congrArg (fun meaning => meaning.value environment) comparison.symm)

#print axioms application_lambda_normal_reduct_value

/-- First projection agrees with an independently checked qualifying
certificate for the first component, not only the pair's retained subtree. -/
theorem first_pair_normal_reduct_value
    (context : Ctx Head n) (level : Head) (A x y : Tm Head n) (B : Tm Head (n + 1))
    (formation firstCode secondCode targetCode : Code Head NoConversion n)
    (first second result target : Meaning.{u} n)
    (sourceAccepted : check R noConversionCheck context (.fst (.pair x y)) A
      (.fstElim B (.pairIntro level formation firstCode secondCode)) = true)
    (targetAccepted : check R noConversionCheck context x A targetCode = true)
    (normal : targetCode.neutralEliminations x A = true)
    (atFirst : assemble heads constants firstCode x A = some first)
    (atSecond : assemble heads constants secondCode y (inst0 x B) = some second)
    (atResult : assemble heads constants (.fstElim B (.pairIntro level formation firstCode secondCode))
      (.fst (.pair x y)) A = some result)
    (atTarget : assemble heads constants targetCode x A = some target)
    (environment : Environment.{u} n) : result.value environment = target.value environment := by
  simp only [check, Bool.and_eq_true] at sourceAccepted
  have comparison := assemble_neutralEliminations_coherent heads constants R targetCode
    targetAccepted normal atTarget sourceAccepted.1.2 atFirst (EqualOrHeads.refl _)
  exact (first_pair_value heads constants level A x y B formation firstCode secondCode
    first second result atFirst atSecond atResult environment).trans
      (congrArg (fun meaning => meaning.value environment) comparison.symm)

/-- Second projection agrees with a qualifying certificate for the second
component at `B[x]`. The source displays `B[fst (pair x y)]`; no syntactic
identification or unproved conversion of these dependent result types is used. -/
theorem second_pair_normal_reduct_value
    (context : Ctx Head n) (level : Head) (A x y : Tm Head n) (B : Tm Head (n + 1))
    (formation firstCode secondCode targetCode : Code Head NoConversion n)
    (first second result target : Meaning.{u} n)
    (sourceAccepted : check R noConversionCheck context (.snd (.pair x y))
      (inst0 (.fst (.pair x y)) B)
      (.sndElim A B (.pairIntro level formation firstCode secondCode)) = true)
    (targetAccepted : check R noConversionCheck context y (inst0 x B) targetCode = true)
    (normal : targetCode.neutralEliminations y (inst0 x B) = true)
    (atFirst : assemble heads constants firstCode x A = some first)
    (atSecond : assemble heads constants secondCode y (inst0 x B) = some second)
    (atResult : assemble heads constants (.sndElim A B (.pairIntro level formation firstCode secondCode))
      (.snd (.pair x y)) (inst0 (.fst (.pair x y)) B) = some result)
    (atTarget : assemble heads constants targetCode y (inst0 x B) = some target)
    (environment : Environment.{u} n) : result.value environment = target.value environment := by
  simp only [check, Bool.and_eq_true] at sourceAccepted
  have comparison := assemble_neutralEliminations_coherent heads constants R targetCode
    targetAccepted normal atTarget sourceAccepted.1.2 atSecond (EqualOrHeads.refl _)
  exact (second_pair_value heads constants level A x y B formation firstCode secondCode
    first second result atFirst atSecond atResult environment).trans
      (congrArg (fun meaning => meaning.value environment) comparison.symm)

#print axioms first_pair_normal_reduct_value
#print axioms second_pair_normal_reduct_value

/-- Substitution of a first-projection redex or its component into any
checked family produces checked formation certificates with equal set values.
These are the actual certificate-instantiation outputs. This validates the
dependent result-type computation for these trees, without adding a
conversion rule or comparing arbitrary certificates for the two types. -/
theorem first_pair_family_values
    (context : Ctx Head n) (level familyLevel : Head)
    (A x y : Tm Head n) (B family : Tm Head (n + 1))
    (formation firstCode secondCode : Code Head NoConversion n)
    (familyCode : Code Head NoConversion (n + 1))
    (first second projected : Meaning.{u} n) (familyMeaning : Meaning.{u} (n + 1))
    (sourceAccepted : check R noConversionCheck context (.fst (.pair x y)) A
      (.fstElim B (.pairIntro level formation firstCode secondCode)) = true)
    (familyAccepted : check R noConversionCheck (.snoc context A) family
      (.head familyLevel) familyCode = true)
    (atFirst : assemble heads constants firstCode x A = some first)
    (atSecond : assemble heads constants secondCode y (inst0 x B) = some second)
    (atProjection : assemble heads constants (.fstElim B (.pairIntro level formation firstCode secondCode))
      (.fst (.pair x y)) A = some projected)
    (atFamily : assemble heads constants familyCode family (.head familyLevel) = some familyMeaning) :
    let sourceCode := Code.instantiate noConversionRename noConversionSubstitute
      family (.head familyLevel) (.fst (.pair x y)) familyCode
      (.fstElim B (.pairIntro level formation firstCode secondCode))
    let targetCode := Code.instantiate noConversionRename noConversionSubstitute
      family (.head familyLevel) x familyCode firstCode
    check R noConversionCheck context (inst0 (.fst (.pair x y)) family)
        (.head familyLevel) sourceCode = true ∧
      check R noConversionCheck context (inst0 x family) (.head familyLevel) targetCode = true ∧
      ∃ source target,
        assemble heads constants sourceCode (inst0 (.fst (.pair x y)) family)
          (.head familyLevel) = some source ∧
        assemble heads constants targetCode (inst0 x family) (.head familyLevel) = some target ∧
        source.value = target.value := by
  have firstAccepted : check R noConversionCheck context x A firstCode = true := by
    simp only [check, Bool.and_eq_true] at sourceAccepted
    exact sourceAccepted.1.2
  have sourceChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) familyAccepted sourceAccepted
  have targetChecked := Code.instantiate_checked noConversionRename noConversionSubstitute
    R noConversionCheck (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible) familyAccepted firstAccepted
  obtain ⟨source, atSource, sourceValues⟩ :=
    assemble_instantiate noConversionRename noConversionSubstitute heads constants R noConversionCheck
      familyCode (.fstElim B (.pairIntro level formation firstCode secondCode))
      familyMeaning projected familyAccepted atFamily atProjection
  obtain ⟨target, atTarget, targetValues⟩ :=
    assemble_instantiate noConversionRename noConversionSubstitute heads constants R noConversionCheck
      familyCode firstCode familyMeaning first familyAccepted atFamily atFirst
  refine ⟨sourceChecked, targetChecked, source, target, atSource, atTarget, ?_⟩
  funext environment
  rw [sourceValues, targetValues, first_pair_value heads constants level A x y B
    formation firstCode secondCode first second projected atFirst atSecond atProjection environment]

#print axioms first_pair_family_values

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
