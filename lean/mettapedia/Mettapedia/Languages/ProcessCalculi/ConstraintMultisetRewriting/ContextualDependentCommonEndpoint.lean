import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopeConsequence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEndpointInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSelectionCompatibility

/-!
# An equation forces recovery over the common parameter context

For normal typed endpoints in the rigid-constant profile, equality after
two variable inclusions forces both the value and its annotation to use
only common parameters. A successful selection of those parameters then
recovers the entire typed endpoint, without a caller-supplied smaller type.

This theorem concerns a witnessed endpoint equality. It does not replace
metavariables in an unsolved problem or discard inhabitation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCommonEndpoint

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentNormalObservations
open ContextualDependentSupport ContextualDependentTypedInversion ContextualDependentEta
open ContextualDependentScopeConsequence

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include rigid complete in
theorem common_type_parameters_forced {n k m : Nat} (left : Ren n m) (right : Ren k m)
    {Γ : Ctx Head m} (formed : CtxFormed S.R Γ) (first : Tm Head n) (second : Tm Head k)
    (same : TypeEq S.R Γ (Presentation.rename left first) (Presentation.rename right second))
    (firstNormal : Normal (S := S) first) (secondNormal : Normal (S := S) second) :
    ∀ index ∈ second.support, commonMask left right index = true := by
  have support := ContextualDependentNormalSupport.typeEq_support rigid complete formed same
    (normal_rename rigid left firstNormal) (normal_rename rigid right secondNormal)
  rw [support_rename, support_rename] at support
  intro index present
  apply (commonMask_iff left right index).mpr
  have imagePresent : right index ∈ second.support.image right :=
    Finset.mem_image.mpr ⟨index, present, rfl⟩
  rw [← support] at imagePresent
  obtain ⟨other, _, image⟩ := Finset.mem_image.mp imagePresent
  exact ⟨other, image⟩

include rigid complete in
theorem endpoint_parameters_forced {leftContext rightContext ambient : Context S.R}
    (left : Inclusion leftContext ambient) (right : Inclusion rightContext ambient)
    (first : TotalTerm leftContext) (second : TotalTerm rightContext)
    (same : (frames S.levels).E (first.reindex left.hom) (second.reindex right.hom))
    (firstTypeNormal : Normal (S := S) first.1.code) (firstValueNormal : Normal (S := S) first.2.code)
    (secondTypeNormal : Normal (S := S) second.1.code) (secondValueNormal : Normal (S := S) second.2.code) :
    ∀ index ∈ second.1.code.support ∪ second.2.code.support, commonMask left.forward right.forward index = true := by
  have types := same.1
  have values := same.2
  change TypeEq S.R ambient.raw (subst (renSub left.forward) first.1.code)
    (subst (renSub right.forward) second.1.code) at types
  change Equal S.R ambient.raw (subst (renSub left.forward) first.2.code)
    (subst (renSub right.forward) second.2.code) (subst (renSub left.forward) first.1.code) at values
  simp only [subst_renSub] at types values
  intro index present
  rcases Finset.mem_union.mp present with inType | inValue
  · exact common_type_parameters_forced rigid complete left.forward right.forward ambient.formed
      first.1.code second.1.code types firstTypeNormal secondTypeNormal index inType
  · exact common_parameters_forced rigid complete left.forward right.forward ambient.formed
      first.2.code second.2.code _ values firstValueNormal secondValueNormal index inValue

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include rigid complete facts roots heads algebra headTypingUnique declared in
theorem selected_recovery_forced {leftContext rightContext ambient : Context S.R}
    (left : Inclusion leftContext ambient) (right : Inclusion rightContext ambient)
    (first : TotalTerm leftContext) (second : TotalTerm rightContext)
    (same : (frames S.levels).E (first.reindex left.hom) (second.reindex right.hom))
    (firstTypeNormal : Normal (S := S) first.1.code) (firstValueNormal : Normal (S := S) first.2.code)
    (secondTypeNormal : Normal (S := S) second.1.code) (secondValueNormal : Normal (S := S) second.2.code)
    (selection : ContextualDependentPruning.Selection rightContext (commonMask left.forward right.forward))
    (compatible : CtxRen selection.source.raw rightContext.raw selection.inclusion.forward) :
    (ContextualDependentEndpointInversion.recover facts roots heads algebra headTypingUnique complete declared
      (root_reflection rigid) selection.inclusion compatible second secondTypeNormal secondValueNormal).isSome = true := by
  apply (ContextualDependentEndpointInversion.success_iff_support facts roots heads algebra headTypingUnique
    complete declared (root_reflection rigid) selection.inclusion compatible second secondTypeNormal secondValueNormal).mpr
  intro index present
  exact (selection.image index).mpr (endpoint_parameters_forced rigid complete left right first second same
    firstTypeNormal firstValueNormal secondTypeNormal secondValueNormal index present)

end ContextualDependentCommonEndpoint
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
