import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextIntersection

/-!
# A recovered common endpoint factors both sides of the equation

Typed endpoint equality reflects exact variable inclusions. Combining this
reflection with the commuting intersection square turns recovery from one
side into a common typed value for both sides. Uniqueness here is typed
endpoint equality, not a claim of unique unifier factor substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionRecovery

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentEta ContextualDependentScopeConsequence
open ContextualDependentNormalSelection ContextualDependentContextIntersection

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra reflects complete in
theorem reindex_reflects {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (first second : TotalTerm source)
    (same : (frames S.levels).E (first.reindex inclusion.hom) (second.reindex inclusion.hom)) :
    (frames S.levels).E first second := by
  have types := same.1
  have values := same.2
  change TypeEq S.R target.raw (subst (renSub inclusion.forward) first.1.code)
    (subst (renSub inclusion.forward) second.1.code) at types
  change Equal S.R target.raw (subst (renSub inclusion.forward) first.2.code)
    (subst (renSub inclusion.forward) second.2.code) (subst (renSub inclusion.forward) first.1.code) at values
  simp only [subst_renSub] at types values
  have sourceTypes := ContextualDependentStrengthening.typeEq_reflects facts roots heads algebra reflects complete
    inclusion.injective compatible source.formed target.formed first.1.isType second.1.isType types
  exact ⟨sourceTypes, ContextualDependentStrengthening.equal_reflects facts roots heads algebra reflects complete
    inclusion.injective compatible source.formed target.formed first.2.typed
    (Typed.convType second.2.typed sourceTypes.symm) values⟩

variable {leftContext rightContext ambient : Context S.R}
  (left : Inclusion leftContext ambient) (right : Inclusion rightContext ambient)
  (leftCompatible : CtxRen leftContext.raw ambient.raw left.forward)
  (rightCompatible : CtxRen rightContext.raw ambient.raw right.forward)
  (selection : Selected rightContext (commonMask left.forward right.forward))

theorem hom_square :
    left.hom ≫ (leftInclusion left right leftCompatible rightCompatible selection).hom =
      right.hom ≫ selection.inclusion.hom := by
  apply Hom.ext
  funext index
  change Tm.var (left.forward ((leftInclusion left right leftCompatible rightCompatible selection).forward index)) =
    Tm.var (right.forward (selection.inclusion.forward index))
  exact congrArg Tm.var (square left right leftCompatible rightCompatible selection index)

include facts roots heads algebra reflects complete in
theorem recovered_left (first : TotalTerm leftContext) (second : TotalTerm rightContext)
    (same : (frames S.levels).E (first.reindex left.hom) (second.reindex right.hom))
    (recovered : ContextualDependentEndpointInversion.Recovered selection.inclusion second) :
    (frames S.levels).E
      (recovered.value.reindex (leftInclusion left right leftCompatible rightCompatible selection).hom) first := by
  apply reindex_reflects facts roots heads algebra reflects complete left leftCompatible
  have compared := (frames S.levels).preserves right.hom recovered.solves
  change (frames S.levels).E ((recovered.value.reindex selection.inclusion.hom).reindex right.hom)
    (second.reindex right.hom) at compared
  rw [← reindex_comp, ← hom_square left right leftCompatible rightCompatible selection, reindex_comp] at compared
  exact ((frames S.levels).equivalence ambient).trans compared (((frames S.levels).equivalence ambient).symm same)

include facts roots heads algebra reflects complete in
theorem common_endpoint_unique (first second : TotalTerm selection.source)
    (sameRight : (frames S.levels).E (first.reindex selection.inclusion.hom) (second.reindex selection.inclusion.hom)) :
    (frames S.levels).E first second :=
  reindex_reflects facts roots heads algebra reflects complete selection.inclusion selection.compatible first second sameRight

end ContextualDependentIntersectionRecovery
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
