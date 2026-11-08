import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCommonEndpoint

/-!
# Common parameters form a dependent context

Exact declaration compatibility forces the intersection of two variable
images to retain every declaration dependency. On normal input contexts,
the common context is therefore computed without a checker budget. A
witnessed equality of normal endpoints then computes the recovered endpoint
over that common context, including its dependent annotation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCommonSelection

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentTypedInversion ContextualDependentEta
open ContextualDependentScopeConsequence ContextualDependentNormalSelection

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem common_closed {n k m : Nat} {leftContext : Ctx Head n} {rightContext : Ctx Head k}
    {ambient : Ctx Head m} (left : Ren n m) (right : Ren k m)
    (leftCompatible : CtxRen leftContext ambient left) (rightCompatible : CtxRen rightContext ambient right) :
    Closed rightContext (commonMask left right) := by
  intro index retained dependency present
  obtain ⟨other, image⟩ := (commonMask_iff left right index).mp retained
  have types : Presentation.rename left (Ctx.lookup leftContext other) =
      Presentation.rename right (Ctx.lookup rightContext index) := by
    rw [← leftCompatible, ← rightCompatible, image]
  have support := congrArg Tm.support types
  rw [ContextualDependentSupport.support_rename, ContextualDependentSupport.support_rename] at support
  have dependencyPresent : right dependency ∈ (Ctx.lookup rightContext index).support.image right :=
    Finset.mem_image.mpr ⟨dependency, present, rfl⟩
  rw [← support] at dependencyPresent
  obtain ⟨original, _, same⟩ := Finset.mem_image.mp dependencyPresent
  exact (commonMask_iff left right dependency).mpr ⟨original, same⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)

def selectCommon {leftContext rightContext ambient : Context S.R}
    (left : Inclusion leftContext ambient) (right : Inclusion rightContext ambient)
    (leftCompatible : CtxRen leftContext.raw ambient.raw left.forward)
    (rightCompatible : CtxRen rightContext.raw ambient.raw right.forward)
    (normal : NormalContext (S := S) rightContext.raw) :
    Selected rightContext (commonMask left.forward right.forward) :=
  (ContextualDependentNormalSelection.select facts roots heads algebra headTypingUnique complete declared reflects
    rightContext.raw rightContext.formed normal (commonMask left.forward right.forward)).get
      (select_of_closed facts roots heads algebra headTypingUnique complete declared reflects
        rightContext.raw rightContext.formed normal _ (common_closed left.forward right.forward leftCompatible rightCompatible))

variable (rigid : ∀ name, S.roles name = .rigid)

def recoverCommon {leftContext rightContext ambient : Context S.R}
    (left : Inclusion leftContext ambient) (right : Inclusion rightContext ambient)
    (leftCompatible : CtxRen leftContext.raw ambient.raw left.forward)
    (rightCompatible : CtxRen rightContext.raw ambient.raw right.forward)
    (contextNormal : NormalContext (S := S) rightContext.raw)
    (first : TotalTerm leftContext) (second : TotalTerm rightContext)
    (same : (frames S.levels).E (first.reindex left.hom) (second.reindex right.hom))
    (firstTypeNormal : Normal (S := S) first.1.code) (firstValueNormal : Normal (S := S) first.2.code)
    (secondTypeNormal : Normal (S := S) second.1.code) (secondValueNormal : Normal (S := S) second.2.code) :
    let selection := selectCommon facts roots heads algebra headTypingUnique complete declared (root_reflection rigid)
      left right leftCompatible rightCompatible contextNormal
    ContextualDependentEndpointInversion.Recovered selection.inclusion second :=
  let selection := selectCommon facts roots heads algebra headTypingUnique complete declared (root_reflection rigid)
    left right leftCompatible rightCompatible contextNormal
  (ContextualDependentEndpointInversion.recover facts roots heads algebra headTypingUnique complete declared
    (root_reflection rigid) selection.inclusion selection.compatible second secondTypeNormal secondValueNormal).get
      (ContextualDependentCommonEndpoint.selected_recovery_forced rigid complete facts roots heads algebra headTypingUnique
        declared left right first second same firstTypeNormal firstValueNormal secondTypeNormal secondValueNormal
        selection.toSelection selection.compatible)

end ContextualDependentCommonSelection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
