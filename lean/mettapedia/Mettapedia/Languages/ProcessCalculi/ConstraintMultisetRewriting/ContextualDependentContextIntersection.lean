import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentVariableFactorization

/-!
# The computed common context is a typed variable intersection

A selection of the common parameter mask embeds into both argument
contexts. Compatible variable inclusions into those contexts with equal
ambient images factor through the selection, uniquely. The factor is
computed by finite lookup and preserves declaration types exactly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentContextIntersection

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentScopeConsequence
open ContextualDependentNormalSelection

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

def ofCompatible {source target : Context S.R} (rho : Ren source.arity target.arity)
    (injective : Function.Injective rho) (compatible : CtxRen source.raw target.raw rho) : Inclusion source target where
  forward := rho
  injective := injective
  typed := by
    intro index
    change Typed S.R target.raw (.var (rho index)) (subst (renSub rho) (Ctx.lookup source.raw index))
    rw [subst_renSub, ← compatible index]
    exact .var _

theorem inclusion_ext {source target : Context S.R} {first second : Inclusion source target}
    (same : first.forward = second.forward) : first = second := by
  cases first
  cases second
  cases same
  rfl

variable {leftContext rightContext ambient : Context S.R}
  (left : Inclusion leftContext ambient) (right : Inclusion rightContext ambient)
  (leftCompatible : CtxRen leftContext.raw ambient.raw left.forward)
  (rightCompatible : CtxRen rightContext.raw ambient.raw right.forward)
  (selection : Selected rightContext (commonMask left.forward right.forward))

def ambientInclusion : Inclusion selection.source ambient :=
  ofCompatible (fun index => right.forward (selection.inclusion.forward index))
    (right.injective.comp selection.inclusion.injective) (CtxRen.comp selection.compatible rightCompatible)

theorem ambient_compatible : CtxRen selection.source.raw ambient.raw
    (ambientInclusion left right rightCompatible selection).forward := by
  intro index
  change Ctx.lookup ambient.raw (right.forward (selection.inclusion.forward index)) =
    Presentation.rename (fun position => right.forward (selection.inclusion.forward position)) (Ctx.lookup selection.source.raw index)
  rw [rightCompatible, selection.compatible, rename_comp]

theorem insideLeft (index : Fin selection.source.arity) :
    ∃ prior, left.forward prior = right.forward (selection.inclusion.forward index) :=
  (commonMask_iff left.forward right.forward _).mp ((selection.image _).mp ⟨index, rfl⟩)

def leftInclusion : Inclusion selection.source leftContext :=
  ContextualDependentVariableFactorization.inclusion left (ambientInclusion left right rightCompatible selection)
    (insideLeft left right selection) leftCompatible (ambient_compatible left right rightCompatible selection)

theorem left_compatible : CtxRen selection.source.raw leftContext.raw
    (leftInclusion left right leftCompatible rightCompatible selection).forward :=
  ContextualDependentVariableFactorization.factor_compatible left.forward _ (insideLeft left right selection)
    left.injective leftCompatible (ambient_compatible left right rightCompatible selection)

theorem square (index : Fin selection.source.arity) :
    left.forward ((leftInclusion left right leftCompatible rightCompatible selection).forward index) =
      right.forward (selection.inclusion.forward index) :=
  ContextualDependentVariableFactorization.factor_image left.forward _ (insideLeft left right selection) index

variable {source : Context S.R} (toLeft : Inclusion source leftContext) (toRight : Inclusion source rightContext)
  (toRightCompatible : CtxRen source.raw rightContext.raw toRight.forward)
  (commutes : ∀ index, left.forward (toLeft.forward index) = right.forward (toRight.forward index))

include toLeft commutes in
theorem insideRight (index : Fin source.arity) : ∃ prior, selection.inclusion.forward prior = toRight.forward index :=
  (selection.image _).mpr ((commonMask_iff left.forward right.forward _).mpr ⟨toLeft.forward index, commutes index⟩)

def coneFactor : Inclusion source selection.source :=
  ContextualDependentVariableFactorization.inclusion selection.inclusion toRight
    (insideRight left right selection toLeft toRight commutes) selection.compatible toRightCompatible

theorem factor_compatible : CtxRen source.raw selection.source.raw
    (coneFactor left right selection toLeft toRight toRightCompatible commutes).forward :=
  ContextualDependentVariableFactorization.factor_compatible selection.inclusion.forward toRight.forward
    (insideRight left right selection toLeft toRight commutes) selection.inclusion.injective selection.compatible toRightCompatible

theorem factor_right (index : Fin source.arity) :
    selection.inclusion.forward ((coneFactor left right selection toLeft toRight toRightCompatible commutes).forward index) =
      toRight.forward index :=
  ContextualDependentVariableFactorization.factor_image selection.inclusion.forward toRight.forward
    (insideRight left right selection toLeft toRight commutes) index

theorem factor_left (index : Fin source.arity) :
    (leftInclusion left right leftCompatible rightCompatible selection).forward
      ((coneFactor left right selection toLeft toRight toRightCompatible commutes).forward index) = toLeft.forward index := by
  apply left.injective
  rw [square, factor_right]
  exact (commutes index).symm

theorem factor_unique (other : Inclusion source selection.source)
    (rightImage : ∀ index, selection.inclusion.forward (other.forward index) = toRight.forward index) :
    other = coneFactor left right selection toLeft toRight toRightCompatible commutes := by
  have maps := ContextualDependentVariableFactorization.factor_unique selection.inclusion.forward toRight.forward
    (insideRight left right selection toLeft toRight commutes) selection.inclusion.injective other.forward rightImage
  exact inclusion_ext maps

include toRightCompatible commutes in
/-- The other cone leg need not carry an additional compatibility premise:
the right leg and the ambient commuting square already determine it. -/
theorem universal : ∃! factor : Inclusion source selection.source,
    (∀ index, (leftInclusion left right leftCompatible rightCompatible selection).forward (factor.forward index) =
      toLeft.forward index) ∧
    (∀ index, selection.inclusion.forward (factor.forward index) = toRight.forward index) := by
  refine ⟨coneFactor left right selection toLeft toRight toRightCompatible commutes,
    ⟨factor_left left right leftCompatible rightCompatible selection toLeft toRight toRightCompatible commutes,
     factor_right left right selection toLeft toRight toRightCompatible commutes⟩, ?_⟩
  intro other images
  exact factor_unique left right selection toLeft toRight toRightCompatible commutes other images.2

end ContextualDependentContextIntersection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
