import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-! # Concrete instances and controls for TelescopeAbstraction -/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TelescopeAbstraction

def identityContext (level : LevelExpr Nat) : Tower.Ctx 2 :=
  .snoc (.snoc .nil (sortTm level)) (.var 0)

/-- An actual dependent identity body, not a theorem-existence replacement. -/
def identityType (level : LevelExpr Nat) : Tower.Tm 0 :=
  closeType (identityContext level) (.var 1)

def identityTerm (level : LevelExpr Nat) : Tower.Tm 0 :=
  closeTerm (identityContext level) (.var 0)

theorem identity_typed (level : LevelExpr Nat) :
    Tower.HasType .nil (identityTerm level) (identityType level) := by
  apply close_typed
  simpa [identityContext, Ctx.lookup_snoc_zero, rename, wk] using
    (HasType.var (R := Tower.rules) (Γ := identityContext level) 0)

theorem identity_type_formed (level : LevelExpr Nat) :
    Tower.HasType .nil (identityType level)
      (sortTm (.max (.succ level) (.max level level))) := by
  apply HasType.piForm (u := .sort (.succ level)) (v := .sort (.max level level))
  · exact .headType (.sort level)
  · exact .sort _
  · apply HasType.piForm (u := .sort level) (v := .sort level)
    · exact .var 0
    · exact .sort _
    · exact .var 1
    · exact .sort _
    · exact .sorts _ _
  · exact .sort _
  · exact .sorts _ _

private def zero : LevelExpr Nat := .const 0
private def one : LevelExpr Nat := .succ zero
private def two : LevelExpr Nat := .succ one

private def specialization : Sub Tower.Head 2 0 :=
  consSub (sortTm zero) (consSub (sortTm one) (renSub Fin.elim0))

@[simp] private theorem specialization_newest : specialization 0 = sortTm zero := rfl
@[simp] private theorem specialization_prior : specialization 1 = sortTm one := rfl

theorem specialization_typed :
    Presentation.CtxMor Tower.rules (identityContext two) .nil specialization := by
  apply Presentation.CtxMor.extend
  · apply Presentation.CtxMor.extend
    · intro index
      exact Fin.elim0 index
    · exact .headType (.sort one)
  · exact .headType (.sort zero)

theorem specialization_executes :
    BetaSteps
      (.app (.app (identityTerm two) (sortTm one)) (sortTm zero))
      (sortTm zero) := by
  simpa [applyClosed, identityContext, identityTerm, closeTerm,
    liftClosed_zero, subst] using
    (applyClosed_beta (identityContext two) specialization (.var 0))

theorem specialization_checked :
    Tower.HasType .nil
      (.app (.app (identityTerm two) (sortTm one)) (sortTm zero))
      (sortTm one) := by
  simpa [applyClosed, identityContext, liftClosed_zero, subst] using
    (applyClosed_typed specialization_typed
      (show HasType Tower.rules .nil (liftClosed (identityTerm two))
        (liftClosed (identityType two)) by
          simpa only [liftClosed_zero] using identity_typed two))

/-- The result is the inner value argument, not the outer type argument. -/
theorem specialization_does_not_return_type_argument :
    (subst specialization (.var 0) : Tower.Tm 0) ≠ sortTm one := by
  intro equality
  cases equality


#print axioms identity_type_formed
#print axioms specialization_typed
#print axioms specialization_checked
#print axioms specialization_executes
#print axioms specialization_does_not_return_type_argument

end TelescopeAbstraction
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
